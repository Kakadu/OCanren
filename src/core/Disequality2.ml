(*
  Going to implement very naive disequality constraints
  which will be stored internally as disjunction of conjunction (DNF)
*)

open Format

exception Violated

let ( !!! ) = Obj.magic
let use_logging = false
let log fmt = Format.kasprintf (fun s -> if use_logging then Format.printf "%s\n%!" s) fmt

open Term

let is_wc_var v =
  match Term.var v with
  | Some { Var.index = -42 } -> true
  | _ -> false
;;

module type EXTRA = sig
  type t

  open Logic

  val neq : (int, int logic) injected -> (int, int logic) injected -> t -> t option
  val is_interesting_var : Term.Var.t -> t -> bool
end

module Make (FDC : EXTRA) = struct
  module Conjunct = struct
    type t = Subst.Binding.t

    let pp ppf Subst.Binding.{ var; term } =
      Format.fprintf ppf "{ %d -> '%s' }" var.Term.Var.index (Term.show term)
    ;;

    let intersects_with ~set : t -> bool =
     fun c ->
      (* log "set = %a" Term.VarSet.pp set; *)
      let open Subst.Binding in
      let { var; term } = c in
      if Term.VarSet.mem var set
      then true
      else (
        match Term.var term with
        | Some var when Term.VarSet.mem var set -> true
        | _ ->
          (* log "%s %d" __FILE__ __LINE__; *)
          false)
   ;;
  end

  type extra = FDC.t

  module Disjunct : sig
    type t

    val pp : Format.formatter -> t -> unit
    val empty : t
    val is_empty : t -> bool
    val singleton : Var.t -> Obj.t -> t
    val of_bindings : Subst.Binding.t list -> extra -> (t * extra) option
    val intersects_with : set:VarSet.t -> t -> bool
    val conj : t -> t -> t

    val recheck_exn
      :  Env.t
      -> Subst.t
      -> Subst.Binding.t list
      -> extra
      -> t
      -> (t * extra) option

    val extract : t -> Term.Var.t -> Obj.t list
  end = struct
    type t =
      { conjs : Conjunct.t list
      ; wcs : VarSet.t
      }

    let empty = { wcs = VarSet.empty; conjs = [] }

    let is_empty = function
      | { conjs = []; wcs } when VarSet.is_empty wcs -> true
      | _ -> false
    ;;

    let singleton : Term.Var.t -> _ -> t =
     fun var term ->
      if is_wc_var var && is_var term
      then { conjs = []; wcs = VarSet.(add !!!term empty) }
      else if is_wc_var term && is_var var
      then { conjs = []; wcs = VarSet.(add !!!var empty) }
      else { conjs = [ Subst.Binding.{ var; term } ]; wcs = VarSet.empty }
   ;;

    let pp ppf { wcs; conjs } =
      Format.fprintf ppf "[ ";
      Stdlib.List.iter (Conjunct.pp ppf) conjs;
      Format.fprintf ppf " ] {| ";
      VarSet.iteri
        (fun i v ->
          match Term.var v with
          | None -> fprintf ppf "..; "
          | Some v -> fprintf ppf "%d; " v.Term.Var.index)
        wcs;
      Format.fprintf ppf "|}"
    ;;

    let conj : t -> t -> t =
     fun l r -> { wcs = VarSet.union l.wcs r.wcs; conjs = List.append l.conjs r.conjs }
   ;;

    let intersects_with ~set { conjs } =
      (* TODO: should we check wildcard variables ? *)
      let rec helper = function
        | [] -> false
        | c :: ctl -> if Conjunct.intersects_with ~set c then true else helper ctl
      in
      let ans = helper conjs in
      (* log "Disjunct.intersects_with = %b" ans; *)
      ans
    ;;

    let of_bindings bnds extra0 =
      assert (not ([] = bnds));
      try
        Stdlib.List.fold_left
          (fun ({ wcs; conjs }, extra) (Subst.Binding.{ var; term } as bnd) ->
            if Term.Var.is_wildcard var
            then
              if Term.is_var term
              then { conjs; wcs = VarSet.add (Obj.magic term) wcs }, extra
              else { wcs; conjs }, extra
            else (
              (* need to check finite domain constraints too *)
              let checker =
                FDC.is_interesting_var var extra
                ||
                match Term.var term with
                | None -> false
                | Some v when Term.Var.is_wildcard v -> false
                | Some v -> FDC.is_interesting_var var extra
              in
              if not checker
              then { conjs = bnd :: conjs; wcs }, extra
              else (
                match FDC.neq (Obj.magic var) (Obj.magic term) extra with
                | None -> raise Violated
                | Some e -> { conjs = bnd :: conjs; wcs }, e)))
          (empty, extra0)
          bnds
        |> Stdlib.Option.some
      with
      | Violated -> None
    ;;

    let recheck_exn env subst bnds extra { wcs; conjs } =
      let a = List.map (fun { Subst.Binding.var } -> var) conjs in
      let b = List.map (fun { Subst.Binding.term } -> term) conjs in
      (* TODO: implement unification of bindings list *)
      match Subst.unify env subst (Obj.repr a) (Obj.repr b) with
      | None -> None
      | Some ([], _) -> raise Violated
      | Some (bnds, _) -> of_bindings bnds extra
    ;;

    let extract { conjs } v =
      let rec helper acc = function
        | [] -> acc
        | { Subst.Binding.var; Subst.Binding.term } :: ctl ->
          let acc = if Term.Var.equal var v then term :: acc else acc in
          let acc =
            match Term.var term with
            | None -> acc
            | Some v2 when Term.Var.equal v v2 -> Obj.repr var :: acc
          in
          helper acc ctl
      in
      helper [] conjs
    ;;
  end

  type t = Disjunct.t list

  let pp ppf xs =
    printf "All disjuncts (%d)\n%!" (List.length xs);
    Stdlib.List.iteri (fun i x -> fprintf ppf "\t%d: %a\n%!" i Disjunct.pp x) xs
  ;;

  let empty : t = []
  let disj : t -> t -> t = Stdlib.List.append

  let conj : t -> t -> t =
   fun l r ->
    l
    |> Stdlib.List.concat_map (fun (c1 : Disjunct.t) ->
           Stdlib.List.map (fun (c2 : Disjunct.t) -> Disjunct.conj c1 c2) r)
 ;;

  let disequality_of_terms l r : t =
    try
      Term.fold_monoid
        l
        r
        ~fvar:(fun v t -> [ Disjunct.singleton v (Obj.magic t) ])
        ~fk:(fun _ v t -> [ Disjunct.singleton v (Obj.magic t) ])
        ~empty
        ~fval:(fun v1 v2 ->
          (* two non-boxed values that are not equal *)
          empty)
        ~join:Stdlib.List.append
    with
    | Term.Different_shape (_, _) -> empty
  ;;

  let ( >>=? ) : 'a 'b. 'a option -> ('a -> 'b option) -> 'b option = Stdlib.Option.bind

  let add env subst cstrs l r extra =
    (* printf "add: %s %d\n%!" __FILE__ __LINE__; *)
    match Subst.unify env subst l r with
    | None -> Some (cstrs, extra)
    | Some ([], _) ->
      (* easily violated *)
      None
    | Some (bnds, _subst) ->
      (match cstrs with
      | [] ->
        (Disjunct.of_bindings bnds extra >>=? fun (d, extra) -> Some ([ d ], extra)
          : (t * extra) option)
      | cstrs ->
        Disjunct.of_bindings bnds extra
        >>=? fun (d, extra) ->
        let ans = Stdlib.List.map Disjunct.(conj d) cstrs in
        (* Format.printf "all disjuncts: %a\n%!" pp ans; *)
        Some (ans, extra))
  ;;

  let recheck env subst cs bnds extra =
    (* For every disjunct we try to simplify it using [bnds]. If it simplifies to empty disjunct, then we simplify it to False.
    If all disjuncts has been simpifies to False, then constraint is violated *)
    let simplify =
      let rec helper extra acc = function
        | [] -> acc
        | hc :: tlc ->
          let (_ : Disjunct.t) = hc in
          (* Format.printf "got a disjunct: %a\n%!" Disjunct.pp hc; *)
          let rez = Disjunct.recheck_exn env subst bnds extra hc in
          (match rez with
          | None -> helper extra acc tlc
          | Some (d, extra) ->
            (* We have an updated disjunct *)
            helper extra (d :: acc) tlc)
      in
      helper extra []
    in
    try
      match cs with
      | [] -> Some ([], extra)
      | _ ->
        (match simplify cs with
        | [] -> raise Violated
        | newc -> Some (newc, extra))
    with
    | Violated -> None
  ;;

  let merge_disjoint _ = assert false

  module Answer = struct
    type t = Disjunct.t

    let extract d v =
      (* Format.printf "Extracting from %a\n%!" Disjunct.pp d; *)
      Disjunct.extract d v
    ;;

    let subsumed _env c1 c2 = false
  end

  let vars_in_term =
    let rec helper acc x =
      if Obj.is_block x
      then (
        match Term.var x with
        | Some v -> Term.VarSet.add v acc
        | None ->
          let sz = Obj.size x in
          let rec inner acc i =
            if i >= sz then acc else inner (helper acc (Obj.field x i)) (1 + i)
          in
          inner acc 0)
      else acc
    in
    fun root -> helper Term.VarSet.empty (Obj.repr root)
  ;;

  let reify env subst cs t =
    (* log "reify: %s %d" __FILE__ __LINE__; *)
    (* Format.printf "all : %a\n%!" pp cs; *)
    let t = Subst.reify env subst t in
    let vars = vars_in_term t in
    List.filter_map
      (fun d -> if Disjunct.intersects_with ~set:vars d then Some d else None)
      cs
  ;;
end

(** *******************  tests ***************************  *)
module _ = struct
  open Make (struct
    type t

    let neq _ _ _ = assert false
    let is_interesting_var _ _ = assert false
  end)

  let make_var i = Obj.magic (Term.Var.make ~env:0 ~scope:Term.Var.non_local_scope i)

  let%expect_test _ =
    let v1 = make_var 1 in
    Format.printf "%a" pp (disequality_of_terms v1 v1);
    [%expect {xxx|
      All disjuncts (1)
      	0: [ { 1 -> '_.1' } ] {| |}
    |xxx}]
  ;;

  let%expect_test _ =
    let v1 = make_var 1 in
    let v2 = make_var 2 in
    Format.printf "%a" pp (disequality_of_terms !!!(1, 2) !!!(v1, v2));
    [%expect
      {xxx|
      All disjuncts (2)
      	0: [ { 1 -> 'int<1>' } ] {| |}
      	1: [ { 2 -> 'int<2>' } ] {| |}
    |xxx}]
  ;;

  let%expect_test _ =
    let v1 = make_var 1 in
    let v2 = make_var 2 in
    Format.printf "%a" pp (disequality_of_terms !!!(1, v1) !!!(2, v2));
    [%expect {xxx|
      All disjuncts (1)
      	0: [ { 1 -> '_.2' } ] {| |}
    |xxx}]
  ;;

  let%expect_test _ =
    let v1 = make_var 1 in
    let v2 = make_var 2 in
    Format.printf "%a" pp (disequality_of_terms !!!(1, v1) !!!(2, v2));
    [%expect {xxx|
      All disjuncts (1)
      	0: [ { 1 -> '_.2' } ] {| |}
    |xxx}]
  ;;

  let%expect_test _ =
    let v1 = make_var 1 in
    let v2 = make_var 2 in
    let v3 = make_var 3 in
    let v4 = make_var 4 in
    let d1 = disequality_of_terms !!!(1, 2) !!!(v1, v2) in
    Format.printf "%a\n" pp d1;
    let d2 = disequality_of_terms !!!(3, 4) !!!(v3, v4) in
    Format.printf "%a\n" pp d2;
    let d3 = conj d1 d2 in
    Format.printf "%a" pp d3;
    [%expect
      {xxx|
      All disjuncts (2)
      	0: [ { 1 -> 'int<1>' } ] {| |}
      	1: [ { 2 -> 'int<2>' } ] {| |}

      All disjuncts (2)
      	0: [ { 3 -> 'int<3>' } ] {| |}
      	1: [ { 4 -> 'int<4>' } ] {| |}

      All disjuncts (4)
      	0: [ { 1 -> 'int<1>' }{ 3 -> 'int<3>' } ] {| |}
      	1: [ { 1 -> 'int<1>' }{ 4 -> 'int<4>' } ] {| |}
      	2: [ { 2 -> 'int<2>' }{ 3 -> 'int<3>' } ] {| |}
      	3: [ { 2 -> 'int<2>' }{ 4 -> 'int<4>' } ] {| |}
    |xxx}]
  ;;
end
