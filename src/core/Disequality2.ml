(*
  Going to implement very naive disequality constraints
  which will be stored internally as disjunction of conjunction (DNF)
*)

open Format

exception Violated

let ( !!! ) = Obj.magic
let use_logging = true
let use_logging = false

let log fmt =
  if use_logging
  then Format.kasprintf (fun s -> Format.printf "%s\n%!" s) fmt
  else Format.ifprintf Format.std_formatter fmt
;;

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

let rec a_la_cartesian = function
  | [] -> [ [] ]
  | [] :: xs ->
    (* Important for filteering unneeded results.*)
    (* Not a feature of cartesion product *)
    a_la_cartesian xs
  | x :: xs ->
    let xs = a_la_cartesian xs in
    List.concat_map (fun x -> List.map (fun xs -> x :: xs) xs) x
;;

module SS = Streaming.Stream

let rec a_la_cartesian_seq : 'a. 'a SS.t list -> 'a SS.t list = function
  | [] -> List.cons SS.empty []
  | e :: xs when SS.is_empty e ->
    (* Important for filteering unneeded results.*)
    (* Not a feature of cartesion product *)
    a_la_cartesian_seq xs
  | x :: xs ->
    let xs = a_la_cartesian_seq xs in
    SS.flat_map (fun x -> List.map (SS.prepend x) xs |> SS.of_list) x |> SS.to_list
;;

let%test _ =
  let ans = a_la_cartesian [ [ 1; 2 ]; [ 3; 4 ] ] in
  ans = [ [ 1; 3 ]; [ 1; 4 ]; [ 2; 3 ]; [ 2; 4 ] ]
;;

let%test _ =
  let ans =
    a_la_cartesian_seq [ SS.of_list [ 1; 2 ]; SS.of_list [ 3; 4 ] ] |> List.map SS.to_list
  in
  print_endline @@ GT.show GT.list (GT.show GT.list @@ GT.show GT.int) ans;
  ans = [ [ 1; 3 ]; [ 1; 4 ]; [ 2; 3 ]; [ 2; 4 ] ]
;;

let cartesian2 ~f l l' = List.concat_map (fun e -> List.map (f e) l') l

let%test _ =
  let ans = cartesian2 ~f:(sprintf "%d%d") [ 1; 2 ] [ 3; 4 ] in
  ans = [ "13"; "14"; "23"; "24" ]
;;

module _ = struct
  module type ttt = sig
    type 'a t

    val return : 'a -> 'a t
    val bind : ('a -> 'b t) -> 'a t -> 'b t
    val map : ('a -> 'b) -> 'a t -> 'b t
    val head : 'a t -> 'a option
    val rest : 'a t -> 'a t
    val cons : 'a -> 'a t -> 'a t
    val empty : 'a t
  end

  module Cartesian (CNT : ttt) = struct
    (* let cartesian2 ~f l l' = X.bind (fun e -> X.map (f e) l') l *)
    let rec cartesian : 'a. 'a CNT.t CNT.t -> 'a CNT.t CNT.t =
     fun xss ->
      match CNT.head xss with
      | None -> CNT.cons CNT.empty CNT.empty
      (* | [] -> List.cons SS.empty [] *)
      | Some h when CNT.head h = None ->
        (* Important for filteering unneeded results.*)
        (* Not a feature of cartesion product *)
        cartesian (CNT.rest xss)
        (* | e :: xs when SS.is_empty e -> a_la_cartesian_seq xs *)
      | Some x ->
        let xs = cartesian (CNT.rest xss) in
        CNT.bind (fun x -> CNT.map (CNT.cons x) xs) x
   ;;
    (*
      | x :: xs ->
        let xs = a_la_cartesian_seq xs in
        SS.flat_map (fun x -> List.map (SS.prepend x) xs |> SS.of_list) x |> SS.to_list
        *)
  end

  module ExtList = struct
    include List

    let empty = []
    let rest = List.tl

    let head = function
      | x :: _ -> Some x
      | _ -> None
    ;;

    let bind = concat_map
    let return x = [ x ]
  end

  let%test _ =
    let module M = Cartesian (ExtList) in
    let ans = M.cartesian [ [ 1; 2 ]; [ 3; 4 ] ] in
    ans = [ [ 1; 3 ]; [ 1; 4 ]; [ 2; 3 ]; [ 2; 4 ] ]
  ;;

  module ExtStream = struct
    include Streaming.Stream

    let cons = prepend
    let return = yield
    let head = first
    let bind = flat_map
    let ( !! ) = of_list
  end

  let%test _ =
    let module M = Cartesian (ExtStream) in
    let open ExtStream in
    let ans = M.cartesian !![ !![ 1; 2 ]; !![ 3; 4 ] ] in
    to_list (map to_list ans) = [ [ 1; 3 ]; [ 1; 4 ]; [ 2; 3 ]; [ 2; 4 ] ]
  ;;
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

    val of_bindings
      :  Subst.Binding.t list
      -> extra
      -> (t * extra, [ `ToRemove | `Violated ]) Result.t

    val intersects_with : set:VarSet.t -> t -> bool
    val conj : t -> t -> t

    val recheck_exn
      :  Env.t
      -> Subst.t
      -> Subst.Binding.t list
      -> extra
      -> t
      -> (t list * extra) option

    val extract : t -> Term.Var.t -> Obj.t list
  end = struct
    module LLL = struct
      include List

      let empty = []

      let is_empty = function
        | [] -> true
        | _ :: _ -> false
      ;;
    end

    type t =
      { conjs : Conjunct.t LLL.t
      ; wcs : VarSet.t
      }

    let empty = { wcs = VarSet.empty; conjs = LLL.empty }
    let is_empty { conjs; wcs } = LLL.is_empty conjs && VarSet.is_empty wcs

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

    type sort =
      | VarNTerm of Term.Var.t * Obj.t
      | WcNVar of Term.Var.t
      | WcNSmth of Obj.t

    let classify Subst.Binding.{ var; term } =
      let () = log "%s %d" __FILE__ __LINE__ in
      match Term.var term with
      | None ->
        let () = log "%s %d" __FILE__ __LINE__ in
        if Term.Var.is_wildcard var
        then WcNSmth term
        else (* let () = log "%s %d" __FILE__ __LINE__ in *)
          VarNTerm (var, term)
      | Some v2 ->
        let () = log "%s %d" __FILE__ __LINE__ in
        (match Term.Var.(is_wildcard var, is_wildcard v2) with
        | true, true -> failwith "We should not get two wildcards from unification"
        | false, false ->
          log "%s %d" __FILE__ __LINE__;
          VarNTerm (var, term)
        | false, true -> WcNVar var
        | true, false -> WcNVar v2)
    ;;

    let of_bindings bnds extra0 =
      assert ([] <> bnds);
      let exception ToRemove in
      try
        Stdlib.List.fold_left
          (fun ({ wcs; conjs }, extra) bnd ->
            log "%d %a" __LINE__ Subst.pp_binding_list [ bnd ];
            match classify bnd with
            | WcNVar var when FDC.is_interesting_var var extra ->
              log "is interesting";
              { wcs = VarSet.add var wcs; conjs }, extra
            | WcNVar var ->
              (* no domain spec., so domain is infinited => violated *)
              raise ToRemove
            | WcNSmth term ->
              log "WcNSmth";
              { wcs; conjs }, extra
            | VarNTerm (var, term) ->
              log "VarNTerm";
              (* need to check finite domain constraints too *)
              (match FDC.neq (Obj.magic var) (Obj.magic term) extra with
              | None -> raise Violated
              | Some e ->
                let __ _ =
                  log
                    "Successfully added new  FD constraint %s=/=%s"
                    (Term.show !!!var)
                    (Term.show term)
                in
                { conjs = Subst.Binding.{ var; term } :: conjs; wcs }, e))
          (empty, extra0)
          bnds
        |> Stdlib.Result.ok
      with
      | ToRemove -> Stdlib.Result.error `ToRemove
      | Violated -> Stdlib.Result.error `Violated
    ;;

    let recheck_exn env subst _bnds extra { wcs; conjs } =
      (* For every conjunct we should check that this conjuct is a sensible constraint.
         For every wildcard variable we should check that they could be inhabited. (but let's implement it later)
         Some changes
      *)
      log "recheck_exn of %a" pp { wcs; conjs };
      try
        let conjs =
          List.map
            (fun { Subst.Binding.var; term } ->
              log "In current subst var is '%a'" Term.pp (Subst.reify env subst var);
              match Subst.unify env subst (Obj.repr var) (Obj.repr term) with
              | None ->
                log "%s %d" __FILE__ __LINE__;
                []
              | Some ([], _) ->
                log "%s %d" __FILE__ __LINE__;
                raise Violated
              | Some (bnds, _) ->
                log "%s %d" __FILE__ __LINE__;
                log "bnds = %a" Subst.pp_binding_list bnds;
                log
                  "lefting as is: %s =/= %s"
                  (Term.show @@ Obj.repr var)
                  (Term.show @@ Obj.repr term);
                (* TODO: what if we would rewrite a disjunct here ??? *)
                bnds)
            conjs
        in
        Some (List.map (fun conjs -> { wcs; conjs }) (a_la_cartesian conjs), extra)
      with
      | Violated -> None
    ;;

    (* let a = List.map (fun { Subst.Binding.var } -> var) conjs in
      let b = List.map (fun { Subst.Binding.term } -> term) conjs in
      (* TODO: implement unification of bindings list *)
      match Subst.unify env subst (Obj.repr a) (Obj.repr b) with
      | None ->
        log "%s %d unification failed" __FILE__ __LINE__;
        log "  conjs = %a" pp { wcs; conjs };
        None
      | Some ([], _) -> raise Violated
      | Some (bnds, _) -> of_bindings bnds extra *)

    let extract { conjs } v =
      let rec helper acc = function
        | [] -> acc
        | { Subst.Binding.var; Subst.Binding.term } :: ctl ->
          let acc = if Term.Var.equal var v then term :: acc else acc in
          let acc =
            match Term.var term with
            | Some v2 when Term.Var.equal v v2 -> Obj.repr var :: acc
            | _ -> acc
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

  let is_empty = function
    | [] -> true
    | _ -> false
  ;;

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

  let of_bindings : Subst.Binding.t list -> extra -> (t * extra) option =
   fun xs e ->
    try
      List.fold_left
        (fun (acc, e) b ->
          match Disjunct.of_bindings [ b ] e with
          | Result.Ok (d, e) -> d :: acc, e
          | Result.Error `Violated -> raise Violated
          | Result.Error `ToRemove -> acc, e)
        ([], e)
        xs
      |> Stdlib.Option.some
    with
    | Violated -> None
 ;;

  let add env subst cstrs l r extra =
    log
      "add: '%a' and '%a' on  %s %d"
      Term.pp
      (Obj.repr l)
      Term.pp
      (Obj.repr r)
      __FILE__
      __LINE__;
    match Subst.unify env subst l r with
    | None -> Some (cstrs, extra)
    | Some ([], _) ->
      (* easily violated *)
      log "violated";
      None
    | Some (bnds, _subst) ->
      log "%d %a" __LINE__ Subst.pp_binding_list bnds;
      (match cstrs with
      | [] -> (of_bindings bnds extra : (t * extra) option)
      | cstrs ->
        log "%s %d" __FILE__ __LINE__;
        of_bindings bnds extra
        >>=? fun (d, extra) ->
        let (_ : t) = d in
        let (_ : t) = cstrs in
        (* let ans = Stdlib.List.map Disjunct.(conj d) cstrs in *)
        (* let (_ : t) = a_la_cartesian [ d; cstrs ] in *)
        (* let ans = disj d cstrs in *)
        log "cstrs : %a\n%!" pp cstrs;
        log "d     : %a\n%!" pp d;
        let ans =
          if is_empty d
          then cstrs
          else if is_empty cstrs
          then d
          else cartesian2 d cstrs ~f:Disjunct.conj
        in
        (* Format.printf "all disjuncts: %a\n%!" pp ans; *)
        Some (ans, extra))
  ;;

  let recheck env subst cs bnds extra =
    log "Disequality2.recheck";
    log "bindings = %d %a" __LINE__ Subst.pp_binding_list bnds;
    log "cs = %a" pp cs;
    (* For every disjunct we try to simplify it using [bnds]. If it simplifies to empty disjunct, then we simplify it to False.
    If all disjuncts has been simpifies to False, then constraint is violated *)
    let simplify =
      let rec helper extra acc = function
        | [] -> acc
        | hc :: tlc ->
          let (_ : Disjunct.t) = hc in
          log "got a disjunct: %a\n%!" Disjunct.pp hc;
          (match Disjunct.recheck_exn env subst bnds extra hc with
          | exception Violated ->
            log "rechecking disjunct failed %s %d" __FILE__ __LINE__;
            helper extra acc tlc
          | None ->
            log "rechecking disjunct failed %s %d" __FILE__ __LINE__;
            helper extra acc tlc
          | Some (d, extra) ->
            (* We have an updated disjunct *)
            (* log "Updated disjunct %s %d: %a" __FILE__ __LINE__ Disjunct.pp d; *)
            helper extra (d @ acc) tlc)
      in
      helper extra []
    in
    try
      match cs with
      | [] ->
        log "%s %d" __FILE__ __LINE__;
        Some ([], extra)
      | _ ->
        (match simplify cs with
        | [] ->
          log "%s %d" __FILE__ __LINE__;
          raise Violated
        | newc ->
          (* log "recheck successful %s %d" __FILE__ __LINE__; *)
          Some (newc, extra))
    with
    | Violated ->
      log "got exception Violated %s %d" __FILE__ __LINE__;
      None
  ;;

  let merge_disjoint _ = failwith "merge_disjoint is not implemented"

  module Answer = struct
    type t = Disjunct.t

    let extract d v =
      (* Format.printf "Extracting from %a\n%!" Disjunct.pp d; *)
      Disjunct.extract d v
    ;;

    (* let subsumed _env c1 c2 = false *)
    let subsumed _env c1 c2 = Stdlib.compare c1 c2 = 0
  end

  let vars_in_term =
    let rec helper acc x =
      (* Format.printf "%a\n%!" Term.pp (Obj.repr x); *)
      if Obj.is_block x
      then (
        match Term.var x with
        | Some v -> Term.VarSet.add v acc
        | None when Obj.(tag x = string_tag) -> acc
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
    log "reify: %s %d" __FILE__ __LINE__;
    log "constraints: %a" pp cs;
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
