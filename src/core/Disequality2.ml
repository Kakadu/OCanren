(*
  Going to implement very naive disequality constraints
  which will be stored internally as disjunction of conjunction (DNF)
*)

let ( !!! ) = Obj.magic

module Conjunct = struct
  type t = Subst.Binding.t

  let pp ppf Subst.Binding.{ var; term } =
    Format.fprintf ppf "{ %d -> '%s' }" var.Term.Var.index (Term.show term)
  ;;

  let intersects_with ~set : t -> bool =
    let open Subst.Binding in
    let rec helper set = function
      | [] -> false
      | { var; term } :: tl when Term.VarSet.mem var set -> true
      | { term } :: tl ->
        (match Term.var term with
        | Some var when Term.VarSet.mem var set -> true
        | _ -> helper set tl)
    in
    fun c -> helper set [ c ]
  ;;
end

module Disjunct = struct
  type t = Conjunct.t list

  let empty = []
  let singleton : Term.Var.t -> _ -> t = fun var term -> [ Subst.Binding.{ var; term } ]

  let pp ppf xs =
    Format.fprintf ppf "[ ";
    Stdlib.List.iter (Conjunct.pp ppf) xs;
    Format.fprintf ppf " ]"
  ;;

  let conj : t -> t -> t = fun l r -> l @ r

  let intersects_with ~set =
    let rec helper = function
      | [] -> false
      | c :: ctl -> if Conjunct.intersects_with ~set c then true else helper ctl
    in
    helper
  ;;
end

type t = Disjunct.t list

let pp ppf xs = Stdlib.List.iter (Disjunct.pp ppf) xs
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

let add env subst cstrs l r : t option =
  match Subst.unify env subst l r with
  | None -> Some cstrs
  | Some ([], _) ->
    (* easily violated *)
    None
  | Some (bnds, _subst) ->
    let add_to_disjunct d = Some d in
    (match cstrs with
    | [] -> Some [ bnds ]
    | cstrs -> Some (Stdlib.List.map (Stdlib.List.append bnds) cstrs))
;;

(* let rec unify_list env fst snd (subst as _acc) = function
  | [] -> acc
  | h :: tl ->
    (match Subst.unify env subst !!!(fst h) !!!(snd tl) with
    | None -> None
    | Some (_, subst) -> unify_list env fst snd subst tl )
;; *)

exception Violated

let recheck env subst cs bnds =
  (* For every disjunct we try to simplify it using [bnds]. If it simplifies to empty disjunct, then we simplify it to False.
    If all disjuncts has been simpifies to False, then constraint is violated *)
  let simplify =
    let rec helper acc = function
      | [] -> acc
      | hc :: tlc ->
        let (_ : Disjunct.t) = hc in
        (* Format.printf "got a disjunct: %a\n%!" Disjunct.pp hc; *)
        let rez =
          let a = List.map (fun { Subst.Binding.var } -> var) hc in
          let b = List.map (fun { Subst.Binding.term } -> term) hc in
          (* TODO: implement unification of bindings list *)
          Subst.unify env subst (Obj.repr a) (Obj.repr b)
        in
        (match rez with
        | None -> helper acc tlc
        | Some ([], _) -> raise Violated
        | Some (bnds, subst1) ->
          (* We have an updated disjunct *)
          helper (bnds :: acc) tlc)
    in
    helper []
  in
  try
    match cs with
    | [] -> Some []
    | _ ->
      (match simplify cs with
      | [] -> raise Violated
      | newc -> Some newc)
  with
  | Violated -> None
;;

(* match Term.is_var l, Term.is_var r with
  | _, _ -> assert false *)

let merge_disjoint _ = assert false

module Answer = struct
  type t = Disjunct.t

  let extract ans v =
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
    helper [] ans
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
        let rec inner acc i =
          if i >= Obj.size x then acc else helper acc (Obj.field x i)
        in
        inner acc 0)
    else acc
  in
  fun root -> helper Term.VarSet.empty (Obj.repr root)
;;

let reify env subst cs t =
  (* Format.printf "%s %d\n%!" __FILE__ __LINE__;
  Format.printf "%a\n%!" pp cs; *)
  let vars = vars_in_term t in
  cs
  |> List.filter_map (fun d ->
         if Disjunct.intersects_with ~set:vars d then Some d else None)
;;

(** *******************  tests ***************************  *)
module _ = struct
  let make_var i = Obj.magic (Term.Var.make ~env:0 ~scope:Term.Var.non_local_scope i)

  let%expect_test _ =
    let v1 = make_var 1 in
    Format.printf "%a" pp (disequality_of_terms v1 v1);
    [%expect {|
      [ { 1 -> '_.1' } ]
    |}]
  ;;

  let%expect_test _ =
    let v1 = make_var 1 in
    let v2 = make_var 2 in
    Format.printf "%a" pp (disequality_of_terms !!!(1, 2) !!!(v1, v2));
    [%expect {|
      [ { 1 -> 'int<1>' } ][ { 2 -> 'int<2>' } ]
    |}]
  ;;

  let%expect_test _ =
    let v1 = make_var 1 in
    let v2 = make_var 2 in
    Format.printf "%a" pp (disequality_of_terms !!!(1, v1) !!!(2, v2));
    [%expect {|
      [ { 1 -> '_.2' } ]
    |}]
  ;;

  let%expect_test _ =
    let v1 = make_var 1 in
    let v2 = make_var 2 in
    Format.printf "%a" pp (disequality_of_terms !!!(1, v1) !!!(2, v2));
    [%expect {|
      [ { 1 -> '_.2' } ]
    |}]
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
      {|
      [ { 1 -> 'int<1>' } ][ { 2 -> 'int<2>' } ]
      [ { 3 -> 'int<3>' } ][ { 4 -> 'int<4>' } ]
      [ { 1 -> 'int<1>' }{ 3 -> 'int<3>' } ][ { 1 -> 'int<1>' }{ 4 -> 'int<4>' } ][ { 2 -> 'int<2>' }{ 3 -> 'int<3>' } ][ { 2 -> 'int<2>' }{ 4 -> 'int<4>' } ]
    |}]
  ;;
end
