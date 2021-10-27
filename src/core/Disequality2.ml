(*
  Going to implement very naive disequality constraints
  which will be stored internally as disjunction of conjunction (DNF)
*)

let ( !!! ) = Obj.magic

module Conjunct = struct
  type t = Subst.Binding.t
  (* let make l r =  *)

  let pp ppf Subst.Binding.{ var; term } =
    Format.fprintf ppf "{ %d -> '%s' }" var.Term.Var.index (Term.show term)
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
end

type t = Disjunct.t list

let pp ppf xs = Stdlib.List.iter (Disjunct.pp ppf) xs
let empty : t = []
let disj : t -> t -> t = Stdlib.List.append
let conj : t -> t -> t = fun l r -> assert false

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
end

let reify _ = assert false
let recheck _ = assert false

let add _env _subst _ l r =
  match Term.is_var l, Term.is_var r with
  | _, _ -> assert false
;;

let merge_disjoint _ = assert false

module Answer = struct
  type t

  let extract _ = assert false
  let subsumed _ = assert false
end
