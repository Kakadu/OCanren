
type ground = int * Nat.ground
let of_int n = (n, Nat.O)

let core_unify l r : Core.State.t -> Core.State.t Stream.t =
  Obj.magic (Core.unify l r)

let rec unify l r st =
  (* TODO: walk *)
  match Term.var l, Term.var r with
  | None, None ->
    let (lc, l), (rc, r) = (Obj.magic l, Obj.magic r) in
    let d = lc - rc in
    if d>0 then on_two_ground d l r st
    else if d<0 then on_two_ground d r l st
    else (* *)
      on_two_peanos l r st
  | Some _, Some _ -> core_unify l r st
  | Some v, None -> core_unify l r st
  | None, Some v -> core_unify l r st
and on_two_ground lconst l r st = assert false
and on_two_peanos _ _ st = assert false
