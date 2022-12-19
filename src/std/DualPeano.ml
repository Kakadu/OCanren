
type ground = int * Nat.ground
let of_int n = (n, Nat.O)

let core_unify l r : Core.State.t -> Core.State.t Stream.t =
  Obj.magic (Core.unify l r)

let rec unify lstart rstart st =
  (* TODO: walk *)
  let env = Core.State.env st in
  let subst  = Core.State.subst st in
  let iwalk t = Subst.walk env subst (Obj.magic t) in
  match iwalk lstart, iwalk  rstart with
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
