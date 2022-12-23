
type ground = int * Nat.ground
let of_int n = (n, Nat.O)

type injected = (int * Nat.injected) Logic.ilogic

let core_unify l r : Core.State.t -> Core.State.t Stream.t =
  Obj.magic (Core.unify l r)

let normalize v =
  (* accepts walked value *)
  let rec helper acc v =
    if Term.is_var v then Obj.repr (acc, v)
    else
      let v = Obj.repr v in
      if Obj.is_int v then Obj.repr (acc, v)
    else
      let () = assert (Obj.is_block v) in
      let () = assert (Obj.tag v = 0) in (* S constructor *)
      helper (acc+1) (Obj.field v 0)
  in
  if Term.is_var (Obj.magic v) then v
  else let (acc, p) = Obj.magic v in
  helper acc p

let rec unify lstart rstart : Core.goal = Obj.magic @@ fun st ->
  (* TODO: walk *)
  let env = Core.State.env st in
  let subst  = Core.State.subst st in
  let classify = function
  | Subst.Var v -> `Var v
  | Subst.Value x ->
    let x = normalize x in
    let (n, p) : int * Obj.t = Obj.magic x in
    if n = 0 then `Var (Obj.magic p)
    else `D (n,p)
  in
  let iwalk t = classify (Subst.walk env subst (Obj.magic t)) in

  match iwalk lstart, iwalk  rstart with
  | `D(lc, l), `D (rc, r) when lc >= rc ->
    (* l and r are either Zero peanos or varibles *)
    (* let d = lc - rc in *)
    core_unify (Obj.magic l) (Obj.magic r) st |> Stream.map (fun st ->
      (* Need to update original values *)
      Core.State.modify_subst (fun sub ->
        let foo sub varg data =
          match Term.var varg with
          | None -> sub
          | Some v -> Subst.set v (Obj.magic data) sub
        in
        foo (foo sub lstart (lc,l)) rstart (rc,r)
      ) st
    )
  | `D(lc, l), `D (rc, r) -> assert false
  | `Var l, `D r -> core_unify (Obj.magic l) (Obj.magic r) st
  | `D l, `Var r -> core_unify (Obj.magic l) (Obj.magic r) st
  | `Var l, `Var r -> core_unify (Obj.magic l) (Obj.magic r) st


let (===) = unify

let zero : injected = Obj.magic (0, Nat.O)
let succ n = assert false

let%test _ = true

let%expect_test _ = ()