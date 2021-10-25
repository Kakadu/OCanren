open OCanren.Moiseenko
open OCanren.ILogic


let ret = Env.return

(* test that reifiyng a variable yeilds variable *)
let%test _ =
  match Reifier.(apply reify @@ run (fun v -> ret v)) with
  | Var _ -> true
  | Value _ -> false

(* test that reifiyng a fresh variable yeilds variable *)
let%test _ =
  match Reifier.(apply reify @@ run (fun v -> fresh (fun x -> ret x))) with
  | Var _ -> true
  | Value _ -> false

(* test that reifiyng a value yeilds value *)
let%test _ =
  match Reifier.(apply reify @@ run (fun v -> ret @@ inj 42)) with
  | Value i -> i = 42
  | Var _ -> false

(* test that runaway variables are handled *)
(* let%test _ =
  let runaway : int ilogic ref = ref (Obj.magic ()) in
  let _ =
    run (fun v ->
        runaway := v;
        ret v)
  in
  try
    let _ = Reifier.(apply reify @@ run (fun v -> ret !runaway)) in
    false
  with Var_scope_violation v -> true *)
