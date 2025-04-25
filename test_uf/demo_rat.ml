open OCanren
open Tester




let () =
  run_r Std.Nat.reify Std.Nat.rat_show 1 qr qrh (REPR(fun x y ->
    fresh (v u)
      (rat_unify x (Std.Nat.succ v))
      (rat_unify v (Std.Nat.succ y))
      (rat_unify y (Std.Nat.succ u))
      (rat_unify u (Std.Nat.succ x))
      (debug_var !!1 OCanren.reify (fun _ -> print_endline ""; success))
      (rat_unify x (Std.Nat.succ y))
    ))