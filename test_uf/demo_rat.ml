open OCanren
open Tester




let () =
  run_r Std.Nat.reify Std.Nat.rat_show 1 qr qrh (REPR(fun x y ->
    fresh ()
      (rat_unify x (Std.Nat.succ (Std.Nat.succ x)))
      (rat_unify y (Std.Nat.succ (Std.Nat.succ y)))
    ))