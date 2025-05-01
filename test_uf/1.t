  $ export OCAMLRUNPARAM="b,l=10"
  $ ./demo_rat.exe -demo1 2>&1 #| nl -ba  | head -n 60
  fun x ->
    fun y ->
      fresh () (rat_unify x (Std.Nat.succ (Std.Nat.succ x)))
        (rat_unify y (Std.Nat.succ (Std.Nat.succ y))), 1 answer {
  q=S (S (_.10)); r=S (S (_.11));
  }
