  $ export OCAMLRUNPARAM="b,l=10"
  $ ./demo_rat.exe -demo1 2>&1 #| nl -ba  | head -n 60
  fun x ->
    fun y ->
      fresh (v u) (rat_unify x (Std.Nat.succ v)) (rat_unify v (Std.Nat.succ y))
        (rat_unify y (Std.Nat.succ u)) (rat_unify u (Std.Nat.succ x))
        (debug_var (!! 1) OCanren.reify (fun _ -> print_endline ""; success))
        (rat_unify x (Std.Nat.succ y)), 1 answer {
  
  q=S (S (S (S (_.10)))); r=S (S (S (S (_.11))));
  }
