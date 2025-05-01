  $ export OCAMLRUNPARAM="b,l=10"
How this should work?
(x === S(S y))
(y === S(S x))
(x === S y)      | x = _.10, y = _.11
TRACE:
Helper: _.10 and boxed 0 <boxed 0 <_.11>>
extend _.10 |-> S(_.12)
......._.12 |-> S(_.11)

Helper: _.11 and boxed 0 <boxed 0 <_.10>>
extend _.11 |-> S(_.13)
......._.13 |-> S(_.10)
Helper: _.10 and boxed 0 <_.11>

Helper: boxed 0 <_.12> and boxed 0 <_.11>


  $ ./demo_rat.exe -demo2 2>&1 #| nl -ba  | head -n 60
  
  fun x ->
    fun y ->
      fresh () (rat_unify x (Std.Nat.succ (Std.Nat.succ y)))
        (rat_unify y (Std.Nat.succ (Std.Nat.succ x)))
        (debug_var (!! 1) OCanren.reify (fun _ -> print_endline ""; success))
        (rat_unify x (Std.Nat.succ y)) {
  q = S (S (S (S (_.10)))); r=S (S (S (S (_.11))))}

