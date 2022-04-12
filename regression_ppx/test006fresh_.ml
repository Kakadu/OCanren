open OCanren
open Tester

let goal q = fresh_ n (q =/= Std.pair n !!1) trace_diseq_constraints

let run eta =
  runR
    (Std.Pair.reify reify reify)
    (GT.show Std.Pair.ground (GT.show GT.int) (GT.show GT.int))
    (GT.show
       Std.Pair.logic
       (GT.show logic (GT.show GT.int))
       (GT.show logic (GT.show GT.int)))
    eta
;;

let () = run 1 q qh (REPR goal)
