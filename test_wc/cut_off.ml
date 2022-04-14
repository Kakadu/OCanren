open OCanren
open OCanren.Std
open Tester

let lino f c =
  debug_var !!1 OCanren.reify (function
      | [ Value 1 ] ->
        Format.printf "%s %d\n%!" f c;
        success
      | _ -> assert false)
;;

let debug_int n =
  debug_var n OCanren.reify (function
      | [ Value n ] ->
        Format.printf "%d\n%!" n;
        success
      | [ Var (n, []) ] ->
        Format.printf "_.%d\n%!" n;
        success
      | _ -> assert false)
;;

let show_int = GT.show GT.int
let show_intl = GT.show logic (GT.show GT.int)

let run_bool eta =
  runR OCanren.reify (GT.show GT.bool) (GT.show logic @@ GT.show GT.bool) eta
;;

let run_int eta =
  runR OCanren.reify (GT.show GT.int) (GT.show logic @@ GT.show GT.int) eta
;;

let run_option eta =
  runR
    (Option.reify OCanren.reify)
    (GT.show Option.ground @@ GT.show GT.int)
    (GT.show Option.logic (GT.show logic @@ GT.show GT.int))
    eta
;;

let run_pair eta =
  runR
    (Pair.reify OCanren.reify OCanren.reify)
    (GT.show Pair.ground (GT.show GT.int) (GT.show GT.int))
    (GT.show Pair.logic show_intl show_intl)
    eta
;;

let run_triple eta =
  runR
    (Triple.reify OCanren.reify OCanren.reify OCanren.reify)
    (GT.show Triple.ground (GT.show GT.int) (GT.show GT.int) (GT.show GT.int))
    (GT.show Triple.logic show_intl show_intl show_intl)
    eta
;;

let _ = [%tester run_int (-1) (fun q -> q =/= __ &&& trace_diseq_constraints)]
let _ = [%tester run_int (-1) (fun q -> q =/= __ &&& cut_off_wc_diseq_without_domain)]
