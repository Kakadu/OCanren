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
  run_r OCanren.reify (GT.show logic @@ GT.show GT.bool) eta
;;

let run_int eta =
  run_r OCanren.reify (GT.show logic @@ GT.show GT.int) eta
;;

let run_option eta =
  run_r
    (Option.reify OCanren.reify)
    (GT.show Option.logic (GT.show logic @@ GT.show GT.int))
    eta
;;

let run_pair eta =
  run_r
    (Pair.reify OCanren.reify OCanren.reify)
    (GT.show Pair.logic show_intl show_intl)
    eta
;;

let run_triple eta =
  run_r
    (Triple.reify OCanren.reify OCanren.reify OCanren.reify)
    (GT.show Triple.logic show_intl show_intl show_intl)
    eta
;;

let _ = [%tester run_pair (-1) (fun q -> fresh x (q =/= pair __ !!1) (q === pair !!1 __))]
let _ = [%tester run_int (-1) (fun q -> fresh () (FD.domain q [ 1; 2 ]))]
let _ = [%tester run_int (-1) (fun q -> fresh () (FD.domain q [ 1; 2 ]) (q =/= !!1))]

let _ =
  [%tester
    run_int (-1) (fun q -> fresh () (FD.domain q [ 1; 2 ]) (q =/= !!1) (q =/= !!2))]
;;

(* let _ = exit 0 *)

let _ =
  [%tester
    run_int (-1) (fun q -> fresh () (FD.domain q [ 1; 2 ]) (FD.neq q !!1) (FD.neq q !!2))]
;;

let _ =
  [%tester
    run_option (-1) (fun q -> fresh x (q =/= Option.some __) (q === Option.some x))]
;;

let _ =
  [%tester
    run_option (-1) (fun q ->
        fresh
          x
          (q =/= Option.some __)
          (q === Option.some x)
          cut_off_wc_diseq_without_domain)]
;;

let _ =
  [%tester
    run_option (-1) (fun q ->
        fresh
          x
          (q =/= Option.some __)
          (FD.domain x [ 1; 2 ])
          (x =/= !!1)
          (x =/= !!2)
          (q === Option.some x))]
;;

let () =
  print_endline
    "\tTo repair the next example we should decide existance of the answer in the moment \
     of reification "
;;

let _ =
  [%tester
    run_option (-1) (fun q ->
        fresh
          x
          (q =/= Option.some __)
          (FD.domain x [ 1; 2; 3 ])
          (x =/= !!1)
          (x =/= !!2)
          (q === Option.some x))]
;;

let _ =
  [%tester
    run_pair (-1) (fun q ->
        fresh
          _11
          (FD.domain _11 [ 1; 2 ])
          (_11 =/= !!2)
          (* trace_domain_constraints *)
          (q =/= pair _11 __)
          (q === pair !!1 !!1))]
;;

let _ =
  (* In this case a variable [v] could have different domains:
     + empty domain should lead to simplification of constraint
       + Currently the query will give an answer
       + TODO: we could check that not values could inhabit q and return empty stream
       +
     *)
  [%tester run_pair (-1) (fun q -> fresh v (q === pair !!1 v) (q =/= pair !!1 __))]
;;

(* we could enforce that domain is not empty which will lead to empty result for previous query *)
let _ =
  [%tester
    run_pair (-1) (fun q ->
        fresh v (q === pair !!1 v) (q =/= pair !!1 __) cut_off_wc_diseq_without_domain)]
;;

(* A more complicated version of two previous ones *)
let _ =
  [%tester
    run_pair (-1) (fun q ->
        fresh
          _11
          (FD.domain _11 [ 1; 2 ])
          (_11 =/= !!2)
          (* trace_domain_constraints *)
          (q === pair _11 __)
          (q =/= pair !!1 __)
          cut_off_wc_diseq_without_domain)]
;;

let _ =
  [%tester
    run_pair (-1) (fun q ->
        fresh
          _11
          (FD.domain _11 [ 1; 2 ])
          (q =/= pair _11 __)
          (q === pair !!1 !!1)
          (_11 =/= !!2))]
;;

let _ =
  [%tester
    run_int (-1) (fun q ->
        fresh
          ()
          (q =/= !!1)
          (FD.domain q [ 1; 2 ])
          trace_domain_constraints
          (q =/= !!2)
          success)]
;;

let _ =
  [%tester
    run_int (-1) (fun q ->
        fresh () (q =/= !!1) (q =/= !!2) (FD.domain q [ 1; 2 ]) success)]
;;
