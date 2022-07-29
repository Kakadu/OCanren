open OCanren
open OCanren.Std
open Tester

let show_int = GT.show GT.int
let show_intl = GT.show logic (GT.show GT.int)
let show_bool = GT.show GT.bool
let show_booll = GT.show logic (GT.show GT.bool)
let run_bool eta = run_r OCanren.reify (GT.show logic @@ GT.show GT.bool) eta
let run_int eta = run_r OCanren.reify (GT.show logic @@ GT.show GT.int) eta

let run_pair eta =
  run_r
    (Pair.reify OCanren.reify OCanren.reify)
    (GT.show Pair.logic show_intl show_intl)
    eta
;;

let run_pair_bool eta =
  run_r
    (Pair.reify OCanren.reify OCanren.reify)
    (GT.show Pair.logic show_booll show_booll)
    eta
;;

let run_pair_int eta =
  run_r
    (Pair.reify OCanren.reify OCanren.reify)
    ([%show: (GT.int OCanren.logic, GT.int OCanren.logic) Std.Pair.logic] ())
    eta
;;

let run_list eta = run_r (List.reify OCanren.reify) (GT.show Std.List.logic show_intl) eta
let triple a b c = pair a (pair b c)

let run_triple eta =
  run_r
    (Pair.reify OCanren.reify (Pair.reify OCanren.reify OCanren.reify))
    (GT.show Pair.logic show_intl (GT.show Pair.logic show_intl show_intl))
    eta
;;

let run_exn eta = run_r OCanren.prj_exn show_int eta

let __ _ =
  run_exn (-1) q qh (REPR (fun q -> fresh (x y) (x === y) (x =/= y)));
  run_exn (-1) q qh (REPR (fun q -> fresh (x y) (x =/= y) (x === y)));
  exit 1
;;

let _ = [%tester run_int (-1) (fun q -> q === __)]
let _ = [%tester run_int (-1) (fun q -> q =/= __)]
let _ = [%tester run_int (-1) (fun q -> !!5 =/= __)]
let _ = [%tester run_pair (-1) (fun q -> pair !!2 __ =/= pair __ !!2)]
(* let _ = exit 0 *)

let _ =
  [%tester run_pair (-1) (fun q -> fresh () (q =/= pair __ !!1) (q === pair !!1 __))]
;;

(* ***************************** *)
let _ = [%tester run_pair (-1) (fun q -> pair !!1 __ === pair __ !!1)]
let _ = [%tester run_pair (-1) (fun q -> q === pair __ !!1 &&& (q === pair !!1 __))]
let _ = [%tester run_pair (-1) (fun q -> pair !!1 __ =/= pair __ !!1)]
let _ = [%tester run_pair (-1) (fun q -> pair !!1 __ =/= pair !!2 __)]
let _ = [%tester run_int (-1) (fun q -> triple q !!2 __ =/= triple !!1 __ !!2)]
let _ = [%tester run_int (-1) (fun q r -> pair q r =/= pair !!1 __)]
let _ = [%tester run_int (-1) (fun q -> pair q !!1 =/= pair !!1 __)]

let _ =
  [%tester
    run_pair (-1) (fun q ->
      fresh
        (a b)
        (q === pair a b)
        (* (debug_var a OCanren.reify (fun _ ->
               let () = OCanren.set_diseq_logging true in
               success)) *)
        (q =/= pair !!1 __)
        (q === pair __ !!1))]
;;

let () = OCanren.set_diseq_logging false

let _ =
  [%tester
    run_pair (-1) (fun q ->
      fresh (a b) (q =/= pair !!1 __) (* (q =/= pair __ !!1)  *) (q === pair a b))]
;;

let _ =
  [%tester run_pair (-1) (fun q -> fresh () (q =/= pair !!1 __) (q =/= pair __ !!1))]
;;

let _ =
  [%tester
    run_pair (-1) (fun q ->
      fresh (a b) (q =/= pair !!1 __) (q === pair __ !!1) (q === pair a b))]
;;

let _ =
  [%tester run_list (-1) (fun q -> fresh () (q === !!1 % (!!2 % __)) (q === __ % __))]
;;

let _ =
  [%tester run_list (-1) (fun q -> fresh (a b) (q === !!1 % (!!2 % __)) (q === a % b))]
;;

let _ =
  [%tester
    run_list (-1) (fun q -> fresh (a b) (q === __ % __) (q === !<(!!1)) (q === !<(!!2)))]
;;

let _ = [%tester run_int (-1) (fun q -> q === !!1 &&& (__ =/= !!1 % __))]
let _ = [%tester run_int (-1) (fun q -> fresh (a b) (q === !!1) (a =/= !!1 % b))]
let _ = [%tester run_int (-1) (fun q -> fresh a (q === !!1) (a =/= !!1 % a))]

let rec non_membero x xs =
  let open OCanren.Std in
  fresh
    ()
    (xs =/= List.cons x __)
    (conde
       [ fresh (h tl) (xs === List.cons h tl) (non_membero x tl); xs === List.nil () ])
;;

let _ =
  [%tester run_int (-1) (fun q -> non_membero !!0 (Std.list ( !! ) [ 1; 2; 3 ]))];
  [%tester run_int (-1) (fun q -> non_membero !!0 (Std.list ( !! ) []))];
  [%tester run_int (-1) (fun q -> non_membero !!0 (Std.list ( !! ) [ 0 ]))];
  ()
;;

let _ = [%tester run_list (-1) (fun q -> q =/= __ % __ &&& (q =/= List.nil ()))]

(*      fresh () (q =/= pair true_ __) (q === pair __ true_) *)
let _ =
  [%tester
    run_pair_bool (-1) (fun q -> q =/= Std.pair !!true __ &&& (q === Std.pair __ !!true))]
;;

let _ = [%tester run_pair_bool (-1) (fun q -> __ =/= Std.pair __ !!true)]

let _ =
  [%tester
    run_pair_bool (-1) (fun q ->
      fresh () (q === Std.pair !!false !!true) (q =/= Std.pair !!true __))]
;;

let __ _ =
  [%tester
    run_pair_bool (-1) (fun q ->
      fresh () (Std.pair !!false !!true =/= Std.pair !!true __))]
;;

let _ =
  [%tester
    run_pair_bool (-1) (fun q ->
      fresh () (q =/= Std.pair !!true __) (q === Std.pair !!false !!true))]
;;

let __ _ =
  [%tester
    run_list (-1) (fun q -> fresh (x y) (!![ x; !!1 ] =/= !![ !!2; y ]) (x === !!2))]
;;

let _ =
  [%tester
    run_list (-1) (fun q ->
      fresh
        (x y)
        (* TODO: document that using logic lists is not strongly required *)
        (!![ x; !!1 ] =/= !![ !!2; y ])
        (* trace_diseq_constraints *)
        (y === !!1)
        success)]
;;

(* let () = OCanren.set_diseq_logging false *)

let _ =
  [%tester
    run_pair_int (-1) (fun q ->
      fresh
        (x y)
        (Std.pair x !!1 =/= Std.pair !!2 y)
        (x === !!2)
        (* (debug_var x OCanren.reify (fun _ ->
               let () = OCanren.set_diseq_logging true in
               trace_diseq_constraints)) *)
        (y === !!9)
        (Std.pair x y === q))]
;;

(* let () = OCanren.set_diseq_logging false *)

let _ =
  [%tester
    run_pair (-1) (fun q ->
      fresh (a b) (q === pair a b) (q =/= pair !!1 __) (* trace_diseq_constraints *))]
;;

let _ =
  [%tester
    run_pair (-1) (fun q ->
      fresh
        (a b)
        (q === pair a b)
        (q =/= pair !!1 __)
        (* trace_diseq_constraints *)
        (q === pair __ !!1))]
;;

(* let () = OCanren.set_diseq_logging false *)
