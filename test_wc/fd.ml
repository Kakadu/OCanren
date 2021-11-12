open OCanren
open OCanren.Std
open Tester

let lino f c =
  debug_var !!1 OCanren.reify (function
    | [Value 1] ->
        Format.printf "%s %d\n%!" f c;
        success
    | _ -> assert false )

let debug_int n =
  debug_var n OCanren.reify (function
    | [Value n] -> Format.printf "%d\n%!" n; success
    | [Var (n, [])] -> Format.printf "_.%d\n%!" n; success
    | _ -> assert false )

let show_int = GT.show GT.int
let show_intl = GT.show logic (GT.show GT.int)

let run_bool eta =
  runR OCanren.reify (GT.show GT.bool) (GT.show logic @@ GT.show GT.bool) eta

let run_int eta =
  runR OCanren.reify (GT.show GT.int) (GT.show logic @@ GT.show GT.int) eta

let _ = [%tester run_int (-1) (fun q -> fresh () (FD.domain q [1; 2]))]

let _ =
  [%tester run_int (-1) (fun q -> fresh () (FD.domain q [1; 2]) (q =/= !!1))]

let _ =
  [%tester
    run_int (-1) (fun q ->
        fresh () (FD.domain q [1; 2]) (q =/= !!1) (q =/= !!2) )]

let _ =
  [%tester
    run_int (-1) (fun q ->
        fresh () (FD.domain q [1; 2]) (FD.neq q !!1) (FD.neq q !!2) )]
