open OCanren
open OCanren.Std
open Tester

let all_give_same_answer_or_fail (ans : (int, int logic) OCanren.injected)
    (gs : ((int, int logic) OCanren.injected -> goal) list) =
  let rec helper = function
    | h :: tl ->
        fresh (r opt)
          (Unique.unique_answers h (opt : (int, int logic) Unique.injected))
          (conde
             [opt === Unique.noanswer; opt === Unique.unique r &&& (ans === r)] )
          (helper tl)
    | [] -> success in
  assert (gs <> []);
  helper gs

let flip f x env = f env x

let lino f c =
  debug_var !!1 (flip OCanren.reify) (function
    | [Value 1] ->
        Format.printf "%s %d\n%!" f c;
        success
    | _ -> assert false )

let debug_int n =
  debug_var n (flip OCanren.reify) (function
    | [Value n] -> Format.printf "%d\n%!" n; success
    | [Var (n, [])] -> Format.printf "_.%d\n%!" n; success
    | _ -> assert false )

let show_int = GT.show GT.int
let show_intl = GT.show logic (GT.show GT.int)

let run_bool eta =
  runR OCanren.reify (GT.show GT.bool) (GT.show logic @@ GT.show GT.bool) eta

let run_int eta =
  runR OCanren.reify (GT.show GT.int) (GT.show logic @@ GT.show GT.int) eta

let run_unique eta =
  runR
    (Unique.reify OCanren.reify)
    (GT.show Unique.ground show_int)
    (GT.show Unique.logic show_intl)
    eta

let _ =
  [%tester
    run_unique (-1) (fun q ->
        let g _ = failure in
        Unique.unique_answers g q )]

let _ =
  [%tester
    run_unique (-1) (fun q ->
        let g x = x === !!1 in
        Unique.unique_answers g q )]

let _ =
  [%tester
    run_unique (-1) (fun q ->
        let g x = conde [x === !!1] in
        Unique.unique_answers g q )]

let _ =
  [%tester
    run_unique (-1) (fun q ->
        let g x = conde [x === !!1; x === !!2] in
        Unique.unique_answers g q )]

let _ =
  [%tester
    run_int (-1) (fun q ->
        all_give_same_answer_or_fail q [(fun q -> q === !!1)] )]

let _ =
  [%tester
    run_int (-1) (fun q ->
        let g1 q = q === !!1 in
        let g2 q = conde [q === !!1; q === !!1] in
        all_give_same_answer_or_fail q [g1; g2] )]

let _ =
  [%tester
    run_int (-1) (fun q ->
        let g1 q = q === !!1 in
        let g2 q = conde [q === !!1; q === !!2] in
        all_give_same_answer_or_fail q [g1; g2] )]

let _ =
  [%tester
    run_int (-1) (fun q ->
        let g1 q = q === !!1 in
        let g2 q = conde [q === !!1; q === !!1] in
        let g3 _ = failure in
        all_give_same_answer_or_fail q [g1; g2; g3] )]

let _ =
  [%tester
    run_int (-1) (fun q ->
        let g1 q = q === !!2 in
        let g2 q = q === !!3 in
        all_give_same_answer_or_fail q [g1; g2] )]
