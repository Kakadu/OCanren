open GT
open OCanren
open OCanren.Std
open Tester
open Printf

let ilist xs = list (!!) xs
let just_a a = a === !!5

let occurs x =
  (x === List.cons !!1 x)

let two_vars x y = x===y
let a_and_b a =
  call_fresh (fun b ->
      (a === !!7) &&&
      conde [ (b === !!6); (b === !!5) ]
  )

let a_and_b' b =
  call_fresh (fun a ->
      (a === !!7) &&&
      conde [ (b === !!6); (b === !!5) ]
  )

let rec fives x =
  conde
    [ (x === !!5)
    ; defer (fives x)
    ]

let show_int       = show(int)
let show_int_list   = show(List.ground) (show int)
let show_intl_list  = show(List.logic ) (show(logic) (show int))

let (===) a b =
  let reif = Std.Pair.reify (Std.List.reify OCanren.reify) (Std.List.reify OCanren.reify) in
  (debug_var (Std.pair a b) (Fun.flip reif) (function
    | [ Value (x, y) ] ->
      Format.printf "unify `%s` and `%s`\n%!" (show_intl_list x) (show_intl_list y);
      success
    | _ -> assert false
  )) &&& (OCanren.unify a b)

let rec appendo a b ab =
  conde
    [ ((a === nil ()) &&& (b === ab))
    ; fresh (h t ab')
        (a === h%t)
        (h%ab' === ab)
        (appendo t b ab')
    ]

let rec reverso a b =
  conde
    [ ((a === nil ()) &&& (b === nil ()))
    ; fresh (h t a')
        (a === h%t)
        (appendo a' !<h b)
        (defer (reverso t a'))
    ]

let run_exn eta = run_r (Std.List.prj_exn OCanren.prj_exn) eta
let __ () =
  run_exn show_int_list  1  q qh (REPR (fun q   -> appendo q (ilist [3; 4]) (ilist [1; 2; 3; 4])   ));
  ()


let __ () =
  run_exn show_int_list (-1)  qr qrh (REPR (fun q r  ->
    appendo q r (ilist [1; 2; 3; 4])   ));
  ()

let  () =
  run_exn show_int_list (-1)  q qh (REPR (fun q   ->
    reverso q (ilist [1])   ));
  ()
