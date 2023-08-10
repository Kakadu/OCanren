open OCanren
open Tester

let run_option n =
  run_r
    [%reify: GT.int Std.Option.ground]
    (GT.show Std.Option.logic (GT.show OCanren.logic (GT.show GT.int)))
    n
;;

let __ () =
  let open Std in
  run_option 1 q qh (REPR (fun q -> q === none ()));
  run_option 1 q qh (REPR (fun q -> fresh x (q === some x)));
  run_option 1 q qh (REPR (fun q -> fresh () (q === some !!42)))
;;

let run_int n = run_r [%reify: GT.int] (GT.show OCanren.logic (GT.show GT.int)) n

let conde_demo q =
  conde
    [ conde [ q === !!1; q === !!2; q === !!3; q === !!4; q === !!5 ]
    ; conde [ q === !!11; q === !!12; q === !!13; q === !!14; q === !!15 ]
    ; conde [ q === !!21; q === !!22; q === !!23; q === !!24; q === !!25 ]
    ; conde [ q === !!31; q === !!32; q === !!33; q === !!34; q === !!35 ]
    ; conde [ q === !!41; q === !!4; q === !!43; q === !!44; q === !!45 ]
    ]
;;

let () =
  let open Std in
  run_int (-1) q qh (REPR conde_demo)
;;

(*
let ( === ) a b =
  debug_var a (Fun.flip OCanren.reify) (function [ h ] ->
      Printf.printf "%s\n" (GT.show OCanren.logic (GT.show GT.int) h);
      success)
  &&& debug_var b (Fun.flip OCanren.reify) (function [ h ] ->
          Printf.printf "%s\n" (GT.show OCanren.logic (GT.show GT.int) h);
          success)
  &&& OCanren.( === ) a b
;; *)

let condeep_demo q =
  (* condeep [ q === !!1; q === !!2 ] *)
  condeep
    [ condeep [ q === !!1; q === !!2; q === !!3; q === !!4; q === !!5 ]
    ; condeep [ q === !!11; q === !!12; q === !!13; q === !!14; q === !!15 ]
    ; condeep [ q === !!21; q === !!22; q === !!23; q === !!24; q === !!25 ]
    ; condeep [ q === !!31; q === !!32; q === !!33; q === !!34; q === !!35 ]
    ; condeep [ q === !!41; q === !!42; q === !!43; q === !!44; q === !!45 ]
    ]
;;

let () =
  let open Std in
  run_int (-1) q qh (REPR condeep_demo)
;;
