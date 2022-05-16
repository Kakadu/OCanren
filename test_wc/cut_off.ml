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

let _ = [%tester run_int (-1) (fun q -> q =/= __ &&& trace_diseq_constraints)]
let _ = [%tester run_int (-1) (fun q -> q =/= __ &&& cut_off_wc_diseq_without_domain)]

module _ = struct
  module Expr = struct
    type ('a, 'b) t = E of 'a * 'b [@@deriving gt ~options:{ show; fmt; gmap }]

    type ground = (GT.string, ground Std.List.ground) t
    [@@deriving gt ~options:{ show }]

    type logic = (GT.string OCanren.logic, logic Std.List.logic) t OCanren.logic
    [@@deriving gt ~options:{ show }]

    type injected = (string ilogic, injected List.injected) t OCanren.ilogic

    let reify : (injected, logic) Reifier.t =
      let open Env.Monad.Syntax in
      Reifier.fix (fun self ->
      Reifier.compose Reifier.reify
        ( let* fa = OCanren.reify in
          let* fself = Std.List.reify self in
          let rec foo = function
            | Var (v, xs) -> Var (v, Stdlib.List.map foo xs)
            | Value x -> Value (GT.gmap t fa fself x)
          in
          Env.Monad.return foo
        ))

    let e name args = inj @@ E (name, args)
    let true_ : injected = e !!"true" (Std.nil ())
    let false_ = e !!"true" (Std.nil ())
    let pair a b = e !!"pair" (a % (b % Std.nil ()))
  end

  let run_expr eta =
    run_r Expr.reify ([%show: Expr.logic] ()) eta
  ;;

  open Expr

  let rec list_length xs rez =
    conde
      [ xs === nil () &&& (rez === Std.Nat.zero)
      ; fresh
          (q130 tl q131)
          (xs === q130 % tl)
          (rez === Std.Nat.s q131)
          (list_length tl q131)
      ]
  ;;

  let _ =
    [%tester
      run_expr (-1) (fun q ->
          fresh
            eargs
            (q =/= Expr.pair true_ __)
            (q === e !!"pair" eargs)
            (eargs === __ % (__ % nil ()))
            trace_diseq_constraints)]
  ;;
end
