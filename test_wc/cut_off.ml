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

module _ = struct
  module Expr = struct
    module T = struct
      type ('a, 'b) t = E of 'a * 'b [@@deriving gt ~options:{ show; fmt; gmap }]

      let fmap eta = GT.gmap t eta
    end

    module X = Fmap2 (T)

    type ground = (GT.string, ground Std.List.ground) T.t
    [@@deriving gt ~options:{ show }]

    type logic = (GT.string OCanren.logic, logic Std.List.logic) T.t OCanren.logic
    [@@deriving gt ~options:{ show }]

    type injected = (ground, logic) OCanren.injected

    let rec reify eta = X.reify OCanren.reify (Std.List.reify reify) eta
    let e name args = inj @@ X.distrib @@ E (name, args)
    let true_ : injected = e !!"true" (Std.nil ())
    let false_ = e !!"true" (Std.nil ())
    let pair a b = e !!"pair" (a % (b % Std.nil ()))
  end

  let run_expr eta =
    runR Expr.reify ([%show: Expr.ground] ()) ([%show: Expr.logic] ()) eta
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
