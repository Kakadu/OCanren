open OCanren

let trace_helper reifier pp bv fmt =
  Format.kasprintf
    (fun msg ->
      debug_var bv reifier (function
        | [ q ] ->
          Format.printf "%s: %a\n%!" msg pp q;
          success
        | _ -> failwith "Will not happen in trace_helper"))
    fmt
;;

let bv_size = 2

module BV = struct
  type cmp_t =
    | GT
    | LT
    | EQ
  [@@deriving gt ~options:{ show; fmt; gmap }]

  let build_num n =
    let rec helper i n =
      let b = n mod 2 in
      if i >= bv_size then Std.nil () else Std.List.cons !!b (helper (1 + i) (n / 2))
    in
    helper 0 n
  ;;

  type ground = GT.int Std.List.ground [@@deriving gt ~options:{ show; fmt; gmap }]

  type logic = GT.int OCanren.logic Std.List.logic
  [@@deriving gt ~options:{ show; fmt; gmap }]

  type injected = int ilogic Std.List.injected

  let prj_exn : (injected, ground) Reifier.t = Std.List.prj_exn OCanren.prj_exn
  let reify : (injected, logic) Reifier.t = Std.List.reify OCanren.reify
  let pp_logic = GT.fmt logic

  let debug_n : injected -> (int OCanren.logic Std.List.logic list -> goal) -> goal =
    fun n -> debug_var n (fun a b -> OCanren.Std.List.reify OCanren.reify a b)
  ;;

  let trace_n n fmt =
    debug_var n (OCanren.Std.List.reify OCanren.reify) (function
      | [ n ] ->
        Format.printf
          "%s: %s\n%!"
          (Format.asprintf fmt)
          (GT.show Std.List.logic (GT.show OCanren.logic @@ GT.show GT.int) n);
        success
      | _ -> assert false)
  ;;

  let trace_cmp n fmt =
    debug_var n OCanren.reify (function
      | [ n ] ->
        Format.printf
          "%s: %a\n%!"
          (Format.asprintf fmt)
          (GT.fmt OCanren.logic (GT.fmt cmp_t))
          n;
        success
      | _ -> assert false)
  ;;

  let compare_bits a b rez =
    conde
      [ a === !!0 &&& (b === !!0) &&& (rez === !!EQ)
      ; a === !!0 &&& (b === !!1) &&& (rez === !!LT)
      ; a === !!1 &&& (b === !!1) &&& (rez === !!EQ)
      ; a === !!1 &&& (b === !!0) &&& (rez === !!GT)
      ]
  ;;

  let rec compare_helper0 pos l r rez =
    let open Std in
    conde
      [ !!pos === !!0 &&& conde [ l =/= Std.nil (); r =/= Std.nil () ] &&& failure
      ; !!pos === !!0 &&& (l === Std.nil ()) &&& (r === l) &&& (rez === !!EQ)
      ; fresh
          (lh ltl rh rtl top_rez)
          (!!pos =/= !!0)
          (l === lh % ltl)
          (r === rh % rtl)
          (* (trace_n l " leo_helper.l")
             (trace_n r " leo_helper.r") *)
          (compare_helper0 (pos - 1) ltl rtl top_rez)
          (conde
             [ top_rez === !!GT &&& (rez === !!GT)
             ; top_rez === !!LT &&& (rez === !!LT)
             ; top_rez === !!EQ &&& compare_bits lh rh rez
               (* TODO: optimize intro two cases? *)
             ])
      ]
  ;;

  let compare_helper l r rez =
    fresh
      ()
      (* (trace_n l " compare_helper l")
         (trace_n r " compare_helper r")
         (trace_cmp rez " compare_helper rez") *)
      (compare_helper0 bv_size l r rez)
  ;;
end

module Op = struct
  [%%ocanren_inject type nonrec op = Shl [@@deriving gt ~options:{ show; fmt; gmap }]]
end

module T = struct
  [%%ocanren_inject
  type nonrec ('self, 'op, 'int, 'varname) t =
    | Const of 'int
    | SubjVar of 'varname
    | Binop of 'op * 'self * 'self
  [@@deriving gt ~options:{ show; fmt; gmap }]

  type ground = (ground, Op.ground, BV.ground, GT.string) t]

  let pp_logic = GT.fmt logic
  let var = subjVar
end

module Ph = struct
  [%%ocanren_inject
  type nonrec ('self, 'term) t =
    | Not of 'self
    | LE of 'term * 'term
  [@@deriving gt ~options:{ show; fmt; gmap }]

  type ground = (ground, T.ground) t]
end

let trace_cmp eta =
  trace_helper OCanren.reify (GT.fmt OCanren.logic (GT.fmt BV.cmp_t)) eta
;;

let trace_line eta = trace_helper OCanren.reify (GT.fmt OCanren.logic (GT.fmt GT.int)) eta
let trace_bv eta = trace_helper BV.reify BV.pp_logic eta

(* let trace_ph eta = trace_helper Types.Ph.reify Types.Ph.PPNew.my_logic_pp eta *)
let trace_term eta = trace_helper T.reify T.pp_logic eta
(* let trace_env eta = trace_helper Types.Env.reify Types.Env.pp_logic eta *)

(* TODO(Kakadu): represent variable names as integers *)
let terms_tbl : OCanren.tbl = Hashtbl.create 10

let evalo =
  let bv_iconst_0 = BV.build_num 0 in
  let bv_iconst_1 = BV.build_num 1 in
  let bv_iconst_2 = BV.build_num 2 in
  let bv_iconst_3 = BV.build_num 3 in
  let rec evalo ph is_tauto =
    conde
      [ fresh
          (a b a2 b2 cmp_rez)
          (ph === Ph.lE a b)
          (* (a =/= b &&& (Std.pair a b =/= Std.pair (T.const __) (T.const __))) *)
          (* (trace_term a "a") *)
          (* (trace_term b "b") *)
          (* (trace_line [%here]) *)
          (termo a (T.const a2))
          (* (trace_line [%here]) *)
          (termo b (T.const b2))
          (* (trace_line !!__LINE__ "") *)
          (conde
             [ cmp_rez === !!BV.GT &&& (is_tauto === !!false)
             ; cmp_rez =/= !!BV.GT &&& (is_tauto === !!true)
             ])
          (* (trace_line [%here]) *)
          (BV.compare_helper a2 b2 cmp_rez)
        (* (trace_bv a2 "Left  part of <=") *)
        (* (trace_bv b2 "Right part of <=") *)
        (* (trace_cmp cmp_rez "cmp_rez = ") *)
      ; fresh
          (prev rez)
          (ph === Ph.not_ prev)
          (prev =/= Ph.not_ __)
          (conde
             [ is_tauto === !!true &&& (rez === !!false)
             ; is_tauto === !!false &&& (rez === !!true)
             ])
          (evalo prev rez)
      ]
  and termo (t : T.injected) (rez : T.injected) =
    conde
      [ conde
          [ (* t === rez &&& (t === T.const bv_iconst_0); *)
            t === rez &&& (t === T.const bv_iconst_1)
            (* &&& trace_term rez "before hash_consing" *)
            (* &&& hashcons ~verbose:true terms_tbl rez *)
            (* &&& trace_term rez "after hash_consing" *)
            (* &&& success *)
          ; t === rez &&&& (t === T.const bv_iconst_2)
          ; t === rez &&&& (t === T.const bv_iconst_3)
          ]
      ]
  in
  evalo
;;

let run_ph eta = Tester.run_r Ph.reify (GT.show Ph.logic) eta

let run_bool eta =
  Tester.run_r OCanren.reify (GT.show OCanren.logic @@ GT.show GT.bool) eta
;;

let __ () =
  let open Tester in
  [%tester
    run_bool 1 (fun rez ->
      evalo (Ph.lE (T.const @@ BV.build_num 1) (T.const @@ BV.build_num 2)) rez)]
;;

let () =
  let open Tester in
  [%tester run_ph 10 (fun ph -> evalo ph !!true)]
;;
