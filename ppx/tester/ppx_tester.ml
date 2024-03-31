(*
 * OCanren. PPX syntax extensions.
 * Copyright (C) 2016-2024
 *   Dmitrii Kosarev aka Kakadu
 * St.Petersburg State University, JetBrains Research
 *)

(**
  An extension that allows not to write errornous qh, qrh and stuff like that.
  It looks at number of lambdas in the last argument, and insert numberals as penultimate argument.

  Expands

    {[ let __ _ = [%tester runR OCanren.reify show_int show_intl (fun q -> q === !!1)] ]}

  to

  {[
    let __ _ =
      runR OCanren.reify show_int show_intl q qh
        ("<string repr of goal>", (fun q -> q === (!! 1)))
  ]}

*)

open Ppxlib

let string_of_expression e =
  Format.set_margin 1000;
  Format.set_max_indent 0;
  Format.asprintf "%a" Pprintast.expression e
;;

let name = "tester"

type mode =
  | Long of
      { runner : expression
      ; reifier : expression
      ; shower : expression
      ; n : expression
      ; relation : expression
      }
  | Short of expression * expression * expression

let pp_mode ppf = function
  | Long _ -> Format.fprintf ppf "Long"
  | Short _ -> Format.fprintf ppf "Short"
;;

let pattern () =
  let open Ast_pattern in
  let map3 pat ~f = map2 pat ~f:(fun a b -> a, b) |> map2 ~f:(fun (a, b) c -> f a b c) in
  (* let map4 pat ~f = map2 pat ~f:(fun a b -> a, b) |> map3 ~f:(fun (a, b) c d -> f a b c d) in *)
  let map5 pat ~f =
    map3 pat ~f:(fun a b c -> a, b, c) |> map3 ~f:(fun (a, b, c) d e -> f a b c d e)
  in
  let left () =
    pstr
      (pstr_eval
         (pexp_apply
            __
            ((nolabel ** __) ^:: (nolabel ** __) ^:: (nolabel ** __) ^:: (nolabel ** __) ^:: nil))
         nil
       ^:: nil
      |> map5 ~f:(fun runner reifier shower n relation ->
             Long { reifier; runner; shower; n; relation }))
  in
  let right () =
    pstr
      (pstr_eval (pexp_apply __ ((nolabel ** __) ^:: (nolabel ** __) ^:: nil)) nil ^:: nil
      |> map3 ~f:(fun a b c -> Short (a, b, c)))
  in
  left () ||| right ()
;;

let%expect_test _ =
  let loc = Location.none in
  let item = [%stri run reifier shower 5 (fun q -> q)] in
  let on_error _ = print_endline "ERROR" in
  let on_success = Format.printf "SUCCESS: %a\n%!" pp_mode in
  Ast_pattern.parse (pattern ()) loc ~on_error (PStr [ item ]) on_success;
  [%expect {| SUCCESS: Long |}];
  let item = [%stri run_int 5 (fun q -> q)] in
  Ast_pattern.parse (pattern ()) loc ~on_error (PStr [ item ]) on_success;
  [%expect {| SUCCESS: Short |}];
  let item = [%stri run_nat (-1) (fun q -> q === !!1 &&& trace_int q)] in
  Ast_pattern.parse (pattern ()) loc ~on_error (PStr [ item ]) on_success;
  [%expect {| SUCCESS: Short |}]
;;

let count_abstractions ~loc =
  let rec helper acc e =
    match e.pexp_desc with
    | Pexp_fun (_, _, _, body) -> helper (1 + acc) body
    | _ -> acc
  in
  fun rel ->
    match helper 0 rel with
    | 0 -> failwith "Bad syntax"
    | 1 -> [ [%expr OCanren.q]; [%expr qh] ]
    | 2 -> [ [%expr OCanren.qr]; [%expr qrh] ]
    | 3 -> [ [%expr OCanren.qrs]; [%expr qrsh] ]
    | 4 -> [ [%expr OCanren.qrst]; [%expr qrsth] ]
    | _ -> failwith (Printf.sprintf "5 and more arguments are not supported")
;;

let () =
  let extensions =
    [ Extension.declare name Extension.Context.Expression (pattern ()) (fun ~loc ~path:_ -> function
        | Short (runner, n, relation) ->
            let open Ppxlib.Ast_builder.Default in
            let middle = count_abstractions ~loc relation in
            let last =
              let s = string_of_expression @@ relation in
              let open Ppxlib.Ast_builder.Default in
              [%expr [%e pexp_constant ~loc (Pconst_string (s, loc, None))], [%e relation]]
            in
            pexp_apply ~loc runner
            @@ List.map (fun e -> Nolabel, e)
            @@ List.concat [ [ n ]; middle; [ last ] ]
        | Long { runner; reifier; shower; n; relation } ->
            let open Ppxlib.Ast_builder.Default in
            let middle = count_abstractions ~loc relation in
            let last =
              let s = string_of_expression @@ relation in
              let open Ppxlib.Ast_builder.Default in
              [%expr [%e pexp_constant ~loc (Pconst_string (s, loc, None))], [%e relation]]
            in
            pexp_apply ~loc runner
            @@ List.map (fun e -> Nolabel, e)
            @@ List.concat [ [ reifier; shower; n ]; middle; [ last ] ])
    ]
  in
  Ppxlib.Driver.register_transformation ~extensions name
;;
