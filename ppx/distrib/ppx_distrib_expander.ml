(*
 * OCanren PPX
 * Copyright (C) 2016-2021
 *   Dmitrii Kosarev aka Kakadu, Petr Lozov
 * St.Petersburg State University, JetBrains Research
 *)

module Pprintast_ = Pprintast
open Base
open Ppxlib
open Ppxlib.Ast_builder.Default
open Ppxlib.Ast_helper
open Printf
module Format = Caml.Format
open Myhelpers

let use_logging = true

let log fmt =
  if use_logging
  then Format.kasprintf (fun s -> Format.printf "%s\n%!" s) fmt
  else Format.ifprintf Format.std_formatter fmt
;;

let failwiths ?(loc = Location.none) fmt = Location.raise_errorf ~loc fmt

let notify fmt =
  Printf.ksprintf
    (fun s ->
      let _cmd = Printf.sprintf "notify-send \"%s\"" s in
      let (_ : int) = Caml.Sys.command _cmd in
      ())
    fmt
;;

let ( @@ ) = Caml.( @@ )

module Naming = struct end

let nolabel = Asttypes.Nolabel

(* let get_param_names pcd_args =
  let (Pcstr_tuple pcd_args) = pcd_args in
  extract_names pcd_args
;; *)

let mangle_construct_name name =
  let low =
    String.mapi
      ~f:(function
        | 0 -> Char.lowercase
        | _ -> Fn.id)
      name
  in
  match low with
  | "val" | "if" | "else" | "for" | "do" | "let" | "open" | "not" -> low ^ "_"
  | _ -> low
;;

let lower_lid lid = Location.{ lid with txt = mangle_construct_name lid.Location.txt }

let has_name_attr (xs : attributes) =
  let exception Found of string in
  try
    List.iter xs ~f:(function
        | { attr_loc; attr_name = { txt = "name" }; attr_payload = PStr [ si ] } ->
          let open Ast_pattern in
          let p = pstr_eval (pexp_constant (pconst_string __ __ none)) nil in
          parse p attr_loc ~on_error:(fun _ -> ()) si (fun s -> raise (Found s))
        | _ -> ());
    None
  with
  | Found s -> Some s
;;

let decorate_with_attributes tdecl ptype_attributes = { tdecl with ptype_attributes }

include struct
  let make_typ_exn ?(ccompositional = false) ~loc oca_logic_ident kind typ =
    let rec helper = function
      | [%type: int] as t -> oca_logic_ident ~loc:t.ptyp_loc t
      | t ->
        (match t.ptyp_desc with
        | Ptyp_constr ({ txt = Ldot (Lident "GT", s) }, []) ->
          (* ptyp_constr ~loc (oca_logic_ident ~loc:t.ptyp_loc) [ t ] *)
          oca_logic_ident ~loc:t.ptyp_loc t
        | Ptyp_constr ({ txt = Ldot (Lident "GT", "list") }, xs) ->
          ptyp_constr
            ~loc
            (Located.mk
               ~loc:t.ptyp_loc
               (lident_of_list [ "OCanren"; "Std"; "List"; kind ]))
            (List.map ~f:helper xs)
        | Ptyp_constr ({ txt = Ldot (path, "ground") }, xs) ->
          ptyp_constr ~loc (Located.mk ~loc (Ldot (path, kind))) (List.map ~f:helper xs)
        | Ptyp_constr ({ txt = Lident "ground" }, xs) ->
          ptyp_constr ~loc (Located.mk ~loc (Lident kind)) xs
        | Ptyp_tuple [ l; r ] ->
          ptyp_constr
            ~loc
            (Located.mk
               ~loc:t.ptyp_loc
               (lident_of_list [ "OCanren"; "Std"; "Pair"; kind ]))
            [ helper l; helper r ]
        | Ptyp_constr ({ txt = Lident s }, []) -> oca_logic_ident ~loc:t.ptyp_loc t
        | Ptyp_constr (({ txt = Lident "t" } as id), xs) ->
          oca_logic_ident ~loc:t.ptyp_loc @@ ptyp_constr ~loc id (List.map ~f:helper xs)
        | _ -> t)
    in
    match typ with
    | { ptyp_desc = Ptyp_constr (id, args) } ->
      if ccompositional
      then helper typ
      else (
        let ttt = ptyp_constr ~loc id (List.map ~f:helper args) in
        oca_logic_ident ~loc ttt)
    | { ptyp_desc = Ptyp_tuple [ l; r ] } ->
      ptyp_constr
        ~loc
        (Located.mk ~loc @@ lident_of_list [ "OCanren"; "Std"; "Pair"; kind ])
        (List.map ~f:helper [ l; r ])
    | _ -> failwiths "can't generate %s type: %a" kind Pprintast_.core_type typ
  ;;

  let ltypify_exn ?(ccompositional = false) ~loc typ =
    let oca_logic_ident ~loc = Located.mk ~loc (lident_of_list [ "OCanren"; "logic" ]) in
    make_typ_exn
      ~ccompositional
      ~loc
      (fun ~loc t -> ptyp_constr ~loc (oca_logic_ident ~loc:t.ptyp_loc) [ t ])
      "logic"
      typ
  ;;

  let gtypify_exn ?(ccompositional = false) ~loc typ =
    make_typ_exn ~ccompositional ~loc (fun ~loc t -> t) "ground" typ
  ;;

  let%expect_test _ =
    let loc = Location.none in
    let test i =
      let t2 =
        match i.pstr_desc with
        | Pstr_type (_, [ { ptype_manifest = Some t } ]) ->
          ltypify_exn ~ccompositional:true ~loc t
        | _ -> assert false
      in
      Format.printf "%a\n%!" Pprintast_.core_type t2
    in
    test [%stri type t1 = (int * int) Std.List.ground];
    [%expect
      {| (int OCanren.logic, int OCanren.logic) OCanren.Std.Pair.logic Std.List.logic |}];
    ()
  ;;
end

let injectify ~loc typ =
  let oca_logic_ident ~loc = Located.mk ~loc (Ldot (Lident "OCanren", "ilogic")) in
  let add_ilogic ~loc t = ptyp_constr ~loc (oca_logic_ident ~loc) [ t ] in
  let rec mangle_typ t =
    (* Format.printf "HERR %a\n%!" PPP.core_type t; *)
    (* .... ground ~~~> injected ...
       .... t      ~~~> .... t ilogic
    *)
    match t.ptyp_desc with
    | Ptyp_constr ({ txt = Ldot (Lident "GT", s) }, []) ->
      ptyp_constr ~loc (oca_logic_ident ~loc:t.ptyp_loc) [ t ]
    | Ptyp_constr ({ txt = Ldot (path, "ground") }, []) ->
      ptyp_constr ~loc (Located.mk ~loc (Ldot (path, "injected"))) []
    | Ptyp_constr ({ txt = Lident "t" }, xs) ->
      add_ilogic ~loc
      @@ ptyp_constr ~loc (Located.mk ~loc (Lident "t")) (List.map ~f:mangle_typ xs)
    | Ptyp_constr ({ txt = Lident "ground" }, xs) ->
      ptyp_constr ~loc (Located.mk ~loc (Lident "injected")) (List.map ~f:mangle_typ xs)
    | _ -> t
  in
  let ttt = mangle_typ typ in
  ttt
;;

let%expect_test _ =
  let loc = Location.none in
  let test i =
    let t2 =
      match i.pstr_desc with
      | Pstr_type (_, [ { ptype_manifest = Some t } ]) -> injectify ~loc t
      | _ -> assert false
    in
    Format.printf "%a\n%!" Pprintast_.core_type t2
  in
  test [%stri type nonrec x = GT.int t];
  [%expect {|    GT.int OCanren.ilogic t OCanren.ilogic |}];
  test [%stri type nonrec ground = ground t];
  [%expect {|    injected t OCanren.ilogic |}];
  ()
;;

type kind =
  | Reify
  | Prj_exn

let process_main ~loc base_tdecl (rec_, tdecl) =
  let is_rec =
    match rec_ with
    | Recursive -> true
    | Nonrecursive -> false
  in
  let ltyp =
    let ptype_manifest =
      match tdecl.ptype_manifest with
      | None -> failwith "no manifest"
      | Some ({ ptyp_desc = Ptyp_constr (id, args) } as typ) ->
        Some (ltypify_exn ~loc typ)
      | t -> t
    in
    let ptype_attributes =
      List.filter tdecl.ptype_attributes ~f:(fun attr ->
          match attr.attr_name.txt with
          | "distrib" -> false
          | _ -> true)
    in
    { tdecl with ptype_name = Located.mk ~loc "logic"; ptype_manifest; ptype_attributes }
  in
  let names = extract_names tdecl.ptype_params in
  let injected_typ =
    let ptype_manifest =
      match tdecl.ptype_manifest with
      | None -> failwith ""
      | Some ({ ptyp_desc = Ptyp_constr (id, args) } as typ) ->
        Option.some (injectify ~loc typ)
      | t -> t
    in
    type_declaration
      ~loc
      ~name:(Located.mk ~loc "injected")
      ~private_:Public
      ~kind:Ptype_abstract
      ~cstrs:[]
      ~params:(List.map names ~f:(fun s -> Typ.var s, (NoVariance, NoInjectivity)))
      ~manifest:ptype_manifest
  in
  let creators =
    let name cd = mangle_construct_name cd.pcd_name.txt in
    match base_tdecl.ptype_kind with
    | Ptype_variant cds ->
      List.map cds ~f:(fun cd ->
          let name =
            match has_name_attr cd.pcd_attributes with
            | None -> name cd
            | Some name -> name
          in
          match cd.pcd_args with
          | Pcstr_tuple xs ->
            let args = List.map xs ~f:(fun _ -> Ppxlib.gen_symbol ()) in
            let add_args rhs =
              match args with
              | [] -> [%expr fun () -> [%e rhs]]
              | args ->
                List.fold_right ~init:rhs args ~f:(fun x acc ->
                    Exp.fun_ nolabel None (Pat.var (Located.mk ~loc x)) acc)
            in
            [%stri
              let [%p Pat.var ~loc (Located.mk ~loc name)] =
                [%e
                  add_args
                    [%expr
                      OCanren.inji
                        [%e
                          Exp.construct
                            (Located.map_lident cd.pcd_name)
                            (if List.is_empty args
                            then None
                            else
                              Some (Exp.mytuple ~loc (List.map args ~f:(Exp.lident ~loc))))]]]
              ;;]
          | _ -> failwith "constructors with records are not implemented")
    | Ptype_record _ ->
      failwiths
        "%s %d Record constructors are not implemented"
        Caml.__FILE__
        Caml.__LINE__
    | Ptype_open | Ptype_abstract ->
      failwiths
        "%s %d Open and abstract types are not supported"
        Caml.__FILE__
        Caml.__LINE__
  in
  let mk_arg_reifier s = sprintf "r%s" s in
  let make_reifier_gen ~kind ?(typ = None) inner_func is_rec tdecl =
    let pat, base_reifier, name =
      match kind with
      | Reify -> [%pat? reify], [%expr OCanren.reify], "reify"
      | Prj_exn -> [%pat? prj_exn], [%expr OCanren.prj_exn], "prj_exn"
    in
    let manifest =
      match tdecl.ptype_manifest with
      | None ->
        failwiths
          "types without manifest are not allowed %s %d"
          Caml.__FILE__
          Caml.__LINE__
      | Some m -> m
    in
    let add_args, add_heading, add_to_gmap =
      let loc = tdecl.ptype_loc in
      let args rhs =
        List.fold_right names ~init:rhs ~f:(fun name acc ->
            [%expr fun [%p Pat.var (Located.mk ~loc (mk_arg_reifier name))] -> [%e acc]])
      in
      let heading rhs =
        let rhs =
          List.fold_right
            names
            ~f:(fun s acc ->
              [%expr
                let* [%p Pat.var (Located.mk ~loc s)] =
                  [%e Exp.lident ~loc (mk_arg_reifier s)]
                in
                [%e acc]])
            ~init:rhs
        in
        [%expr
          let open Env.Monad.Syntax in
          let* _shallowr = [%e base_reifier] in
          [%e
            if is_rec
            then
              [%expr
                Reifier.fix (fun rself ->
                    Reifier.compose
                      [%e base_reifier]
                      (let* self = rself in
                       [%e rhs]))]
            else [%expr Reifier.compose [%e base_reifier] [%e rhs]]]]
      in
      let add_to_gmap init =
        List.fold_left ~init names ~f:(fun acc s ->
            [%expr [%e acc] [%e Exp.lident ~loc s]])
      in
      args, heading, add_to_gmap
    in
    let rname_of_lident =
      let rec helper acc = function
        | Lident s -> sprintf "%s_%s" acc s
        | Ldot (x, s) -> sprintf "%s_%s" (helper acc x) s
        | Lapply (_, _) -> failwith "Not supported"
      in
      helper ""
    in
    let rec helper typ : _ list * expression =
      match typ with
      | { ptyp_desc = Ptyp_constr ({ txt = Lident "ground" }, _) } -> [], [%expr self]
      | { ptyp_desc = Ptyp_var s } -> [], pexp_ident ~loc (Located.mk ~loc (lident s))
      | [%type: GT.int] | { ptyp_desc = Ptyp_constr ({ txt = Lident "int" }, []) } ->
        [], [%expr _shallowr]
      | { ptyp_desc = Ptyp_constr ({ txt = Ldot (m, _) }, args) } ->
        let rhs = pexp_ident ~loc (Located.mk ~loc (Ldot (m, name))) in
        let name = rname_of_lident (Ldot (m, name)) in
        let acc, args =
          List.fold_right
            args
            ~init:([ name, rhs ], [])
            ~f:(fun arg (acc, args) ->
              let acc2, arg0 = helper arg in
              acc2 @ acc, arg0 :: args)
        in
        acc, Exp.apply ~loc (pexp_ident ~loc (Located.mk ~loc @@ lident name)) args
      | _ -> failwiths ~loc:typ.ptyp_loc "not supported: %a" Pprintast.core_type typ
    in
    let body, add_binds =
      match manifest.ptyp_desc with
      | Ptyp_constr ({ txt }, args) ->
        let acc, add =
          let foo = [%expr GT.gmap t] in
          let acc, args =
            List.fold_right
              ~init:([], [])
              ~f:(fun s (prefixes, args) ->
                let prefix, arg = helper s in
                prefix @ prefixes, (nolabel, arg) :: args)
              args
          in
          acc, pexp_apply ~loc foo args
        in
        ( inner_func add
        , fun (init : expression) ->
            List.fold_left acc ~init ~f:(fun acc (ident, rhs) ->
                [%expr
                  let* [%p Pat.var ~loc (Located.mk ~loc ident)] = [%e rhs] in
                  [%e acc]]) )
      | _ -> failwiths "should not happen %s %d" Caml.__FILE__ Caml.__LINE__
    in
    let pat =
      match typ with
      | None -> pat
      | Some t -> ppat_constraint ~loc pat t
    in
    pstr_value
      ~loc
      Nonrecursive
      [ value_binding ~loc ~pat ~expr:[%expr [%e add_args (add_heading (add_binds body))]]
      ]
  in
  let make_reifier is_rec tdecl =
    let manifest =
      match tdecl.ptype_manifest with
      | None ->
        failwiths
          "types without manifest are not allowed %s %d"
          Caml.__FILE__
          Caml.__LINE__
      | Some m -> m
    in
    make_reifier_gen
      ~kind:Reify
      ~typ:
        (if List.is_empty tdecl.ptype_params
        then
          Some [%type: (_, [%t ltypify_exn ~ccompositional:true ~loc manifest]) Reifier.t]
        else None)
      (fun add ->
        [%expr
          let rec foo = function
            | Var (v, xs) -> Var (v, Stdlib.List.map foo xs)
            | Value x -> Value ([%e add] x)
          in
          Env.Monad.return foo])
      is_rec
      tdecl
  in
  let make_prj_exn is_rec tdecl =
    let manifest =
      match tdecl.ptype_manifest with
      | None ->
        failwiths
          "types without manifest are not allowed %s %d"
          Caml.__FILE__
          Caml.__LINE__
      | Some m -> m
    in
    make_reifier_gen
      ~kind:Prj_exn
      ~typ:
        (if List.is_empty tdecl.ptype_params
        then
          Some [%type: (_, [%t gtypify_exn ~ccompositional:true ~loc manifest]) Reifier.t]
        else None)
      (fun add -> [%expr Env.Monad.return [%e add]])
      is_rec
      tdecl
  in
  List.concat
    [ [ pstr_type ~loc Nonrecursive [ base_tdecl ] ]
    ; [ pstr_type ~loc rec_ [ decorate_with_attributes tdecl base_tdecl.ptype_attributes ]
      ]
    ; [ pstr_type ~loc rec_ [ decorate_with_attributes ltyp base_tdecl.ptype_attributes ]
      ]
    ; [ pstr_type ~loc rec_ [ injected_typ ] ]
    ; [ make_prj_exn is_rec tdecl; make_reifier is_rec tdecl ]
    ; creators
    ]
;;

let process_composable =
  List.map ~f:(fun tdecl ->
      let loc = tdecl.pstr_loc in
      match tdecl.pstr_desc with
      | Pstr_type (flg, [ t ]) ->
        (match t.ptype_manifest with
        | Some m ->
          pstr_type
            ~loc
            Nonrecursive
            [ { t with
                ptype_attributes =
                  [ attribute
                      ~loc
                      ~name:(Located.mk ~loc "deriving")
                      ~payload:(PStr [ [%stri reify] ])
                  ]
              }
            ]
        | None -> tdecl)
      | _ -> tdecl)
;;
