(*
 * OCanren PPX
 * Copyright (C) 2016-2021
 *   Dmitrii Kosarev aka Kakadu, Petr Lozov
 * St.Petersburg State University, JetBrains Research
 *)

module PPP = Printast
open Base
open Ppxlib
open Ppxlib.Ast_builder.Default
open Ppxlib.Ast_helper
open Printf
module Format = Caml.Format

let failwiths fmt = Format.ksprintf failwith fmt

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

(* TODO: maybe use Ppxlib.name_type_params_in_td ? *)
let extract_names =
  List.map ~f:(fun (typ, _) ->
      match typ.ptyp_desc with
      | Ptyp_var s -> s
      | _ ->
        failwith
          (Caml.Format.asprintf "Don't know what to do with %a" Pprintast.core_type typ))
;;

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

module Located = struct
  include Located

  (* let mknoloc txt = { txt; loc = Location.none } *)
  let map_loc ~f l = { l with txt = f l.txt }
end

module Exp = struct
  include Exp

  let mytuple ~loc ?(attrs = []) = function
    (* | [] -> Exp.construct (Located.mk ~loc (lident "()")) None *)
    | [] -> failwith "Bad argument: mytuple"
    | [ x ] -> x
    | xs -> tuple ~loc ~attrs xs
  ;;

  let apply ~loc f = function
    | [] -> f
    | xs -> apply ~loc f xs
  ;;
end

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

(*
let make_reifier_composition ~pat tdecl =
  let add_args, add_heading, add_to_gmap =
    let loc = tdecl.ptype_loc in
    let args rhs =
      List.fold_right names ~init:rhs ~f:(fun name acc ->
          [%expr fun [%p Pat.var (Located.mk ~loc (mk_arg_reifier name))] -> [%e acc]])
    in
    let heading rhs =
      let rhs =
        [%expr
          [%e
            List.fold_right
              names
              ~f:(fun s acc ->
                [%expr
                  let* [%p Pat.var (Located.mk ~loc s)] =
                    [%e Exp.ident (Located.mk ~loc (Lident (mk_arg_reifier s)))]
                  in
                  [%e acc]])
              ~init:rhs]]
      in
      [%expr
        let open Env.Monad.Syntax in
        [%e
          if is_rec
          then
            [%expr
              Reifier.fix (fun rself ->
                  Reifier.compose
                    [%e base_reifier]
                    (let* self = rself in
                     let* _shallowr = OCanren.reify in
                     [%e rhs]))]
          else [%expr Reifier.compose [%e base_reifier] [%e rhs]]]]
    in
    let add_to_gmap init =
      List.fold_left ~init names ~f:(fun acc s ->
          [%expr [%e acc] [%e Exp.ident (Located.mk ~loc (Lident s))]])
    in
    args, heading, add_to_gmap
  in
  let rec helper typ =
    Format.eprintf "%a\n%!" (PPP.payload 0) (PTyp typ);
    match typ with
    | { ptyp_desc = Ptyp_constr ({ txt = Lident "ground" }, _) } -> [%expr self]
    (* | Ptyp_constr ({ txt = Ldot (Lident "GT", _) }, []) -> [%expr OCanren.reify] *)
    (* | Ptyp_constr ({ txt = Ldot (m, "ground") }, args) ->
        pexp_ident ~loc (Located.mk ~loc (Ldot (m, "reify"))) *)
    | { ptyp_desc = Ptyp_var s } -> pexp_ident ~loc (Located.mk ~loc (lident s))
    | [%type: GT.int] | { ptyp_desc = Ptyp_constr ({ txt = Lident "int" }, []) } ->
      base_reifier
    | { ptyp_desc = Ptyp_constr ({ txt = Ldot (Lident m, _) }, args) } ->
      pexp_apply
        ~loc
        (pexp_ident ~loc (Located.mk ~loc (Ldot (lident m, "reify"))))
        (List.map args ~f:(fun t -> nolabel, helper t))
    | _ -> [%expr reify23s]
  in
  let body =
    match tdecl.ptype_manifest with
    | None -> failwiths "should not happen %s %d" Caml.__FILE__ Caml.__LINE__
    | Some m ->
      (match m.ptyp_desc with
      | Ptyp_constr ({ txt }, args) ->
        let add =
          let foo = [%expr GT.gmap t] in
          pexp_apply ~loc foo (List.map ~f:(fun s -> Nolabel, helper s) args)
        in
        inner_func add
      | _ ->
        (* Format.eprintf "%a\n%!" Pprintast.core_type m; *)
        (* Format.eprintf "%a\n%!" (PPP.payload 0) (PTyp m); *)
        failwiths "should not happen %s %d" Caml.__FILE__ Caml.__LINE__)
  in
  pstr_value
    ~loc
    Nonrecursive
    [ value_binding
        ~loc (* ~pat:(Pat.constraint_ [%pat? reify] typ) *)
        ~pat
        ~expr:[%expr [%e add_args (add_heading body)]]
    ]
;;
*)
let process_main ~loc base_tdecl (rec_, tdecl) =
  let is_rec =
    match rec_ with
    | Recursive -> true
    | Nonrecursive -> false
  in
  let ltyp =
    let oca_logic_ident ~loc = Located.mk ~loc (Ldot (Lident "OCanren", "logic")) in
    let mangle_typ t =
      match t.ptyp_desc with
      | Ptyp_constr ({ txt = Ldot (Lident "GT", s) }, []) ->
        ptyp_constr ~loc (oca_logic_ident ~loc:t.ptyp_loc) [ t ]
      | Ptyp_constr ({ txt = Ldot (path, "ground") }, xs) ->
        ptyp_constr ~loc (Located.mk ~loc (Ldot (path, "logic"))) xs
      | Ptyp_constr ({ txt = Lident "ground" }, xs) ->
        ptyp_constr ~loc (Located.mk ~loc (Lident "logic")) xs
      | _ -> t
    in
    let ptype_manifest =
      match tdecl.ptype_manifest with
      | None -> failwith ""
      | Some { ptyp_desc = Ptyp_constr (id, args) } ->
        let ttt = ptyp_constr ~loc id (List.map ~f:mangle_typ args) in
        Option.some (ptyp_constr ~loc (oca_logic_ident ~loc) [ ttt ])
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
    let oca_logic_ident ~loc = Located.mk ~loc (Ldot (Lident "OCanren", "ilogic")) in
    let rec mangle_typ t =
      match t.ptyp_desc with
      | Ptyp_constr ({ txt = Ldot (Lident "GT", s) }, []) ->
        ptyp_constr ~loc (oca_logic_ident ~loc:t.ptyp_loc) [ t ]
      | Ptyp_constr ({ txt = Ldot (path, "ground") }, []) ->
        ptyp_constr ~loc (Located.mk ~loc (Ldot (path, "injected"))) []
      | Ptyp_constr ({ txt = Lident "ground" }, xs) ->
        ptyp_constr ~loc (Located.mk ~loc (Lident "injected")) (List.map ~f:mangle_typ xs)
      | _ -> t
    in
    let ptype_manifest =
      match tdecl.ptype_manifest with
      | None -> failwith ""
      | Some { ptyp_desc = Ptyp_constr (id, args) } ->
        let ttt = ptyp_constr ~loc id (List.map ~f:mangle_typ args) in
        Option.some (ptyp_constr ~loc (oca_logic_ident ~loc) [ ttt ])
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
                              Some
                                (Exp.mytuple
                                   ~loc
                                   (List.map args ~f:(fun s ->
                                        Exp.ident (Located.mk ~loc @@ lident s)))))]]]
              ;;]
          | _ -> failwith "constructors with records are not implemented "
          (* [%stri let () = ()] *))
    | _ -> assert false
  in
  let mk_arg_reifier s = sprintf "r%s" s in
  let make_reifier_gen ~pat base_reifier inner_func is_rec tdecl =
    let add_args, add_heading, add_to_gmap =
      let loc = tdecl.ptype_loc in
      let args rhs =
        List.fold_right names ~init:rhs ~f:(fun name acc ->
            [%expr fun [%p Pat.var (Located.mk ~loc (mk_arg_reifier name))] -> [%e acc]])
      in
      let heading rhs =
        let rhs =
          [%expr
            [%e
              List.fold_right
                names
                ~f:(fun s acc ->
                  [%expr
                    let* [%p Pat.var (Located.mk ~loc s)] =
                      [%e Exp.ident (Located.mk ~loc (Lident (mk_arg_reifier s)))]
                    in
                    [%e acc]])
                ~init:rhs]]
        in
        [%expr
          let open Env.Monad.Syntax in
          [%e
            if is_rec
            then
              [%expr
                Reifier.fix (fun rself ->
                    Reifier.compose
                      [%e base_reifier]
                      (let* self = rself in
                       let* _shallowr = OCanren.reify in
                       [%e rhs]))]
            else [%expr Reifier.compose [%e base_reifier] [%e rhs]]]]
      in
      let add_to_gmap init =
        List.fold_left ~init names ~f:(fun acc s ->
            [%expr [%e acc] [%e Exp.ident (Located.mk ~loc (Lident s))]])
      in
      args, heading, add_to_gmap
    in
    let rec helper typ =
      Format.eprintf "%a\n%!" (PPP.payload 0) (PTyp typ);
      match typ with
      | { ptyp_desc = Ptyp_constr ({ txt = Lident "ground" }, _) } -> [%expr self]
      (* | Ptyp_constr ({ txt = Ldot (Lident "GT", _) }, []) -> [%expr OCanren.reify] *)
      (* | Ptyp_constr ({ txt = Ldot (m, "ground") }, args) ->
        pexp_ident ~loc (Located.mk ~loc (Ldot (m, "reify"))) *)
      | { ptyp_desc = Ptyp_var s } -> pexp_ident ~loc (Located.mk ~loc (lident s))
      | [%type: GT.int] | { ptyp_desc = Ptyp_constr ({ txt = Lident "int" }, []) } ->
        base_reifier
      | { ptyp_desc = Ptyp_constr ({ txt = Ldot (Lident m, _) }, args) } ->
        pexp_apply
          ~loc
          (pexp_ident ~loc (Located.mk ~loc (Ldot (lident m, "reify"))))
          (List.map args ~f:(fun t -> nolabel, helper t))
      | _ -> [%expr reify23s]
    in
    let body =
      match tdecl.ptype_manifest with
      | None -> failwiths "should not happen %s %d" Caml.__FILE__ Caml.__LINE__
      | Some m ->
        (match m.ptyp_desc with
        | Ptyp_constr ({ txt }, args) ->
          let add =
            let foo = [%expr GT.gmap t] in
            pexp_apply ~loc foo (List.map ~f:(fun s -> Nolabel, helper s) args)
          in
          inner_func add
        | _ ->
          (* Format.eprintf "%a\n%!" Pprintast.core_type m; *)
          (* Format.eprintf "%a\n%!" (PPP.payload 0) (PTyp m); *)
          failwiths "should not happen %s %d" Caml.__FILE__ Caml.__LINE__)
    in
    (* let typ = [%type: (_, _) Reifier.t] in *)
    pstr_value
      ~loc
      Nonrecursive
      [ value_binding
          ~loc (* ~pat:(Pat.constraint_ [%pat? reify] typ) *)
          ~pat
          ~expr:[%expr [%e add_args (add_heading body)]]
      ]
  in
  let make_reifier =
    make_reifier_gen
      ~pat:[%pat? reify]
      [%expr OCanren.reify]
      (fun add ->
        [%expr
          let rec foo = function
            | Var (v, xs) -> Var (v, Stdlib.List.map foo xs)
            | Value x -> Value ([%e add] x)
          in
          Env.Monad.return foo])
  in
  let make_prj_exn =
    make_reifier_gen
      ~pat:[%pat? prj_exn]
      [%expr OCanren.prj_exn]
      (fun add -> [%expr Env.Monad.return [%e add]])
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
