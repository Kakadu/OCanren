open Ppx_core
open Ast_builder.Default
open Printf
let (@@) = Caml.(@@)

module Attrs = struct
  let default =
    Attribute.declare "sexp.default"
      Attribute.Context.label_declaration
      Ast_pattern.(pstr (pstr_eval __ nil ^:: nil))
      (fun x -> x)

  let drop_default =
    Attribute.declare "sexp.sexp_drop_default"
      Attribute.Context.label_declaration
      Ast_pattern.(pstr nil)
      ()

  let drop_if =
    Attribute.declare "sexp.sexp_drop_if"
      Attribute.Context.label_declaration
      Ast_pattern.(pstr (pstr_eval __ nil ^:: nil))
      (fun x -> x)
end

module TypeNameMap = Map.M(String)

module FoldInfo = struct
  (* using fields of structure below we can generate ground type and the logic type *)
  type item = {param_name:string; rtyp: core_type; ltyp: core_type}
  exception ItemFound of item
  type t = item list

  let param_for_rtyp typ ts =
    let typ_repr =
      Pprintast.core_type Caml.Format.str_formatter typ;
      Caml.Format.flush_str_formatter ()
    in
    try List.iter ts (fun i ->
                    let new_repr : string =
                      Pprintast.core_type Caml.Format.str_formatter i.rtyp;
                      Caml.Format.flush_str_formatter ()
                    in
                    if String.equal new_repr typ_repr then raise (ItemFound i)
                  );
        None
    with ItemFound i -> Some i

    let map ~f (xs: t) = List.map ~f xs
    let empty = []
    let is_empty : t -> bool = List.is_empty
    let extend param_name rtyp ltyp ts =
(*      printf "extending by `%s`\n%!" param_name;*)
      {param_name; rtyp; ltyp} :: ts
end

let extract_names = List.map ~f:(fun typ ->
    match typ.ptyp_desc with
    | Ptyp_var s -> s
    | _ ->
      Buffer.clear Caml.Format.stdbuf;
      Pprintast.core_type Caml.Format.str_formatter typ;
      failwith (Printf.sprintf "Don't know what to do with %s" (Caml.Format.flush_str_formatter ()))
  )

(* let str_type_ ?loc flg = pstr_type ~loc flg  *)

let nolabel =
      Asttypes.Nolabel

let get_param_names pcd_args =
  let Pcstr_tuple pcd_args  = pcd_args in
  extract_names pcd_args

let mangle_construct_name name =
  let low = String.mapi ~f:(function 0 -> Char.lowercase | _ -> fun x -> x ) name in
  match low with
  | "val" | "if" | "else" | "for" | "do" | "let" | "open" | "not" -> low ^ "_"
  | _ -> low

let lower_lid lid = Location.{lid with txt = mangle_construct_name lid.Location.txt }

module Location = struct
  include Location
  let mknoloc txt = { txt; loc = none }
  let map_loc ~f l = {l with txt = f l.txt}
end

let prepare_distribs ~loc tdecl fmap_decl =
  let open Location in
  let open Longident in
  let Ptype_variant constructors = tdecl.ptype_kind in

  let gen_module_str = Location.mknoloc @@ "For_" ^ tdecl.ptype_name.txt in
  let distrib_lid = mknoloc Longident.(Ldot (Lident gen_module_str.txt, "distrib")) in
  [ pstr_module ~loc @@ module_binding ~loc ~name:(Location.mknoloc "T")
     ~expr:(pmod_structure ~loc
        [ fmap_decl
        ; pstr_type ~loc Nonrecursive
            [ type_declaration ~loc
                ~params:tdecl.ptype_params
                ~kind:Ptype_abstract
                ~private_: Public
                ~cstrs:[] (* TODO: something is wrong here *)
                ~manifest:(Some (ptyp_constr ~loc (mknoloc @@ Lident tdecl.ptype_name.txt) @@ List.map ~f:fst tdecl.ptype_params))
                ~name:(mknoloc "t") ]
        ])
  ; pstr_module ~loc @@ module_binding ~loc ~name:gen_module_str
     ~expr:(pmod_apply ~loc
        (pmod_ident ~loc (mknoloc @@ Lident (match tdecl.ptype_params with [] -> "Fmap" | xs -> sprintf "Fmap%d" (List.length xs)) ))
        (pmod_ident ~loc (mknoloc @@ Lident "T")) )
  ] @ (List.map constructors ~f:(fun {pcd_name; pcd_args} ->
      let names = get_param_names pcd_args |> List.mapi ~f:(fun i _ -> sprintf "a%d" i) in
      let body =
        let constr_itself args = econstruct (constructor_declaration ~loc ~name:(mknoloc pcd_name.txt) ~res:None ~args:pcd_args) args in
        match names with
        | [] -> constr_itself None
        | [one] -> constr_itself (Some (pexp_ident ~loc @@ mknoloc (Lident one)))
        | xs -> (* construct tuple here *)
            constr_itself (Some (pexp_tuple ~loc @@ List.map ~f:(fun name -> pexp_ident ~loc @@ mknoloc (Lident name)) xs))
      in
      let body = [%expr inj [%e pexp_apply ~loc (pexp_ident ~loc distrib_lid) [nolabel, body] ] ] in
      pstr_value ~loc Asttypes.Nonrecursive [
      value_binding ~loc ~pat:(ppat_var ~loc @@ lower_lid pcd_name)
        ~expr:(match names with
        | [] -> pexp_fun ~loc nolabel None (ppat_construct ~loc (mknoloc (Lident "()")) None) body
        | names -> List.fold_right ~f:(fun name acc -> pexp_fun ~loc nolabel None (ppat_var ~loc @@ mknoloc name) acc) names ~init:body)
    ]
    )
    )

(* At the moment we genrate fmap here but it is totally fine to reuse the one genrated by GT *)
let prepare_fmap ~loc tdecl =
  let open Location in
  let open Ast_helper in

  let param_names = extract_names (List.map ~f:fst tdecl.ptype_params) in
  let Ptype_variant constructors = tdecl.ptype_kind in
  let cases = constructors |> List.map ~f:(fun {pcd_name; pcd_args} ->
    let argnames = get_param_names pcd_args in
    let cname = pcd_name.txt in
    let clid = mknoloc @@ Longident.Lident cname in
    let make_f_expr name = pexp_ident ~loc @@ mknoloc @@ Longident.Lident ("f"^name) in
    let pc_lhs, pc_rhs =
      let wrap_one_arg typname new_name =
        pexp_apply ~loc (make_f_expr typname) [nolabel, pexp_ident ~loc @@ mknoloc @@ Longident.Lident new_name]
      in
      let get_pat_name i name = sprintf "%s_%d" name i in
      match argnames with
      | [] -> (None, None)
      | [s] -> Some (ppat_var ~loc (mknoloc s)), (Some (wrap_one_arg s s))
      | ___ ->
          Some (ppat_tuple ~loc @@ List.mapi ~f:(fun n name -> ppat_var ~loc (mknoloc @@ get_pat_name n name)) argnames),
          Some (pexp_tuple ~loc @@ List.mapi ~f:(fun n name -> wrap_one_arg name @@ get_pat_name n name) argnames)
    in
    let pc_lhs = Ast_helper.Pat.construct clid pc_lhs in
    let pc_rhs = Exp.construct clid pc_rhs in
    let pc_guard = None in
    { pc_rhs; pc_lhs; pc_guard }
  )
  in

  [%stri let rec fmap = [%e
    List.fold_right ~f:(function
      | name -> pexp_fun ~loc nolabel None (ppat_var ~loc @@ mknoloc ("f"^name))
      ) param_names ~init:(Exp.function_ cases) ] ]

let revisit_adt ~loc tdecl ctors =
  let der_typ_name = tdecl.ptype_name.Asttypes.txt in
  (* Let's forget about mutal recursion for now *)
  (* For every constructor argument we need to put ground types to parameters *)
  let mapa, full_t =
    List.fold_right
      ~f:(fun cd (n, acc_map,cs) ->
          let n,map2,new_args = List.fold_right
            ~f:(fun typ (n, map,args) ->
                  match typ with
                  | [%type: _] -> assert false
                  | {ptyp_desc = Ptyp_var s; _} -> (n, map, typ::args)
                  | arg ->
                      match FoldInfo.param_for_rtyp arg map with
                      | Some {param_name; } -> (n, map, (ptyp_var ~loc param_name)::args)
                      | None ->
                          let new_name = sprintf "a%d" n in
                          (n+1, FoldInfo.extend new_name arg arg map, (ptyp_var ~loc new_name)::args)
              )
            (match cd.pcd_args with Pcstr_tuple tt -> tt | Pcstr_record _ -> assert false)
            ~init:(n, acc_map,[])
          in
          let new_args = Pcstr_tuple new_args in
          (n, map2, { cd with pcd_args = new_args } :: cs)
      )
      ctors
      ~init:(0, FoldInfo.empty, [])
      |> (fun (_, mapa, cs) -> mapa, {tdecl with ptype_kind = Ptype_variant cs})
  in
  (* now we need to add some parameters if we collected ones *)
  let functor_typ, typ_to_add =
    if FoldInfo.is_empty mapa
    then
      let fmap_for_typ = prepare_fmap ~loc full_t in
      let show_stuff = Ppx_gt_expander.str_type_decl ~loc ~path:"" (Recursive, [tdecl]) true false in
      [], (pstr_type ~loc Nonrecursive [full_t]) :: show_stuff @ (prepare_distribs ~loc full_t fmap_for_typ)
    else
      let functor_typ =
        let extra_params = FoldInfo.map mapa
          ~f:(fun fi -> (Ast_helper.Typ.var fi.FoldInfo.param_name, Asttypes.Invariant))
        in
        let open Location in
        {full_t with ptype_params = full_t.ptype_params @ extra_params;
                     ptype_name = { full_t.ptype_name with txt = "g" ^ full_t.ptype_name.txt }}
      in

      let fmap_for_typ = prepare_fmap ~loc functor_typ in
      let show_stuff = Ppx_gt_expander.str_type_decl ~loc ~path:"" (Recursive, [functor_typ]) true false in

      let ground_typ =
        let alias_desc =
          let old_params = List.map ~f:fst tdecl.ptype_params  in
          let extra_params = FoldInfo.map ~f:(fun {FoldInfo.rtyp} -> rtyp)  mapa in
          Ptyp_constr (Location.mknoloc (Longident.Lident functor_typ.ptype_name.Asttypes.txt), old_params @ extra_params)
        in
        pstr_type ~loc Recursive
          [ { tdecl with ptype_kind = Ptype_abstract
            ; ptype_manifest = Some { ptyp_loc = Location.none; ptyp_attributes = []; ptyp_desc = alias_desc}
            } ]
      in
      (* let logic_typ =
       *   let alias_desc =
       *     let old_params = List.map ~f:fst tdecl.ptype_params  in
       *     let extra_params = FoldInfo.map ~f:(fun {FoldInfo.ltyp} -> ltyp)  mapa in
       *     ptyp_constr ~loc (Located.lident ~loc "logic")
       *       [ Ptyp_constr (Location.mknoloc (Longident.Lident functor_typ.ptype_name.Asttypes.txt), old_params @ extra_params)
       *       ]
       *   in
       *   pstr_type ~loc Recursive
       *     [ { tdecl with
       *         ptype_kind = Ptype_abstract
       *       ; ptype_manifest = Some { ptyp_loc = Location.none; ptyp_attributes = []; ptyp_desc = alias_desc}
       *       ; ptype_name = Location.map_loc ~f:((^)"l") tdecl.ptype_name
       *       } ]
       * in *)
      let generated_types =
        let functor_typ = pstr_type ~loc Nonrecursive [functor_typ] in
        [ functor_typ; ground_typ (*; logic_typ *) ]
      in
      (generated_types), (show_stuff @ [fmap_for_typ] @ (prepare_distribs ~loc functor_typ fmap_for_typ))
  in
  functor_typ @ typ_to_add

let has_to_gen_attr (xs: attributes) =
  try let _ = List.find ~f:(fun (name,_) -> String.equal name.Location.txt "distrib") xs in
      true
  with Not_found -> false

let suitable_tydecl_wrap ~on_ok ~on_fail tdecl =
  match tdecl.ptype_kind with
  | Ptype_variant cs when Option.is_none tdecl.ptype_manifest &&
                          has_to_gen_attr tdecl.ptype_attributes ->
    Attribute.explicitly_drop#type_declaration tdecl;
    on_ok cs { tdecl with ptype_attributes = [] }
  | _ -> on_fail ()

let suitable_tydecl =
  suitable_tydecl_wrap ~on_ok:(fun _ _ -> true) ~on_fail:(fun () -> false)

let str_type_decl ~loc (flg,tdls) =
  let wrap_tydecls loc ts =
    let f tdecl =
      suitable_tydecl_wrap tdecl
        ~on_ok:(fun cs tdecl -> revisit_adt ~loc tdecl cs)
        ~on_fail:(fun () ->
            failwith "Only variant types without manifest are supported")
    in
    List.concat (List.map ~f ts)
  in
  wrap_tydecls loc tdls


