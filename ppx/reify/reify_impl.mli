module Format = Format

type naming =
  | Old_naming
  | New_naming

type config = { mutable naming_style : naming }

val config : config
val is_old : unit -> bool
val is_new : unit -> bool

type kind =
  | Reify
  | Prj_exn

val typ_for_kind : kind -> string
val string_of_kind : kind -> string
val unwrap_kind : loc:Warnings.loc -> kind -> Parsetree.expression * string

module type NAME_MANGLER = sig
  val mangle_lident :
       loc:Warnings.loc
    -> Longident.t
    -> ((Parsetree.core_type list -> Parsetree.core_type) -> 'a)
    -> 'a
end

val make_new_mangler : kind -> string -> (module NAME_MANGLER)

val make :
     (module NAME_MANGLER)
  -> (loc:Warnings.loc -> Parsetree.core_type -> Parsetree.core_type)
  -> loc:Warnings.loc
  -> Parsetree.core_type
  -> Parsetree.core_type

val ltypify_exn : loc:Warnings.loc -> string -> Parsetree.core_type -> Parsetree.core_type
val gtypify_exn : loc:Warnings.loc -> string -> Parsetree.core_type -> Parsetree.core_type
val make_fmapt_body : loc:Warnings.loc -> Parsetree.expression -> int -> Parsetree.expression
val make_reifier_for_tuple : loc:Warnings.loc -> kind -> 'a list -> Parsetree.expression

val create_lident_mangler :
     [< `Injected | `Prj_exn | `Reify ]
  -> loc:Warnings.loc
  -> Parsetree.core_type list lazy_t
  -> Longident.t
  -> Parsetree.core_type

val reifier_of_core_type :
     ?reifier_for_var:(string -> string)
  -> loc:Warnings.loc
  -> kind
  -> Parsetree.core_type
  -> Parsetree.expression

val make_reifier_composition :
     pat:Parsetree.pattern
  -> ?typ:Parsetree.core_type option
  -> kind
  -> Parsetree.type_declaration
  -> Parsetree.structure_item

val make_reifier_name : Parsetree.type_declaration -> string
val make_prj_name : Parsetree.type_declaration -> string

(*
val make_prj_type :
  loc:Warnings.loc ->
  Parsetree.core_type -> Parsetree.type_declaration -> Parsetree.core_type
val make_reifier_type :
  loc:Warnings.loc ->
  Parsetree.core_type -> Parsetree.type_declaration -> Parsetree.core_type *)
val make_reifier :
  loc:Warnings.loc -> Parsetree.core_type -> Parsetree.type_declaration -> Parsetree.structure_item

val make_prj :
  loc:Warnings.loc -> Parsetree.core_type -> Parsetree.type_declaration -> Parsetree.structure_item

val process_str : Parsetree.type_declaration -> Parsetree.structure_item list
val process_sig : Parsetree.type_declaration -> Parsetree.signature_item list
