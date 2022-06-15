module type EXTRA = sig
  type t

  open Logic

  val neq : int ilogic -> int ilogic -> t -> t option
  val is_interesting_var : Term.Var.t -> t -> bool
  val get_domain_size: Term.Var.t -> t -> int list option
  val trace : t -> unit
end

module Make : functor (E : EXTRA) -> sig
  include DISEQ_SIG.S with type extra := E.t

  val pp : Format.formatter -> t -> unit

  val cut_off_wc_without_domain: t -> t option
  val debug_enriching_subst: t -> E.t -> unit
end


val set_logging : bool -> unit
