module type EXTRA = sig
  type t

  open Logic

  val neq : int ilogic -> int ilogic -> t -> t option
  val is_interesting_var : Term.Var.t -> t -> bool
  val trace : t -> unit
end

module Make : functor (E : EXTRA) -> sig
  include DISEQ_SIG.S with type extra := E.t

  val pp : Format.formatter -> t -> unit

  val cut_off_wc_without_domain: t -> t option
end
