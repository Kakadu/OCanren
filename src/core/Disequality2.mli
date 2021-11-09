module type EXTRA = sig end

module Make : functor (_ : EXTRA) -> sig
  include DISEQ_SIG.S
end
