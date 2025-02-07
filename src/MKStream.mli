
type t
val nil : t
val is_nil : 'a -> bool
val inc : (unit -> t) -> t
val from_fun : (unit -> t) -> t
val single : 'a -> t
val choice : 'a -> 'b -> Obj.t
val case_inf :
  Obj.t ->
  f1:(unit -> Obj.t) ->
  f2:((unit -> Obj.t) -> Obj.t) ->
  f3:(Obj.t -> Obj.t) -> f4:(Obj.t -> (unit -> Obj.t) -> Obj.t) -> Obj.t

val mplus : t -> t -> t
val bind : t -> ('a -> t) -> t

val  msplit : t -> ('a *  t) option