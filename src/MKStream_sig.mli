module type S = sig
  type 'a t

  val nil : 'a t
  (* val is_nil : 'a -> bool *)
  (* val inc : (unit -> t) -> t *)
  val from_fun : (unit -> 'a t) -> 'a t
  val single : 'a -> 'a t
  (* val choice : 'a -> 'b -> Obj.t *)
  (* val case_inf :
    Obj.t ->
    f1:(unit -> Obj.t) ->
    f2:((unit -> Obj.t) -> Obj.t) ->
    f3:(Obj.t -> Obj.t) -> f4:(Obj.t -> (unit -> Obj.t) -> Obj.t) -> Obj.t *)

  val mplus : 'a t -> 'a t -> 'a t
  val bind : 'a t -> ('a -> 'b t) -> 'b t

  val msplit: 'a t -> ('a * 'a t) option

end