(*
 * OCanren.
 * Copyright (C) 2015-2021
 * Dmitri Boulytchev, Dmitry Kosarev, Alexey Syomin, Evgeny Moiseenko
 * St.Petersburg State University, JetBrains Research
 *
 * This software is free software; you can redistribute it and/or
 * modify it under the terms of the GNU Library General Public
 * License version 2, as published by the Free Software Foundation.
 *
 * This software is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.
 *
 * See the GNU Library General Public License version 2 for more details
 * (enclosed in the file COPYING).
 *)

(** {3 Logic values} *)

(** A type of a logic value *)
@type 'a logic =
| Var   of GT.int * 'a logic GT.list
| Value of 'a with show, gmap, html, eq, compare, foldl, foldr, fmt

(** [to_logic x] makes a logic value from a regular one *)
val to_logic : 'a -> 'a logic

(** [from_logic x] makes a regular value from a logic one.
    Raises exception [Not_a_value] if [x] contains free variables
*)
val from_logic : 'a logic -> 'a

(** {3 Injections/projections} *)
(*
(**  The type [('a, 'b) injected] describes an injection of a type ['a] into ['b] *)
type ('a, 'b) injected

(** [lift x] lifts [x] into injected doamin *)
val lift : 'a -> ('a, 'a) injected

(** [inj x] injects [x] into logical [x] *)
val inj : ('a, 'b) injected -> ('a, 'b logic) injected

(** A synonym for [fun x -> inj @@ lift x] (for non-parametric types) *)
val (!!) : 'a -> ('a, 'a logic) injected

(** [prj x] returns a regular value from injected representation.
    Raises exception [Not_a_value] if [x] contains free variables
 *)
val prj : ('a, 'b) injected -> 'a
*)
(** The exception is raised when we try to extract a regular term from the answer with some free variables *)
exception Not_a_value

type 'a ilogic

(* val to_ilogic: ('a, 'b) injected -> 'b ilogic *)
val inji : 'a -> 'a ilogic

(** Reification result *)
class type ['a,'b] reified =
object
  (** Returns [true] if the term has any free logic variable inside *)
  method is_open: bool

  (** Gets the answer as regular term. Raises exception [Not_a_value] when the answer contains free variables *)
  method prj: 'a

  (** Gets the answer as a logic value using provided injection function [inj] *)
  (* method reify: (Env.t -> ('a, 'b) injected -> 'b) -> 'b *)

  (* method prjc : (Env.t -> ('a, 'b) injected -> 'a) -> 'a *)
  (* method prj_exn: (Env.t -> 'a ilogic -> 'b) -> 'b *)
  method reify: (Env.t -> 'a ilogic -> 'b) -> 'b
end

val make_rr : Env.t -> 'a ilogic -> ('a,'b) reified

(* A default shallow reifier *)
(* val reify : Env.t -> ('a, 'a logic) injected -> 'a logic *)

(* val prjc : (int -> 'a list -> 'a) -> Env.t -> ('a, 'a logic) injected -> 'a *)

(* val project : ('a, 'b) reified -> 'a *)


module ILogic : sig
  type 'a ilogic
  val inj : 'a -> 'a ilogic
end

module Reifier : sig
  (* Reifier from type `'a` into type `'b` is an `'a -> 'b` function
    * dipped into the `Env.t` monad, will see how it plays later.
    * Perhaps, it is possible to not expose the reifier type and make it itself
    * a monad or something else that composes nicely, but I haven't figured out yet.
    *)
  type ('a, 'b) t = ('a -> 'b) Env.Monad.t

  (* Some predefined reifiers from which other reifiers will be composed *)

  (* this one transforms implicit logic value into regular logic value *)
  val reify : ('a ilogic, 'a logic) t

  (* this one projects implicit logic into the underlying type,
    * handling variables with the help of the user provided function
    *)
  (* val prj : (int -> 'a) -> ('a ilogic, 'a) t *)

  (* this one projects implicit logic into the underlying type,
    * raising an exception if it finds a variable
    *)
  val prj_exn : ('a ilogic, 'a) t

  (* Interesting part --- we can apply a reifier to a value dipped into `State.t` comonad *)
  (* val apply : ('a, 'b) t -> 'a State.t -> 'b *)

  (* composition of two reifiers *)
  val compose : ('a, 'b) t -> ('b, 'c) t -> ('a, 'c) t

  (* Reifier is a profunctor, so we get combinators
    * to compose reifiers with regular functions
    *)

  val fmap : ('b -> 'c) -> ('a, 'b) t -> ('a, 'c) t

  val fcomap : ('a -> 'b) -> ('b, 'c) t -> ('a, 'c) t
end
