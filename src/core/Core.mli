(* SPDX-License-Identifier: LGPL-2.1-or-later *)
(*
 * OCanren.
 * Copyright (C) 2015-2022
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

open Logic

module State :
  sig
    (** @canonical OCanren.State.t *)
    type t
  end

(** Goal is a function that converts a state into a lazy stream of states. *)
type 'a goal'

(** @canonical OCanren.goal *)
type goal = State.t Stream.t goal'

(** {3 miniKanren basic combinators} *)

(** [call_fresh f] creates a fresh logical variable and passes it to the
    parameter *)
val call_fresh : ((_,_) injected -> goal) -> goal

(** [x === y] creates a goal, which performs a unification of [x] and [y] *)
val (===) : ('a, 'b) injected -> ('a, 'b) injected -> goal

(** [unify x y] is a prefix synonym for [x === y] *)
val unify : ('a, 'b) injected -> ('a, 'b) injected -> goal

(** [x =/= y] creates a goal, which introduces a disequality constraint for [x] and [y] *)
val (=/=) : ('a, 'b) injected -> ('a, 'b) injected -> goal

(** [diseq x y] is a prefix synonym for [x =/= y] *)
val diseq : ('a, 'b) injected -> ('a, 'b) injected -> goal

(** Call [structural var reifier checker] adds a structural constraint for future use.
 Every time substitution is updated it reifies [var] using [reifier] and checks that
  the result satisfies desired predicate [checker].

 The predicate [checker] returns false when constraint is violated.
 Call [structural] saves constraint and return substitution nonmodified.

 See also: {!debug_var}.
*)
(* val structural :
  'a  ->
  ('a , 'b) Reifier.t ->
  ('b -> bool) ->
  goal *)


(** [conj s1 s2] creates a goal, which is a conjunction of its arguments *)
val conj : goal -> goal -> goal

(** [&&&] is a left-associative infix synonym for [conj] *)
val (&&&) : goal -> goal -> goal

(** [disj s1 s2] creates a goal, which is a disjunction of its arguments *)
val disj : goal -> goal -> goal

(** [|||] is a left-associative infix synonym for [disj] *)
val (|||) : goal -> goal -> goal

(** [?| [s1; s2; ...; sk]] calculates [s1 ||| (s2 ||| ... ||| sk)...)] for a non-empty list of goals
    (note the {i right} association)
*)
val (?|) : goal list -> goal

(** [conde] is a synonym for [?|] *)
val conde : goal list -> goal

(** [?& [s1; s2; ...; sk]] calculates [s1 &&& (s2 && ... &&& sk)...)] for a non-empty list of goals
    (note the {i right} association)
*)
val (?&) : goal list -> goal

(** {2 Some predefined goals} *)

(** [success] always succeeds *)
val success : goal

(** [failure] always fails *)
val failure : goal

(** {2 Combinators to produce fresh variables} *)
module Fresh :
  sig
    (** [succ num f] increments the number of free logic variables in
        a goal; can be used to get rid of ``fresh'' syntax extension
    *)
    val succ : ('a -> 'b goal') -> ((_,_) injected -> 'a) -> 'b goal'

    (** Zero logic parameters *)
    val zero : 'a -> 'a

    (** {3 One to five logic parameter(s)} *)
    val one   : ((_,_) injected->                                                         goal) -> goal
    val two   : ((_,_) injected -> (_,_) injected ->                                           goal) -> goal
    val three : ((_,_) injected -> (_,_) injected -> (_,_) injected ->                             goal) -> goal
    val four  : ((_,_) injected -> (_,_) injected -> (_,_) injected -> (_,_) injected ->               goal) -> goal
    val five  : ((_,_) injected -> (_,_) injected -> (_,_) injected -> (_,_) injected -> (_,_) injected -> goal) -> goal

    (** {3 One to five logic parameter(s), conventional names} *)
    val q     : ((_,_) injected ->                                                         goal) -> goal
    val qr    : ((_,_) injected -> (_,_) injected ->                                           goal) -> goal
    val qrs   : ((_,_) injected -> (_,_) injected -> (_,_) injected ->                             goal) -> goal
    val qrst  : ((_,_) injected -> (_,_) injected -> (_,_) injected -> (_,_) injected ->               goal) -> goal
    val pqrst : ((_,_) injected -> (_,_) injected -> (_,_) injected -> (_,_) injected -> (_,_) injected -> goal) -> goal
  end

(** {2 Top-level running primitives} *)

(** The primitive [delay] helps to construct recursive goals, which depend on themselves. For example,
    we can't write [let rec fives q = (q === !!5) ||| (fives q)] because the generation of this goal leads to
    infinite recursion. The correct way to implement this is [let rec fives q = (q === !!5) ||| delay (fun () -> fives q)]

    See also syntax extension [defer].
*)
val delay : (unit -> goal) -> goal

(** [run n g h] runs a goal [g] with [n] logical parameters and passes reified results to the handler [h].
    The number of parameters is encoded using variadic machinery {i à la} Olivier Danvy and represented by
    a number of predefined numerals and successor function (see below). The reification replaces each variable,
    passed to [g], with the stream of values, associated with that variable as the goal succeeds.

    See also original Olivier's Danvy
    {{: https://www.brics.dk/RS/98/12/BRICS-RS-98-12.pdf}paper}
    ``Functional Unparsing''.

    Examples:

    - [run one        (fun q   -> q === !!5)               (fun qs    -> ...)]. Here [qs] --- a stream of all values, associated with the variable [q].
    - [run two        (fun q r -> q === !!5 ||| r === !!6) (fun qs rs -> ...)]. Here [qs], [rs] --- streams of all values, associated with the variable [q] and [r], respectively.
    - [run (succ one) (fun q r -> q === !!5 ||| r === !!6) (fun qs rs -> ...)]. The same as the above.
*)
val run : (unit ->
            ('a -> State.t -> 'b) * ('c -> Env.t -> 'd) *
            ('b -> 'c * State.t Stream.t) * ('e -> 'd -> 'f)) ->
           'a -> 'e -> 'f Stream.t

(** Successor function *)
val succ : (unit ->
            ('a -> State.t -> 'b) * ('c -> Env.t -> 'd) * ('e -> 'f * 'g) *
            ('h -> 'i -> 'j)) ->
           unit ->
           ((('k, 'l) injected -> 'a) -> State.t -> ('k, 'l) injected * 'b) *
           (('m, 'n) injected * 'c -> Env.t -> ('m, 'n) reified * 'd) *
           ('o * 'e -> ('o * 'f) * 'g) * (('p -> 'h) -> 'p * 'i -> 'j)

(** A module with predefined type aliases for numerals [one], [succ one], etc. *)
module NUMERAL_TYPS : sig
  type ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h) one = unit ->
    ((('a, 'b) injected -> 'c goal') ->
    State.t ->
    ('a, 'b) injected * 'c)
    * (('d, 'e) injected -> Env.t -> ('d, 'e) reified)
    * ('f -> 'f)
    * (('g -> 'h) -> 'g -> 'h)

  type ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j, 'k, 'l, 'm, 'n, 'o) two = unit ->
    ((('a, 'b) injected -> ('c, 'd) injected -> 'e goal') ->
    State.t ->
    ('a, 'b) injected * (('c, 'd) injected * 'e))
    * (('f, 'g) injected * ('h, 'i) injected ->
      Env.t ->
      ('f, 'g) reified * ('h, 'i) reified)
    * ('j * ('k * 'l) -> ('j * 'k) * 'l)
    * (('m -> 'n -> 'o) -> 'm * 'n -> 'o)

  type ('a,'c,'d,'e,'f,'g,'h,'i,'j,'k,'l,'m,'n,'o,'p,'q,'r,'s,'t,'u,'v) three = unit ->
    ((('a, 'c) injected ->
      ('d, 'e) injected ->
      ('f, 'g) injected ->
      'h goal') ->
    State.t ->
    ('a, 'c) injected
    * (('d, 'e) injected * (('f, 'g) injected * 'h)))
    * (('i, 'j) injected * (('k, 'l) injected * ('m, 'n) injected) ->
      Env.t ->
      ('i, 'j) reified * (('k, 'l) reified * ('m, 'n) reified))
    * ('o * ('p * ('q * 'r)) -> ('o * ('p * 'q)) * 'r)
    * (('s -> 't -> 'u -> 'v) -> 's * ('t * 'u) -> 'v)

  type ('a,'b,'c,'d,'e,'f,'g,'h,'i,'j,'k,'l,'m,'n,'o,'p,'q,'r,'s,'t,'u,'v,'w,'x,'y,'z,'a1) four =unit ->
    ((('a, 'b) injected ->
     ('c, 'd) injected ->
     ('e, 'f) injected ->
     ('g, 'h) injected ->
     'i goal') ->
    State.t ->
    ('a, 'b) injected
    * (('c, 'd) injected
      * (('e, 'f) injected * (('g, 'h) injected * 'i))))
    * (('j, 'k) injected
       * (('l, 'm) injected
         * (('n, 'o) injected * ('p, 'q) injected)) ->
      Env.t ->
      ('j, 'k) reified
      * (('l, 'm) reified * (('n, 'o) reified * ('p, 'q) reified)))
    * ('r * ('s * ('t * ('u * 'v))) ->
      ('r * ('s * ('t * 'u))) * 'v)
    * (('w -> 'x -> 'y -> 'z -> 'a1) ->
      'w * ('x * ('y * 'z)) ->
      'a1)

end

(** {3 Predefined numerals (one to five)} *)
val one : (_, _, _, _, _, _, _, _) NUMERAL_TYPS.one
val two : (_, _, _, _, _, _, _, _, _, _, _, _, _, _, _) NUMERAL_TYPS.two
val three : (_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _) NUMERAL_TYPS.three
val four : (_, _, _, _, _, _, _, _, _, _, _, _, _, _,_,_,_,_, _, _, _, _, _,_,_,_,_) NUMERAL_TYPS.four


(** {3 The same numerals with conventional names} *)
val q : (_, _, _,  _, _, _,  _, _) NUMERAL_TYPS.one
val qr : (_, _, _, _, _, _, _, _, _, _, _, _, _, _, _) NUMERAL_TYPS.two
val qrs : (_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _) NUMERAL_TYPS.three
val qrst : (_, _, _, _, _, _, _, _, _, _, _, _, _, _,_,_,_,_, _, _, _, _, _,_,_,_,_) NUMERAL_TYPS.four

IFDEF STATS THEN
val unification_counter : unit -> int
val unification_time    : unit -> Timer.span
val conj_counter        : unit -> int
val disj_counter        : unit -> int
val delay_counter       : unit -> int
END

(** The call [debug_var var reifier callback] performs reification of variable [var] in a current state using [reifier] and passes list of answer to [callback] (multiple answers can arise in presence of disequality constraints). The [callback] can investigate reified value and construct required goal to continue search.

See also: {!structural}.
*)
val debug_var : ('a, 'b) injected -> ('a, 'b) Reifier.t -> ('b list -> goal) -> goal

(** The goal [only_head f] returns no answers when [f] returns:
  - empty stream when [f] returns empty stream;
  - hangs when [f] hangs during search for first answer;
  - stream with head answer if [f] returns stream that has at least 1 answer.
*)
val only_head : goal -> goal

(* module PrunesControl : sig
  val reset : unit -> unit
  val enable_skips: on:bool -> unit
  val set_max_skips: int -> unit
  val incr : unit -> unit
  val is_exceeded: unit -> bool
  val skipped_prunes : unit -> int
end *)
