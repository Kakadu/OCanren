(* open Core
open Logic

(** Tabling primitives.
    Tabling allows to cache answers of the goal between different queries.

  Usage:
    General form : [Tabling.tabled/tabledrec n g] where [n] is the number of parameters and [g] is the goal.
    Returns modified `tabled` goal.

    1) For non-recursive goals:

       [let g = Tabling.(tabled two) (fun q r -> q === r)]

    2) For recursive goals:
       In this case it is necessery to `abstract` from recursive calls.
       The goal should take additional (first) argument [grec] and use it instead of recursive calls to itself.

       [let g = Tabling.(tabledrec one) (fun grec q -> (q === O) ||| (fresh (n) (q === S n) &&& (grec n)))]
*)
module Tabling : sig
  val succ
    :  (unit -> (('a -> 'b) -> 'c) * ('d -> 'e -> 'f))
    -> unit
    -> ((('g, 'h) injected * 'a -> 'b) -> ('g, 'h) injected -> 'c)
       * (('i -> 'd) -> 'i * 'e -> 'f)

  val one
    :  unit
    -> ((('a, 'b) injected -> 'c) -> ('a, 'b) injected -> 'c) * (('d -> 'e) -> 'd -> 'e)

  val two
    :  unit
    -> ((('a, 'b) injected * ('c, 'd) injected -> 'e)
        -> ('a, 'b) injected
        -> ('c, 'd) injected
        -> 'e)
       * (('f -> 'g -> 'h) -> 'f * 'g -> 'h)

  val three
    :  unit
    -> ((('a, 'b) injected * (('c, 'd) injected * ('e, 'f) injected) -> 'g)
        -> ('a, 'b) injected
        -> ('c, 'd) injected
        -> ('e, 'f) injected
        -> 'g)
       * (('h -> 'i -> 'j -> 'k) -> 'h * ('i * 'j) -> 'k)

  val four
    :  unit
    -> ((('a, 'b) injected * (('c, 'd) injected * (('e, 'f) injected * ('g, 'h) injected))
         -> 'i)
        -> ('a, 'b) injected
        -> ('c, 'd) injected
        -> ('e, 'f) injected
        -> ('g, 'h) injected
        -> 'i)
       * (('j -> 'k -> 'l -> 'm -> 'n) -> 'j * ('k * ('l * 'm)) -> 'n)

  val five
    :  unit
    -> ((('a, 'b) injected
         * (('c, 'd) injected
           * (('e, 'f) injected * (('g, 'h) injected * ('i, 'j) injected)))
         -> 'k)
        -> ('a, 'b) injected
        -> ('c, 'd) injected
        -> ('e, 'f) injected
        -> ('g, 'h) injected
        -> ('i, 'j) injected
        -> 'k)
       * (('l -> 'm -> 'n -> 'o -> 'p -> 'q) -> 'l * ('m * ('n * ('o * 'p))) -> 'q)

  val tabled
    :  (unit
        -> (('a -> State.t Stream.t goal') -> 'b) * ('c -> 'a -> State.t Stream.t goal'))
    -> 'c
    -> 'b

  val tabledrec
    :  (unit
        -> (('a -> State.t Stream.t goal') -> 'b -> 'c)
           * ('d -> 'a -> State.t Stream.t goal'))
    -> (('b -> 'c) -> 'd)
    -> 'b
    -> 'c
end *)
