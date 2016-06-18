# OCanren

OCanren is a strongly-typed embedding of [miniKanren](http://minikanren.org) relational 
programming language into [Objective Caml] (http://ocaml.org). More precisely, OCanren
implements [microKanren](http://webyrd.net/scheme-2013/papers/HemannMuKanren2013.pdf) 
with [disequality constraints] (http://scheme2011.ucombinator.org/papers/Alvis2011.pdf).

The correspondence between original MiniKanren and OCanren constructs is shown below:

| miniKanren                        | OCanren                                         |
| --------------------------------- | ------------------------------------------------|
| `#u`                              | success                                         |
| `#f`                              | failure                                         |
| `((==) a b)`                      | `(a === b)`                                     |
| `((=/=) a b)`                     | `(a =/= b)`                                     |
| `(conde (a b ...) (c d ...) ...)` | `conde [a &&& b &&& ...; c &&& d &&& ...; ...]` |
| `(fresh (x y ...) a b ...      )` | `fresh (x y ...) a b ...`                       |

In addition, OCanren introduces explicit disjunction (`|||`) and conjunction
(`&&&`) operators for goals.

## Injecting and Projecting User-Type Data

To make it possible to work with OCanren, user-type data have to be *injected* into
logic domain. In the simplest case (non-parametric, non-recursive) the function

```ocaml
inj : 'a -> 'a logic
```

can be used for this purpose:

```ocaml
inj 1
```

```ocaml
inj true
```

```ocaml
inj "abc"
```

There is also a prefix synonym `!!` for `inj`.

If the type is parametric (but non-recursive), then (as a rule) all its type parameters
have to be injected as well:

```ocaml
!! (gmap(option) (!!) (Some x))
```

```ocaml
!! (gmap(pair) (!!) (!!) (x, y))
```
 
Here `gmap(type)` is a type-indexed morphism for the type `type`; it can be written
by hands, or constructed using one of the existing generic programming 
frameworks (the library itself uses [GT](https://github.com/dboulytchev/generic-transformers)).

If the type is recursive, then, as a rule, it has to be abstracted from itself, and then
injected as in the previous case, for example,

```ocaml
type tree = Leaf | Node of tree * tree
```

is converted into

```ocaml
type 'self tree = Leaf | Node of 'self * 'self

let rec inj_tree t = !! (gmap(tree) inj_tree t)
```

Pragmatically speaking, it is desirable to make a type fully abstract, thus
logic variables can be placed in arbitrary position, for example, 

```ocaml
type ('a, 'b, 'self) tree = Leaf of 'a | Node of 'b * 'self * 'self

let rec inj_tree t = !! (gmap(tree) (!!) (!!) inj_tree t)

```

instead of

```ocaml
type tree = Leaf of int | Node of string * t * t
```

Symmetrically, there is a projection function `prj` (and a prefix
synonym `!?`), which can be used to project logical values into
regular ones. Note, that this function is partial, and can
raise `Not_a_value` exception. There is failure-continuation-passing
version of `prj`, which can be used to react on this situation. See
autogenerated documentation for details.

## Bool, Nat, List

There are three predefined types

| Regular lists   | OCanren              |
|-----------------|----------------------|
| `[]`            | `nil`                |
| `[x]`           | `!< x`               |
| `[x; y]`        | `x %< y`             |
| `[x; y; z]`     | `x % (y %< z)`       |
| `x::y::z::tl`   | `x % (y % (z % tl))` |
| `x::xs`         | `x % xs`             |

## Run

## Installation

Prerequisites:

- [ocaml](http://ocaml.org) version >= 4.01.0
- [camlp5](http://camlp5.gforge.inria.fr) version >= 6.11
- [findlib](http://projects.camlcity.org/projects/findlib.html)
- [GT](https://github.com/dboulytchev/generic-transformers)

Build steps:

- `./configure`
- `make`
- `make check` (optional)
- `make install` (to install), `make uninstall` (to uninstall)
- `make doc` (optional)

# More info

See autogenerated documentation or samples in `/regression` subdirectory.



