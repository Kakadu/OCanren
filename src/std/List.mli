(*
 * OCanren.
 * Copyright (C) 2015-2020
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

(** {1 Relational Lists} *)

open Logic
open Core

(** Abstract list type *)
@type ('a, 'l) list =
| Nil
| Cons of 'a * 'l
with show, gmap, html, eq, compare, foldl, foldr, fmt

(** {2 GT-related API} *)

(** Type synonym to prevent toplevel [logic] from being hidden *)
@type 'a logic' = 'a logic with show, gmap, html, eq, compare, foldl, foldr, fmt

(** Synonym for abstract list type *)
@type ('a, 'l) t = ('a, 'l) list with show, gmap, html, eq, compare, foldl, foldr, fmt

(** Ground lists (isomorphic to regular ones) *)
@type 'a ground = ('a, 'a ground) t with show, gmap, html, eq, compare, foldl, foldr, fmt

(** Logic lists (with the tails as logic lists) *)
@type 'a logic  = ('a, 'a logic) t logic' with show, gmap, html, eq, compare, foldl, foldr, fmt

(** {2 Relational API} *)

(** A synonym for injected list *)
type 'a groundi = ('a, 'a groundi) t Logic.ilogic

(** {3 Constructors} *)

val nil : unit -> 'a groundi

val cons : 'a  -> 'a groundi -> 'a groundi

(** Infix synonym for [cons] *)
val (%) : 'a  -> 'a groundi -> 'a groundi

(** [x %< y] is a synonym for [cons x (cons y (nil ()))] *)
val (%<) : 'a  -> 'a -> 'a groundi

(** [!< x] is a synonym for [cons x (nil ())] *)
val (!<) : 'a  ->  'a groundi

(** {3 Built-in relations} *)

(** [of_list l] converts regular OCaml list [l] into isomorphic OCanren [ground] list *)
val of_list : ('a -> 'b) -> 'a GT.list -> 'b ground

(** [to_list g] converts OCanren list [g] into regular OCaml list *)
val to_list : ('a -> 'b) -> 'a ground -> 'b GT.list

(** [inj x] makes a logic list from a ground one *)
val inj : ('a -> 'b) -> 'a ground -> 'b logic

(** Make injected [list] from ground one of injected elements *)
val list : 'a  GT.list -> 'a groundi

(** Reifier *)
val reify :  ('a, 'b) Reifier.t -> ('a groundi, 'b logic) Reifier.t

val prj : ('a, 'b) Reifier.t -> ('a groundi, 'b ground) Reifier.t
(*
(** Relational foldr *)
val foldro : (('a, 'b) injected -> ('acc, _ logic' as 'acc2) injected -> ('acc, 'acc2) injected -> goal) -> ('acc, 'acc2) injected -> ('a, 'b) groundi -> ('acc, 'acc2) injected -> goal

(** Relational map *)
val mapo : (('a, 'b) injected -> ('q, 'w) injected -> goal) -> ('a, 'b) groundi -> ('q, 'w) groundi -> goal

(** Relational filter *)
val filtero : (('a, 'b) injected -> Bool.groundi -> goal) -> ('a, 'b) groundi -> ('a, 'b) groundi -> goal

(** Relational lookup *)
val lookupo : (('a, 'b) injected -> Bool.groundi -> goal) -> ('a, 'b) groundi -> ('a option, 'b option logic') injected -> goal

(** Relational association list lookup *)
val assoco : ('a, 'b logic') injected -> (('a, 'c) Pair.ground, ('b logic', 'd logic') Pair.logic) groundi -> ('c, 'd logic') injected -> goal

(** Boolean list disjunctions *)
val anyo : (Bool.ground, Bool.logic) groundi -> Bool.groundi -> goal

(** Boolean list conjunction *)
val allo : (Bool.ground, Bool.logic) groundi -> Bool.groundi -> goal

(** Relational length *)
val lengtho : (_, _) groundi -> Nat.groundi -> goal

(** Relational append *)
val appendo : ('a, 'b) groundi -> ('a, 'b) groundi  -> ('a, 'b) groundi -> goal

(** Relational reverse *)
val reverso : ('a, 'b) groundi -> ('a, 'b) groundi -> goal

(** Relational occurrence check (a shortcut) *)
val membero : ('a, 'b logic') groundi  -> ('a, 'b logic') injected  -> goal

*)

(** Relational check for empty list *)
val nullo : _ groundi -> goal

(** Relational head of the list *)
val caro  : 'a groundi -> 'a -> goal

(** Alias for [caro] *)
val hdo   : 'a groundi -> 'a -> goal

(** Relational tail of the list *)
val cdro  : 'a Logic.ilogic groundi -> 'a Logic.ilogic groundi -> goal

(** Alias for [cdro] *)
val tlo   : 'a Logic.ilogic groundi -> 'a Logic.ilogic groundi -> goal
