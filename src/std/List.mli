(* SPDX-License-Identifier: LGPL-2.1-or-later *)
(*
 * OCanren.
 * Copyright (C) 2015-2025
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

@type ('a, 'l) t = ('a, 'l) list with show, gmap, html, eq, compare, foldl, foldr, fmt

(** Ground lists (isomorphic to regular ones) *)
(* @type 'a ground     = ('a, 'a ground) t with show, gmap, html, eq, compare, foldl, foldr, fmt *)
@type 'a ground     = 'a GT.list with show, gmap, html, eq, compare, foldl, foldr, fmt

(** Logic lists (with the tails as logic lists) *)
@type 'a logic  = ('a, 'a logic) t Logic.logic with show, gmap, html, eq, compare, foldl, foldr, fmt

(** {2 Relational API} *)

(** A synonym for injected list *)
type ('a, 'b) injected = ('a ground, 'b logic) Logic.injected


(** {3 Conversions between data types} *)

(** The [of_list l] converts regular OCaml list [l] into isomorphic OCanren [ground] list.
    See [to_list] for a reverse conversion. *)
val of_list : ('a -> 'b) -> 'a GT.list -> 'b ground
[@@deprecated "Use Stdlib.List.map instead"]

(** The [to_list g] converts OCanren list [g] into regular OCaml list. See [of_list]
    for a reverse conversion. *)
(* val to_list : ('a -> 'b) -> 'a ground -> 'b GT.list *)
(* [@@deprecated "Use Stdlib.List.map instead"] *)

(** The [inj x] makes a logic list from a ground one. See [logic_to_ground_exn]
    for a partial reverse conversion. *)
val inj : ('a -> 'b) -> 'a ground -> 'b logic

(** Converts a logic list to ground one.
    @raise [Failure] when a logic variable occurs inside a list. *)
val logic_to_ground_exn: ('a -> 'b) -> 'a logic -> 'b ground

(** Make injected [list] from ground one of injected elements. The reverse conversion
    is availble only through reifiers (see {!section-reifiers} for details). *)
(* val list : 'a GT.list -> 'a injected *)
val list : ('a, 'b) Logic.injected GT.list -> ('a, 'b) injected

val to_logic: ('a -> 'b) -> 'a ground -> 'b logic

(** {3 Constructors} *)

(** A logical empty list. Extra unit parameter prevents weak type variables. *)
val nil : unit -> ('a ground, 'b logic) Logic.injected

(** A dual for [cons] (a.k.a. [::]) constructor. *)
val cons : ('a, 'b) Logic.injected  -> ('a, 'b) injected -> ('a, 'b) injected

(** Infix synonym for {!cons} *)
val (%) : ('a, 'b) Logic.injected  -> ('a, 'b) injected -> ('a, 'b) injected

(** [x %< y] is a synonym for [cons x (cons y (nil ()))] *)
val (%<) : ('a, 'b) Logic.injected  -> ('a, 'b) Logic.injected -> ('a, 'b) injected

(** [!< x] is a synonym for [cons x (nil ())] *)
val (!<) : ('a, 'b) Logic.injected  -> ('a, 'b) injected

(** {3:reifiers Reifiers} *)

(** Reifier *)
val reify :  ('a, 'b) Reifier.t -> ('a ground, 'b logic) Reifier.t

val list_reify :  ('a, 'b) Reifier.t -> ('a ground, 'b logic) Reifier.t

val prj_exn : ('a, 'b) Reifier.t -> ('a ground, 'b ground) Reifier.t
val list_prj_exn : ('a, 'b) Reifier.t -> ('a ground, 'b ground) Reifier.t
val ground_prj_exn : ('a, 'b) Reifier.t -> ('a ground, 'b ground) Reifier.t

(* val prj_to_list_exn :  ('a, 'b) Reifier.t -> ('a ground, 'b GT.list) Reifier.t *)

(* val prj : (int -> 'b ground) -> ('a, 'b) Reifier.t -> ('a ground, 'b ground) Reifier.t *)

(** {3 Built-in relations} *)

(** Relational foldr *)
val foldro :
  (('a, 'b) Logic.injected ->
    ('c, 'd) Logic.injected ->
    ('c, 'd) Logic.injected ->
    goal) ->
  ('c, 'd) Logic.injected ->
    ('a ground, 'b logic) Logic.injected ->
    ('c, 'd) Logic.injected ->
goal

(** Relational map *)
val mapo : (('a, 'b) Logic.injected -> ('c, 'd) Logic.injected -> goal) ->
    ('a, 'b) injected -> ('c, 'd) injected -> goal


(** Relational filter *)
val filtero : (('a, 'b) Logic.injected -> OCanren__Bool.injected -> goal) ->
    ('a ground, 'b logic) Logic.injected ->
    ('a ground, 'b logic) Logic.injected ->
    goal

(** Relational lookup *)
val lookupo : (('a, 'b) Logic.injected -> OCanren__Bool.injected -> goal) ->
    ('a ground, 'b logic) Logic.injected ->
    ('a option, 'b option Logic.logic) Logic.injected ->
    goal

(** Relational association list lookup *)
val assoco : ('a, 'b) Logic.injected ->
    (('a * 'c) ground, ('b * 'd) Logic.logic logic) Logic.injected ->
    ('c, 'd) Logic.injected ->
    goal


(** Boolean list disjunctions *)
val anyo : (bool, bool Logic.logic) injected ->
    (bool, bool Logic.logic) Logic.injected ->
    goal

(** Boolean list conjunction *)
val allo : (bool, bool Logic.logic) injected ->
    (bool, bool Logic.logic) Logic.injected ->
    goal

(** Relational length *)
val lengtho : ('a ground, 'b logic) Logic.injected ->
    (Nat.ground, Nat.logic) Logic.injected ->
    goal
(*
(** Relational append *)
val appendo : (_ ilogic as 'a) groundi -> 'a groundi -> 'a groundi -> goal

(** Relational reverse *)
val reverso : (_ ilogic as 'a)groundi -> 'a groundi -> goal

(** Relational occurrence check (a shortcut) *)
val membero : 'a ilogic groundi  -> 'a ilogic  -> goal
*)
(** Relational check for empty list *)
val nullo : ('a, 'b) injected -> goal

(** Relational head of the list *)
val caro  : ('a, 'b) injected -> ('a, 'b) Logic.injected -> goal

(** Alias for [caro] *)
val hdo   : ('a, 'b) injected -> ('a, 'b) Logic.injected -> goal

(** Relational tail of the list *)
val cdro  : ('a, 'b) injected -> ('a, 'b) injected -> goal

(** Alias for [cdro] *)
val tlo   : ('a, 'b) injected -> ('a, 'b) injected -> goal
