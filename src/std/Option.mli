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

(** {1 Relational [option]} *)

open Logic
open Core

(** {2 GT-related API} *)

(** Synonym for regular option type *)
@type 'a t = 'a GT.option with show, gmap, html, eq, compare, foldl, foldr, fmt

(** Ground option (the regular one) *)
@type 'a ground = 'a GT.option with show, gmap, html, eq, compare, foldl, foldr, fmt

(** Logic option *)
@type 'a logic = 'a GT.option Logic.logic with show, gmap, html, eq, compare, foldl, foldr, fmt

(** {2 Relational API} *)

(** Logic injection (for reification) *)
val inj : ('a -> 'b) -> 'a ground -> 'b logic

(** A synonym for injected option *)
type ('a, 'b) groundi = ('a option, 'b option Logic.logic) Logic.injected

(** Make injected [option] from ground one with injected value *)
val option : ('a, 'b) Logic.injected option -> ('a option, 'b option Logic.logic) Logic.injected

(** {3 Reifiers} *)

(** Reifier *)
val reify : ('a, 'b) Reifier.t -> ('a option, 'b option Logic.logic) Reifier.t

(* Shallow non-variable projection *)
val prj_exn : ('a, 'b) Reifier.t -> ('a option, 'b option) Reifier.t

(** {3 Constructors} *)
(*
(** Logic dual of constructor [Some] from {!Stdlib.Option}. *)
val some : 'a -> 'a option

(** Logic dual of constructor [None] from {!Stdlib.Option}.
    It has an extra unit argument to workaround weak type variables.

    {!Stdlib.Option.t} test *)
val none : unit -> 'a option *)

val some: ('a, 'b) injected -> ('a option, 'b option Logic.logic) injected
val none: unit -> ('a option, 'b option Logic.logic) injected