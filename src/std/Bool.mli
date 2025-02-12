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

(** {1 Relational booleans} *)

open Logic
open Core

(** {2 GT-related API} *)

(** Synonym for boolean type *)
@type t = GT.bool with show, html, eq, compare, foldr, foldl, gmap, fmt

(** Ground boolean (the regular one) *)
@type ground = GT.bool with show, html, eq, compare, foldr, foldl, gmap, fmt

(** Logic boolean *)
@type logic = GT.bool Logic.logic with show, html, eq, compare, foldr, foldl, gmap, fmt

(** Type synonyms to comply with the generic naming scheme *)
@type bool       = ground with show, html, eq, compare, foldr, foldl, gmap, fmt
@type bool_logic = logic  with show, html, eq, compare, foldr, foldl, gmap, fmt

(** {2 Relational API} *)

(** Logic injection (for reification) *)
val inj : ground -> logic

(** A synonym for injected boolean; use [Logic.inji] operator to make a [injected] from a regular [bool] *)
type injected = (bool, bool Logic.logic) Logic.injected

(** Reifier *)
val reify: (bool, bool Logic.logic) Reifier.t

(** Shallow reifier *)
val prj_exn: (bool  , bool) Reifier.t

(** Synonyms to comply with the generic naming scheme *)
val reify_bool   : (bool, bool Logic.logic) Reifier.t
val prj_exn_bool : (bool, bool) Reifier.t

(** Constants *)
val falso : injected
val truo  : injected

(** Sheffer stroke *)
val (|^) : injected -> injected -> injected -> goal

(** Negation *)
val noto : injected -> injected -> goal

(** Negation as a goal *)
val (~~) : injected -> goal

(** Disjunction *)
val oro : injected -> injected -> injected -> goal

(** Disjunction as a goal *)
val (||) : injected -> injected -> goal

(** Conjunction *)
val ando : injected -> injected -> injected -> goal

(** Conjunction as a goal *)
val (&&) : injected -> injected -> goal
