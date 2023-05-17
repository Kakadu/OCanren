(* SPDX-License-Identifier: LGPL-2.1-or-later *)
(*
 * OCanren.
 * Copyright (C) 2015-2023
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

(** {1 Relational numbers} *)

open Logic
open Core

(** Abstract nat type *)
type 'a ground_fuly =
| O
| S of 'a [@@deriving gt ~options:{ show; gmap; html; eq; compare; foldl; foldr; fmt }]

type 'a t = 'a ground_fuly
[@@deriving gt ~options:{ show; gmap; html; eq; compare; foldl; foldr; fmt }]

(** Ground nat are ismorphic for regular one *)
type ground = ground t [@@deriving gt ~options:{ show; gmap; html; eq; compare; foldl; foldr; fmt }]

(** Logic nat *)
type logic = logic t Logic.logic [@@deriving gt ~options:{ show; gmap; html; eq; compare; foldl; foldr; fmt }]

(** Type synonyms to comply with the generic naming scheme *)
type nat       = ground [@@deriving gt ~options:{ show; gmap; html; eq; compare; foldl; foldr; fmt }]
type nat_logic = logic  [@@deriving gt ~options:{ show; gmap; html; eq; compare; foldl; foldr; fmt }]

(** Logic injection (for reification) *)
val inj : ground -> logic

(** {2 Relational API} *)

(** A type synonym for injected nat *)
type injected = injected t Logic.ilogic

(** {3:reifiers Reifiers} *)

(** Reifier *)
val reify : (injected, logic) Reifier.t

(** Shallow non-variable projection *)
val prj_exn : (injected, ground) Reifier.t

(** Synonyms to comply with the generic naming scheme *)
val reify_nat   : (injected, logic) Reifier.t
val prj_exn_nat : (injected, ground) Reifier.t
  
(** [of_int n] converts integer [n] into [ground]; negative integers become [O] *)
val of_int : int -> ground

(** [to_int g] converts ground [g] into integer *)
val to_int : ground -> int

(** Make injected [nat] from ground one *)
val nat : ground -> injected

(** {3 Constructors} *)

(** A zero. The name {!o} was selected because it looks similar to arabic digit 0. *)
val o : injected

(** Constructs next number (a successor) after the provided one. *)
val s : injected -> injected

(** A synomym for {!o}. *)
val zero : injected

(** An alias for [s zero]. *)
val one  : injected

(** A synomym for {!s}. *)
val succ : injected -> injected

(** {3 Built-in relations} *)

(** Relational addition. *)
val addo  : injected -> injected -> injected -> goal

(** Infix synonym for [addo]. *)
val ( + ) : injected -> injected -> injected -> goal

(** Relational multiplication. *)
val mulo  : injected -> injected -> injected -> goal

(** Infix synonym for [mulo]. *)
val ( * ) : injected -> injected -> injected -> goal

(** Comparisons *)
val leo : injected -> injected -> Bool.injected -> goal
val geo : injected -> injected -> Bool.injected -> goal
val gto : injected -> injected -> Bool.injected -> goal
val lto : injected -> injected -> Bool.injected -> goal

(** Comparisons as goals *)
val (<=) : injected -> injected -> goal
val (>=) : injected -> injected -> goal
val (>)  : injected -> injected -> goal
val (<)  : injected -> injected -> goal

(** Minimum/maximum *)
val maxo : injected -> injected -> injected -> goal
val mino : injected -> injected -> injected -> goal
