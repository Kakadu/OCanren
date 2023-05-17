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

type ('a, 'b, 'c) t = 'a * 'b * 'c
[@@deriving gt ~options:{ show; gmap; html; eq; compare; foldl; foldr; fmt }]

let fmap f g h x = GT.gmap(t) f g h x

type ('a, 'b, 'c) ground          = 'a * 'b * 'c
[@@deriving gt ~options:{ show; gmap; html; eq; compare; foldl; foldr; fmt }]
type ('a, 'b, 'c) logic           = ('a * 'b * 'c) Logic.logic
[@@deriving gt ~options:{ show; gmap; html; eq; compare; foldl; foldr; fmt }]

open Core

type ('a, 'b, 'c) injected = ('a * 'b * 'c) Logic.ilogic

let logic = {
  logic with
  GT.plugins =
    object(this)
      method compare       = logic.GT.plugins#compare
      method gmap          = logic.GT.plugins#gmap
      method eq            = logic.GT.plugins#eq
      method foldl         = logic.GT.plugins#foldl
      method foldr         = logic.GT.plugins#foldr
      method html          = logic.GT.plugins#html
      method fmt           = logic.GT.plugins#fmt
      method show fa fb fc = GT.show(Logic.logic) (fun l -> GT.show(ground) fa fb fc l)
    end
}

let inj f g h p = Logic.to_logic (GT.gmap(ground) f g h p)

let make x y z = Logic.inj (x, y, z)

let triple = make

module Reifier = Logic.Reifier

let reify : 'a 'b 'c 'd . ('a, 'b) Reifier.t -> ('c, 'd) Reifier.t -> ('e, 'f) Reifier.t ->
  (('a, 'c, 'e) injected, ('b, 'd, 'f) logic) Reifier.t =
  fun ra rb rc ->
    let ( >>= ) = Env.Monad.bind in
    Reifier.fix (fun self ->
      Reifier.compose Reifier.reify
       ( ra >>= fun fa ->
         rb >>= fun fb ->
         rc >>= fun fc ->
          let rec foo = function
              | Logic.Var (v, xs) ->
                Logic.Var (v, Stdlib.List.map foo xs)
              | Value x -> Value (GT.gmap t fa fb fc x)
          in
          Env.Monad.return foo
        ))

let prj_exn : ('a, 'b) Reifier.t -> ('c, 'd) Reifier.t -> ('e, 'f) Reifier.t ->
  (('a, 'c, 'e) injected, ('b, 'd, 'f) ground) Reifier.t =
  fun ra rb rc ->
    let ( >>= ) = Env.Monad.bind in
    Reifier.compose Reifier.prj_exn
    (ra >>= fun fa ->
     rb >>= fun fb ->
     rc >>= fun fc ->
     Env.Monad.return (fun x -> GT.gmap t fa fb fc x))
