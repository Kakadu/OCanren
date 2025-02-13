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
open Core

(* to avoid clash with Std.List (i.e. logic list) *)
module List = Stdlib.List;;

@type 'a logic'                = 'a logic                                   with show, gmap, html, eq, compare, foldl, foldr, fmt

let logic' = logic;;

@type ('a, 'b, 'c) t = 'a * 'b * 'c with show, gmap, html, eq, compare, foldl, foldr, fmt
let fmap f g x = GT.gmap(t) f g x;;

@type ('a, 'b, 'c) ground          = 'a * 'b * 'c                                    with show, gmap, html, eq, compare, foldl, foldr, fmt
@type ('a, 'b, 'c) logic           = ('a * 'b * 'c) logic'                           with show, gmap, html, eq, compare, foldl, foldr, fmt

type ('a, 'b, 'c, 'd, 'e, 'f) injected = ('a * 'b * 'c, ('d * 'e * 'f) Logic.logic) Logic.injected

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
      method show    fa fb fc = GT.show(logic') (fun l -> GT.show(ground) fa fb fc l)
    end
}

let inj f g p x = to_logic (GT.gmap(ground) f g p x)

include Fmap3(struct
    type nonrec ('a,'b,'c) t = ('a,'b,'c) t
    let fmap eta = GT.gmap t eta
end)

let fmapt fa fb fc subj =
  let open Env.Monad in
  Env.Monad.return (GT.gmap t) <*> fa <*> fb <*> fc <*> subj

let make x y z = Logic.inj @@ distrib (x, y, z)

let reify : 'a 'b 'c 'd . ('a,'d) Reifier.t -> ('b,'e) Reifier.t -> ('c,'f) Reifier.t ->
  ( ('a * 'b * 'c), ('d * 'e * 'f) Logic.logic ) Reifier.t =
  fun ra rb rc ->
    let open Env.Monad in
  Reifier.fix (fun self ->
    Reifier.reify <..>
      chain (Reifier.zed (Reifier.rework ~fv:(fmapt ra rb rc)))
    )

let prj_exn : 'a 'b 'c 'd . ('a, 'd) Reifier.t -> ('b,'e) Reifier.t -> ('c,'f) Reifier.t ->
  ( ('a * 'b * 'c), ('d * 'e * 'f)) Reifier.t =
  fun ra rb rc ->
    let open Env.Monad in
    Reifier.fix (fun self ->
      Reifier.prj_exn <..> chain (fmapt ra rb rc))
