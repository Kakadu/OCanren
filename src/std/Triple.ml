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
module List = Stdlib.List

type 'a logic'                = 'a logic
[@@deriving gt ~options:{show; gmap;  eq; compare; foldl; foldr; fmt}]
let logic' = logic;;

type ('a, 'b, 'c) ground          = 'a * 'b * 'c
[@@deriving gt ~options:{show; gmap;  eq; compare; foldl; foldr; fmt}]

type ('a, 'b, 'c) logic           = ('a * 'b * 'c) logic'
[@@deriving gt ~options:{show; gmap;  eq; compare; foldl; foldr; fmt}]

type ('a, 'b, 'c, 'd, 'e, 'f) groundi = (('a, 'c, 'e) ground, ('b, 'd, 'f) logic) injected

let logic = {
  logic with
  GT.plugins =
    object(this)
      method compare       = logic.GT.plugins#compare
      method gmap          = logic.GT.plugins#gmap
      method eq            = logic.GT.plugins#eq
      method foldl         = logic.GT.plugins#foldl
      method foldr         = logic.GT.plugins#foldr
      method fmt           = logic.GT.plugins#fmt
      method show fa fb fc = GT.show(logic') (fun l -> GT.show(ground) fa fb fc l)
    end
}

let inj f g h p = to_logic (GT.gmap(ground) f g h p)

module T =
  struct
    type ('a, 'b, 'c) t = 'a * 'b * 'c
    let fmap f g h x = GT.gmap(ground) f g h x
  end

include T
include Fmap3 (T)

let pair x y z = Logic.inj @@ distrib (x, y, z)

let prjc fa fb fc onvar env xs = prjc fa fb fc onvar env xs
