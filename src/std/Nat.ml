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

open Logic
open Core

(* Rewriter adds many explict module paths, but in OCanren.Std it is painful
   An alternative would be to add command line switch which removes explicit module paths
*)
module OCanren = struct
  type 'a ilogic = 'a Logic.ilogic
  type 'a logic = 'a Logic.logic= | Var   of GT.int * 'a logic GT.list
                                  | Value of 'a
  [@@deriving gt ~options:{ show; gmap; html; eq; compare; foldl; foldr; fmt }]

  let logic = Logic.logic
  module Env = Env
  module Reifier = Reifier
  let prj_exn = Logic.prj_exn
  let reify = Logic.reify
end

[%%ocanren_inject
type 'a ground = O | S of 'a [@@deriving gt ~options:{ show; gmap; html; eq; compare; foldl; foldr; fmt }]
]

type 'a t = 'a ground_fuly
[@@deriving gt ~options:{ show; gmap; html; eq; compare; foldl; foldr; fmt }]

type nat  = nat ground
[@@deriving gt ~options:{ show; gmap; html; eq; compare; foldl; foldr; fmt }]
type nat_logic   = nat_logic ground_logic
[@@deriving gt ~options:{ show; gmap; html; eq; compare; foldl; foldr; fmt }]

type ground  = nat
[@@deriving gt ~options:{ show; gmap; html; eq; compare; foldl; foldr; fmt }]
type logic   = nat_logic
[@@deriving gt ~options:{ show; gmap; html; eq; compare; foldl; foldr; fmt }]
type injected = injected ground_injected

let logic = {
  logic with
  GT.plugins =
    object(this)
      method compare = logic.GT.plugins#compare
      method gmap    = logic.GT.plugins#gmap
      method eq      = logic.GT.plugins#eq
      method foldl   = logic.GT.plugins#foldl
      method foldr   = logic.GT.plugins#foldr
      method html    = logic.GT.plugins#html
      method fmt     = logic.GT.plugins#fmt
      method show    = GT.show(Logic.logic) (fun l -> GT.show(ground_fuly) this#show l)
    end
}

let rec of_int n = if n <= 0 then O else S (of_int (n-1))
let rec to_int   = function O -> 0 | S n -> 1 + to_int n

let rec inj n = to_logic (GT.gmap ground_fuly inj n)

let reify =
  let open Env.Monad.Syntax in
  Reifier.fix (fun self ->
  Reifier.compose Reifier.reify
      (
        let* fr = self in
        let rec foo = function
          | Var (v, xs) ->
            Var (v, Stdlib.List.map foo xs)
          | Value x -> Value (GT.gmap ground_fuly fr x)
        in
        Env.Monad.return foo
    ))

let prj_exn : (injected, ground) Reifier.t =
  let ( >>= ) = Env.Monad.bind in
  Reifier.fix (fun self ->
    Reifier.compose Reifier.prj_exn
    ( self >>= fun fr ->
      Env.Monad.return (fun x -> GT.gmap ground_fuly fr x))
    )

let reify_nat = reify
let prj_exn_nat = prj_exn

let o   = Logic.inj O
let s x = Logic.inj (S x)

let rec nat n = Logic.inj @@ (GT.gmap ground_fuly) nat n

let zero = o
let one  = s o
let succ = s

let rec addo x y z =
  conde [
    (x === o) &&& (z === y);
    Fresh.two (fun x' z' ->
       (x === (s x')) &&&
       (z === (s z')) &&&
       (addo x' y z')
    )
  ]

let (+) = addo

let rec mulo x y z =
  conde
    [ (x === o) &&& (z === o)
    ; Fresh.two (fun x' z' ->
        (x === (s x')) &&&
        (addo y z' z) &&&
        (mulo x' y z')
      )
    ]

let ( * ) = mulo

let rec leo x y b =
  conde [
    (x === o) &&& (b === Bool.truo);
    (x =/= o) &&& (y === o) &&& (b === Bool.falso);
    Fresh.two (fun x' y' ->
      (x === (s x')) &&& (y === (s y')) &&& (leo x' y' b)
    )
  ]

let geo x y b = leo y x b

let (<=) x y = leo x y Bool.truo
let (>=) x y = geo x y Bool.truo

let rec gto x y b = conde
  [ (x =/= o) &&& (y === o) &&& (b === Bool.truo)
  ; (x === o) &&& (b === Bool.falso)
  ; Fresh.two (fun x' y' ->
      (x === s x') &&& (y === s y') &&& (gto x' y' b)
    )
  ]

let lto x y b = gto y x b

let (>) x y = gto x y Bool.truo
let (<) x y = lto x y Bool.truo

let maxo x y z = conde [
  (z === x) &&& (x >= y);
  (z === y) &&& (x <  y)
]
               
let mino x y z = conde [
  (z === x) &&& (x <= y);
  (z === y) &&& (x >  y)
]
