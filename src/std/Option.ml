(*
 * OCanren.
 * Copyright (C) 2015-2021
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
(* module List = Stdlib.List *)

@type 'a logic'        = 'a logic                       with show, gmap, html, eq, compare, foldl, foldr, fmt

let logic' = logic;;

@type 'a ground        = 'a GT.option                   with show, gmap, html, eq, compare, foldl, foldr, fmt
@type 'a logic         = 'a GT.option logic'            with show, gmap, html, eq, compare, foldl, foldr, fmt

let logic = {
  logic with
  GT.plugins =
    object(this)
      method compare    = logic.GT.plugins#compare
      method gmap       = logic.GT.plugins#gmap
      method eq         = logic.GT.plugins#eq
      method foldl      = logic.GT.plugins#foldl
      method foldr      = logic.GT.plugins#foldr
      method html       = logic.GT.plugins#html
      method fmt        = logic.GT.plugins#fmt
      method show    fa = GT.show(logic') (fun l -> GT.show(GT.option) fa l)
    end
};;

@type 'a t = 'a ground with show, gmap, html, eq, compare, foldl, foldr, fmt;;
let t = ground

let inj f x = to_logic (GT.(gmap option) f x)

type 'a groundi = 'a ground ilogic

let rec reify : ('a, 'b) Reifier.t -> ('a groundi, 'b logic) Reifier.t =
  fun ra ->
  let ( >>= ) = Env.Monad.bind in
  Reifier.reify >>= fun r ->
  ra >>= fun fa ->
  Env.Monad.return (fun x ->
    match r x with
    | Var (v, _) ->
      Format.eprintf "Reification of constraints is not implemented\n%!";
      Var (v,[])
    | Value t -> Value (GT.gmap ground fa t))

let prj : 'a 'b. ('a, 'b) Reifier.t ->
  (* (int -> 'b) ->  *)
  ('a groundi, 'b ground) Reifier.t
    =
  fun ra (* onvar *) ->
  let ( >>= ) = Env.Monad.bind in
  Reifier.prj_exn >>= fun r ->
  ra >>= fun fa -> Env.Monad.return (fun x -> GT.gmap ground fa (r x))

(*
module T =
  struct
    @type 'a t = 'a GT.option with show, gmap, html, eq, compare, foldl, foldr, fmt
    let fmap f x = GT.(gmap option) f x
  end

include T
include Fmap (T)
*)
let some x  = Logic.inji (Some x)
let none () = Logic.inji None

(* let option : 'a . 'a ilogic ground -> 'a groundi = function None -> none () | Some x -> Logic.inji (Some (x)) *)
