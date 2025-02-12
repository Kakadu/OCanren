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

open Printf

(* to avoid clash with Std.List (i.e. logic list)
  It may be fixed in next release of GT
*)
module List = Stdlib.List

@type 'a logic =
| Var   of GT.int * 'a logic GT.list
| Value of 'a
with show, gmap, html, eq, compare, foldl, foldr, fmt

let logic = {logic with
  plugins =
    object(self)
      method gmap      = logic.plugins#gmap
      method html      = logic.plugins#html
      method eq        = logic.plugins#eq
      method compare   = logic.plugins#compare
      method foldl     = logic.plugins#foldl
      method foldr     = logic.plugins#foldr
      method fmt fa =
        let rec self ppf = function
        | Value a -> fa ppf a
        | Var (n, []) -> Format.fprintf ppf "_.%d" n
        | Var (n, cs) -> Format.fprintf ppf "_.%d =/= [ %a ]" n (Format.pp_print_list self) cs
        in
        self

      method show fa x =
        GT.transform(logic)
          (fun fself -> object
             inherit ['a, _] @logic[show]  (GT.lift fa) fself
             method! c_Var _ s i cs =
               let c = match cs with
               | [] -> ""
               | _  -> sprintf " %s" (GT.show(GT.list) (fun l -> "=/= " ^ fself () l) cs)
               in
               sprintf "_.%d%s" i c
             method! c_Value _ _ x = fa x
           end)
          ()
          x
    end
}

exception Not_a_value

let to_logic x = Value x

let from_logic = function
| Var _ -> raise Not_a_value
| Value x -> x

type 'a ilogic

type ('a, 'b) injected = 'a

external lift: 'a -> ('a, 'a) injected = "%identity"
let inj: ('a, 'b) injected -> ('a, 'b logic) injected = fun x -> Obj.magic (Value x)

let (!!) = inj

module Reifier = struct
  type ('a, 'b) t = ('a -> 'b) Env.Monad.t

  let rec reify : ('a, 'a logic) t =
    fun env t ->
      match Term.var t with
      | None -> (Obj.magic t)
      | Some v ->
        let i, cs = Term.Var.reify (reify env) v in
        Var (i, cs)

  (* can be implemented more efficiently,
    * without allocation of `'a logic`,
    * but for demonstration purposes this implementation is okay
    *)
  let prj_exn env t =
    (* Printf.printf "Reifier.prj_exn: %s\n" (Term.show (Obj.magic t)); *)
    match reify env t with
    | Value x -> x
    | Var (v, _) -> raise Not_a_value

  let prj onvar env t =
    match reify env t with
    | Var (v, _) -> onvar v
    | Value x -> x

  let apply r (env, a) = r env a

  let compose r r' env a = r' env (r env a)

  let fmap f r env a = f (r env a)

  let fcomap f r env a = r env (f a)

  let rec fix f = fun env eta -> f (fix f) env eta

  let rework : 'a 'b. fv:('a Env.m -> 'b Env.m)
            -> ('a logic Env.m -> 'b logic Env.m)
            -> 'a logic Env.m -> 'b logic Env.m
  = fun ~fv fdeq x ->
      let open Env.Monad in
      let open Env.Monad.Syntax in
      let* x = x in
      match x with
      | Var (v, xs) ->
        let+ diseq = list_mapm ~f:fdeq xs in
        Var (v, diseq)
      | Value t ->
        let+ inner = fv (return t) in
        Value inner

  let rec zed f x = f (zed f) x
end

let reify = Reifier.reify
let prj_exn = Reifier.prj_exn

module type T0 =
  sig
    type t
    val fmap : t -> t
  end
module type T1 =
  sig
    type 'a t
    val fmap : ('a -> 'b) -> 'a t -> 'b t
  end

module type T2 =
  sig
   type ('a, 'b) t
   val fmap : ('a -> 'c) -> ('b -> 'd) -> ('a, 'b) t -> ('c, 'd) t
  end

module type T3 =
  sig
    type ('a, 'b, 'c) t
    val fmap : ('a -> 'q) -> ('b -> 'r) -> ('c -> 's) -> ('a, 'b, 'c) t -> ('q, 'r, 's) t
  end

module type T4 =
sig
  type ('a, 'b, 'c, 'd) t
  val fmap : ('a -> 'q) -> ('b -> 'r) -> ('c -> 's) -> ('d -> 't) -> ('a, 'b, 'c, 'd) t -> ('q, 'r, 's, 't) t
end

module type T5 =
sig
  type ('a, 'b, 'c, 'd, 'e) t
  val fmap : ('a -> 'q) -> ('b -> 'r) -> ('c -> 's) -> ('d -> 't) -> ('e -> 'u) -> ('a, 'b, 'c, 'd, 'e) t -> ('q, 'r, 's, 't, 'u) t
end

module type T6 =
sig
  type ('a, 'b, 'c, 'd, 'e, 'f) t
  val fmap : ('a -> 'q) -> ('b -> 'r) -> ('c -> 's) -> ('d -> 't) -> ('e -> 'u) -> ('f -> 'v) -> ('a, 'b, 'c, 'd, 'e, 'f) t -> ('q, 'r, 's, 't, 'u, 'v) t
end

type helper = Env.t

module Fmap1 (T : T1) = struct
  external distrib : ('a,'b) injected T.t -> ('a T.t, 'b T.t) injected = "%identity"

  let fmapt fa subj =
    let open Env.Monad in
    Env.Monad.return T.fmap <*> fa <*> subj

  let reify:
    'a 'b . ('a, 'b) Reifier.t -> ('a T.t, 'b T.t logic) Reifier.t
    = fun arg1 -> Reifier.fix (fun self ->
      let open Env.Monad in
        reify
        <..> chain
               (Reifier.zed
                  (Reifier.rework
                     ~fv:(fmapt arg1))))

  let prj_exn:
        'a 'b . ('a, 'b) Reifier.t -> ('a T.t, 'b T.t) Reifier.t =
    fun arg ->
      let open Env.Monad in
      Reifier.fix (fun self ->
        prj_exn <..> chain (fmapt arg) )

end
module Fmap2 (T : T2) = struct
  external distrib : (('a,'c) injected, ('b,'d) injected) T.t -> (('a, 'b) T.t, ('c, 'd) T.t) injected = "%identity"

  let fmapt fa fb subj =
    let open Env.Monad in
    Env.Monad.return T.fmap <*> fa <*> fb <*> subj

  let reify:
    'a 'b .  ('a, 'c) Reifier.t -> ('b, 'd) Reifier.t -> (('a, 'b) T.t, ('c, 'd) T.t logic) Reifier.t
    = fun arg1 arg2 -> Reifier.fix (fun _ ->
      let open Env.Monad in
        reify
        <..> chain
               (Reifier.zed
                  (Reifier.rework
                     ~fv:(fmapt arg1 arg2))))

  let prj_exn:
    'a 'b .  ('a, 'c) Reifier.t -> ('b, 'd) Reifier.t -> (('a, 'b) T.t, ('c, 'd) T.t) Reifier.t =
  fun arg1 arg2 ->
    let open Env.Monad in
    Reifier.fix (fun self ->
      prj_exn <..> chain (fmapt arg1 arg2) )
end


class type ['a, 'b] reified = object
  method is_open : bool
  method reify   : 'b . ('a, 'b) Reifier.t -> 'b
end

let make_rr : Env.t -> ('a, 'b) injected -> ('a, 'b) reified  = fun env x ->
  object (self)
    method is_open            = Env.is_open env x
    method reify : 'b . ('a, 'b) Reifier.t -> 'b = fun reifier ->
      Reifier.apply reifier (env, x)
  end

(* let prj x = let rr = make_rr (Env.empty ()) x in rr#prj *)

(* let rec reify env x =
  match Env.var env x with
  | Some v -> let i, cs = Term.Var.reify (reify env) v in Var (i, cs)
  | None   -> Value (Obj.magic x)

let rec prjc of_int env x =
  match Env.var env x with
  | Some v -> let i, cs = Term.Var.reify (prjc of_int env) v in of_int i cs
  | None   -> Obj.magic x
 *)
