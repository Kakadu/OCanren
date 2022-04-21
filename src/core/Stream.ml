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

IFDEF STATS THEN
type stat = {
    mutable unwrap_suspended_counter : int;
    mutable force_counter            : int;
    mutable from_fun_counter         : int;
    mutable bind_counter             : int;
    mutable mplus_counter            : int
}

let stat = {
    unwrap_suspended_counter = 0;
    force_counter            = 0;
    from_fun_counter         = 0;
    bind_counter             = 0;
    mplus_counter            = 0
}

let unwrap_suspended_counter () = stat.unwrap_suspended_counter
let unwrap_suspended_counter_incr () = stat.unwrap_suspended_counter <- stat.unwrap_suspended_counter + 1

let force_counter () = stat.force_counter
let force_counter_incr () = stat.force_counter <- stat.force_counter + 1

let from_fun_counter () = stat.from_fun_counter
let from_fun_counter_incr () = stat.from_fun_counter <- stat.from_fun_counter + 1

let bind_counter () = stat.bind_counter
let bind_counter_incr () = stat.bind_counter <- stat.bind_counter + 1

let mplus_counter () = stat.mplus_counter
let mplus_counter_incr () = stat.mplus_counter <- stat.mplus_counter + 1

END

(* to avoid clash with Std.List (i.e. logic list) *)
module List = Stdlib.List

type 'a t =
  | Nil     : 'a t
  | Cons    : 'a * 'a t -> 'a t
  | Thunk   : 'a thunk -> 'a t
  | Bind    : 'a t * ('a -> 'a t) * ('a -> 'a t) list -> 'a t
  | Waiting : 'a suspended list -> 'a t
and 'a thunk =
  unit -> 'a t
and 'a suspended =
  {is_ready: unit -> bool; zz: 'a thunk}

let rec pp ppf = function
  | Nil -> Format.fprintf ppf "Nil"
  | Cons (a, xs) -> Format.fprintf ppf "(Cons (?, %a))" pp xs
  | Thunk f ->
      (* Format.fprintf ppf "(Thunk %d)" (Obj.magic f) *)
      Format.fprintf ppf "(Thunk _)"
  | Bind (xs, f, fs) -> Format.fprintf ppf "(Bind (%a, [_]))" pp xs
  | Waiting _ -> assert false

let nil         = Nil
let single x    = Cons (x, Nil)
let cons x s    = Cons (x, s)
let from_fun zz =
  let () = IFDEF STATS THEN from_fun_counter_incr () ELSE () END in
  Thunk zz

let suspend ~is_ready f = Waiting [{is_ready; zz=f}]

let rec of_list = function
| []    -> Nil
| x::xs -> Cons (x, of_list xs)

let force x =
  let () = IFDEF STATS THEN force_counter_incr () ELSE () END in
  match x with
  | Thunk zz  -> zz ()
  | xs        -> xs

let bind: 'a . 'a t -> ('a -> 'a t) -> 'a t = fun x f ->
  match x with
  | Bind (base, h, tl) -> Bind (base, h, tl @ [f])
  | _ -> Bind (x, f, [])

let rec mplus: 'a . 'a t -> 'a t -> 'a t = fun xs ys ->
  let () = IFDEF STATS THEN mplus_counter_incr () ELSE () END in
  (* Format.printf "mplus: `%a` and `%a`\n%!" pp xs pp ys; *)
  match xs with
  | Nil           -> force ys
  | Cons (x, xs)  -> cons x (from_fun @@ fun () -> mplus (force ys) xs)
  | Thunk   _     ->
      from_fun (fun () -> mplus (force ys) xs)
  | Bind (st, fh, ftl)  ->
      mplus ys (bind_impl st fh ftl)
  | Waiting ss    ->
    let ys = force ys in
    (* handling waiting streams is tricky *)
    match unwrap_suspended ss, ys with
    (* if [xs] has no ready streams and [ys] is also a waiting stream then we merge them  *)
    | Waiting ss, Waiting ss' -> Waiting (ss @ ss')
    (* if [xs] has no ready streams but [ys] is not a waiting stream then we swap them,
       pushing waiting stream to the back of the new stream *)
    | Waiting ss, _           -> mplus ys @@ from_fun (fun () -> xs)
    (* if [xs] has ready streams then [xs'] contains some lazy stream that is ready to produce new answers *)
    | xs', _ -> mplus xs' ys

and unwrap_suspended ss =
  let () = IFDEF STATS THEN unwrap_suspended_counter_incr () ELSE () END in
  let rec find_ready prefix = function
    | ({is_ready; zz} as s)::ss ->
      if is_ready ()
      then Some (from_fun zz), (List.rev prefix) @ ss
      else find_ready (s::prefix) ss
    | [] -> None, List.rev prefix
  in
  match find_ready [] ss with
    | Some s, [] -> s
    | Some s, ss -> mplus (force s) @@ Waiting ss
    | None , ss  -> Waiting ss
and bind_impl: 'a . 'a t -> ('a -> 'a t) -> ('a -> 'a t) list -> 'a t = fun s fh ftl ->
  (* Format.fprintf Format.std_formatter "bind_impl: `%a`\n%!" pp s; *)
  match s with
  | Nil           -> Nil
  | Cons (x, s)   ->
      mplus
        (match ftl with
          | [] -> fh x
          | gh::gtl -> bind_impl (fh x) gh gtl)
        (from_fun (fun () -> Bind (force s, fh, ftl)))
  | Thunk zz      -> from_fun (fun () -> bind_impl (zz ()) fh ftl)
  | Bind (st, h1, tl1) ->
      Bind (st, h1, tl1 @ (fh::ftl))
  | Waiting ss    -> failwith "Waiting streams commented out"

let rec old_bind: 'a 'b . 'a t -> ('a -> 'b t) -> 'b t = fun s f ->
  (* Format.fprintf Format.std_formatter "old_bind: `%a`\n%!" pp s; *)
  match s with
  | Nil           -> Nil
  | Cons (x, s)   -> mplus (f x) (from_fun (fun () -> old_bind (force s) f))
  | Thunk zz      -> from_fun (fun () -> old_bind (zz ()) f)
  | Bind (x, g, []) -> old_bind (old_bind x g) f
  | Bind (Nil, _, _) -> Nil
  | Bind (gh,h1,tl1) -> old_bind (bind_impl gh h1 tl1) f
  | Bind (Waiting _, _, _) -> assert false
  | Waiting ss    -> assert false
    (* match unwrap_suspended ss with
    | Waiting ss ->
      let helper {zz} as s = {s with zz = fun () -> old_bind (zz ()) f} in
      Waiting (List.map helper ss)
    | s          -> old_bind s f *)

let rec msplit = function
| Nil           -> None
| Cons (x, xs)  -> Some (x, xs)
| Thunk zz      -> msplit @@ zz ()
| Waiting ss    ->
  match unwrap_suspended ss with
  | Waiting _ -> None
  | xs        -> msplit xs

let is_empty s =
  match msplit s with
  | Some _  -> false
  | None    -> true

let rec map f = function
| Nil          -> Nil
| Cons (x, xs) -> Cons (f x, map f xs)
| Thunk zzz    -> from_fun (fun () -> map f @@ zzz ())
| Waiting ss   ->
  let helper {zz} as s = {s with zz = fun () -> map f (zz ())} in
  Waiting (List.map helper ss)

(* let old_bind = map *)

let mapi f =
  let rec helper i xs = match msplit xs with
    | None -> Nil
    | Some (h, tl) -> Cons (f i h, from_fun (fun () -> helper (1+i) tl))
  in
  helper 0

let rec iter f s =
  match msplit s with
  | Some (x, s) -> f x; iter f s
  | None        -> ()

let rec filter p s =
  match msplit s with
  | Some (x, s) when p x -> Cons (x, from_fun (fun () -> filter p s))
  | Some (x, s) -> from_fun (fun () -> filter p s)
  | None        -> Nil

let rec fold f acc s =
  match msplit s with
  | Some (x, s) -> fold f (f acc x) s
  | None        -> acc

let rec zip xs ys =
  match msplit xs, msplit ys with
  | None,         None          -> Nil
  | Some (x, xs), Some (y, ys)  -> Cons ((x, y), zip xs ys)
  | _                           -> invalid_arg "OCanren fatal (Stream.zip): streams have different lengths"

let hd s =
  match msplit s with
  | Some (x, _) -> x
  | None        -> invalid_arg "OCanren fatal (Stream.hd): empty stream"

let tl s =
  match msplit s with
  | Some (_, xs) -> xs
  | None         -> Nil

let rec retrieve ?(n=(-1)) s =
  if n = 0
  then [], s
  else match msplit s with
  | None          -> [], Nil
  | Some (x, s)  -> let xs, s = retrieve ~n:(n-1) s in x::xs, s

let take ?n s = fst @@ retrieve ?n s
