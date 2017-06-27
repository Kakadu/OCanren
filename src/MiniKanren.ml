(*
 * MiniKanren: miniKanren implementation.
 * Copyright (C) 2015-2016
 * Dmitri Boulytchev, Dmitry Kosarev, Alexey Syomin,
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

let printfn fmt = kprintf (printf "%s\n%!") fmt
let (!!!) = Obj.magic


type w = Unboxed of Obj.t | Boxed of int * int * (int -> Obj.t) | Invalid of int

let is_valid_tag t =
  let open Obj in
  not (List.mem t
    [lazy_tag; closure_tag; object_tag; infix_tag; forward_tag; no_scan_tag;
     abstract_tag; custom_tag; custom_tag; unaligned_tag; out_of_heap_tag])

let rec wrap (x : Obj.t) =
  Obj.(
    let is_unboxed obj =
      is_int obj ||
      (fun t -> t = string_tag || t = double_tag) (tag obj)
    in
    if is_unboxed x
    then Unboxed x
    else
      let t = tag x in
      if is_valid_tag t
      then
        let f = if t = double_array_tag then !!! double_field else field in
        Boxed (t, size x, f x)
      else Invalid t
    )

let generic_show x =
  let x = Obj.repr x in
  let b = Buffer.create 1024 in
  let rec inner o =
    match wrap o with
    | Invalid n                                         -> Buffer.add_string b (Printf.sprintf "<invalid %d>" n)
    | Unboxed s when Obj.(string_tag = (tag @@ repr s)) -> bprintf b "\"%s\"" (!!!s)
    | Unboxed n when !!!n = 0                           -> Buffer.add_string b "[]"
    | Unboxed n                                         -> Buffer.add_string b (Printf.sprintf "int<%d>" (!!!n))
    | Boxed  (t, l, f) ->
        Buffer.add_string b (Printf.sprintf "boxed %d <" t);
        for i = 0 to l - 1 do (inner (f i); if i<l-1 then Buffer.add_string b " ") done;
        Buffer.add_string b ">"
  in
  inner x;
  Buffer.contents b
;;

let list_filter_map ~f xs =
  let rec helper acc = function
  | [] -> List.rev acc
  | x::xs -> begin
      match f x with None -> helper acc xs | Some y -> helper (y::acc) xs
    end
  in
  helper [] xs

module OldList = List

let log_enabled =
  let ans = ref false in
  Arg.parse
    [("-v", Unit (fun () -> ans := true), "verbose mode")]
    (fun s -> printfn "anon argument '%s'" s)
    "usage msg";
  !ans

let mylog f = if log_enabled then f () else ignore (fun () -> f ())

(*
(* miniKanren-like stream, more generator than a stream *)
module MKStream =
  struct

    type 'a t = Nil
              | Thunk of (unit -> 'a t)
              | Single of 'a
              | Compoz of 'a * (unit -> 'a t)

    let cur_inc = ref 0

    let from_fun (f: unit -> 'a t) : 'a t =
      (* printf "    Thunk created: "; *)
      (* incr cur_inc;
      let n = !cur_inc in *)
      let result = fun () ->
        (* let () = printfn "    forcing thunk: %d" n in *)
        f ()
      in
      (* printfn "%d" n; *)
      Thunk result

    let inc = from_fun

    (* let inc2 (thunk: unit -> 'a -> 'b t) : 'a -> 'b t =
      fun st -> inc (fun () -> thunk () st)
    let inc3 (thunk: 'a -> unit -> 'b t) : 'a -> 'b t =
      fun st -> inc (thunk st) *)

    let nil = Nil

    let single x = Single x

    let rec is_empty = function
    | Nil      -> true
    | Thunk f  -> is_empty @@ f ()
    | Single _
    | Compoz _ -> false

    let choice a f =
      (* printfn "    created Choice %d" (2 * (Obj.magic f)); *)
      Compoz (a, f)

    let force = function
    | Nil -> Nil
    | Thunk f ->
        (* printfn "      forcing thunk %d" (2 * (Obj.magic f)); *)
        f ()
    | Single a -> Single a
    | Compoz (a,f) -> assert false

    let rec mplus fs gs =
      match fs with
      | Nil           ->
          (* printfn " mplus: 1st case"; *)
          force gs
      | Thunk f       ->
          (* The we force 2nd argument and left 1st one for later
            ... because fasterMK does that
          *)
          (* printfn " mplus: 2nd case"; *)
          (* Thunk (fun () -> let r = force gs in mplus r fs) *)
          from_fun (fun () ->
            (* printfn " forcing thunk created by 2nd case of mplus"; *)
            let r = force gs in
            mplus r fs
          )
      | Single a      ->
          (* printfn " mplus: 3rd case"; *)
          choice a (fun () -> gs)
      | Compoz (a, f) ->
          (* printfn " mplus: 4th case "; *)
          choice a (fun () -> mplus gs @@ f ())

    let rec mplus_star : 'a t list -> 'a t = function
    | [] -> failwith "wrong argument"
    | [h] -> h
    | h::tl -> mplus h (from_fun (fun () -> mplus_star tl))

    let show = function
    | Nil -> "Nil"
    | Thunk f -> sprintf "Thunk: %d" (2 * (Obj.magic f))
    | _ -> "wtf"

    let rec bind xs g =
      match xs with
      | Nil ->
            (* printfn " bind: 1std case"; *)
            Nil
      | Thunk f ->
          (* printfn " bind: 2nd case"; *)
          (* delay here because miniKanren has it *)
          from_fun (fun () ->
            (* printfn " forcing thunk created by 2nd case of bind: %d" (2 * (Obj.magic f)); *)
            let r = f () in
            bind r g)
      | Single c ->
          (* printfn " bind: 3rd case"; *)
          g c
      | Compoz (c, f) ->
          (* printfn " bind: 4th case"; *)
          let arg1 = g c in
          mplus arg1 (from_fun (fun () ->
            (* printfn " force thunk created by 5th case of bind: %d" (2 * (Obj.magic f)); *)
            let r = f () in
            (* printfn " r is %s" (show r); *)
            bind r g
          ))

  end
*)

(* miniKanren-like stream, most unsafe implementation *)
module MKStream =
  struct
    open Obj
    (*
      Very unsafe implementation of streams
      * false -- an empty list
      * closure -- delayed list
      * block with tag 1 -- single value
      * (x,closure)   -- a value and continuation (pair has tag 0)
    *)

    type t = Obj.t

    let nil : t = !!!false
    let is_nil s = (s = !!!false)

    let cur_inc = ref 0

    let inc (f: unit -> t) : t =
      mylog (fun () -> printf "    thunk created ");
      incr cur_inc;
      let n = !cur_inc in
      let result = fun () ->
        let () = mylog @@ fun () -> printfn "    forcing thunk %d" n in
        f ()
      in
      mylog (fun () -> printfn "%d" n);
      Obj.repr result

    let from_fun = inc

    type wtf = Dummy of int*string | Single of Obj.t
    let () = assert (Obj.tag @@ repr (Single !!![]) = 1)

    let single : 'a -> t = fun x ->
      (* mylog (fun () -> printfn "Single called"); *)
      Obj.repr @@ Obj.magic (Single !!!x)

    let choice a f =
      assert (closure_tag = tag@@repr f);
      let ans = Obj.repr @@ Obj.magic (a,f) in
      (* let () = mylog (fun () -> printfn "    created choice for value"
                  (2 * (Obj.magic f)) )
      in *)
      ans

    let case_inf xs ~f1 ~f2 ~f3 ~f4 : Obj.t =
      if is_int xs then f1 ()
      else
        let tag = Obj.tag (repr xs) in
        if tag = Obj.closure_tag
        then f2 (!!!xs: unit -> Obj.t)
        else if tag = 1 then f3 (field (repr xs) 0)
        else
          (* let () = printfn "\t%s" @@ generic_show xs in *)
          let () = assert (0 = tag) in
          let () = assert (2 = size (repr xs)) in
          f4 (field (repr xs) 0) (!!!(field (repr xs) 1): unit -> Obj.t)
      (* [@@inline ] *)



    let step gs =
      assert (closure_tag = tag @@ repr gs);
      !!!gs ()

    let rec mplus : t -> t -> t  = fun cinf (gs: t) ->
      assert (closure_tag = tag @@ repr gs);
      case_inf cinf
        ~f1:(fun () ->
              mylog (fun () -> printfn " mplus: 1st case");
              step gs)
        ~f2:(fun f ->
              mylog (fun () -> printfn " mplus: 2nd case");
              inc begin fun () ->
                mylog (fun () -> printfn " forcing thunk created by 2nd case of mplus");
                let r = step gs in
                mplus r !!!f
              end)
        ~f3:(fun c ->
              mylog (fun () -> printfn " mplus: 3rd case");
              choice c gs
          )
        ~f4:(fun c ff ->
              mylog (fun () -> printfn " mplus: 4th case ");
              (* choice a (inc @@ fun () -> mplus gs @@ f ()) *)
              choice c (inc @@ fun () -> mplus (step gs) !!!ff)
          )

    let rec bind cinf g =
      case_inf cinf
        ~f1:(fun () ->
                mylog (fun () -> printfn " bind: 1st case");
                nil)
        ~f2:(fun f ->
              mylog (fun () -> printfn " bind: 2nd case");
              (* delay here because miniKanren has it *)
              inc begin fun () ->
                mylog (fun () -> printfn " forcing thunk created by 2nd case of bind: %d" (2 * (Obj.magic f)) );
                let r = f () in
                bind r g
              end)
        ~f3:(fun c ->
              mylog (fun () -> printfn " bind: 3rd case");
              (!!! g c) )
        ~f4:(fun c f ->
              mylog (fun () -> printfn " bind: 4th case");
              let arg1 = !!!g c in
              mplus arg1 @@
                    inc begin fun () ->
                      mylog (fun () -> printfn " force thunk created by 5th case of bind: %d" (2 * (Obj.magic f)) );
                      bind (step f) g
                    end
          )
  end

module Stream =
  struct
    type 'a t = Nil | Cons of 'a * 'a t | Lazy of 'a t Lazy.t

    let from_fun (f: unit -> 'a t) : 'a t = Lazy (Lazy.from_fun f)

    let nil = Nil

    let cons h t = Cons (h, t)

    let rec of_mkstream : MKStream.t -> 'a t = fun xs ->
      let rec helper xs =
        !!!MKStream.case_inf !!!xs
          ~f1:(fun () -> !!!Nil)
          ~f2:(fun f  ->
              (* printfn "f = %s, is_int=%b" (generic_show f) (Obj.is_int !!!f); *)
              !!! (from_fun (fun () ->
                (* printfn "f () = %s" (generic_show @@ f ()); *)
                helper @@ f ())) )
          ~f3:(fun a -> !!!(cons a Nil) )
          ~f4:(fun a f -> !!!(cons a @@ from_fun (fun () -> helper @@ f ())) )
      in
      !!!(helper !!!xs)

    let rec is_empty = function
    | Nil    -> true
    | Lazy s -> is_empty @@ Lazy.force s
    | _      -> false

    let rec retrieve ?(n=(-1)) s =
      if n = 0
      then [], s
      else match s with
          | Nil          -> [], s
          | Cons (x, xs) -> let xs', s' = retrieve ~n:(n-1) xs in x::xs', s'
          | Lazy  z      -> retrieve ~n (Lazy.force z)

    let take ?(n=(-1)) s = fst @@ retrieve ~n s

    let hd s = List.hd @@ take ~n:1 s
    let tl s = snd @@ retrieve ~n:1 s

    (* let rec mplus fs gs =
      match fs with
      | Nil           -> gs
      | Cons (hd, tl) -> cons hd @@ from_fun (fun () -> mplus gs tl)
      | Lazy z        -> from_fun (fun () -> mplus gs (Lazy.force z) )

    let rec bind xs f =
      match xs with
      | Cons (x, xs) -> from_fun (fun () -> mplus (f x) (bind xs f))
      | Nil          -> nil
      | Lazy z       -> from_fun (fun () -> bind (Lazy.force z) f) *)


    let rec map f = function
    | Nil          -> Nil
    | Cons (x, xs) -> Cons (f x, map f xs)
    | Lazy s       -> Lazy (Lazy.from_fun (fun () -> map f @@ Lazy.force s))

    let rec iter f = function
    | Nil          -> ()
    | Cons (x, xs) -> f x; iter f xs
    | Lazy s       -> iter f @@ Lazy.force s

    let rec zip fs gs =
      match (fs, gs) with
      | Nil         , Nil          -> Nil
      | Cons (x, xs), Cons (y, ys) -> Cons ((x, y), zip xs ys)
      | _           , Lazy s       -> Lazy (Lazy.from_fun (fun () -> zip fs (Lazy.force s)))
      | Lazy s      , _            -> Lazy (Lazy.from_fun (fun () -> zip (Lazy.force s) gs))
      | Nil, _      | _, Nil       -> failwith "MiniKanren.Stream.zip: streams have different lengths"

  end


let (!!!) = Obj.magic;;

@type 'a logic =
| Var   of GT.int * 'a logic GT.list
| Value of 'a with show, gmap, html, eq, compare, foldl, foldr

(* miniKanren-related stuff starts here *)
type ('a, 'b) injected = 'a

external lift: 'a -> ('a, 'a) injected = "%identity"
external inj: ('a, 'b) injected -> ('a, 'b logic) injected = "%identity"
;;

(* The [token_t] type is use to connect logic variables with environment where they were created *)
@type token_env = GT.int with show,gmap,html,eq,compare,foldl,foldr;;

(* Global token will not be exported outside and will be used to detect the value
 * was actually created by us *)
type token_mk = int list
let global_token: token_mk = [8];;

type inner_logic =
| InnerVar of token_mk * token_env * int * Obj.t list

let (!!!) = Obj.magic

let rec bprintf_logic: Buffer.t -> ('a -> unit) -> 'a logic -> unit = fun b f x ->
  let rec helper = function
  | Value x -> f x
  | Var (i,cs) ->
    bprintf b " _.%d" i;
    List.iter (fun x -> bprintf b "=/= "; helper x) cs
  in
  helper x

let logic = {logic with
 gcata = ();
 plugins =
   object
     method gmap    = logic.plugins#gmap
     method html    = logic.plugins#html
     method eq      = logic.plugins#eq
     method compare = logic.plugins#compare
     method foldl   = logic.plugins#foldl
     method foldr   = logic.plugins#foldr
     method show fa x =
       GT.transform(logic)
          (GT.lift fa)
          (object inherit ['a] @logic[show]
            method c_Var _ s i cs =
              (* I have some issues with callign show_logic there, so copy-paste*)
              (* show_logic (fun _ -> assert false) (Var(_token,i,cs)) *)
              let c = match cs with
              | [] -> ""
              | _  -> sprintf " %s" (GT.show(GT.list) (fun l -> "=/= " ^ s.GT.f () l) cs)
              in
              sprintf "_.%d%s" i c
            method c_Value _ _ x = x.GT.fx ()
           end)
          ()
          x
   end
};;

let (!!) x = inj (lift x)

let inj_pair : ('a, 'c) injected -> ('b,'d) injected -> ('a * 'b, ('c * 'd) logic) injected =
  fun x y -> (x, y)

let inj_tuple3 a b c = (a,b,c)

external inj_int : int -> (int, int logic) injected = "%identity"

exception Not_a_value
exception Occurs_check

module Int = struct type t = int let compare : int -> int -> int = Pervasives.compare end
module MultiIntMap : sig
  type key = Int.t
  type 'a t
  val empty: 'a t
  val add : key -> 'a -> 'a t -> 'a t
  val find_exn: key -> 'a t -> 'a list
  val replace: key -> 'a list -> 'a t -> 'a t
end = struct
  module M = Map.Make(Int)

  type key = Int.t
  type 'a t = 'a list M.t

  let empty : 'a t = M.empty
  let add k v m =
    try let vs = M.find k m in
        let vs = if List.memq v vs then vs else v::vs in
        M.add k vs m
    with Not_found -> M.add k [v] m

  let find_exn : key -> 'a t -> 'a list = M.find
  let replace: key -> 'a list -> 'a t -> 'a t = M.add
end

let pretty_generic_show ?(maxdepth= 99999) is_var x =
  let x = Obj.repr x in
  let b = Buffer.create 1024 in
  let rec inner depth term =
    if depth > maxdepth then Buffer.add_string b "..." else
    if is_var !!!term then begin
      let var = (!!!term : inner_logic) in
      match var.subst with
      | Some term ->
          bprintf b "{ _.%d with subst=" var.index;
          inner (depth+1) term;
          bprintf b " }"
      | None -> bprintf b "_.%d" var.index
    end else match wrap term with
      | Invalid n                                         -> bprintf b "<invalid %d>" n
      | Unboxed s when Obj.(string_tag = (tag @@ repr s)) -> bprintf b "\"%s\"" (!!!s)
      | Unboxed n when !!!n = 0                           -> Buffer.add_string b "[]"
      | Unboxed n                                         -> bprintf b  "int<%d>" (!!!n)
      | Boxed  (t, l, f) ->
        Buffer.add_string b (Printf.sprintf "boxed %d <" t);
        for i = 0 to l - 1 do (inner (depth+1) (f i); if i<l-1 then Buffer.add_string b " ") done;
        Buffer.add_string b ">"
  in
  inner 0 x;
  Buffer.contents b
;;

module Env :
  sig
    type t

    val empty  : unit -> t
    val fresh  : ?name:string -> t -> 'a * t
    val var    : t -> 'a -> int option
    val is_var : t -> 'a -> bool
  end =
  struct
    type t = { token : token_env;
               mutable next: int;
               (* mutable reifiers: Obj.t MultiIntMap.t; *)
              }

    let last_token : token_env ref = ref 0
    let empty () =
      incr last_token;
      { token= !last_token; next=10 }

    let fresh ?name e =
      let v = InnerVar (global_token, e.token, e.next, []) in
      (* printf "new fresh var %swith index=%d\n"
        (match name with None -> "" | Some n -> sprintf "'%s' " n)
        e.next; *)
      e.next <- 1+e.next;
      (!!!v, e)

    let var_tag, var_size =
      let dummy_index = 0 in
      let dummy_token = 0 in
      let v = InnerVar (global_token, dummy_token, dummy_index, []) in
      Obj.tag (!!! v), Obj.size (!!! v)

    let var {token=env_token;_} x =
      (* There we detect if x is a logic variable and then that it belongs to current env *)
      let t = !!! x in
      if Obj.tag  t = var_tag  &&
         Obj.size t = var_size &&
         (let q = Obj.field t 0 in
          (Obj.is_block q) && q == (!!!global_token)
         )
      then (let q = Obj.field t 1 in
            if (Obj.is_int q) && q == (!!!env_token)
            then let InnerVar (_,_,i,_) = !!! x in Some i
            else failwith "You hacked everything and pass logic variables into wrong environment"
            )
      else None

    let is_var env v = None <> var env v

    (* Some tests for to check environment self-correctness *)
    (*
    let () =
      let e1 = empty () in
      let e2 = empty () in
      assert (e1 != e2);
      assert (e1.token != e2.token);
      let (q1,e11) = fresh e1 in
      assert (is_var e1  q1);
      assert (is_var e11 q1);
      assert (is_var e2  q1);
      ()
    *)
  end

module Subst :
  sig
    type t

    val empty   : t

    type content = { lvar: Obj.t; new_val: Obj.t }
    val make_content : 'a -> 'b  -> content

    val of_list : (int * content) list -> t
    (* splits substitution into two lists of the same length. 1st contains logic vars,
     * second values to substitute *)
    val split   : t -> Obj.t list * Obj.t list
    val walk    : Env.t -> 'a -> t -> 'a
    val unify   : Env.t -> 'a -> 'a -> t option -> (int * content) list * t option
    val show    : t -> string
    val pretty_show : ('a -> bool) -> t -> string
  end = struct

    (* module InnerLogicKey = struct
      type t = inner_logic
      let compare : t -> t -> int = (compare: int -> int -> int)
    end *)
    module M = Map.Make (Int)

    (* map from var indicies to tuples of (actual vars, value) *)
    type content = { lvar: Obj.t; new_val: Obj.t }
    type t = content M.t
    let new_val {new_val=x;_} = Obj.obj x
    let lvar    {lvar=v;_}    = Obj.obj v
    let make_content a b = { lvar=Obj.repr a; new_val=Obj.repr b }

    let show m =
      let b = Buffer.create 40 in
      Buffer.add_string b "subst {\n";
      M.iter (fun i {new_val} -> bprintf b "  %d -> %s;\n" i (generic_show new_val)) m;
      Buffer.add_string b "}";
      Buffer.contents b

    let pretty_show is_var m =
      let b = Buffer.create 40 in
      bprintf b "subst {\n";
      M.iter (fun i {new_val} -> bprintf b "  %d -> %s;\n" i (pretty_generic_show is_var new_val)) m;
      bprintf b "}";
      Buffer.contents b

    let empty = M.empty

    let of_list l = List.fold_left (fun s (i, cnt) -> M.add i cnt s) empty l

    let split s = M.fold (fun _ {lvar;new_val} (xs, ts) -> (lvar::xs, new_val::ts)) s ([], [])

    let rec walk : Env.t -> 'a -> t -> 'a = fun env var subst ->
      match Env.var env !!!var with
      | None   -> var
      | Some i ->
          try walk env (new_val @@ M.find i subst) subst
          with Not_found -> var

    let rec occurs env xi term subst =
      let y = walk env term subst in
      match Env.var env y with
      | Some yi -> xi = yi
      | None ->
         let wy = wrap (Obj.repr y) in
         match wy with
         | Invalid n when n = Obj.closure_tag -> false
         | Unboxed _ -> false
         | Invalid n -> invalid_arg (sprintf "Invalid value in occurs check (%d)" n)
         | Boxed (_, s, f) ->
            let rec inner i =
              if i >= s then false
              else occurs env xi (!!!(f i)) subst || inner (i+1)
            in
            inner 0

    let unify env x y subst =
      let extend xi x term delta subst =
        if occurs env xi term subst then raise Occurs_check
        else
          let cnt = make_content x term in
          ((xi, cnt)::delta, Some (M.add xi cnt (!!! subst)) )
      in
      let rec unify x y (delta, subst) =
        match subst with
        | None -> delta, None
        | (Some subst) as s ->
            let x, y = walk env x subst, walk env y subst in
            match Env.var env x, Env.var env y with
            | Some xi, Some yi -> if xi = yi then delta, s else extend xi x y delta subst
            | Some xi, _       -> extend xi x y delta subst
            | _      , Some yi -> extend yi y x delta subst
            | _ ->
                let wx, wy = wrap (Obj.repr x), wrap (Obj.repr y) in
                (match wx, wy with
                 | Unboxed vx, Unboxed vy -> if vx = vy then delta, s else delta, None
                 | Boxed (tx, sx, fx), Boxed (ty, sy, fy) ->
                    if tx = ty && sx = sy
                    then
                      let rec inner i (delta, subst) =
                      match subst with
                        | None -> delta, None
                        | Some _ ->
                          if i < sx
                          then inner (i+1) (unify (!!!(fx i)) (!!!(fy i)) (delta, subst))
                          else delta, subst
                      in
                      inner 0 (delta, s)
                    else delta, None
                 | Invalid n, _
                 | _, Invalid n -> invalid_arg (sprintf "Invalid values for unification (%d)" n)
                 | _ -> delta, None
                )
      in
      unify x y ([], subst)

  end

let rec refine : Env.t -> Subst.t -> _ -> Obj.t -> Obj.t = fun env subst do_diseq x ->
  let rec walk' forbidden term =
    let var = Subst.walk env term subst in
    match Env.var env var with
    | None ->
        (match wrap (Obj.repr var) with
          | Unboxed _ -> Obj.repr var
          | Boxed (t, s, f) ->
            let copy = Obj.dup (Obj.repr var) in (* not a shallow copy *)
            let sf =
              if t = Obj.double_array_tag
              then !!! Obj.set_double_field
              else Obj.set_field
            in

            for i = 0 to s-1 do
              sf copy i @@ walk' forbidden (!!!(f i))
            done;
            copy
          | Invalid n -> invalid_arg (sprintf "Invalid value for reconstruction (%d)" n)
        )
    | Some n when List.mem n forbidden -> var
    | Some n ->
        (match !!!var with
        | InnerVar (token1, token2, i, _) ->
          (* assert (i=n); *)
          let cs : _ list = do_diseq !!!var in
          let cs = List.filter (fun x -> match Env.var env x with Some n -> not (List.mem n forbidden) | None -> true) cs in
          let cs = List.map (walk' (i::forbidden)) cs in
          Obj.repr @@ InnerVar (token1, token2, i, cs)
        )
  in
  walk' [] x

exception Disequality_violated

module type CONSTRAINTS = sig
  type t
  val empty: t
  val show: t -> string

  (** [refine env c x] refines [x] and maybe changes constraints [c].
   *  It returns a list of term that [x] should not be equal
   *)
  val refine: Env.t -> Subst.t -> t -> Obj.t -> Obj.t list

  val extend : prefix:(int * Subst.content) list -> Env.t -> t -> t

  val check  : prefix:(int * Subst.content) list -> Env.t -> Subst.t option -> t -> t
end

module FastConstraints : CONSTRAINTS =
struct
  (* We store constraints as associative lists where first element of pair is a variable index *)
  type single_constraint = (int * Subst.content) list
  type t = single_constraint list

  let empty = []
  let bprintf_single b cs =
    let rec helper = function
    | [] -> ()
    | (n,x) :: tl ->
          bprintf b "%d -> %s;" n (generic_show x.Subst.new_val);
          helper tl
    in
    helper cs

  let show_single c =
    let b = Buffer.create 40 in
    bprintf b " ( ";
    let () = bprintf_single b c in
    bprintf b " ) ";
    Buffer.contents b

  let show cstore =
    let b = Buffer.create 40 in
    let rec helper = function
    | [] -> ()
    | h::tl ->  bprintf_single b h;  helper tl
    in
    helper cstore;
    Buffer.contents b

  let split_and_unify ~prefix env subst =
    (* There we can save on memory allocations if we will
      do incremental unification of the list *)
    let open Subst in
    let vs,ts = List.split @@
      List.map (fun (_, {lvar;new_val}) -> (lvar, new_val)) prefix
    in
    try  Subst.unify env !!!vs !!!ts subst
    with Occurs_check -> [],None

  let is_subsumed env d d2 =
    let rec helper = function
    | [] -> false
    | h::tl -> begin
        let (_,s) = split_and_unify ~prefix:d env (Some Subst.empty) in
        match split_and_unify ~prefix:h env s with
        | __, None -> helper tl
        | [], Some _ -> true
        | pref, maybeS ->
            helper tl
      end
    in
    helper d2

  let rem_subsumed env cs =
    let rec helper d acc =
      match d with
      | [] -> acc
      | h::tl when is_subsumed env h tl || is_subsumed env h acc ->
          helper tl acc
      | h:: tl -> helper tl (h::acc)
    in
    helper cs []

  exception ReallyNotEqual
  let simplify_single_constraint ~env ~subst maybe_swap cs =
    (* We need this to simplify answer in that case:
     *   subst: [ q -> (a,b); ]
     *   constr: [ (a=/=5) || (b=/=6) ]
     *   extend subst with (a === 3)
     *   ask to refine: q
     *   expected answer: q = (3, b)
     *   without simplification: q = (3, b {{ =/= 6}})
     **)
    let rec helper acc = function
    | [] -> List.rev acc
    | (_n,cont)::tl -> begin
        match Subst.(unify env cont.lvar cont.new_val (Some subst)) with
        | _,None -> raise ReallyNotEqual
        | [],Some _ -> (* terms will be disequal by some other reason *)
                        helper acc tl
        | prefix,Some _ -> (* this constraint worth printing *)
                            helper ((maybe_swap (_n,cont)) :: acc) tl
      end
    in
    try helper [] cs
    with ReallyNotEqual -> []

  let refine: Env.t -> Subst.t -> t -> Obj.t -> Obj.t list = fun env base_subst cs term ->
    let maybe_swap =
      match Env.var env term with
      | None   -> (fun p -> p)
      | Some n -> (fun ((_,cnt) as p) ->
                    if cnt.Subst.new_val = term then (n, { lvar = term; new_val = cnt.Subst.lvar})
                    else p)
    in
    list_filter_map ~f:(fun prefix ->
      (* For every constraint we need to simplify using current substitution because previously
         we checked only head of the constraint *)
      let prefix = simplify_single_constraint ~env ~subst:base_subst maybe_swap prefix in
      let cs_sub = Subst.of_list prefix in
      let dest = Subst.walk env !!!term cs_sub in
      if dest == term then None
      else Some dest
    ) (rem_subsumed env cs)

  let interacts_with ~prefix (c: single_constraint) =
    let (n,_) = List.hd c in
    try let m,dest = List.find (fun (m,_) -> m=n) prefix in
        Some dest
    with Not_found -> None

  let check ~prefix env (subst: Subst.t option) (c_store: t) =
    let rec apply_subst = function
    | [] -> []
    | (_n,cnt)::tl -> begin
        match Subst.unify env cnt.Subst.lvar cnt.Subst.new_val subst with
        | __, None   -> raise ReallyNotEqual
        | [], Some _ -> raise Disequality_violated
        | pr, Some _ -> pr @ tl
      end
    in

    let rec loop acc = function
      | []      -> List.rev acc
      | [] :: _ -> raise Disequality_violated
      | ((ch::ctl) as c) :: cothers -> begin
          match interacts_with ~prefix c with
          | None -> loop (c::acc) cothers
          | Some dest -> begin
              match Subst.(unify env (c |> List.hd |> snd).new_val dest.new_val) subst with
              |  _, None -> (* non-unifiable, we can forget a constraint *)
                  loop acc cothers
              | [], Some _ ->
                  (* a part of constraint is violated but two terms can still be distinct *)
                  let revisited_constraints =
                    try (apply_subst ctl) :: cothers
                    with ReallyNotEqual -> cothers
                  in
                  loop acc revisited_constraints
              | prefix, Some _ ->
                  (* we need to update constraint with new information *)
                  loop ((prefix @ c) :: acc) cothers
          end
        end
    in
    loop [] c_store

  let extend ~prefix _env cs = prefix :: cs
end

module DefaultConstraints : CONSTRAINTS =
struct
  type t = Subst.t list

  let empty = []
  let show c = GT.show(GT.list) Subst.show c

  let normalize_store ~prefix env constr =
    (* This implementation ignores first list of prefix which contains variable indicies *)
    let subst  = Subst.of_list prefix in
    let open Subst in
    let prefix = List.split @@ List.map (fun (_, {lvar;new_val}) -> (lvar, new_val)) prefix in
    (* There we can save on memory allocations if we will
       do incremental unification of the list *)
    let subsumes subst (vs, ts) =
      try
        match Subst.unify env !!!vs !!!ts (Some subst) with
        | [], Some _ -> true
        | _ -> false
      with Occurs_check -> false
    in
    let rec traverse = function
    | [] -> [subst]
    | (c::cs) as ccs ->
        if subsumes subst (Subst.split c)
        then ccs
        else if subsumes c prefix
             then traverse cs
             else c :: traverse cs
    in
    traverse constr

  let extend ~prefix env cs : t = normalize_store ~prefix env cs

  let refine env subs cs term =
    list_filter_map cs ~f:(fun cs_sub ->
      let dest = Subst.walk env !!!term cs_sub in
      if dest == term then None else Some dest
    )

  let check ~prefix env subst' cstr =
    (* TODO: only apply constraints with the relevant vars *)
    ListLabels.fold_left cstr ~init:[] ~f:(fun css' cs_sub ->
      (* TODO: here is room for optimization memory usage *)
      let x,t = Subst.split cs_sub in
      try
        let p, s' = Subst.unify env (!!!x) (!!!t) subst' in
        match s' with
        | None -> css'
        | Some _ ->
            match p with
            | [] -> raise Disequality_violated
            | _  -> (Subst.of_list p)::css'
      with Occurs_check -> css'
    )
end

(* module Constraints = DefaultConstraints *)
module Constraints = FastConstraints

module State =
  struct
    type t = Env.t * Subst.t * Constraints.t
    let empty () = (Env.empty (), Subst.empty, Constraints.empty)
    let env   (env, _, _) = env

    let show  (env, subst, constr) = sprintf "st {%s, %s}" (Subst.show subst) (Constraints.show constr)
    let new_var (env,_,_) =
      let (x,_) = Env.fresh env in
      let InnerVar (_,_,i,_) = x in
      (x,i)
  end

type 'a goal' = State.t -> 'a
type goal = MKStream.t goal'

let call_fresh f = fun (env, subst, constr) ->
  let x, env' = Env.fresh env in
  f x (env', subst, constr)

let call_fresh_named name f = fun (env, subst, constr) ->
  let x, env' = Env.fresh ~name env in
  f x (env', subst, constr)

let unif_counter = ref 0
let logged_unif_counter = ref 0
let diseq_counter = ref 0
let logged_diseq_counter = ref 0

let report_counters () =
  printfn "total  unifications: %d" !unif_counter;
  printfn "logged unifications: %d" !logged_unif_counter;
  printfn "total diseq calls : %d" !diseq_counter;
  printfn "logged diseq calls : %d" !logged_diseq_counter



let (===) ?loc (x: _ injected) y (env, subst, constr) =
  (* we should always unify two injected types *)
  (* mylog (fun () ->
            printfn "unify";
            printfn "\t%s" (generic_show x);
            printfn "\t%s" (generic_show y);
  ); *)
  (* incr unif_counter; *)
  try
    let prefix, subst' = Subst.unify env x y (Some subst) in
    begin match subst' with
    | None -> MKStream.nil
    | (Some s) as subst ->
        try
          let constr' = Constraints.check ~prefix env subst constr in
          MKStream.single (env, s, constr')
        with Disequality_violated -> MKStream.nil

    end
  with Occurs_check -> MKStream.nil

let (=/=) x y ((env, subst, constrs) as st) =
  try
    let prefix, subst' = Subst.unify env x y (Some subst) in
    match subst' with
    | None -> MKStream.single st
    | Some s ->
        (match prefix with
        | [] -> MKStream.nil
        | _  ->
          let new_constrs = Constraints.extend ~prefix env constrs in
          MKStream.single (env, subst, new_constrs)
        )
  with Occurs_check -> MKStream.single st

let delay : (unit -> goal) -> goal = fun g ->
  fun st -> MKStream.from_fun (fun () -> g () st)

(* let delay2 : (unit -> goal) -> goal = MKStream.inc2 *)

let delay_goal : goal -> goal = fun g st -> MKStream.from_fun (fun () -> g st)
let inc = delay_goal


let conj f g st = MKStream.bind (f st) g

let (&&&) = conj

let disj f g st =
  let open MKStream in
  mplus (f st)
    (MKStream.from_fun (fun () ->
      (* printfn " force inc from mplus*"; *)
      g st))

let (|||) = disj

(* mplus_star *)
let rec (?|) = function
| []    -> failwith "wrong argument of ?|"
| [h]   -> h
| h::tl -> h ||| (?| tl)

let rec my_mplus_star xs st = match xs with
| []    -> failwith "wrong argument of my_mplus_star|"
| [h]   -> h st
| h::tl -> disj h (my_mplus_star tl) st

(* "bind*" *)
let rec (?&) = function
| []   -> failwith "wrong argument of ?&"
| [h]  -> h
| x::y::tl -> ?& ((x &&& y)::tl)

let bind_star = (?&)

let rec bind_star2 : MKStream.t -> goal list -> MKStream.t = fun s -> function
| [] -> s
| x::xs ->
    (* printfn "2nd case of bind* 2"; *)
    bind_star2 (MKStream.bind s x) xs

let bind_star_simple s = bind_star2 s []

let conde xs : goal = fun st ->
  (* printfn " creaded inc in conde"; *)
  MKStream.inc (fun () ->
    (* printfn " force a conde"; *)
    my_mplus_star xs st)

module Fresh =
  struct

    let succ prev f = call_fresh (fun x -> prev (f x))

    let zero  f = f
    let one   f = succ zero f
    let two   f = succ one f
    let three f = succ two f
    let four  f = succ three f
    let five  f = succ four f

    let q     = one
    let qr    = two
    let qrs   = three
    let qrst  = four
    let pqrst = five

  end

let success st = MKStream.single st
let failure _  = MKStream.nil

exception FreeVarFound
let has_free_vars is_var x =
  let rec walk x =
    if is_var x then raise FreeVarFound
    else
      match wrap (Obj.repr x) with
      | Boxed (_tag, size, f) ->
        for i = 0 to size - 1 do
          walk (!!!(f i))
        done
      | _ -> ()
  in
  try walk x; false
  with FreeVarFound -> true

exception WithFreeVars of (Obj.t -> bool) * Obj.t

module ExtractDeepest =
  struct
    let ext2 x = x

    let succ prev (a, z) =
      let foo, base = prev z in
      ((a, foo), base)
  end

type helper = < isVar : 'a . 'a -> bool >
let helper_of_state st : helper =
  !!!(object method isVar x = Env.is_var (State.env st) (Obj.repr x) end)

class type ['a,'b] refined = object
  method is_open: bool
  method prj: 'a
  method refine: (helper -> ('a, 'b) injected -> 'b) -> inj:('a -> 'b) -> 'b
end

let make_rr : ('a, 'b) injected -> State.t -> ('a, 'b) refined = fun x ((env, s, cs) as st) ->
  let ans = !!!(refine env s (Constraints.refine env s cs) (Obj.repr x)) in
  let is_open = has_free_vars (Env.is_var env) (Obj.repr ans) in
  let c: helper = helper_of_state st in

  object(self)
    method is_open = is_open
    method prj = if self#is_open then raise Not_a_value else !!!ans
    method refine refiner ~inj =
      if self#is_open then refiner c ans else inj ans
  end

module R : sig
  type ('a, 'b) refiner

  val refiner :  ('a, 'b) injected -> ('a, 'b) refiner

  val apply_refiner : State.t Stream.t -> ('a, 'b) refiner -> ('a, 'b) refined Stream.t
end = struct
  type ('a, 'b) refiner = State.t Stream.t -> ('a, 'b) refined Stream.t

  let refiner : ('a,'b) injected -> ('a,'b) refiner = fun x -> Stream.map (make_rr x)
  let apply_refiner = fun st r -> r st
end

module ApplyTuple =
  struct
    let one arg r = R.apply_refiner arg r

    let succ prev = fun arg (r, y) -> (R.apply_refiner arg r, prev arg y)
  end

module ApplyLatest =
  struct
    let two = (ApplyTuple.one, ExtractDeepest.ext2)

    let apply (appf, extf) tup =
      let x, base = extf tup in
      appf (Stream.of_mkstream base) x

    let succ (appf, extf) = (ApplyTuple.succ appf, ExtractDeepest.succ extf)
  end

module Uncurry =
  struct
    let succ k f (x,y) = k (f x) y
  end

type ('a, 'b) refiner = ('a, 'b) R.refiner
let refiner = R.refiner

module LogicAdder :
  sig
    val zero : 'a -> 'a
    val succ: ('a -> State.t -> 'd) -> (('e, 'f) injected -> 'a) -> State.t -> ('e, 'f) R.refiner * 'd
  end = struct
    let zero f = f

    let succ prev f =
      call_fresh (fun logic st -> (R.refiner logic, prev (f logic) st))
  end


let succ n () =
  let adder, currier, app = n () in
  (LogicAdder.succ adder, Uncurry.succ currier, ApplyLatest.succ app)

let one   () = (fun x -> LogicAdder.(succ zero) x), (@@), ApplyLatest.two
let two   () = succ one   ()
let three () = succ two   ()
let four  () = succ three ()
let five  () = succ four  ()

let q     = one
let qr    = two
let qrs   = three
let qrst  = four
let pqrst = five

let run n goalish f =
  let adder, currier, app_num = n () in
  let run f = f (State.empty ()) in
  run (adder goalish) |> ApplyLatest.apply app_num |> (currier f)

let trace msg g = fun state ->
  printf "%s: %s\n%!" msg (State.show state);
  g state

let refine_with_state (env,subs,cs) term = refine env subs (Constraints.refine env subs cs) (Obj.repr term)

let project1 ~msg : (helper -> 'b -> string) -> ('a, 'b) injected -> goal = fun shower q st ->
  printf "%s %s\n%!" msg (shower (helper_of_state st) @@ Obj.magic @@ refine_with_state st q);
  success st

let project2 ~msg : (helper -> 'b -> string) -> (('a, 'b) injected as 'v) -> 'v -> goal = fun shower q r st ->
  printf "%s '%s' and '%s'\n%!" msg (shower (helper_of_state st) @@ Obj.magic @@ refine_with_state st q)
                                    (shower (helper_of_state st) @@ Obj.magic @@ refine_with_state st r);
  success st

let project3 ~msg : (helper -> 'b -> string) -> (('a, 'b) injected as 'v) -> 'v -> 'v -> goal = fun shower q r s st ->
  printf "%s '%s' and '%s' and '%s'\n%!" msg
    (shower (helper_of_state st) @@ Obj.magic @@ refine_with_state st q)
    (shower (helper_of_state st) @@ Obj.magic @@ refine_with_state st r)
    (shower (helper_of_state st) @@ Obj.magic @@ refine_with_state st s);
  success st

let unitrace ?loc shower x y = fun st ->
  incr logged_unif_counter;
  printf "%d: unify '%s' and '%s'" !logged_unif_counter (shower (helper_of_state st) x) (shower (helper_of_state st) y);
  (match loc with Some l -> printf " on %s" l | None -> ());
  let ans = (x === y) st in
  if MKStream.is_nil ans then printfn "  -"
  else  printfn "  +";
  ans

let diseqtrace shower x y = fun st ->
  incr logged_diseq_counter;
  printf "%d: (=/=) '%s' and '%s'\n%!" !logged_diseq_counter
    (shower (helper_of_state st) x)
    (shower (helper_of_state st) y);
  (x =/= y) st



(* ************************************************************************** *)
module type T1 = sig
  type 'a t
  val fmap : ('a -> 'b) -> 'a t -> 'b t
end
module type T2 = sig
  type ('a, 'b) t
  val fmap : ('a -> 'c) -> ('b -> 'd) -> ('a, 'b) t -> ('c, 'd) t
end
module type T3 = sig
  type ('a, 'b, 'c) t
  val fmap : ('a -> 'q) -> ('b -> 'r) -> ('c -> 's) -> ('a, 'b, 'c) t -> ('q, 'r, 's) t
end
module type T4 = sig
  type ('a, 'b, 'c, 'd) t
  val fmap : ('a -> 'q) -> ('b -> 'r) -> ('c -> 's) -> ('d -> 't) -> ('a, 'b, 'c, 'd) t -> ('q, 'r, 's, 't) t
end
module type T5 = sig
  type ('a, 'b, 'c, 'd, 'e) t
  val fmap : ('a -> 'q) -> ('b -> 'r) -> ('c -> 's) -> ('d -> 't) -> ('e -> 'u) -> ('a, 'b, 'c, 'd, 'e) t -> ('q, 'r, 's, 't, 'u) t
end
module type T6 = sig
  type ('a, 'b, 'c, 'd, 'e, 'f) t
  val fmap : ('a -> 'q) -> ('b -> 'r) -> ('c -> 's) -> ('d -> 't) -> ('e -> 'u) -> ('f -> 'v) -> ('a, 'b, 'c, 'd, 'e, 'f) t -> ('q, 'r, 's, 't, 'u, 'v) t
end

let var_of_injected_exn : helper -> ('a,'b) injected -> (helper -> ('a,'b) injected -> 'b) -> 'b = fun c x r ->
  if c#isVar x
  then let InnerVar (_,_,n,cstr) = !!!x in !!!(Var (n, List.map (!!!(r c)) cstr))
  else failwith "Bad argument of var_of_injected: it should be logic variable"

module Fmap1 (T : T1) = struct
  external distrib : ('a,'b) injected T.t -> ('a T.t, 'b T.t) injected = "%identity"

  let rec reify: (helper -> ('a,'b) injected -> 'b) -> helper ->
        ('a T.t, 'b T.t logic as 'r) injected -> 'r
    = fun arg_r c x ->
      if c#isVar x
      then var_of_injected_exn c x (reify arg_r)
      else Value (T.fmap (arg_r c) x)
end

module Fmap2 (T : T2) = struct
  external distrib : (('a,'b) injected, ('c, 'd) injected) T.t -> (('a, 'b) T.t, ('c, 'd) T.t) injected = "%identity"

  let rec reify:
        (helper -> ('a,'b) injected -> 'b) ->
        (helper -> ('c,'d) injected -> 'd) ->
         helper -> (('a,'c) T.t, ('b,'d) T.t logic) injected -> ('b,'d) T.t logic
    = fun r1 r2 c x ->
      if c#isVar x then var_of_injected_exn c x (reify r1 r2)
      else Value (T.fmap (r1 c) (r2 c) x)
end

module Fmap3 (T : T3) = struct
  type ('a, 'b, 'c) t = ('a, 'b, 'c) T.t
  external distrib : (('a, 'b) injected, ('c, 'd) injected, ('e, 'f) injected) t -> (('a, 'c, 'e) t, ('b, 'd, 'f) t) injected = "%identity"

  let rec reify r1 r2 r3 (c: helper) x =
    if c#isVar x then var_of_injected_exn c x (reify r1 r2 r3)
    else Value (T.fmap (r1 c) (r2 c) (r3 c) x)
end

module Fmap4 (T : T4) = struct
  type ('a, 'b, 'c, 'd) t = ('a, 'b, 'c, 'd) T.t
  external distrib : (('a,'b) injected, ('c, 'd) injected, ('e, 'f) injected, ('g, 'h) injected) t ->
                     (('a, 'c, 'e, 'g) t, ('b, 'd, 'f, 'h) t) injected = "%identity"

  let rec reify r1 r2 r3 r4 (c: helper) x =
    if c#isVar x then var_of_injected_exn c x (reify r1 r2 r3 r4)
    else Value (T.fmap (r1 c) (r2 c) (r3 c) (r4 c) x)
end

module Fmap5 (T : T5) = struct
  type ('a, 'b, 'c, 'd, 'e) t = ('a, 'b, 'c, 'd, 'e) T.t
  external distrib : (('a,'b) injected, ('c, 'd) injected, ('e, 'f) injected, ('g, 'h) injected, ('i, 'j) injected) t ->
                     (('a, 'c, 'e, 'g, 'i) t, ('b, 'd, 'f, 'h, 'j) t) injected = "%identity"

  let rec reify r1 r2 r3 r4 r5 (c: helper) x =
    if c#isVar x then var_of_injected_exn c x (reify r1 r2 r3 r4 r5)
    else Value (T.fmap (r1 c) (r2 c) (r3 c) (r4 c) (r5 c) x)
end

module Fmap6 (T : T6) = struct
  type ('a, 'b, 'c, 'd, 'e, 'f) t = ('a, 'b, 'c, 'd, 'e, 'f) T.t
  external distrib : (('a,'b) injected, ('c, 'd) injected, ('e, 'f) injected, ('g, 'h) injected, ('i, 'j) injected, ('k, 'l) injected) t ->
                     (('a, 'c, 'e, 'g, 'i, 'k) t, ('b, 'd, 'f, 'h, 'j, 'l) t) injected = "%identity"

  let rec reify r1 r2 r3 r4 r5 r6 (c: helper) x =
    if c#isVar x then var_of_injected_exn c x (reify r1 r2 r3 r4 r5 r6)
    else Value (T.fmap (r1 c) (r2 c) (r3 c) (r4 c) (r5 c) (r6 c) x)
end

module Pair = struct
  module X = struct
    type ('a,'b) t = 'a * 'b
    let fmap f g (x,y) = (f x, g y)
  end
  include Fmap2(X)
end

module Tuple3 = Fmap3(struct
    type ('a,'b,'c) t = 'a * 'b * 'c
    let fmap f g h (x,y,z) = (f x, g y, h z)
  end)

module ManualReifiers = struct
  let rec simple_reifier: helper -> ('a, 'a logic) injected -> 'a logic = fun c n ->
    if c#isVar n
    then var_of_injected_exn c n simple_reifier
    else Value  n

  let bool_reifier : helper -> (bool, bool logic) injected -> bool logic =
    simple_reifier

  let rec int_reifier: helper -> (int, int logic) injected -> int logic = fun c n ->
    if c#isVar n
    then var_of_injected_exn c n int_reifier
    else Value n

  let rec string_reifier: helper -> (string, string logic) injected -> string logic = fun c x ->
    if c#isVar x
    then var_of_injected_exn c x string_reifier
    else Value  x

  let rec pair_reifier: (helper -> ('a,'b) injected -> 'b) ->
                        (helper -> ('c,'d) injected -> 'd) ->
                        helper -> ('a * 'c, ('b * 'd) logic as 'r) injected -> 'r
    = fun r1 r2 c p ->
      if c#isVar p then var_of_injected_exn c p (pair_reifier r1 r2)
      else Pair.reify r1 r2 c p

  let rec tuple3 = fun r1 r2 r3 (c: helper) p ->
    if c#isVar p
    then var_of_injected_exn c p (tuple3 r1 r2 r3)
    else Tuple3.reify r1 r2 r3 c p

end;;
(*
let () =
  let (===) = unitrace (fun h t -> GT.(show logic @@ show int)
    @@ ManualReifiers.int_reifier h t) in
  let goal1 exp st =
    MKStream.mplus
      (call_fresh_named "t" (fun t st ->
        MKStream.inc (fun () ->
          ?& [ exp === !!0
             ; exp === !!1 ] st )) st)
      (Thunk (fun () ->
        (* printfn "herr"; *)
        MKStream.mplus
          (call_fresh_named "es" (fun t st ->
            MKStream.inc (fun () -> (exp=== !!2) st)) st)
          (Thunk (fun () ->
           call_fresh_named "zz" (fun t st ->
             MKStream.inc (fun () -> (exp=== !!3) st)) st))
      ))
  in
  (* let goal2 exp st =
    disj
      (call_fresh_named "t" (fun _t  ->
        MKStream.inc2 (fun () -> exp === !!1 )) )
      (disj
          (call_fresh_named "es" (fun _t ->
            MKStream.inc2 (fun () -> exp === !!2  )) )
          (call_fresh_named "zz" (fun _t ->
            MKStream.inc2 (fun () -> exp === !!3 )) )
      ) st
  in *)
  let goal2 exp =
    conde
      [ call_fresh_named "t" (fun _t  ->
          MKStream.inc2 (fun () ->
          ?&  [ exp === !!0
              ; exp === !!1
              ])
        )
      ; call_fresh_named "es" (fun _t ->
            MKStream.inc2 (fun () -> exp === !!2 ))
      ; call_fresh_named "zz" (fun _t ->
            MKStream.inc2 (fun () -> exp === !!3 ))
      ]
  in

  run q goal1 (fun qs -> Stream.take ~n:2 qs
      |> List.map (fun rr -> rr#prj) |> List.iter (printfn "%d"));
  print_newline ();
  run q goal2 (fun qs -> Stream.take ~n:2 qs
      |> List.map (fun rr -> rr#prj) |> List.iter (printfn "%d"));
  ()
;;
*)

(*
let ____ () =
  let (===) = unitrace (fun h t -> GT.(show logic @@ show int)
    @@ ManualReifiers.int_reifier h t) in

  let goal1 exp =
    conde [ call_fresh_named "t1" (fun t1 ->
              MKStream.inc2 @@ fun () ->
              ?&  [ (exp === !!0) ]
              )
          ; call_fresh_named "t2" (fun t2 ->
              MKStream.inc2 @@ fun () ->
              ?&  [ (exp === !!3) ]
              )
          ; call_fresh_named "t3" (fun t3 ->
              MKStream.inc2 @@ fun () ->
              ?&  [ (exp === !!6) ]
              )
          ]
  in
  run q goal1 (fun qs -> Stream.take ~n:(-1) qs
    |> List.map (fun rr -> rr#prj) |> List.iter (printfn "%d") );
  ()
;;

let __ () =
  let (===) = unitrace (fun h t -> GT.(show logic @@ show int)
    @@ ManualReifiers.int_reifier h t) in

  (* let rec evalo m =
    printfn " applying evalo to m";
    call_fresh_named "f2" (fun f2 ->
      let () = printfn "create inc in fresh ==== (f2)" in
      delay2 @@ fun () ->
        printfn "inc in fresh forced: (f2)";
        (fun st ->
          MKStream.bind
            ( printfn " creaded inc in conde";
              MKStream.inc2 (fun () ->
                printfn " force a conde";
                fun st ->
                MKStream.mplus
                  (call_fresh_named "x" (fun _x ->
                      printfn "create inc in fresh ==== (x)";
                      MKStream.inc2 @@ fun () ->
                        printfn "inc in fresh forced: (x)" ;
                        (f2 === !!1)
                    ) st)
                  (Thunk (fun () ->
                    printfn " force inc from mplus*";
                    call_fresh_named "p" (fun _p ->
                        printfn "create inc in fresh ==== (p)";
                        MKStream.inc2 @@ fun () ->
                          printfn "inc in fresh forced: (p)" ;
                          (f2 === !!2)
                      ) st))
              ) st
            )
            (evalo !!4 )
        )
    )
  in *)
  let rec evalo m =
    printfn " applying evalo to m";
    call_fresh_named "f2" (fun f2 ->
      let () = printfn "create inc in fresh ==== (f2)" in
      delay2 @@ fun () ->
        printfn "inc in fresh forced: (f2)" ;
        ?&
      [ conde
          [ call_fresh_named "x" (fun _x ->
              printfn "create inc in fresh ==== (x)";
              delay2 @@ fun () ->
                printfn "inc in fresh forced: (x)" ;
                (f2 === !!1)
            )
          ; call_fresh_named "p" (fun _p ->
              printfn "create inc in fresh ==== (p)";
              delay2 @@ fun () ->
                printfn "inc in fresh forced: (p)" ;
                (f2 === !!2)
            )
          ]
      ; (evalo !!4 )
      ]
    )
  in
  run q evalo (fun qs -> Stream.take ~n:1 qs
    |> List.map (fun rr -> rr#prj) |> List.iter (printfn "%d") );
  ()
;;
*)
let () = ();;
(* ***************************** a la relational StdLib here ***************  *)
@type ('a, 'l) llist = Nil | Cons of 'a * 'l with show, gmap, html, eq, compare, foldl, foldr;;
@type 'a lnat = O | S of 'a with show, html, eq, compare, foldl, foldr, gmap;;

let none () = inj@@lift None
let some x  = inj@@lift (Some x)

module Bool =
  struct

    type 'a logic' = 'a logic
    let logic' = logic

    type ground = bool

    let ground = {
      GT.gcata = ();
      GT.plugins =
        object(this)
          method html    n   = GT.html   (GT.bool) n
          method eq      n m = GT.eq     (GT.bool) n m
          method compare n m = GT.compare(GT.bool) n m
          method foldr   n   = GT.foldr  (GT.bool) n
          method foldl   n   = GT.foldl  (GT.bool) n
          method gmap    n   = GT.gmap   (GT.bool) n
          method show    n   = GT.show   (GT.bool) n
        end
    }

    type logic = bool logic'

    let logic = {
      GT.gcata = ();
      GT.plugins =
        object(this)
          method html    n   = GT.html   (logic') (GT.html   (ground)) n
          method eq      n m = GT.eq     (logic') (GT.eq     (ground)) n m
          method compare n m = GT.compare(logic') (GT.compare(ground)) n m
          method foldr   a n = GT.foldr  (logic') (GT.foldr  (ground)) a n
          method foldl   a n = GT.foldl  (logic') (GT.foldl  (ground)) a n
          method gmap    n   = GT.gmap   (logic') (GT.gmap   (ground)) n
          method show    n   = GT.show   (logic') (GT.show   (ground)) n
        end
    }

    type boolf = (bool, bool logic') injected
    type groundi = boolf
    type injected   = groundi

    let false_ : boolf = inj@@lift false
    let true_  : boolf = inj@@lift true

    let (|^) a b c =
      conde [
        (a === false_) &&& (b === false_) &&& (c === true_);
        (a === false_) &&& (b === true_)  &&& (c === true_);
        (a === true_)  &&& (b === false_) &&& (c === true_);
        (a === true_)  &&& (b === true_)  &&& (c === false_);
      ]

    let noto' a na = (a |^ a) na

    let noto a = noto' a true_

    let oro a b c =
      Fresh.two (fun aa bb ->
        ((a  |^ a) aa) &&&
        ((b  |^ b) bb) &&&
        ((aa |^ bb) c)
      )

    let ando a b c =
      Fresh.one (fun ab ->
        ((a  |^ b) ab) &&&
        ((ab |^ ab) c)
      )

    let (&&) a b = ando a b true_
    let (||) a b = oro  a b true_

    let show_ground  : ground  -> string = string_of_bool

    let inj b : boolf = inj@@lift b
  end

let eqo x y t =
  conde [
    (x === y) &&& (t === Bool.true_);
    (x =/= y) &&& (t === Bool.false_);
  ]

let neqo x y t =
  conde [
    (x =/= y) &&& (t === Bool.true_);
    (x === y) &&& (t === Bool.false_);
  ];;

module Nat = struct
    type 'a logic' = 'a logic
    let logic' = logic

    module X = struct
      type 'a t = 'a lnat
      let fmap f = function
      | O -> O
      | S n -> S (f n)
    end
    include X
    module F = Fmap1(X)

    type ground = ground t
    type logic = logic t logic'
    type groundi = (ground, logic) injected

    let rec reify : helper -> (ground, logic) injected -> logic  = fun c x ->
      if c#isVar x then var_of_injected_exn c x reify
      else F.reify reify c x

    let ground = {
      GT.gcata = ();
      GT.plugins =
        object(this)
          method html    n = GT.html   (lnat) this#html    n
          method eq      n = GT.eq     (lnat) this#eq      n
          method compare n = GT.compare(lnat) this#compare n
          method foldr   n = GT.foldr  (lnat) this#foldr   n
          method foldl   n = GT.foldl  (lnat) this#foldl   n
          method gmap    n = GT.gmap   (lnat) this#gmap    n
          method show    n = GT.show   (lnat) this#show    n
        end
    }

    let logic = {
      GT.gcata = ();
      GT.plugins =
        object(this)
          method html    n   = GT.html   (logic') (GT.html   (lnat) this#html   ) n
          method eq      n m = GT.eq     (logic') (GT.eq     (lnat) this#eq     ) n m
          method compare n m = GT.compare(logic') (GT.compare(lnat) this#compare) n m
          method foldr   a n = GT.foldr  (logic') (GT.foldr  (lnat) this#foldr  ) a n
          method foldl   a n = GT.foldl  (logic') (GT.foldl  (lnat) this#foldl  ) a n
          method gmap    n   = GT.gmap   (logic') (GT.gmap   (lnat) this#gmap   ) n
          method show    n   = GT.show   (logic') (GT.show   (lnat) this#show   ) n
        end
    }

    let rec of_int n = if n <= 0 then O else S (of_int (n-1))
    let rec to_int   = function O -> 0 | S n -> 1 + to_int n
    let prj_ground   = to_int

    let rec inj_ground: ground -> logic = fun n ->
      Value (GT.(gmap lnat) inj_ground n)

    let o = inj@@lift O
    let s x = inj@@lift (S x)

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
      conde [
        ((x === o)) &&& (z === o);
        Fresh.two (fun x' z' ->
          (x === (s x')) &&& (
          (addo y z' z) &&&
          (mulo x' y z'))
        )
      ]

    let ( * ) = mulo

    let rec leo x y b =
      conde [
        (x === o) &&& (b === Bool.true_);
        (x =/= o) &&& (y === o) &&& (b === Bool.false_);
        Fresh.two (fun x' y' ->
          (x === (s x')) &&& (y === (s y')) &&& (leo x' y' b)
        )
      ]

    let geo x y b = leo y x b

    let (<=) x y = leo x y Bool.true_
    let (>=) x y = geo x y Bool.false_

    let rec gto x y b = conde
      [ (x =/= o) &&& (y === o) &&& (b === Bool.true_)
      ; (x === o) &&& (b === Bool.false_)
      ; Fresh.two (fun x' y' ->
          (x === s x') &&& (y === s y') &&& (gto x' y' b)
        )
      ]

    let lto x y b = gto y x b

    let (>) x y = gto x y Bool.true_
    let (<) x y = lto x y Bool.true_

    let show_ground: ground -> string = GT.show(ground)

  end

let rec inj_nat n =
  if n <= 0 then inj O
  else inj  (S (inj_nat @@ n-1))

module List =
  struct

    include List

    type 'a logic' = 'a logic

    let logic' = logic

    type ('a, 'l) t = ('a, 'l) llist

    module X = struct
      type ('a,'b) t = ('a, 'b) llist
      let fmap f g = function
      | Nil -> Nil
      | Cons (x,xs) -> Cons (f x, g xs)
    end
    module F = Fmap2(X)

    let nil ()  = inj (F.distrib Nil)
    let cons x y = inj (F.distrib (Cons (x, y)))

    type 'a ground = ('a, 'a ground) t;;
    type 'a logic  = ('a, 'a logic) t logic'

    let rec reify : _ -> helper -> (_ ground, 'b logic) injected -> 'b logic = fun arg_r c x ->
      if c#isVar x then var_of_injected_exn c x (reify arg_r)
      else F.reify arg_r (reify arg_r) c x

    let rec of_list = function [] -> nil () | x::xs -> cons x (of_list xs)

    let ground = {
      GT.gcata = ();
      GT.plugins =
        object(this)
          method html    fa l = GT.html   (llist) fa (this#html    fa) l
          method eq      fa l = GT.eq     (llist) fa (this#eq      fa) l
          method compare fa l = GT.compare(llist) fa (this#compare fa) l
          method foldr   fa l = GT.foldr  (llist) fa (this#foldr   fa) l
          method foldl   fa l = GT.foldl  (llist) fa (this#foldl   fa) l
          method gmap    fa l = GT.gmap   (llist) fa (this#gmap    fa) l
          method show    fa l = "[" ^
            let rec inner l =
              (GT.transform(llist)
                 (GT.lift fa)
                 (GT.lift inner)
                 (object inherit ['a,'a ground] @llist[show]
                    method c_Nil   _ _      = ""
                    method c_Cons  i s x xs = x.GT.fx () ^ (match xs.GT.x with Nil -> "" | _ -> "; " ^ xs.GT.fx ())
                  end)
                 ()
                 l
              )
            in inner l ^ "]"
        end
    }

    let logic = {
      GT.gcata = ();
      GT.plugins =
        object(this)
          method compare fa l = GT.compare (logic') (GT.compare (llist) fa (this#compare fa)) l
          method gmap    fa l = GT.gmap    (logic') (GT.gmap    (llist) fa (this#gmap    fa)) l
          method eq      fa l = GT.eq      (logic') (GT.eq      (llist) fa (this#eq      fa)) l
          method foldl   fa l = GT.foldl   (logic') (GT.foldl   (llist) fa (this#foldl   fa)) l
          method foldr   fa l = GT.foldr   (logic') (GT.foldr   (llist) fa (this#foldr   fa)) l
          method html    fa l = GT.html    (logic') (GT.html    (llist) fa (this#html    fa)) l

          (* We override default implementation to show list as semicolon-separated *)
          method show : ('a -> string) -> 'a logic -> GT.string = fun fa l ->
            GT.show(logic')
              (fun l -> "[" ^
                 let rec inner l =
                    GT.transform(llist)
                      (GT.lift fa)
                      (GT.lift (GT.show(logic) inner))
                      (object inherit ['a,'a logic] @llist[show]
                         method c_Nil   _ _      = ""
                         method c_Cons  i s x xs =
                           x.GT.fx () ^ (match xs.GT.x with Value Nil -> "" | _ -> "; " ^ xs.GT.fx ())
                       end)

                    () l
                   in inner l ^ "]"
              )
              l
        end
    }

    let rec inj_ground : ('a -> 'b) -> 'a ground -> 'b logic = fun f xs ->
      Value (GT.(gmap llist) f (inj_ground f) xs)

    let to_logic = inj_ground
    let rec prj_ground : ('a -> 'b) -> 'a ground -> 'b list = fun f -> function
    | Nil -> []
    | Cons (x,xs) -> (f x)::(prj_ground f xs)

    type ('a,'b) groundi = ('a ground, 'b logic) injected

    let groundi =
      { GT.gcata = ()
      ; plugins = object
          method show : ('a -> string) -> ('a,_) groundi -> string = fun fa l ->
          (* we expect no free variables here *)
          GT.show(ground) fa (Obj.magic l : 'a ground)
        end
      }

    let (%): ('a,'b) injected -> ('a,'b) groundi -> ('a,'b) groundi = cons
    let (%<): ('a,'b) injected -> ('a,'b) injected -> ('a,'b) groundi = fun x y -> cons x @@ cons y @@ nil ()
    let (!<) : ('a,'b) injected -> ('a,'b) groundi = fun x -> cons x @@ nil ()

    let rec foldro f a xs r =
      conde [
        (xs === nil ()) &&& (a === r);
        Fresh.three (fun h t a'->
            (xs === h % t) &&&
            (f h a' r) &&&
            (foldro f a t a')
        )
      ]

    let rec mapo f xs ys =
      conde [
        (xs === nil ()) &&& (ys === nil ());
        Fresh.two (fun z zs ->
          (xs === z % zs) &&&
          (Fresh.two (fun a1 a2 ->
              (f z a1) &&&
              (mapo f zs a2) &&&
              (ys === a1 % a2)
          ))
        )
      ]

    let filtero p xs ys =
      let folder x a a' =
        conde [
          (p x Bool.true_) &&& (x % a === a');
          (p x Bool.false_) &&& (a === a')
        ]
      in
      foldro folder (nil ()) xs ys

    let rec lookupo p xs mx =
      conde [
        (xs === nil ()) &&& (mx === none ());
        Fresh.two (fun h t ->
          (h % t === xs) &&&
          (conde [
            (p h Bool.true_) &&& (mx === (some h));
            (p h Bool.false_) &&& (lookupo p t mx)
          ])
        )
      ]

    let anyo = foldro Bool.oro Bool.false_

    let allo = foldro Bool.ando Bool.true_

    let rec lengtho l n =
      conde [
        (l === nil ()) &&& (n === Nat.o);
        Fresh.three (fun x xs n' ->
          (l === x % xs)  &&&
          (n === (Nat.s n')) &&&
          (lengtho xs n')
        )
      ]

    let rec appendo a b ab =
      conde [
        (a === nil ()) &&& (b === ab);
        Fresh.three (fun h t ab' ->
          (a === h%t) &&&
          (h%ab' === ab) &&&
          (appendo t b ab')
        )
      ]

    let rec reverso a b =
      conde [
        (a === nil ()) &&& (b === nil ());
        Fresh.three (fun h t a' ->
          (a === h%t) &&&
          (appendo a' !<h b) &&&
          (reverso t a')
        )
      ]

    let rec membero l a =
      Fresh.two (fun x xs ->
        (l === x % xs) &&&
        (conde [
          x === a;
          (x =/= a) &&& (membero xs a)
        ])
      )

    let nullo q : goal = (q === nil())

    let caro xs h  : goal = call_fresh (fun tl -> xs === (h % tl))
    let cdro xs tl : goal = call_fresh (fun h  -> xs === (h % tl))
    let hdo = caro
    let tlo = cdro

  end

let (%)  = List.cons
let (%<) = List.(%<)
let (!<) = List.(!<)
let nil  = List.nil

let rec inj_list: ('a, 'b) injected list -> ('a, 'b) List.groundi = function
| []    -> nil ()
| x::xs -> List.cons x (inj_list xs)

let inj_list_p xs = inj_list @@ List.map (fun (x,y) -> inj_pair x y) xs

let rec inj_nat_list = function
| []    -> nil()
| x::xs -> inj_nat x % inj_nat_list xs
