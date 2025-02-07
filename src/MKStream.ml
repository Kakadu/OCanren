[@@@ocaml.warning "-unused-constructor"]

let (!!!) = Obj.magic
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

let inc (f: unit -> t) : t =
  Obj.repr f

let from_fun = inc

type wtf = Dummy of int*string | Single of Obj.t
let () = assert (Obj.tag @@ repr (Single !!![]) = 1)

let single : 'a -> t = fun x ->
  Obj.repr @@ Obj.magic (Single !!!x)

let choice a f =
  assert (closure_tag = tag@@repr f);
  Obj.repr @@ Obj.magic (a,f)

let case_inf xs ~f1 ~f2 ~f3 ~f4  =
  if is_int xs then f1 ()
  else
    let tag = Obj.tag (repr xs) in
    if tag = Obj.closure_tag
    then f2 (!!!xs: unit -> Obj.t)
    else if tag = 1 then f3 (field (repr xs) 0)
    else
      (* let () = assert (0 = tag) in
      let () = assert (2 = size (repr xs)) in *)
      f4 (field (repr xs) 0) (!!!(field (repr xs) 1): unit -> Obj.t)
  (* [@@inline ] *)

let rec msplit : t -> ('a *  t) option = fun xs ->
  case_inf xs ~f1:(fun () -> None)
    ~f2:(fun f -> msplit (f ()))
    ~f3:(fun ans -> Some (Obj.magic ans, nil))
    ~f4:(fun ans tl -> Some (!!!ans, (!!!tl: t)))

let step gs =
  assert (closure_tag = tag @@ repr gs);
  Obj.magic gs ()

let rec mplus : t -> t -> t  = fun cinf (gs: t) ->
  assert (closure_tag = tag @@ repr gs);
  case_inf cinf
    ~f1:(fun () ->
          step gs)
    ~f2:(fun f ->
          inc begin fun () ->
            let r = step gs in
            mplus r !!!f
          end)
    ~f3:(fun c ->
          choice c gs
      )
    ~f4:(fun c ff ->
          choice c (inc @@ fun () -> mplus (step gs) !!!ff)
      )

let rec bind cinf g =
  case_inf cinf
    ~f1:(fun () ->
            nil)
    ~f2:(fun f ->
          (* delay here because miniKanren has it *)
          inc begin fun () ->
            let r = f () in
            bind r g
          end)
    ~f3:(fun c ->
          (Obj.magic g c) )
    ~f4:(fun c f ->
          let arg1 = Obj.magic g c in
          mplus arg1 @@
                inc begin fun () ->
                  bind (step f) g
                end
      )