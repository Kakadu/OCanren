(*
 * OCanren.
 * Copyright (C) 2015-2017
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

[%%if false]

type stat =
  { mutable unification_count : int
  ; mutable unification_time : Mtime.span
  ; mutable conj_counter : int
  ; mutable disj_counter : int
  ; mutable delay_counter : int
  }

let stat =
  { unification_count = 0
  ; unification_time = Mtime.Span.zero
  ; conj_counter = 0
  ; disj_counter = 0
  ; delay_counter = 0
  }
;;

let unification_counter () = stat.unification_count
let unification_time () = stat.unification_time
let conj_counter () = stat.conj_counter
let disj_counter () = stat.disj_counter
let delay_counter () = stat.delay_counter

let ( unification_incr
    , unification_time_incr
    , conj_counter_incr
    , disj_counter_incr
    , delay_counter_incr )
  =
  match Sys.getenv_opt "OCANREN_BENCH_COUNTS" with
  | None ->
    let c _ = () in
    c, c, c, c, c
  | Some _ ->
    let unification_incr () = stat.unification_count <- stat.unification_count 1 in
    let unification_time_incr t =
      stat.unification_time <- Mtime.Span.add stat.unification_time (t ())
    in
    let conj_counter_incr () = stat.conj_counter <- stat.conj_counter 1 in
    let disj_counter_incr () = stat.disj_counter <- stat.disj_counter 1 in
    let delay_counter_incr () = stat.delay_counter <- stat.delay_counter 1 in
    ( unification_incr
    , unification_time_incr
    , conj_counter_incr
    , disj_counter_incr
    , delay_counter_incr )
;;

[%%endif]

(* to avoid clash with Std.List (i.e. logic list) *)
module List = Stdlib.List

module Answer : sig
  (* [Answer.t] - a type that represents (untyped) answer to a query *)
  type t

  (* [make env t] creates the answer from the environment and term (with constrainted variables)  *)
  val make : Env.t -> Term.t -> t

  (* [lift env a] lifts the answer into different environment, replacing all variables consistently *)
  val lift : Env.t -> t -> t

  (* [env a] returns an environment of the answer *)
  val env : t -> Env.t

  (* [unctr_term a] returns a term with unconstrained variables *)
  val unctr_term : t -> Term.t

  (* [ctr_term a] returns a term with constrained variables *)
  val ctr_term : t -> Term.t

  (* [disequality a] returns all disequality constraints on variables in term as a list of bindings *)
  val disequality : t -> Subst.Binding.t list

  (* [equal t t'] syntactic equivalence (not an alpha-equivalence) *)
  val equal : t -> t -> bool

  (* [hash t] hashing that is consistent with syntactic equivalence *)
  val hash : t -> int
end = struct
  type t = Env.t * Term.t

  let make env t = env, t
  let env (env, _) = env

  let unctr_term (_, t) =
    Term.map
      t
      ~fval:(fun x -> Term.repr x)
      ~fvar:(fun v -> Term.repr { v with Term.Var.constraints = [] })
  ;;

  let ctr_term (_, t) = t

  let disequality (env, t) =
    let rec helper acc x =
      Term.fold
        x
        ~init:acc
        ~fval:(fun acc _ -> acc)
        ~fvar:(fun acc var ->
          ListLabels.fold_left var.Term.Var.constraints ~init:acc ~f:(fun acc ctr_term ->
              let ctr_term = Term.repr ctr_term in
              let var = { var with Term.Var.constraints = [] } in
              let term = unctr_term @@ (env, ctr_term) in
              let acc = Subst.(Binding.{ var; term }) :: acc in
              helper acc ctr_term))
    in
    helper [] t
  ;;

  let lift env' (env, t) =
    let vartbl = Term.VarTbl.create 31 in
    let rec helper x =
      Term.map
        x
        ~fval:(fun x -> Term.repr x)
        ~fvar:(fun v ->
          Term.repr
          @@
          try Term.VarTbl.find vartbl v with
          | Not_found ->
            let new_var = Env.fresh ~scope:Term.Var.non_local_scope env' in
            Term.VarTbl.add vartbl v new_var;
            { new_var with
              Term.Var.constraints =
                List.map (fun x -> helper x) v.Term.Var.constraints
                |> List.sort Term.compare
            })
    in
    env', helper t
  ;;

  let check_envs_exn env env' =
    if Env.equal env env'
    then ()
    else failwith "OCanren fatal (Answer.check_envs): answers from different environments"
  ;;

  let equal (env, t) (env', t') =
    check_envs_exn env env';
    Term.equal t t'
  ;;

  let hash (env, t) = Term.hash t
end

module Prunes : sig
  type rez =
    | Violated
    | NonViolated

  type ('a, 'b) reifier = Env.t -> ('a, 'b) Logic.injected -> 'b
  type 'b cond = 'b -> bool
  type t

  val empty : t

  (* Returns false when constraints are violated *)
  val recheck : t -> Env.t -> Subst.t -> rez
  val check_last : t -> Env.t -> Subst.t -> rez
  val extend : t -> Term.VarTbl.key -> ('a, 'b) reifier -> 'b cond -> t
end = struct
  type rez =
    | Violated
    | NonViolated

  type ('a, 'b) reifier = Env.t -> ('a, 'b) Logic.injected -> 'b
  type reifier_untyped = Env.t -> Obj.t -> Obj.t
  type 'b cond = 'b -> bool
  type cond_untyped = Obj.t -> bool

  let make_untyped : ('a, 'b) reifier -> 'b cond -> reifier_untyped * cond_untyped =
   fun a b -> Obj.magic (a, b)
 ;;

  type t = (Obj.t * (reifier_untyped * cond_untyped)) list

  let empty = []

  exception Fail

  let check_last map env subst =
    try
      let term, (reifier, checker) = List.hd map in
      let reified = reifier env (Obj.magic @@ Subst.apply env subst term) in
      if not (checker reified) then raise Fail;
      NonViolated
    with
    | Not_found -> NonViolated
    | Fail -> Violated
  ;;

  let recheck ps env s =
    try
      ps
      |> List.iter (fun (k, (reifier, checker)) ->
             let reified = reifier env (Obj.magic @@ Subst.apply env s k) in
             if not (checker reified) then raise Fail);
      NonViolated
    with
    | Fail -> Violated
  ;;

  let extend map term rr cond =
    let new_item = make_untyped rr cond in
    (Obj.repr term, new_item) :: map
  ;;
end

type prines_control =
  { mutable pc_do_skip : bool
  ; mutable pc_checks_skipped : int
  ; mutable pc_max_to_skip : int
  ; mutable pc_skipped_prunes_total : int
  }

let prunes_control =
  { pc_checks_skipped = 10
  ; pc_do_skip = false
  ; pc_max_to_skip = 11
  ; pc_skipped_prunes_total = 0
  }
;;

module PrunesControl = struct
  let enable_skips ~on =
    (*    Printf.printf "enabling skips: %b\n%!" on;*)
    prunes_control.pc_do_skip <- on
  ;;

  let is_enabled () = prunes_control.pc_do_skip
  let reset_cur_counter () = prunes_control.pc_checks_skipped <- 0

  let reset () =
    reset_cur_counter ();
    prunes_control.pc_skipped_prunes_total <- 0
  ;;

  let set_max_skips n =
    assert (n > 0);
    prunes_control.pc_max_to_skip <- n;
    reset ()
  ;;

  let skipped_prunes () = prunes_control.pc_skipped_prunes_total

  let incr () =
    if is_enabled ()
    then (
      let () = prunes_control.pc_checks_skipped <- 1 + prunes_control.pc_checks_skipped in
      prunes_control.pc_skipped_prunes_total <- 1 + prunes_control.pc_skipped_prunes_total)
  ;;

  let is_exceeded () =
    (not (is_enabled ()))
    ||
    let ans = prunes_control.pc_checks_skipped >= prunes_control.pc_max_to_skip in
    (*    Printf.printf "is_exceeded = %b, cur_steps=%d, max_steps=%d\n%!"
      ans
      prunes_control.pc_checks_skipped
      prunes_control.pc_max_to_skip;*)
    ans
  ;;
end

(*
let do_skip_prunes = ref false
let prunes_checks_skipped = ref 0
let max_prunes_skipped = ref 10

let set_skip_prunes_count n =
  assert (n>0);
  max_prunes_skipped := n
*)
module StateId = struct
  type t = GT.int [@@deriving gt ~options:{ fmt }]

  let hash = Hashtbl.hash
  let equal = ( == )
  let compare = compare
  let show = string_of_int
end

module Listener = struct
  open Printf
  open GT

  type event =
    | Success
    | Failure of string
    | Conj
    | Disj
    | Cont of StateId.t
    | Unif of (string * string) option
    | Diseq of (string * string) option
    | Goal of string * string list
    | Answer of string * string list
    | Custom of string
  [@@deriving gt ~options:{ fmt }]

  let string_of_event = function
    | Success -> "success"
    | Failure reason -> sprintf "failure: %s" reason
    | Conj -> "&&&"
    | Disj -> "conde"
    | Cont id -> sprintf "{%s}" @@ StateId.show id
    | Goal (name, args) -> sprintf "%s %s" name @@ String.concat " " args
    | Answer (name, args) -> sprintf "%s %s" name @@ String.concat " " args
    | Custom str -> str
    | Unif args ->
      (match args with
      | Some (x, y) -> sprintf "%s === %s" x y
      | None -> "===")
    | Diseq args ->
      (match args with
      | Some (x, y) -> sprintf "%s =/= %s" x y
      | None -> "=/=")
  ;;

  type t =
    < init : StateId.t -> unit ; on_event : event -> StateId.t -> StateId.t -> unit >

  (* let log_unif listener *)
end

module State = struct
  module Disequality = Disequality2.Make (struct
    type t = FM.t

    let neq = FM.neq
    let is_interesting_var = FM.is_interesting_var
  end)

  type t =
    { env : Env.t
    ; subst : Subst.t
    ; ctrs : Disequality.t
    ; prunes : Prunes.t
    ; scope : Term.Var.scope
    ; fd : FM.t
    ; id : StateId.t
    ; lastId : int ref
    ; listener : Listener.t option
    }

  type reified = Env.t * Term.t

  let empty ?listener () =
    let id = 0 in
    let () =
      match listener with
      | Some listener -> listener#init id
      | None -> ()
    in
    { env = Env.empty ()
    ; subst = Subst.empty
    ; ctrs = Disequality.empty
    ; prunes = Prunes.empty
    ; scope = Term.Var.new_scope ()
    ; fd = FM.empty ()
    ; id
    ; lastId = ref id
    ; listener
    }
  ;;

  let env { env } = env
  let subst { subst } = subst
  let constraints { ctrs } = ctrs
  let scope { scope } = scope
  let prunes { prunes } = prunes
  let fds { fd } = fd
  let fresh { env; scope } = Env.fresh ~scope env
  let wc { env; scope } = Env.wc ~scope env
  let new_scope st = { st with scope = Term.Var.new_scope () }

  let unify x y ({ env; subst; ctrs; scope; fd } as st) =
    let ( >>=? ) x f =
      match x with
      | Some a -> f a
      | None -> None
    in
    Subst.unify ~scope env subst x y
    >>=? fun (prefix, subst) ->
    Disequality.recheck env subst ctrs prefix fd
    >>=? fun (ctrs, fd) ->
    FM.recheck env subst fd prefix
    >>=? fun fd ->
    let next_state = { st with subst; ctrs; fd } in
    if PrunesControl.is_exceeded ()
    then (
      let () = PrunesControl.reset_cur_counter () in
      match Prunes.recheck (prunes next_state) env subst with
      | Prunes.Violated -> None
      | NonViolated -> Some next_state)
    else (
      let () = PrunesControl.incr () in
      Some next_state)
  ;;

  let diseq x y ({ env; subst; ctrs; scope; fd } as st) =
    match Disequality.add env subst ctrs x y fd with
    | None -> None
    | Some (ctrs, fd) ->
      (match Prunes.recheck (prunes st) env subst with
      | Prunes.Violated -> None
      | NonViolated -> Some { st with ctrs; fd })
  ;;

  (* returns always non-empty list *)
  let reify x { env; subst; ctrs } =
    let rec helper diseq forbidden =
      Term.map
        ~fval:(fun x -> Term.repr x)
        ~fvar:(fun v ->
          Term.repr
            (if List.mem v.Term.Var.index forbidden
            then v
            else
              { v with
                Term.Var.constraints =
                  Disequality.Answer.extract diseq v
                  |> List.filter (fun dt ->
                         match Env.var env dt with
                         | Some u -> not (List.mem u.Term.Var.index forbidden)
                         | None -> true)
                  |> List.map (fun x -> helper diseq (v.Term.Var.index :: forbidden) x)
                  (* TODO: represent [Var.constraints] as [Set];
                   * TODO: hide all manipulations on [Var.t] inside [Var] module;
                   *)
                  |> List.sort Term.compare
              }))
    in
    let val_in_subst = Subst.reify env subst x in
    match Disequality.reify env subst ctrs x with
    | [] -> [ Answer.make env val_in_subst ]
    | diseqs ->
      ListLabels.map diseqs ~f:(fun diseq ->
          Answer.make env (helper diseq [] val_in_subst))
  ;;

  let new_event ?pid e ({ id; lastId; listener } as _st) =
    incr lastId;
    let pid =
      match pid with
      | Some pid -> pid
      | None -> id
    in
    let new_id = !lastId in
    (* Format.printf "new event: (%d -> %d) %s\n%!" pid new_id (Listener.string_of_event e); *)
    (match listener with
    | Some listener -> listener#on_event e pid new_id
    | None -> ());
    new_id
  ;;

  let enter_conde ({ id; scope } as st) =
    let new_id = new_event Listener.Disj st in
    new_scope { st with id = new_id }
  ;;
end

let ( !!! ) = Obj.magic

type 'a goal' = State.t -> 'a
type goal = State.t Stream.t goal'

let success st =
  let _ = State.new_event Listener.Success st in
  Stream.single st
;;

let failure ~reason st =
  let _ = State.new_event (Listener.Failure reason) st in
  Stream.nil
;;

let only_head g st =
  let stream = g st in
  try Stream.single @@ Stream.hd stream with
  | Failure _ -> Stream.nil
;;

module FD = struct
  (* let lt a b st =
    match FM.lt a b (State.fds st) with
    | None -> failure ()
    | Some fd -> success {st with State.fd = fd } *)

  let eq a b st =
    match FM.eq a b (State.fds st) with
    | None -> failure ~reason:"FD.eq" st
    | Some fd -> success { st with State.fd }
  ;;

  let neq a b st =
    match FM.neq a b (State.fds st) with
    | None -> failure ~reason:"FD.neq" st
    | Some fd -> success { st with State.fd }
  ;;

  let domain v xs st =
    match FM.domain v xs (State.fds st) with
    | None -> failure ~reason:"FD.domain" st
    | Some fd -> success { st with State.fd }
  ;;
end

(* ********************************************************************* *)

(*
include (
  struct
    type cost =
      | CFixed of GT.int
      | CAtLeast of GT.int
    [@@deriving gt ~options:{ show }]

    let show_cost x = GT.show cost x

    let minimize cost reifier var goalish state =
      let old_cost = ref None in
      goalish var state
      |> Stream.filter (fun st0 ->
             let reified =
               let env = State.env st0 in
               let s = State.subst st0 in
               reifier env (Obj.magic @@ Subst.apply env s var)
             in
             let c = cost reified in
             match !old_cost with
             | None ->
               Format.printf "setting intial cost %s\n%!" (show_cost c);
               old_cost := Some c;
               true
             | Some old ->
               (match old, c with
               | CFixed old, CFixed new_ when old < new_ -> false
               | CFixed old, CFixed new_ when old = new_ -> true
               | CFixed old, CFixed new_ ->
                 Format.printf "setting cost %s\n%!" (show_cost c);
                 old_cost := Some c;
                 true
               | CAtLeast old, CFixed new_ when old < new_ -> false
               | CAtLeast old, CFixed new_ ->
                 Format.printf "setting cost %s\n%!" (show_cost c);
                 old_cost := Some c;
                 true
               | CFixed old, CAtLeast new_ when old < new_ -> false
               | CFixed old, CAtLeast new_ -> true
               | CAtLeast old, CAtLeast new_ when old < new_ -> false
               | CAtLeast old, CAtLeast new_ ->
                 Format.printf "setting cost %s\n%!" (show_cost c);
                 old_cost := Some c;
                 true))
    ;;
  end :
    sig
      type cost =
        | CFixed of GT.int
        | CAtLeast of GT.int

      val minimize
        :  ('b -> cost)
        -> (Env.t -> 'logicvar -> 'b)
        -> (('a, 'b) injected as 'logicvar)
        -> ('logicvar -> goal)
        -> goal
    end)
*)

(* ******************************************************************************* *)
let call_fresh f st =
  let x = State.fresh st in
  f x st
;;

(* ************************** Reification stuff ********************************** *)
module Refiner : sig
  val zero : (goal * State.t -> goal) -> goal -> goal

  val one
    :  ((State.t -> ('a, 'b) reified) * (goal * State.t) -> goal)
    -> ('a, 'b) injected
    -> goal
    -> goal

  val two
    :  ((State.t -> ('a, 'b) reified) * ((State.t -> ('c, 'd) reified) * (goal * State.t))
        -> goal)
    -> ('a, 'b) injected
    -> ('c, 'd) injected
    -> goal
    -> goal

  val succ
    :  (('a -> 'b) -> 'c)
    -> ((State.t -> ('d, 'e) reified) * 'a -> 'b)
    -> ('d, 'e) injected
    -> 'c
end = struct
  type ('a, 'b) refiner = State.t -> ('a, 'b) Logic.reified

  let succ prev k x = prev (fun y -> k ((fun st -> make_rr (State.env st) x), y))
  let zero : (goal * State.t -> goal) -> goal -> goal = fun k g st -> k (g, st) st
  let one eta = succ zero eta
  let two eta = succ (succ zero) eta
end

module ExtractDeepest = struct
  let ext2 x = x

  let succ prev (a, z) =
    let foo, base = prev z in
    (a, foo), base
  ;;

  let three eta = succ ext2 eta
end

module Curry = struct
  let one = ( @@ )
  let succ k f x = k (fun tup -> f (x, tup))
end

module Uncurry = struct
  let one = ( @@ )
  let succ k f (x, y) = k (f x) y
end

module ApplyState = struct
  let one st r = r st
  let succ prev st (r, y) = r st, prev st y
end

module Trace = struct
  type ('a, 'b) refiner = State.t -> ('a, 'b) Logic.reified

  let succ n () =
    let refiner, uncurrier, app, ext1, ext2 = n () in
    ( Refiner.succ refiner
    , Uncurry.succ uncurrier
    , ApplyState.succ app
    , ExtractDeepest.succ ext1
    , ExtractDeepest.succ ext2 )
  ;;

  let one () =
    ( Refiner.(succ zero)
    , ( @@ )
    , ApplyState.one
    , ExtractDeepest.(succ ext2)
    , ExtractDeepest.ext2 )
  ;;

  let two () = succ one ()
  let three () = succ two ()
  let four () = succ three ()
  let five () = succ four ()

  let trace n callback =
    let refiner, uncurrier, app, ext1, ext2 = n () in
    let f g tup st =
      State.(
        let e = (uncurrier @@ callback) tup in
        g { st with id = State.new_event e st })
    in
    refiner (fun tup ->
        let x, st = ext1 tup in
        let y, g = ext2 x in
        f g (app st y))
  ;;

  let print_pair ?p x y =
    match p with
    | Some p -> Some (p x, p y)
    | None -> None
  ;;

  let unif ?p x y = Listener.Unif (print_pair ?p x y)
  let diseq ?p x y = Listener.Diseq (print_pair ?p x y)
end

module LogicAdder : sig
  val zero : goal -> goal

  val succ
    :  ('a -> State.t -> 'd)
    -> (('e, 'f) injected -> 'a)
    -> State.t
    -> ('e, 'f) injected * 'd
end = struct
  let zero f = f
  let succ prev f = call_fresh (fun logic st -> logic, prev (f logic) st)
end

module ReifyTuple = struct
  let one x env = make_rr env x
  let succ prev (x, xs) env = make_rr env x, prev xs env
end

let succ n () =
  let adder, app, ext, uncurr = n () in
  LogicAdder.succ adder, ReifyTuple.succ app, ExtractDeepest.succ ext, Uncurry.succ uncurr
;;

let one () = LogicAdder.(succ zero), ReifyTuple.one, ExtractDeepest.ext2, Uncurry.one
let two () = succ one ()
let three () = succ two ()
let four () = succ three ()
let five () = succ four ()
let q = one
let qr = two
let qrs = three
let qrst = four
let qrstu = five

let run ?listener n g h =
  let adder, reifier, ext, uncurr = n () in
  let args, stream = ext @@ adder g @@ State.empty ?listener () in
  Stream.bind stream (fun st -> Stream.of_list @@ State.reify args st)
  |> Stream.map (fun answ ->
         uncurr h @@ reifier (Obj.magic @@ Answer.ctr_term answ) (Answer.env answ))
;;

(* **************************************************************************************** *)

let wc f st =
  let x = State.wc st in
  f x st
;;

module Fresh = struct
  let succ prev f = call_fresh (fun x -> prev (f x))
  let zero f = f
  let one f = succ zero f
  let two f = succ one f

  (* N.B. Manual inlining of numerals will speed-up OCanren a bit (mainly because of less memory consumption) *)
  (* let two   g = fun st ->
      let scope = State.scope st in
      let env = State.env st in
      let q = Env.fresh ~scope env in
      let r = Env.fresh ~scope env in
      g q r st *)

  let three f = succ two f
  let four f = succ three f
  let five f = succ four f
  let q = one
  let qr = two
  let qrs = three
  let qrst = four
  let pqrst = five
end

type ('a, 'b) printer = ('a, 'b) Logic.reified -> string

let make_cont g pid =
  let open State in
  fun ({ id } as st) ->
    let cont_id = new_event ~pid (Listener.Cont id) st in
    g { st with id = cont_id }
;;

let unify ?p x y =
  Trace.(trace two @@ unif ?p) x y (fun st ->
      let _t =
        let module _ = struct
          [%%if false]

          let () =
            unification_incr ();
            Timer.make ()
          ;;

          [%%endif]
        end
        in
        ()
      in
      match State.unify x y st with
      | Some st ->
        let module _ = struct
          [%%if false]

          let () = unification_time_incr _t

          [%%endif]
        end
        in
        success st
      | None ->
        let module _ = struct
          [%%if false]

          let () = unification_time_incr _t

          [%%endif]
        end
        in
        failure ~reason:"===" st)
;;

let ( === ) = unify

let ( =/= ) ?p x y =
  Trace.(trace two @@ diseq ?p)
    x
    y
    (let open State in
    fun ({ env; subst; ctrs; scope } as st) ->
      match State.diseq x y st with
      | Some st ->
        let module _ = struct
          [%%if false]

          let () = delay_counter_incr ()

          [%%endif]
        end
        in
        success st
      | None -> failure ~reason:"=/=" st)
;;

let diseq = ( =/= )
let delay g st = Stream.from_fun (fun () -> g () st)

let conj f g st =
  let module _ = struct
    [%%if false]

    let () = conj_counter_incr ()

    [%%endif]
  end
  in
  Stream.bind (f st) g
;;

let debug_var v reifier call st =
  let xs =
    List.map
      (fun answ -> reifier (Answer.env answ) (Obj.magic @@ Answer.ctr_term answ))
      (State.reify v st)
  in
  call xs st
;;

let debug_lino ?(text = "") file col st =
  Format.printf "%s %s %d\n%!" text file col;
  success st
;;

let structural term rr k st =
  let new_constraints = Prunes.extend (State.prunes st) (Obj.magic term) rr k in
  match Prunes.check_last new_constraints (State.env st) (State.subst st) with
  | Prunes.Violated -> failure ~reason:"structural" st
  | NonViolated -> success { st with State.prunes = new_constraints }
;;

let ( &&& ) = conj

let list_fold_left1 ~f ~initer xs =
  match xs with
  | [] -> failwith "bad argument"
  | x :: xs -> ListLabels.fold_left ~init:(initer x) ~f xs
;;

let ( ?& ) =
  let open State in
  fun xs st ->
    let id = new_event Listener.Conj st in
    list_fold_left1
      ~initer:(fun x -> x)
      xs
      ~f:(fun acc g st -> Stream.bind (acc { st with id }) (fun st -> g { st with id }))
    |> fun g -> Stream.from_fun (fun () -> g st)
;;

(*
let ( ?& ) gs st =
  let id = State.new_event Listener.Conj st in
  List.fold_right
    (fun g acc st -> Stream.bind (acc { st with State.id }) (make_cont g id))
    gs
    success
    st
;;
 *)
let compose = ( ?& )
let disj_base f g st = Stream.mplus (f st) (Stream.from_fun (fun () -> g st))

let list_fold_left1 ~f ~initer xs =
  match xs with
  | [] -> failwith "bad argument"
  | x :: xs -> ListLabels.fold_left ~init:(initer x) ~f xs
;;

let list_fold_right1 ~f ~initer xs =
  let rec helper = function
    | [] -> failwith "bad_argument"
    | xs -> list_fold_left1 ~initer ~f xs
  in
  helper (List.rev xs)
;;

let disj f g st =
  let module _ = struct
    [%%if false]

    let () = disj_counter_incr ()

    [%%endif]
  end
  in
  let st = State.new_scope st in
  let st = { st with id = State.new_event Listener.Disj st } in
  disj_base f g |> fun g -> Stream.from_fun (fun () -> g st)
;;

let ( ||| ) = disj

(* "mplus*" *)
let rec ( ?| ) xs st =
  let st = State.enter_conde st in
  list_fold_right1
    ~initer:(fun x -> x)
    xs
    ~f:(fun acc g st -> Stream.mplus (g st) @@ Stream.from_fun (fun () -> acc st))
  |> fun g -> Stream.from_fun (fun () -> g st)
;;

(* let ( ?| ) gs st =
  let st = State.enter_conde st in
  let st = State.new_scope st in
  let rec inner = function
    | [ g ] -> g
    | g :: gs -> disj_base g (inner gs)
    | [] -> failwith "Wrong argument of (?!)"
  in
  inner gs |> fun g -> Stream.from_fun (fun () -> g st)
;; *)

let conde = ( ?| )

let unif_hack x y rez st =
  match State.unify (Obj.magic x) (Obj.magic y) st with
  | Some _ -> ( === ) rez !!true st
  | None -> ( === ) rez !!false st
;;

(* let gives_single_answer g : goal = fun st ->
  let stream = g st in
  let xs = Stream.take ~n:2 stream in
  match xs with
  | [] -> sin *)

(* let rec my_to_string t =
  if Obj.is_int t then string_of_int (!!!t)
  else if Term.is_var t
  then
    let v : Term.Var.t = Obj.magic t in
    Format.sprintf "(var %d)" v.Term.Var.index
  else
    let b = Buffer.create 10 in
    let () = Printf.bprintf b "Block<%d, " (Obj.tag t)  in
    let () =
      for i=0 to Obj.size t -1 do
         Printf.bprintf b " %s" (my_to_string @@ Obj.field t i)
      done in
    let () = Printf.bprintf b ">" in
    Buffer.contents b *)

module Unique = struct
  type 'a t =
    | NoAnswer
    | Unique of 'a
    | DifferentAnswers
  [@@deriving gt ~options:{ show }]

  type 'a ground = 'a t [@@deriving gt ~options:{ show }]
  type 'a logic = 'a t Logic.logic [@@deriving gt ~options:{ show }]
  type nonrec ('a, 'b) injected = ('a ground, 'b t Logic.logic) Logic.injected

  module F = Logic.Fmap (struct
    type nonrec 'a t = 'a t

    let fmap f = function
      | Unique x -> Unique (f x)
      | NoAnswer -> NoAnswer
      | DifferentAnswers -> DifferentAnswers
    ;;
  end)

  let reify = F.reify
  let unique x = inj @@ F.distrib (Unique x)
  let noanswer = Obj.magic (inj @@ F.distrib NoAnswer)
  let different = Obj.magic (inj @@ F.distrib DifferentAnswers)

  let unique_answers g (rez : (_, _) injected) st =
    let v = State.fresh st in
    let stream = g (Obj.magic v) st in
    if Stream.is_empty stream
    then ( === ) rez (Obj.magic NoAnswer) st
    else (
      let xs =
        Stream.take stream
        |> List.map (fun st0 -> Subst.reify (State.env st0) (State.subst st0) v)
      in
      let first = List.hd xs in
      if Stdlib.List.for_all
           (fun el ->
             (* let __ _ = Format.printf "  el = '%s'\n%!" (my_to_string el) in *)
             el = first)
           xs
      then
        (* let __ _ = Format.printf "first = '%s'\n%!" (my_to_string first) in *)
        ( === ) rez (Obj.magic (Unique first)) st
      else
        (* let __ _ = List.iter (fun x -> Format.printf "%s\n%!" (my_to_string !!!x)) xs in *)
        ( === ) rez (Obj.magic DifferentAnswers) st)
  ;;
end
