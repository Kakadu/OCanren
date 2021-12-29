(* open Core
open Logic

(** Tabling primitives                                                        *)
module Table : sig
  (* Type of table.
   * Table is a map from answer term to the set of answer terms,
   * i.e. Answer.t -> [Answer.t]
   *)
  type t

  val create : unit -> t
  val call : t -> ('a -> goal) -> 'a -> goal
end = struct
  module H = Hashtbl.Make (Answer)

  module Cache : sig
    type t

    val create : unit -> t
    val add : t -> Answer.t -> unit
    val contains : t -> Answer.t -> bool
    val consume : t -> 'a -> goal
  end = struct
    (* Cache is a pair of queue-like list of answers plus hashtbl of answers;
     * Queue is used because new answers may arrive during the search,
     * we store this new answers to the end of the queue while read from the beginning.
     * Hashtbl is used for a quick check that new added answer is not already contained in the cache.
     *)
    type t = Answer.t list ref * unit H.t

    let create () = ref [], H.create 11

    let add (cache, tbl) answ =
      cache := List.cons answ !cache;
      H.add tbl answ ()
    ;;

    let contains (_, tbl) answ =
      try
        H.find tbl answ;
        true
      with
      | Not_found -> false
    ;;

    let consume (cache, _) args =
      let open State in
      fun ({ env; subst; scope } as st) ->
        let st = State.new_scope st in
        (* [helper start curr seen] consumes answer terms from cache one by one
         *   until [curr] (i.e. current pointer into cache list) is not equal to [seen]
         *   (i.e. to the head of seen part of the cache list)
         *)
        let rec helper start curr seen =
          if curr == seen
          then (
            (* update `seen` - pointer to already seen part of cache *)
            let seen = start in
            (* delayed check that current head of cache is not equal to head of seen part *)
            let is_ready () = seen != !cache in
            (* delayed thunk starts to consume unseen part of cache  *)
            Stream.suspend ~is_ready @@ fun () -> helper !cache !cache seen)
          else (
            (* consume one answer term from cache and `lift` it to the current environment *)
            let answ, tail = Answer.lift env @@ List.hd curr, List.tl curr in
            match State.unify (Obj.repr args) (Answer.unctr_term answ) st with
            | None -> helper start tail seen
            | Some ({ subst = subst'; ctrs = ctrs'; fd } as st') ->
              (* check `answ` disequalities against external substitution *)
              let ctrs =
                ListLabels.fold_left
                  (Answer.disequality answ)
                  ~init:Disequality.empty
                  ~f:
                    (let open Subst.Binding in
                    fun acc { var; term } ->
                      match
                        Disequality.add env Subst.empty acc (Term.repr var) term fd
                      with
                      (* we should not violate disequalities *)
                      | None -> assert false
                      | Some (acc, _fd) ->
                        (* TODO: we may need to take into account _fd *)
                        acc)
              in
              (match Disequality.recheck env subst' ctrs (Subst.split subst') fd with
              | None -> helper start tail seen
              | Some (ctrs, fd) ->
                let st' =
                  { st' with fd; ctrs = Disequality.merge_disjoint env subst' ctrs' ctrs }
                in
                Stream.(cons st' (from_fun @@ fun () -> helper start tail seen))))
        in
        helper !cache !cache []
    ;;
  end

  type t = Cache.t H.t

  let make_answ args st =
    match State.reify args st with
    | [ answ ] ->
      let env = Env.create ~anchor:Term.Var.tabling_env in
      Answer.lift env answ
    | _ -> failwith "should not happen"
  ;;

  let create () = H.create 1031

  let call tbl g args =
    let open State in
    fun ({ env; subst; ctrs } as st) ->
      (* we abstract away disequality constraints before lookup in the table *)
      let abs_st = { st with ctrs = Disequality.empty } in
      let key = make_answ args abs_st in
      try (* slave call *)
          Cache.consume (H.find tbl key) args st with
      | Not_found ->
        (* master call *)
        let cache = Cache.create () in
        H.add tbl key cache;
        (* auxiliary goal for addition of new answer to the cache  *)
        let hook ({ env = env'; subst = subst'; ctrs = ctrs'; fd } as st') =
          let answ = make_answ args st' in
          if not (Cache.contains cache answ)
          then (
            Cache.add cache answ;
            (* TODO: we only need to check diff, i.e. [subst' \ subst] *)
            match Disequality.recheck env subst' ctrs (Subst.split subst') fd with
            | None -> failure ()
            | Some (ctrs, fd) ->
              success
                { st' with fd; ctrs = Disequality.merge_disjoint env subst' ctrs ctrs' })
          else failure ()
        in
        (g args &&& hook) abs_st
  ;;
end

module Tabling = struct
  let succ n () =
    let currier, uncurrier = n () in
    let sc =
      (Curry.succ
        : (('a -> 'b) -> 'c) -> (((_, _) injected as 'k) * 'a -> 'b) -> 'k -> 'c)
    in
    sc currier, Uncurry.succ uncurrier
  ;;

  let one () = (Curry.(one) : ((_, _) injected -> _ as 'x) -> 'x), Uncurry.one
  let two () = succ one ()
  let three () = succ two ()
  let four () = succ three ()
  let five () = succ four ()

  let tabled n g =
    let tbl = Table.create () in
    let currier, uncurrier = n () in
    currier (Table.call tbl @@ uncurrier g)
  ;;

  let tabledrec n g_norec =
    let tbl = Table.create () in
    let currier, uncurrier = n () in
    let g = ref (fun _ -> assert false) in
    let g_rec args = uncurrier (g_norec !g) args in
    let g_tabled = Table.call tbl g_rec in
    g := currier g_tabled;
    !g
  ;;
end *)
