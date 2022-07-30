(*
  Going to implement very naive disequality constraints
  which will be stored internally as a CNF
*)

open Format

exception Violated

let ( !!! ) = Obj.magic
let use_logging = ref false
let set_logging flg = use_logging := flg
(* TODO: Allowing to set this flag externally could hurt performace. *)

let log fmt =
  if !use_logging
  then Format.kasprintf (fun s -> Format.printf "%s\n%!" s) fmt
  else Format.ifprintf Format.std_formatter fmt
;;

open Term

let is_wc_var v =
  match Term.var v with
  | Some { Var.index = -42 } -> true
  | _ -> false
;;

module type EXTRA = sig
  type t

  open Logic

  val neq : int ilogic -> int ilogic -> t -> t option
  val is_interesting_var : Term.Var.t -> t -> bool
  val get_domain_size : Term.Var.t -> t -> int list option
  val trace : t -> unit
end

let rec a_la_cartesian = function
  | [] -> [ [] ]
  | [] :: xs ->
    (* Important for filteering unneeded results.*)
    (* Not a feature of cartesion product *)
    a_la_cartesian xs
  | x :: xs ->
    let xs = a_la_cartesian xs in
    List.concat_map (fun x -> List.map (fun xs -> x :: xs) xs) x
;;

module SS = Streaming.Stream

let rec a_la_cartesian_seq : 'a. 'a SS.t list -> 'a SS.t list = function
  | [] -> List.cons SS.empty []
  | e :: xs when SS.is_empty e ->
    (* Important for filteering unneeded results.*)
    (* Not a feature of cartesion product *)
    a_la_cartesian_seq xs
  | x :: xs ->
    let xs = a_la_cartesian_seq xs in
    SS.flat_map (fun x -> List.map (SS.prepend x) xs |> SS.of_list) x |> SS.to_list
;;

let%test _ =
  let ans = a_la_cartesian [ [ 1; 2 ]; [ 3; 4 ] ] in
  ans = [ [ 1; 3 ]; [ 1; 4 ]; [ 2; 3 ]; [ 2; 4 ] ]
;;

let%test _ =
  let ans =
    a_la_cartesian_seq [ SS.of_list [ 1; 2 ]; SS.of_list [ 3; 4 ] ] |> List.map SS.to_list
  in
  (* print_endline @@ GT.show GT.list (GT.show GT.list @@ GT.show GT.int) ans; *)
  ans = [ [ 1; 3 ]; [ 1; 4 ]; [ 2; 3 ]; [ 2; 4 ] ]
;;

let cartesian2 ~f l l' = List.concat_map (fun e -> List.map (f e) l') l

let%test _ =
  let ans = cartesian2 ~f:(sprintf "%d%d") [ 1; 2 ] [ 3; 4 ] in
  ans = [ "13"; "14"; "23"; "24" ]
;;

module CartesianHacks = struct
  module type ttt = sig
    type 'a t

    val return : 'a -> 'a t
    val bind : ('a -> 'b t) -> 'a t -> 'b t
    val map : ('a -> 'b) -> 'a t -> 'b t
    val head : 'a t -> 'a option
    val rest : 'a t -> 'a t
    val cons : 'a -> 'a t -> 'a t
    val empty : 'a t
    val ( !! ) : 'a list -> 'a t
    val to_list : 'a t -> 'a list
  end

  module Cartesian (CNT : ttt) = struct
    let rec cartesian : 'a. 'a CNT.t CNT.t -> 'a CNT.t CNT.t =
     fun xss ->
      match CNT.head xss with
      | None -> CNT.cons CNT.empty CNT.empty
      | Some h when CNT.head h = None ->
        (* Important for filteering unneeded results.*)
        (* Not a feature of cartesion product *)
        cartesian (CNT.rest xss)
      | Some x ->
        let xs = cartesian (CNT.rest xss) in
        CNT.bind (fun x -> CNT.map (CNT.cons x) xs) x
   ;;
  end

  module ExtList = struct
    include List

    let empty = []
    let rest = List.tl

    let head = function
      | x :: _ -> Some x
      | _ -> None
    ;;

    let bind = concat_map
    let return x = [ x ]
    let ( !! ) = Fun.id
    let to_list = Fun.id
  end

  module ExtStream = struct
    include Streaming.Stream

    let cons = prepend
    let return = yield
    let head = first
    let bind = flat_map
    let ( !! ) = of_list
  end

  module ExtSeq : ttt with type 'a t = 'a Seq.t = struct
    include Seq

    let cons x xs () = Seq.Cons (x, xs)
    let return = return

    let head : 'a t -> 'a option =
     fun s ->
      match s () with
      | Seq.Nil -> None
      | Seq.Cons (x, _) -> Some x
   ;;

    let rest : 'a t -> 'a t =
     fun s ->
      match s () with
      | Seq.Cons (_, tl) -> tl
      | Nil -> failwith "no tail"
   ;;

    let bind = flat_map
    let ( !! ) = List.to_seq
    let to_list = List.of_seq
  end

  let cartesian_list =
    let module M = Cartesian (ExtList) in
    M.cartesian
  ;;

  let cartesian_stream =
    let module M = Cartesian (ExtStream) in
    M.cartesian
  ;;

  module MS = Cartesian (ExtSeq)

  let cartesian_seq : 'a. 'a Seq.t Seq.t -> 'a Seq.t Seq.t = fun xs -> MS.cartesian xs

  let%test _ =
    let ans = cartesian_list [ [ 1; 2 ]; [ 3; 4 ] ] in
    ans = [ [ 1; 3 ]; [ 1; 4 ]; [ 2; 3 ]; [ 2; 4 ] ]
  ;;

  let%test _ =
    let open ExtStream in
    let ans = cartesian_stream !![ !![ 1; 2 ]; !![ 3; 4 ] ] in
    to_list (map to_list ans) = [ [ 1; 3 ]; [ 1; 4 ]; [ 2; 3 ]; [ 2; 4 ] ]
  ;;

  let%test _ =
    let open ExtSeq in
    let ans = cartesian_seq !![ !![ 1; 2 ]; !![ 3; 4 ] ] in
    to_list (map to_list ans) = [ [ 1; 3 ]; [ 1; 4 ]; [ 2; 3 ]; [ 2; 4 ] ]
  ;;

  let cartesian2_seq ~f l l' = ExtSeq.bind (fun e -> ExtSeq.map (f e) l') l
end

module Make (FDC : EXTRA) = struct
  module Conjunct = struct
    type t = Subst.Binding.t

    let pp ppf Subst.Binding.{ var; term } =
      Format.fprintf ppf "{ %a <> '%s' }" Term.describe_var var (Term.show term)
    ;;

    let compare = Subst.Binding.compare

    let intersects_with ~set : t -> bool =
     fun c ->
      (* log "set = %a" Term.VarSet.pp set; *)
      let open Subst.Binding in
      let { var; term } = c in
      if Term.VarSet.mem var set
      then true
      else (
        match Term.var term with
        | Some var when Term.VarSet.mem var set -> true
        | _ ->
          (* log "%s %d" __FILE__ __LINE__; *)
          false)
   ;;
  end

  type extra = FDC.t

  type subsumes_rez =
    | SuLeft
    | SuRight
    | SuNot
    | SuEqual
  [@@deriving gt ~options:{ fmt }]

  module Disjunct : sig
    type t

    val compare : t -> t -> int
    val pp : Format.formatter -> t -> unit
    val empty : t
    val is_empty : t -> bool
    val singleton : Var.t -> Obj.t -> t

    val of_bindings
      :  Subst.Binding.t list
      -> extra
      -> [ `Meaningful of t * extra | `Violated | `ToRemove of extra ]

    val intersects_with : set:VarSet.t -> t -> bool
    val conj : t -> t -> t

    val recheck_exn
      :  Env.t
      -> Subst.t
      -> bnds:Subst.Binding.t list
      -> extra
      -> t
      -> [ `Meaningful of t * extra | `Violated | `ToRemove of extra ]

    (** returns true if not violated *)
    val shallow_recheck : extra -> t -> bool

    val shallow_recheck_gen : extra -> t -> extra option
    val extract : t -> Term.Var.t -> Obj.t list
    val propagate_to_fdc : t -> extra -> extra option
    val is_violated_rigorously : t -> bool
    val subsumes : t -> t -> subsumes_rez

    (* TODO: remove from interface *)
    val fold_bindings : ('a -> Subst.Binding.t -> 'a) -> 'a -> t -> 'a
    val try_enrich : t -> FDC.t -> Subst.Binding.t list
    val to_seq_without_wcs : t -> Conjunct.t Seq.t
  end = struct
    module LLL = struct
      include Set.Make (Conjunct)

      let append = union
      let any = exists
      let cons = add
      let fold_right = fold
      let fold_left f init set = fold (fun x acc -> f acc x) set init
    end

    type t =
      { conjs : LLL.t
      ; wcs : VarSet.t
      }

    let to_seq_without_wcs { conjs } = LLL.to_seq conjs
    let fold_bindings f init { conjs } = LLL.fold_left f init conjs

    let compare { wcs; conjs } { wcs = wcs2; conjs = conjs2 } =
      let rez_conjs = LLL.compare conjs conjs2 in
      if rez_conjs = 0 then VarSet.compare wcs wcs2 else rez_conjs
    ;;

    let empty = { wcs = VarSet.empty; conjs = LLL.empty }
    let is_empty { conjs; wcs } = LLL.is_empty conjs && VarSet.is_empty wcs

    let subsumes =
      let cmp_wcs l r =
        if VarSet.equal l r
        then SuEqual
        else (
          let u = VarSet.union l r in
          if VarSet.equal u l then SuRight else if VarSet.equal u r then SuLeft else SuNot)
      in
      let cmp_conjs l r =
        if LLL.equal l r
        then SuEqual
        else (
          let u = LLL.union l r in
          if LLL.equal u l then SuRight else if LLL.equal u r then SuLeft else SuNot)
      in
      (*  constraint is a pair of set. One subsumes another that when boths sets are strictly smaller *)
      fun l r ->
        match cmp_wcs l.wcs r.wcs, cmp_conjs l.conjs r.conjs with
        | SuEqual, r -> r
        | r, SuEqual -> r
        | SuLeft, SuLeft -> SuLeft
        | SuRight, SuRight -> SuRight
        | _, _ -> SuNot
    ;;

    let is_violated_rigorously { wcs } =
      (* TODO: assert that wildcard variables didn't get into conjs *)
      not (VarSet.is_empty wcs)
    ;;

    let pp ppf { wcs; conjs } =
      Format.fprintf ppf "[ ";
      LLL.iter (Conjunct.pp ppf) conjs;
      Format.fprintf ppf " ] {| ";
      VarSet.iteri
        (fun i v ->
          match Term.var v with
          | None -> fprintf ppf "..; "
          | Some v -> fprintf ppf "%d; " v.Term.Var.index)
        wcs;
      Format.fprintf ppf "|}"
    ;;

    let conj : t -> t -> t =
     fun l r ->
      match subsumes l r with
      | SuLeft -> l
      | SuRight -> r
      | SuEqual -> l
      | SuNot ->
        { wcs = VarSet.union l.wcs r.wcs; conjs = LLL.append l.conjs r.conjs }
        |> fun ans ->
        (* printf "conj of '%a' and '%a' leads to '%a'\n%!" pp l pp r pp ans; *)
        ans
   ;;

    let intersects_with ~set { conjs } =
      (* TODO: should we check wildcard variables ? *)
      let helper = LLL.any (Conjunct.intersects_with ~set) in
      let ans = helper conjs in
      (* log "Disjunct.intersects_with = %b" ans; *)
      ans
    ;;

    type sort =
      | VarNTerm of Term.Var.t * Obj.t
      | WcNVar of Term.Var.t
      | WcNSmth of Obj.t

    let classify Subst.Binding.{ var; term } =
      (* let () = log "%s %d" __FILE__ __LINE__ in *)
      match Term.var term with
      | None ->
        (* let () = log "%s %d" __FILE__ __LINE__ in *)
        if Term.Var.is_wildcard var
        then WcNSmth term
        else (* let () = log "%s %d" __FILE__ __LINE__ in *)
          VarNTerm (var, term)
      | Some v2 ->
        (* let () = log "%s %d" __FILE__ __LINE__ in *)
        (match Term.Var.(is_wildcard var, is_wildcard v2) with
         | true, true -> failwith "We should not get two wildcards from unification"
         | false, false ->
           (* log "%s %d" __FILE__ __LINE__; *)
           VarNTerm (var, term)
         | false, true -> WcNVar var
         | true, false -> WcNVar v2)
    ;;

    let singleton : Term.Var.t -> _ -> t =
     fun var term ->
      let b = Subst.Binding.{ var; term } in
      match classify b with
      | WcNVar var -> { empty with wcs = VarSet.singleton var }
      | WcNSmth term -> failwith "weird stuff"
      (* { empty with conjs = LLL.singleton } *)
      | VarNTerm (var, term) -> { empty with conjs = LLL.singleton b }
   ;;

    (* if is_wc_var var && is_var term
      then { conjs = LLL.empty; wcs = VarSet.(add !!!term empty) }
      else if is_wc_var term && is_var var
      then { conjs = LLL.empty; wcs = VarSet.(add !!!var empty) }
      else { conjs = LLL.singleton Subst.Binding.{ var; term }; wcs = VarSet.empty } *)

    (**
      Converts bindings and FD constraints to a conjunction of inequalities.
      During this construction all sensible FD constraints are propagated to FD ones.
      And if something fails, the fold is being interrupted.
    **)

    (* Old implementation with DNF *)
    (*
    let of_bindings bnds extra0 =
      (* assert ([] <> bnds); *)
      (* let exception ToRemove in *)
      match bnds with
      | [] -> `ToRemove extra0
      | _ ->
        (try
           let next =
             Stdlib.List.fold_left
               (fun ({ wcs; conjs }, extra) bnd ->
                 (* log "%d %a" __LINE__ Subst.pp_binding_list [ bnd ]; *)
                 match classify bnd with
                 | WcNVar var when FDC.is_interesting_var var extra ->
                   (* log "is interesting"; *)
                   { wcs = VarSet.add var wcs; conjs }, extra
                 | WcNVar var -> { conjs; wcs = VarSet.add var wcs }, extra
                 | WcNSmth term ->
                   (* log "WcNSmth"; *)
                   { wcs; conjs }, extra
                 | VarNTerm (var, term) ->
                   (* log "VarNTerm"; *)
                   (* need to check finite domain constraints too *)
                   if FDC.is_interesting_var var extra
                   then (
                     match FDC.neq (Obj.magic var) (Obj.magic term) extra with
                     | None -> raise Violated
                     | Some e ->
                       let __ _ =
                         log
                           "Successfully added new  FD constraint %s=/=%s"
                           (Term.show !!!var)
                           (Term.show term)
                       in
                       { conjs = LLL.cons Subst.Binding.{ var; term } conjs; wcs }, e)
                   else { conjs = LLL.cons Subst.Binding.{ var; term } conjs; wcs }, extra)
               (empty, extra0)
               bnds
           in
           (* TODO: it could be more efficient to perform a fold, and check FD constraints
              only in the end *)
           `Meaningful next
         with
         (* | ToRemove -> Stdlib.Result.error `ToRemove *)
         | Violated ->
           log "Disjunct.of_bindings said Violated";
           `Violated)
    ;;*)

    (* Implementation for CNF *)
    let of_bindings bnds extra0 =
      (* assert ([] <> bnds); *)
      (* let exception ToRemove in *)
      match bnds with
      | [] -> `ToRemove extra0
      | _ ->
        (try
           let next, extra =
             Stdlib.List.fold_left
               (fun (({ wcs; conjs }, extra) as acc) bnd ->
                 (* log "%d %a" __LINE__ Subst.pp_binding_list [ bnd ]; *)
                 match classify bnd with
                 | WcNVar var ->
                   (* wildcards and fresh variables are always unifieable and can't give an inequality *)
                   acc
                 | WcNSmth term ->
                   (* the same for wildcard and term *)
                   acc
                 | VarNTerm (var, term) ->
                   (* We are not going to think about finite domain constraints here *)
                   { conjs = LLL.cons Subst.Binding.{ var; term } conjs; wcs }, extra)
               (empty, extra0)
               bnds
           in
           if is_empty next then raise Violated else `Meaningful (next, extra)
         with
         (* | ToRemove -> Stdlib.Result.error `ToRemove *)
         | Violated ->
           log "Disjunct.of_bindings said Violated";
           `Violated)
    ;;

    (** Check that every disequality doesn't violate by itself extra constraints
        TODO: Check another half of the constraint of `interesting` variable too.
      *)
    let shallow_recheck_gen extra { conjs; _ } =
      LLL.fold
        (fun conj acc ->
          (* printf "conj = %a\n" Conjunct.pp conj; *)
          match acc with
          | None -> None
          | Some extra ->
            (* TODO: check another part if it is a variable.
               To add more types we should replace (var*term) by
              (`TwoVars of var*var | `VarTerm of var*term )
            *)
            if FDC.is_interesting_var Subst.Binding.(conj.var) extra
            then
              (* let () = printf "conj = %a is interesting\n " Conjunct.pp conj in *)
              FDC.neq
                (Obj.magic Subst.Binding.(conj.var))
                (Obj.magic Subst.Binding.(conj.term))
                extra
            else acc)
        conjs
        (Some extra)
    ;;

    let shallow_recheck extra t =
      match shallow_recheck_gen extra t with
      | None -> false
      | Some _ -> true
    ;;

    (**

      *)
    let recheck_exn env subst ~bnds extra ({ wcs; conjs = pairs } as d) =
      log "Disjunct.recheck_exn of %a" pp d;
      let exception Early_exit of FDC.t in
      try
        (* In fresh bindings we should not concretize variables from 'wcs'*)
        let new_wcs =
          VarSet.map
            (fun v ->
              let v = Subst.apply env subst v in
              if Term.is_var v
              then Obj.magic v
              else (* Wildcards =/= ground term => violation *)
                raise Violated)
            wcs
        in
        (* bnds
        |> List.iter (fun Subst.Binding.{ var; term } ->
               (* TODO: check term too; *)
               if VarSet.mem var wcs then raise Violated;
               ()); *)
        let new_pairs, new_wcs =
          LLL.fold_left
            (fun ((pairs, wcs) as acc) { Subst.Binding.var; term } ->
              let t1 = Subst.apply env subst var in
              let t2 = Subst.apply env subst term in
              match Subst.unify env subst (Obj.repr t1) (Obj.repr t2) with
              | None -> raise (Early_exit extra)
              | Some ([], _) -> acc
              | Some (bnds, _) ->
                List.fold_left
                  (fun (pairs, wcs) bnd ->
                    match classify bnd with
                    | VarNTerm (var, term) -> LLL.add Subst.Binding.{ var; term } pairs, wcs
                    | WcNVar v -> pairs, VarSet.add v wcs
                    | WcNSmth term -> raise Violated)
                  acc
                  bnds)
            (LLL.empty, new_wcs)
            pairs
        in
        if LLL.is_empty new_pairs (* && VarSet.is_empty new_wcs *)
        then raise Violated
        else
          (* We beleive that fresh variables always inequal to wilcards, so we ignore them *)
          `Meaningful ({ wcs = VarSet.empty; conjs = new_pairs }, extra)
        (*

        (* Every conjunct could blowup to many coinjuncts because of recent unifications,
           so we need two Seq's here *)
        let conjs : LLL.elt Seq.t Seq.t =
          Seq.map
            (fun { Subst.Binding.var; term } ->
              log "In current subst var is '%a'" Term.pp (Subst.reify env subst var);
              match Subst.unify env subst (Obj.repr var) (Obj.repr term) with
              | None ->
                log "%s %d" __FILE__ __LINE__;
                Seq.empty
              | Some ([], _) ->
                log "%s %d" __FILE__ __LINE__;
                raise Violated
              | Some (bnds, _) ->
                log "%s %d" __FILE__ __LINE__;
                log "bnds = %a" Subst.pp_binding_list bnds;
                log
                  "lefting as is: %s =/= %s"
                  (Term.show @@ Obj.repr var)
                  (Term.show @@ Obj.repr term);
                (* TODO: what if we would rewrite a disjunct here ??? *)
                List.to_seq bnds)
            (LLL.to_seq conjs)
        in
        let new_diseqs =
          (* A single disjunct has blown up to a pack of disequlity pairs, so we effectively have
             a disjunction of conjuctions. It should be filtered out:
              * some may fail; if all fail the disjuncts are violated
              * if one is empty, then everything could be thrown away
            *)
          let multiplied = CartesianHacks.cartesian_seq conjs |> List.of_seq in
          log "Mulitiplied disjuncts length = %d" (List.length multiplied);
          List.filter_map
            (fun conjs ->
              match of_bindings (List.of_seq conjs) extra with
              | `Violated ->
                log "%d" __LINE__;
                None
              | `ToRemove e ->
                log "%d" __LINE__;
                raise (Early_exit e)
              | `Meaningful (sub_disjunct, extra) ->
                log "%d" __LINE__;
                let sub_disjunct = { sub_disjunct with wcs = VarSet.union wcs sub_disjunct.wcs } in
                if is_empty sub_disjunct
                then raise (Early_exit extra)
                else if shallow_recheck extra sub_disjunct
                then Some sub_disjunct
                else None)
            multiplied
        in
        (* assert (not (is_empty new_diseqs)); *)
        (* printf "There are %d new disjuncts\n%!" (List.length new_diseqs); *)
        (* let () =
          ListLabels.iter new_diseqs ~f:(fun d ->
              if is_empty d then failwith "Empty disjuncts should be filtered out")
        in *)
        match new_diseqs with
        | _ :: _ -> `Meaningful (new_diseqs, extra)
        | [] -> `Violated
        *)
      with
      | Violated ->
        log "Disjunct.recheck_exn said Violated";
        `Violated
      | Early_exit e -> `ToRemove e
    ;;

    let propagate_to_fdc cstr extra = shallow_recheck_gen extra cstr

    let extract { conjs } v =
      let helper acc xs =
        LLL.fold_left
          (fun acc { Subst.Binding.var; Subst.Binding.term } ->
            let acc = if Term.Var.equal var v then term :: acc else acc in
            let acc =
              match Term.var term with
              | Some v2 when Term.Var.equal v v2 -> Obj.repr var :: acc
              | _ -> acc
            in
            acc)
          acc
          xs
      in
      helper [] conjs
    ;;

    let try_enrich t extra : Subst.Binding.t list =
      let new_bindings =
        fold_bindings
          (fun acc (Subst.Binding.{ var; term } as b) ->
            let dom = FDC.get_domain_size var extra in
            match Term.is_var term, dom with
            | false, Some [ v1; v2 ] ->
              let next_val = if Obj.repr v1 = Obj.repr term then v2 else v1 in
              (* printf "Found a candidate for simplifying: %a to be %d\n" Term.pp (Obj.magic var) next_val; *)
              { b with term = Obj.magic next_val } :: acc
            | _ -> acc)
          []
          t
      in
      new_bindings
    ;;
  end

  module DisjSet = struct
    include Set.Make (Disjunct)

    let iteri f xs =
      let i = ref 0 in
      iter
        (fun x ->
          f !i x;
          incr i)
        xs
    ;;

    let fold_left f init xs = fold (fun x acc -> f acc x) xs init

    let fold_left_i f init xs =
      let n = ref (-1) in
      fold
        (fun x acc ->
          incr n;
          f !n acc x)
        xs
        init
    ;;

    let pp ppf xs =
      printf "The CNF (%d)\n%!" (cardinal xs);
      iteri (fun i -> fprintf ppf "\t%d: %a\n%!" i Disjunct.pp) xs
    ;;

    let dedup set =
      let add set x =
        fold_left
          (fun (flg, acc) eset ->
            match Disjunct.subsumes x eset with
            | SuLeft -> flg, acc
            | SuEqual | SuRight -> false, add eset acc
            | SuNot -> flg, add eset acc)
          (true, empty)
          set
        |> function
        | true, set -> add x set
        | false, set -> set
      in
      fold_left add empty set
    ;;

    let union l r =
      (* printf "%s %d \n%!" __FILE__ __LINE__; *)
      let add set x =
        fold_left
          (fun (flg, acc) eset ->
            match Disjunct.subsumes x eset with
            | SuLeft -> flg, acc
            | SuEqual | SuRight -> false, add eset acc
            | SuNot -> flg, add eset acc)
          (true, empty)
          set
        |> function
        | true, set -> add x set
        | false, set -> set
      in
      let ans = fold_left add l r in
      (* printf "DisjSet.union of '%a' and '%a'\nleads to '%a'\n%!" pp l pp r pp ans ; *)
      ans
    ;;

    let union_with_list ~set xs = List.fold_left (fun acc x -> union acc (singleton x)) set xs
    let concat_map f xs = fold (fun x acc -> union (f x) acc) xs empty

    let of_seq_without_duplicates s =
      (* TODO: finish implementation *)
      let add set x =
        fold_left
          (fun (flg, acc) eset ->
            match Disjunct.subsumes x eset with
            | SuLeft -> flg, acc
            | SuEqual | SuRight -> false, add eset acc
            | SuNot -> flg, add eset acc)
          (true, empty)
          set
        |> function
        | true, set -> add x set
        | false, set -> set
      in
      Seq.fold_left add empty s
    ;;
  end

  type t = DisjSet.t

  let pp = DisjSet.pp
  let empty : t = DisjSet.empty
  let is_empty = DisjSet.is_empty
  let disj : t -> t -> t = DisjSet.union

  let conj : t -> t -> t =
   fun l r ->
    (* printf "Disjunct.conj '%a' and '%a'\n" pp l pp r; *)
    l
    |> DisjSet.concat_map (fun (c1 : Disjunct.t) ->
         DisjSet.map (fun (c2 : Disjunct.t) -> Disjunct.conj c1 c2) r (* |> DisjSet.dedup *))
 ;;

  let disequality_of_terms l r : t =
    try
      Term.fold_monoid
        l
        r
        ~fvar:(fun v t -> DisjSet.singleton (Disjunct.singleton v (Obj.magic t)))
        ~fk:(fun _ v t -> DisjSet.singleton (Disjunct.singleton v (Obj.magic t)))
        ~empty:DisjSet.empty
        ~fval:(fun v1 v2 ->
          (* two non-boxed values that are not equal *)
          DisjSet.empty)
        ~join:DisjSet.union
    with
    | Term.Different_shape (_, _) -> DisjSet.empty
  ;;

  let ( >>=? ) : 'a 'b. 'a option -> ('a -> 'b option) -> 'b option = Stdlib.Option.bind

  let of_bindings : Subst.Binding.t list -> extra -> (t * extra) option =
   fun xs e ->
    try
      List.fold_left
        (fun (acc, e) b ->
          match Disjunct.of_bindings [ b ] e with
          | `Violated -> raise Violated
          | `Meaningful (d, e) -> DisjSet.add d acc, e
          | `ToRemove e -> acc, e)
        (DisjSet.empty, e)
        xs
      |> Stdlib.Option.some
    with
    | Violated -> None
 ;;

  let debug_enriching_subst t extra =
    (* we do something only we have single disjunct *)
    if DisjSet.cardinal t <> 1
    then ()
    else (
      let _new_ones =
        Disjunct.try_enrich (DisjSet.min_elt t) extra
        (* |> Disjunct.fold_bindings
        (fun acc Subst.Binding.{var; term} ->
          let dom = FDC.get_domain_size var extra in
          let () =
            match (Term.is_var term), dom with
            | false, Some [v1; v2] ->
              let next_val = if Obj.repr v1 = Obj.repr term then v2 else v1 in
              printf "Found a candidate for simplifying: %a to be %d\n" Term.pp (Obj.magic var) next_val
            | _ -> ()
          in
          acc
        ) [] *)
      in
      ())
  ;;

  let add env subst cstrs l r extra =
    log "add: '%a' and '%a' on  %s %d" Term.pp (Obj.repr l) Term.pp (Obj.repr r) __FILE__ __LINE__;
    match Subst.unify env subst l r with
    | None -> Some (cstrs, extra)
    | Some ([], _) -> None
    | Some (bnds, _subst) ->
      (* In CNF mode, if we get a binding that something is not equal wildcard, it could be immediately removed. *)
      log "%d %a" __LINE__ Subst.pp_binding_list bnds;
      (match Disjunct.of_bindings bnds extra with
       | `Violated -> None
       | `Meaningful (d, e) -> Some (DisjSet.add d cstrs, e)
       | `ToRemove e -> Some (cstrs, e))
  ;;

  (** Rechecking takes contraints ans output
    + Some .. if they are not yet violated
    + None if violated
    *)
  let recheck env subst cs (bnds : Subst.Binding.t list) extra =
    log "Disequality2.recheck";
    log "bindings = %d %a" __LINE__ Subst.pp_binding_list bnds;
    log "%a" pp cs;
    let exception Early_exit of FDC.t in
    (* We have a disjunction of conjuctions of pairs.
      For every conjunct we try to simplify it using [bnds].
      - If it simplifies to empty conjunct, then we simplify it to False (abandone it). ???
        - If all disjuncts has been simpifies to False, then constraint is violated
      - It if is always not equal, then all disjunction could be simplified to True
      - Conjunct could
     *)
    let simplify store =
      DisjSet.fold_left_i
        (fun i (extra, acc) d ->
          match Disjunct.recheck_exn env subst ~bnds extra d with
          | `Violated | (exception Violated) ->
            (* TODO: no model doesn't necessary mean violated *)
            log "rechecking disjunct %d '%a' failed %d" i Disjunct.pp d __LINE__;
            (* In CNF mode it means global failure, in DNF -- simplification *)
            (* extra, acc *)
            raise Violated
          | `ToRemove e ->
            log "Disjunct removed: %a" Disjunct.pp d;
            extra, acc (* raise (Early_exit e) *)
          | `Meaningful (d, extra) ->
            (* We have an updated disjunct *)
            let dset = DisjSet.add d acc in
            log "Updated disjunct %s %d: %a" __FILE__ __LINE__ pp dset;
            extra, dset)
        (extra, DisjSet.empty)
        store
      |> snd
    in
    let answer ?(bnds = []) newc extra = Some (newc, extra, bnds) in
    try
      let newc = simplify cs in
      let card = DisjSet.cardinal newc in
      let () = log "recheck successful with card=%d on line  %d" card __LINE__ in
      let __ () =
        log "New FDC constraints:";
        FDC.trace extra
      in
      match card with
      (* | 1 ->
        let disjunct = DisjSet.min_elt newc in
        (match Disjunct.shallow_recheck_gen extra disjunct with
        | None -> raise Violated
        | Some extra ->
          (match Disjunct.try_enrich disjunct extra with
          | [] -> answer newc extra
          | new_bindings -> answer newc extra ~bnds:new_bindings)) *)
      | _ ->
        let __ () =
          print_endline "shallow_recheck_gen is not applicable ";
          Format.printf "%a\n%!" pp newc
        in
        answer newc extra
    with
    | Early_exit e -> Some (DisjSet.empty, e, [])
    | Violated ->
      log "got exception Violated %s %d" __FILE__ __LINE__;
      None
  ;;

  let cut_off_wc_without_domain : t -> t option =
   fun store ->
    (* TODO *)
    if DisjSet.is_empty store
    then Some store
    else (
      let new_store = DisjSet.filter (fun d -> not (Disjunct.is_violated_rigorously d)) store in
      if DisjSet.is_empty new_store then None else Stdlib.Option.some store)
 ;;

  let merge_disjoint _ = failwith "merge_disjoint is not implemented"

  module Var_multi_map (El : sig
    include Map.OrderedType

    val pp : Format.formatter -> t -> unit
  end) =
  struct
    module El_set = struct
      include Set.Make (El)

      let subset ~small big = subset small big

      let pp ppf set =
        Format.fprintf ppf "[ ";
        iter (El.pp ppf) set;
        Format.fprintf ppf " ]"
      ;;
    end

    type t = El_set.t Term.VarMap.t

    let empty : t = Term.VarMap.empty

    let add key v mapa =
      match Term.VarMap.find key mapa with
      | xs -> Term.VarMap.add key (El_set.add v xs) mapa
      | exception Not_found -> Term.VarMap.add key (El_set.singleton v) mapa
    ;;

    let merge = Term.VarMap.merge
    let find_and_to_list_exn key mapa = Term.VarMap.find key mapa |> El_set.to_seq |> List.of_seq

    let pp ppf x =
      Format.fprintf ppf "{vmm| ";
      Term.VarMap.iter (fun k v -> Format.fprintf ppf "%d -> %a; " k.Var.index El_set.pp v) x;
      Format.fprintf ppf "|vmm}"
    ;;
  end

  module Answer = struct
    module M = Var_multi_map (struct
      type t = Term.t

      let compare l r = compare (Obj.repr l) (Obj.repr r)
      let pp = Term.pp
    end)

    type t = M.t (*  conjunction of inequalites *)

    let empty = M.empty

    let extract (map : t) v =
      (* Format.printf "Extracting from %a\n%!" Disjunct.pp d; *)
      try M.find_and_to_list_exn v map with
      | Not_found -> []
    ;;

    (* The logic about checking subsumption is kind of tricky *)
    let subsumed _env c1 (c2 as _by) =
      log "subsumed of \nleft: %a\n  by: %a\n" M.pp c1 M.pp c2;
      (* if A has strictly more constraints then B, then A could be removed *)
      let exception No_subsumption in
      try
        let _ =
          M.merge
            (fun acc left right ->
              match left, right with
              | None, None -> failwith "Should not happen"
              | None, Some _ -> raise No_subsumption
              | Some _, None -> None
              | Some l, Some r -> if M.El_set.subset ~small:l r then None else raise No_subsumption)
            c1
            c2
        in
        true
      with
      | No_subsumption -> false
    ;;
  end

  let vars_in_term =
    let rec helper acc x =
      if Obj.is_block x
      then (
        match Term.var x with
        | Some v -> Term.VarSet.add v acc
        | None when Obj.(tag x = string_tag) -> acc
        | None ->
          let sz = Obj.size x in
          let rec inner acc i =
            if i >= sz then acc else inner (helper acc (Obj.field x i)) (1 + i)
          in
          inner acc 0)
      else acc
    in
    fun root -> helper Term.VarSet.empty (Obj.repr root)
  ;;

  let reify env subst cs t : Answer.t list =
    log "reify: %s %d" __FILE__ __LINE__;
    log "constraints: %a" pp cs;
    (* Format.printf "all : %a\n%!" pp cs; *)
    let t = Subst.reify env subst t in
    let vars = vars_in_term t in
    let dnf =
      CartesianHacks.cartesian_seq (DisjSet.to_seq cs |> Seq.map Disjunct.to_seq_without_wcs)
    in
    let maybe_add k v acc = if VarSet.mem k vars then Answer.M.add k v acc else acc in
    let ll_dnf = Seq.map List.of_seq dnf |> List.of_seq in
    log "ll_dng = %a" (GT.fmt GT.list (GT.fmt GT.list Conjunct.pp)) ll_dnf;
    let add_to_list newx xs =
      log "add_to_list hERR";
      let exception Early_exit of Answer.t list in
      try
        List.fold_left
          (fun acc e ->
            if Answer.subsumed () newx e
            then raise (Early_exit xs)
            else if Answer.subsumed () e newx
            then acc
            else e :: acc)
          [ newx ]
          xs
      with
      | Early_exit xs -> xs
    in
    let check_subsumptions = false in
    Seq.map
      (Seq.fold_left
         (fun acc { Subst.Binding.var; term } ->
           let term = Subst.apply env subst term in
           let acc = maybe_add var term acc in
           match Term.var term with
           | None -> acc
           | Some v2 -> maybe_add v2 (Obj.repr var) acc)
         Answer.empty)
      dnf
    |> fun pre_answer ->
    if check_subsumptions
    then Seq.fold_left (fun acc x -> add_to_list x acc) [] pre_answer
    else List.of_seq pre_answer
  ;;

  let project _ _ = failwith "not implemented"
end

(** *******************  tests ***************************  *)
module _ = struct
  module FD_dummy = struct
    type t

    let neq _ _ _ = assert false
    let is_interesting_var _ _ = assert false
    let trace _ = ()

    (* let cut_off_wc_without_domain t = Option.some t *)
    let get_domain_size _ _ = None
  end

  open Make (FD_dummy)

  let make_var i = Obj.magic (Term.Var.make ~env:0 ~scope:Term.Var.non_local_scope i)

  let%expect_test _ =
    let v1 = make_var 1 in
    Format.printf "%a" pp (disequality_of_terms v1 v1);
    [%expect {xxx|
      The CNF (1)
      	0: [ { _.1 <> '_.1' } ] {| |}
    |xxx}]
  ;;

  let%expect_test _ =
    let v1 = make_var 1 in
    let v2 = make_var 2 in
    Format.printf "%a" pp (disequality_of_terms !!!(1, 2) !!!(v1, v2));
    [%expect
      {xxx|
      The CNF (2)
      	0: [ { _.1 <> 'int<1>' } ] {| |}
      	1: [ { _.2 <> 'int<2>' } ] {| |}
    |xxx}]
  ;;

  let%expect_test _ =
    let v1 = make_var 1 in
    let v2 = make_var 2 in
    Format.printf "%a" pp (disequality_of_terms !!!(1, v1) !!!(2, v2));
    [%expect {xxx|
      The CNF (1)
      	0: [ { _.1 <> '_.2' } ] {| |}
    |xxx}]
  ;;

  let%expect_test _ =
    let v1 = make_var 1 in
    let v2 = make_var 2 in
    Format.printf "%a" pp (disequality_of_terms !!!(1, v1) !!!(2, v2));
    [%expect {xxx|
      The CNF (1)
      	0: [ { _.1 <> '_.2' } ] {| |}
    |xxx}]
  ;;

  let%expect_test _ =
    let v1 = make_var 1 in
    let v2 = make_var 2 in
    let v3 = make_var 3 in
    let v4 = make_var 4 in
    let d1 = disequality_of_terms !!!(1, 2) !!!(v1, v2) in
    Format.printf "%a\n" pp d1;
    let d2 = disequality_of_terms !!!(3, 4) !!!(v3, v4) in
    Format.printf "%a\n" pp d2;
    let d3 = conj d1 d2 in
    Format.printf "%a" pp d3;
    [%expect
      {xxx|
      The CNF (2)
      	0: [ { _.1 <> 'int<1>' } ] {| |}
      	1: [ { _.2 <> 'int<2>' } ] {| |}

      The CNF (2)
      	0: [ { _.3 <> 'int<3>' } ] {| |}
      	1: [ { _.4 <> 'int<4>' } ] {| |}

      The CNF (4)
      	0: [ { _.1 <> 'int<1>' }{ _.3 <> 'int<3>' } ] {| |}
      	1: [ { _.1 <> 'int<1>' }{ _.4 <> 'int<4>' } ] {| |}
      	2: [ { _.2 <> 'int<2>' }{ _.3 <> 'int<3>' } ] {| |}
      	3: [ { _.2 <> 'int<2>' }{ _.4 <> 'int<4>' } ] {| |}
    |xxx}]
  ;;

  let%expect_test "Removing duplicated disjuncts 1" =
    let v1 = make_var 1 in
    let v2 = make_var 2 in
    let v3 = make_var 3 in
    let v4 = make_var 4 in
    let d1 = disequality_of_terms !!!v1 !!!v2 in
    Format.printf "%a\n" pp d1;
    let d2 = disequality_of_terms !!!(v1, v3) !!!(v2, v4) in
    Format.printf "%a\n" pp d2;
    let d3 = conj d1 d2 in
    Format.printf "%a" pp d3;
    [%expect
      {xxx|
        The CNF (1)
        	0: [ { _.1 <> '_.2' } ] {| |}

        The CNF (2)
        	0: [ { _.1 <> '_.2' } ] {| |}
        	1: [ { _.3 <> '_.4' } ] {| |}

        The CNF (2)
        	0: [ { _.1 <> '_.2' } ] {| |}
        	1: [ { _.1 <> '_.2' }{ _.3 <> '_.4' } ] {| |}

    |xxx}]
  ;;
  (* assert (DisjSet.cardinal d1 = 1);
    assert (DisjSet.cardinal d2 = 2);
    let u = DisjSet.min_elt d3 in
    let v = DisjSet.max_elt d3 in
    Format.printf "u = %a\n%!" Disjunct.pp u;
    Format.printf "v = %a\n%!" Disjunct.pp v;
    printf "%a" (GT.fmt subsumes_rez) (Disjunct.subsumes u  v);
    [%expect
      {xxx|

    |xxx}] *)
end
