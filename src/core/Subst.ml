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

[%%if not_defined_permissive stats]
[%%else]

type stat = {mutable walk_count : int}

let stat = {walk_count = 0}

let walk_counter () = stat.walk_count
let walk_incr () = stat.walk_count <- stat.walk_count + 1

[%%endif]

(* to avoid clash with Std.List (i.e. logic list) *)
module List = Stdlib.List

module Binding =
  struct
    type t =
      { var   : Term.Var.t
      ; term  : Term.t
      }

    let is_relevant env vs {var; term} =
      (Term.VarSet.mem var vs) ||
      (match Env.var env term with Some v -> Term.VarSet.mem v vs | None -> false)

    let equal {var=v; term=t} {var=u; term=p} =
      (Term.Var.equal v u) || (Term.equal t p)

    let compare {var=v; term=t} {var=u; term=p} =
      let res = Term.Var.compare v u in
      if res <> 0 then res else Term.compare t p

    let hash {var; term} = Hashtbl.hash (Term.Var.hash var, Term.hash term)

    let pp ppf {var; term} =
      Format.fprintf ppf "{ var.idx = %d; term=%s }" var.Term.Var.index (Term.show term)
  end

let varmap_of_bindings : Binding.t list -> Term.t Term.VarMap.t =
  Stdlib.List.fold_left (fun (acc: _ Term.VarMap.t) Binding.{var;term}    ->
    assert (not (Term.VarMap.mem var acc));
    Term.VarMap.add var term acc
  )
  Term.VarMap.empty

type t = Term.t Term.VarMap.t
type subst = t

let empty = Term.VarMap.empty

let pp ppf (s: t) =
  Format.fprintf ppf "{subst| ";
  Term.VarMap.iter (fun var term -> Format.fprintf ppf "%a |- %a; " Term.pp (Obj.repr var) Term.pp term) s;
  Format.fprintf ppf "|subst}"


let of_list =
  ListLabels.fold_left ~init:empty ~f:(let open Binding in fun subst {var; term} ->
    if not @@ Term.VarMap.mem var subst then
      Term.VarMap.add var term subst
    else
      invalid_arg "OCanren fatal (Subst.of_list): invalid substituion"
  )

let of_map m = m

let split s = Term.VarMap.fold (fun var term xs -> Binding.({var; term})::xs) s []

type lterm = Var of Term.Var.t | Value of Term.t | WC of Term.Var.t

let walk env subst x =
  (* walk var *)
  let rec walkv env subst v =
    let module _ = struct
      [%%if not_defined_permissive stats]
      [%% else]
      let () = walk_incr ()
      [%%endif]
    end in
    Env.check_exn env v;
    if Term.Var.is_wildcard v
    then WC v
    else match v.Term.Var.subst with
    | Some term -> walkt env subst (Obj.magic term)
    | None ->
        try walkt env subst (Term.VarMap.find v subst)
        with Not_found -> Var v
  (* walk term *)
  and walkt env subst t =
    let module _ = struct
      [%%if not_defined_permissive stats]
      [%% else]
      let () = walk_incr ()
      [%%endif]
    end in
    match Env.var env t with
    | Some v when Term.Var.is_wildcard v -> WC v
    | Some v -> walkv env subst v
    | None   -> Value t
  in
  walkv env subst x

(* same as [Term.map] but performs [walk] on the road *)
let map ~fvar ~fval env subst x =
  let rec deepfvar v =
    Env.check_exn env v;
    match walk env subst v with
    | WC v
    | Var v   -> fvar v
    | Value x -> Term.map x ~fval ~fvar:deepfvar
  in
  Term.map x ~fval ~fvar:deepfvar

(* same as [Term.iter] but performs [walk] on the road *)
let iter ~fvar ~fval env subst x =
  let rec deepfvar v =
    Env.check_exn env v;
    match walk env subst v with
    | WC v
    | Var v   -> fvar v
    | Value x -> Term.iter x ~fval ~fvar:deepfvar
  in
  Term.iter x ~fval ~fvar:deepfvar

(* same as [Term.fold] but performs [walk] on the road *)
let fold ~fvar ~fval ~init env subst x =
  let rec deepfvar acc v =
    Env.check_exn env v;
    match walk env subst v with
    | WC v
    | Var v   -> fvar acc v
    | Value x -> Term.fold x ~fval ~fvar:deepfvar ~init:acc
  in
  Term.fold x ~init ~fval ~fvar:deepfvar

exception Occurs_check

let rec occurs env subst var term =
  iter env subst term
    ~fvar:(fun v -> if Term.Var.equal v var then raise Occurs_check)
    ~fval:(fun x -> ())

let extend ?(skip_occurs=false) ~scope env subst var term  =
  (* if occurs env subst var term then raise Occurs_check *)
  (* if Runconf.do_occurs_check () then occurs env subst var term; *)
    (* assert (VarEnv.var env var <> VarEnv.var env term); *)
  if not skip_occurs
  then occurs env subst var term;

  (* It is safe to modify variables destructively if the case of scopes match.
   * There are two cases:
   * 1) If we do unification just after a conde, then the scope is already incremented and nothing goes into
   *    the fresh variables.
   * 2) If we do unification after a fresh, then in case of failure it doesn't matter if
   *    the variable is be distructively substituted: we will not look on it in future.
   *)
  (* if (scope = var.Term.Var.scope) && (scope <> Term.Var.non_local_scope)
  then begin
    var.subst <- Some (Obj.repr term);
    subst
  end
    else *)
      Term.VarMap.add var (Term.repr term) subst

exception Unification_failed

let log fmt =
  if false
  then Format.kasprintf (Format.printf "%s\n%!") fmt
  else Format.ifprintf Format.std_formatter fmt

let unify ?(subsume=false) ?(scope=Term.Var.non_local_scope) env subst x y =
  (* The idea is to do the unification and collect the unification prefix during the process *)
  let extend var term (prefix, subst) =
    let subst = extend ~scope env subst var term in
    (Binding.({var; term})::prefix, subst)
  in
  let rec helper x y acc =
    (* log "unify '%s' and '%s'" (Term.show x) (Term.show y); *)
    let open Term in
    fold2 x y ~init:acc
      ~fvar:(fun ((_, subst) as acc) x y ->
        match walk env subst x, walk env subst y with
        | WC _, WC _ ->
          (* TODO(Kakadu): explain why we return substitution as is *)
          acc
        | Var z, WC v | WC v, Var z -> extend (Obj.magic v) (Obj.repr z) acc
        | Value z, WC v | WC v, Value z -> extend (Obj.magic v) (Obj.repr z) acc
        | Var x, Var y      ->
          (* if Var.equal x y then acc else extend x (Term.repr y) acc *)
         let cmp = Term.Var.compare x y in
          if cmp < 0 then extend x (Term.repr y) acc
          else if cmp > 0 then extend y (Term.repr x) acc
          else acc
          | Var x, Value y    -> extend x y acc
        | Value x, Var y    -> extend y x acc
        | Value x, Value y  -> helper x y acc
      )
      ~fval:(fun acc x y ->
          if x = y then acc else raise Unification_failed
      )
      ~fk:(fun ((_, subst) as acc) l v y ->
          if Term.Var.is_wildcard v
          then acc
          else if subsume && (l = Term.R)
          then raise Unification_failed
          else match walk env subst v with
          | Var v    -> extend v y acc
          | Value x  -> helper x y acc
          | WC _ -> failwith "Wildcards should not appear in unifications"
      )
  in
  try
    let x, y = Term.(repr x, repr y) in
    Some (helper x y ([], subst))
  with Term.Different_shape _ | Unification_failed | Occurs_check -> None

let apply env subst x = Obj.magic @@
  map env subst (Term.repr x)
    ~fvar:(fun v -> Term.repr v)
    ~fval:(fun x -> Term.repr x)

let unify_map env subst map =
  let vars, terms =
    Term.VarMap.fold (fun v term acc -> (v :: fst acc, term :: snd acc)) map ([],[])
  in
  (* log "var   = %s" (Term.show (Obj.magic (apply env subst vars))); *)
  (* log "terms = %s" (Term.show (Obj.magic (apply env subst terms))); *)
  unify env subst (Obj.magic vars) (Obj.magic terms)


let freevars env subst x =
  Env.freevars env @@ apply env subst x

let is_bound = Term.VarMap.mem

let merge env subst1 subst2 = Term.VarMap.fold (fun var term -> function
  | Some s  -> begin
    match unify env s (Obj.magic var) term with
    | Some (_, s') -> Some s'
    | None         -> None
    end
  | None    -> None
) subst1 (Some subst2)

let merge_disjoint env =
  Term.VarMap.union (fun _ _ ->
    invalid_arg "OCanren fatal (Subst.merge_disjoint): substitutions intersect"
  )

let subsumed env subst =
  Term.VarMap.for_all (fun var term ->
    match unify env subst (Obj.magic var) term with
    | Some ([], _)  -> true
    | _             -> false
  )

module Answer =
  struct
    type t = Term.t

    let subsumed env x y =
      match unify ~subsume:true env empty y x with
      | Some _ -> true
      | None   -> false
  end

let reify env subst x =
  map env subst (Term.repr x)
    ~fvar:(fun v -> Term.repr v)
    ~fval:(fun x -> Term.repr x)


let walk_rational _visited_vars env subst x: _ * _ =
  let rec walkv vis env subst v =
    log "%s %d, vis.size = %d, v = %a" __FUNCTION__ __LINE__ (Term.VarSet.cardinal vis) Term.pp v;
    Env.check_exn env v;
    if Term.Var.is_wildcard v
    then (vis, WC v)
    else if Term.VarSet.mem v vis then (vis, Var v)
    else match v.Term.Var.subst with
    | Some term ->
        let vis = Term.VarSet.add v vis in
        walkt vis env subst (Obj.magic term)
    | None ->
        if Term.VarSet.mem v vis then vis, Var v
        else
        (let vis = Term.VarSet.add v vis in
        log "Mark var %a as visited" Term.pp v;
        try walkt vis env subst (Term.VarMap.find v subst)
        with Not_found -> vis, Var v)
  (* walk term *)
  and walkt vis env subst t : _*_ =
    log "%s %d, vis.size = %d" __FUNCTION__ __LINE__ (Term.VarSet.cardinal vis);
    match Env.var env t with
    | Some v when Term.Var.is_wildcard v -> vis, WC v
    | Some v when Term.VarSet.mem v vis ->
        vis, Var v
    | Some v ->
      log "%s %d" __FUNCTION__ __LINE__;
      walkv vis env subst v
    | None   -> vis, Value t
  in
  walkv _visited_vars env subst x

let reify_rational env subst x : Answer.t =
  log "\t%s %d, x = %a" __FUNCTION__ __LINE__ Term.pp x;
  (* visited_vars := Term.VarSet.empty; *)
  let rec deepfvar curenv v =
    (* log "%s %d, x = %a" __FUNCTION__ __LINE__ Term.pp v; *)
    Env.check_exn env v;
    if Term.VarSet.mem v curenv
    then Term.repr v
    else
      match walk_rational curenv env subst v with
      | _, WC v -> assert false
      | _, Var v -> Term.repr v
      | vis, Value x ->
        Term.eval vis x ~fval:Term.repr ~fvar:deepfvar
  in
  let ans = Term.eval Term.VarSet.empty ~fval:Term.repr ~fvar:deepfvar (Term.repr x) in
  let () = log "exit from %s with %a" __FUNCTION__ Term.pp ans  in
  ans

module UF = UnionFindBasic
let pp_elem ppf el =
  Format.fprintf ppf "%a" Term.pp (UF.get el)

let rat_unify env subst x y =
  log "%s %d" __FUNCTION__ __LINE__;
  (* The idea is to do the unification and collect the unification prefix during the process *)
  let extend0 var term (prefix, subst) =
    let subst = extend ~skip_occurs:true ~scope:Term.Var.non_local_scope env subst var term in
    (Binding.({var; term})::prefix, subst)
  in
  (* let uf = UF.new_store () in *)
  let var2uf_keys_store = ref Term.VarMap.empty in
  let key_of_var var =
    if Term.VarMap.mem var !var2uf_keys_store
    then Term.VarMap.find var !var2uf_keys_store
    else
      let new_key = UF.make var in
      var2uf_keys_store := Term.VarMap.add var new_key !var2uf_keys_store;
      log "Added for key %d elem %d" var.Term.Var.index (Obj.magic new_key);
      log "\t %a" Term.pp new_key;
      new_key
  in
  (* let uf_lookup var = UF.find (key_of_var var) in *)
  (* let are_same_vars x y : bool =
    let xkey, ykey = key_of_var x, key_of_var y in
    (UF.find xkey) = (UF.find ykey)
  in *)
  let rec helper x y acc =
    log "\nHelper: %a and %a" Term.pp x Term.pp y;
    (* let open Term in *)
    Term.fold2 x y ~init:acc
      ~fvar:(fun ((_, subst) as acc) x y ->
        log "  Got two vars: %a and %a" Term.pp x Term.pp y;
        log "  subst = %a" pp subst;
          log "\t%s %d" __FUNCTION__ __LINE__;
          (* if Var.equal x y then acc else extend x (Term.repr y) acc *)
          let xkey, ykey = key_of_var x, key_of_var y in
          if (UF.find xkey) = (UF.find ykey)
          then
            (* let () = log "In the same class" in *)
            acc
          else
            (log "    %a j+ %a " pp_elem xkey pp_elem ykey ;
            let _joined = UF.union xkey ykey in
            log "             ==> %a\n"  pp_elem _joined;
            helper (Obj.repr @@ Term.VarMap.find x subst )
               (Obj.repr @@ Term.VarMap.find y subst)
               acc)
        )
      ~fval:(fun acc x y ->
          log "Got two values: %a and %a" Term.pp x Term.pp y;
          (* two primitive non-boxed values *)
          if x = y then acc else raise Unification_failed
      )
      ~fk:(fun (bnds, subst) l v y ->
          log "Got var %a and term %a (%s %d)" Term.pp v Term.pp y __FILE__ __LINE__;
          let subst,y =
            assert (Obj.is_block (Obj.repr y));
            let y = Obj.repr y in
            let yy = Obj.dup y in
            let sz = Obj.size y in
            let subst = ref subst in
            (* TODO: Don't copy term if changes are not needed. *)
            for i=0 to sz-1 do
              let fi = Obj.field yy i in
              if Env.is_var env fi
              then ()
              else (
                let newvar = Env.fresh ~scope:Term.Var.non_local_scope env  in
                let s0: subst = extend ~skip_occurs:true ~scope:Term.Var.non_local_scope env !subst newvar fi in
                Obj.set_field yy i newvar;
                subst := s0;
                log "\t\tintermediate s0 = %a" pp s0;
              )
            done;
            !subst, yy
          in
          log "\tnew term  = %a (%s %d)" Term.pp y __FILE__ __LINE__;
          log "\tnew subst = %a" pp subst;
          (* Variable and term  *)
          if Term.Var.is_wildcard v
          then (bnds, subst)
          else match walk_rational Term.VarSet.empty env subst v with
          | _, Var v    -> extend0 v y (bnds, subst)
          | _, Value x  -> helper x y (bnds, subst)
          | _, WC _ -> failwith "Wildcards should not appear in unifications"
      )
  in
  try
    let x, y = Term.(repr x, repr y) in
    Some (helper x y ([], subst))
  with Term.Different_shape _ | Unification_failed | Occurs_check -> None
