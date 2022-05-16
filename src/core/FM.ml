open Logic
open Term
open Format

let pp_print_comma ppf () = Format.fprintf ppf ", "
let use_logging = true
let use_logging = false
let trace_models = true
let trace_models = false

let log fmt =
  if use_logging
  then Format.kasprintf (fun s -> Format.printf "%s\n%!" s) fmt
  else Format.ifprintf Format.std_formatter fmt
;;

let trace_a_model m f = f m

let rec fold_cps ~f ~init xs =
  match xs with
  | [] -> init
  | x :: xs -> f init x xs (fun acc -> fold_cps ~f ~init:acc xs)
;;

let list_fold_lefti ~init ~f =
  let rec helper acc i = function
    | [] -> acc
    | x :: xs -> helper (f acc i x) (i + 1) xs
  in
  helper init 0
;;

let ( !!! ) = Obj.magic

type var_idx = GT.int [@@deriving gt ~options:{ fmt; compare }]

type term0 =
  | Var of var_idx
  | Const of GT.int
[@@deriving gt ~options:{ fmt; compare }]

type op =
  (* | LT *)
  (* | LE *)
  | EQ
  | NEQ
[@@deriving gt ~options:{ fmt; compare }]

type phormula0 =
  | FMDom of var_idx * GT.int GT.list
  | FMBinop of op * term0 * term0
[@@deriving gt ~options:{ fmt; compare }]

let pp_term ppf = function
  | Const n -> Format.pp_print_int ppf n
  | Var n -> Format.fprintf ppf "_.%d" n
;;

let pp_binop ppf = function
  | EQ -> Format.fprintf ppf "==="
  | NEQ -> Format.fprintf ppf "=/="
;;

let pp_phormula ppf =
  let open Format in
  function
  | FMDom (n, xs) ->
    fprintf
      ppf
      "_.%d \\in [ %a ]"
      n
      (Format.pp_print_list ~pp_sep:(fun ppf () -> fprintf ppf " ") pp_print_int)
      xs
  | FMBinop (op, l, r) -> Format.fprintf ppf "%a%a%a" pp_term l pp_binop op pp_term r
;;

let domain v ints = FMDom (v.Term.Var.index, ints)
let fmneq l r = FMBinop (NEQ, l, r)
let fmeq l r = FMBinop (EQ, l, r)
(* let fmlt l r = FMBinop (LT, l, r) *)

type inti = int ilogic

(* type ph_desc = phormula list *)
(* type item = VarSet.t * ph_desc *)

(* type checked *)
(* type nonchecked *)

module type MYSOLVER = sig
  type state

  (* val make_solver : unit -> checked t *)
  val clear : unit -> unit
  val size : unit -> int
  val save_state : unit -> state
  val load_state : state -> unit
  val phormulas_in_solver : unit -> phormula0 list
  val phormulas_of_state : state -> phormula0 list

  type term

  val tint : int -> term
  val tvar : Term.Var.t -> term
  val tvar_of_index : int -> term

  type ph

  (* val domain : Term.Var.t -> int list -> ph *)

  (* val singleton : phormula0 -> unit *)
  val eq : term -> term -> ph
  val add_phormula0 : phormula0 -> unit
  val add_phormula_hacky : phormula0 -> unit

  type rez =
    | SAT
    | UNSAT

  val check : unit -> bool
end

(*
module MYAEZ : MYSOLVER = struct
  module Solver = Aez.Smt.Make ()
  module Symbol = Aez.Smt.Symbol
  module Type = Aez.Smt.Type

  let cur_phormulas : phormula0 list ref = ref []

  type state = int * Solver.state * phormula0 list

  let clear () = Solver.clear ()
  let size () = Caml.List.length !cur_phormulas

  let save_state phs : state =
    let ans = 0, Solver.save_state (), !cur_phormulas in
    Solver.clear ();
    cur_phormulas := [];
    ans
  ;;

  let load_state : state -> unit =
   fun (_, st, phs) ->
    Solver.restore_state st;
    cur_phormulas := phs
 ;;

  let phormulas_in_solver () = !cur_phormulas
  let phormulas_of_state (_, _, phs) = phs

  (* ***** Terms ******  *)
  module T = Aez.Smt.Term

  type nonrec term = T.t

  let var_of_idx idx = Aez.Hstring.make (sprintf "x%d" idx)

  let decl_var idx =
    let x = var_of_idx idx in
    try Symbol.declare x [] Type.type_int with
    | Aez.Smt.Error (Aez.Smt.DuplicateSymb _) -> ()
    | Aez.Smt.Error (Aez.Smt.DuplicateTypeName _) -> ()
  ;;

  let tint m = T.make_int (Num.num_of_int m)

  let tvar_of_index n =
    decl_var n;
    T.make_app (var_of_idx n) []
  ;;

  let tvar { Term.Var.index } = tvar_of_index index

  (* ***** Formulas ******  *)
  module F = Aez.Smt.Formula

  type ph = F.t

  (* let make_solver () = [] *)

  let wrap_binop op a b = F.make_lit op [ a; b ]
  let eq a b = wrap_binop F.Lt a b

  let of_term0 : term0 -> term = function
    | Var n ->
      Format.printf "%s %d\n%!" __FILE__ __LINE__;
      decl_var n;
      Format.printf "%s %d\n%!" __FILE__ __LINE__;
      let ans = T.make_app (var_of_idx n) [] in
      Format.printf "%s %d\n%!" __FILE__ __LINE__;
      ans
    | Const m -> T.make_int (Num.num_of_int m)
  ;;

  (* phormulas *)
  let of_phormula0 = function
    | FMLT (a, b) -> wrap_binop F.Lt (of_term0 a) (of_term0 b)
    | FMLE (a, b) -> wrap_binop F.Le (of_term0 a) (of_term0 b)
    | FMEQ (a, b) -> wrap_binop F.Eq (of_term0 a) (of_term0 b)
    | FMNEQ (a, b) ->
      Format.printf "%s %d\n%!" __FILE__ __LINE__;
      let ans = wrap_binop F.Neq (of_term0 a) (of_term0 b) in
      Format.printf "%s %d\n%!" __FILE__ __LINE__;
      ans
    | FMDom (v, xs) ->
      Format.printf "%s %d\n%!" __FILE__ __LINE__;
      F.make
        F.Or
        (xs
        |> Stdlib.List.map (fun n ->
               wrap_binop F.Eq (of_term0 @@ Var v) (of_term0 @@ Const n)))
  ;;

  let last_phormula = ref 0

  let add_phormula0 : phormula0 -> unit =
   fun ph0 ->
    cur_phormulas := ph0 :: !cur_phormulas;
    Format.printf "adding a phormula: %s %d\n%!" __FILE__ __LINE__;
    incr last_phormula;
    Solver.assume ~profiling:false ~id:!last_phormula (of_phormula0 ph0);
    Format.printf "phormula is assumed: %s %d\n%!" __FILE__ __LINE__
 ;;

  let add_phormula_hacky : phormula0 -> unit =
   fun ph0 ->
    Format.printf "hacky adding a phormula: %s %d\n%!" __FILE__ __LINE__;
    let f = of_phormula0 ph0 in
    incr last_phormula;
    Format.printf "%s %d\n%!" __FILE__ __LINE__;
    Solver.assume ~profiling:false ~id:!last_phormula f;
    Format.printf "hacky phormula is assumed: %s %d\n%!" __FILE__ __LINE__
 ;;

  let singleton ph = [ ph ]

  type rez =
    | SAT
    | UNSAT

  let check () =
    try
      Format.printf "check: %s %d\n%!" __FILE__ __LINE__;
      Solver.check ();
      true
    with
    | Aez.Smt.Unsat _core -> false
  ;;

  let wrap_term = function
    | Var n ->
      decl_var n;
      T.make_app (var_of_idx n) []
    | Const m -> T.make_int (Num.num_of_int m)
  ;;
end
*)
module MYZ3 = struct
  open Z3

  let ctx = Z3.mk_context []

  module IntMap = Map.Make (Int)

  module IntListMap = Map.Make (struct
    type t = int list

    let cmp : int -> int -> int = Caml.compare

    let rec compare : t -> t -> int =
     fun a b ->
      match a, b with
      | h1 :: t1, h2 :: t2 ->
        let c = cmp h1 h2 in
        if c = 0 then compare t1 t2 else c
      | [], _ :: _ -> -1
      | _ :: _, [] -> 1
      | [], [] -> 0
   ;;
  end)

  module PhSet = Stdlib.Set.Make (struct
    type t = phormula0

    let compare a b = GT.cmp_to_int @@ GT.compare phormula0 a b
  end)

  type state =
    { solver : Z3.Solver.solver
    ; vars : (Z3.Expr.expr * int list option) IntMap.t
    ; sorts : Z3.Sort.sort IntListMap.t
    ; phs : PhSet.t
    }

  let trace { vars; phs } =
    Format.printf "\027[%dm" 33;
    let classify map =
      let add_many k v map =
        try
          let vs = IntListMap.find k map in
          IntListMap.add k (v :: vs) map
        with
        | Not_found -> IntListMap.add k [ v ] map
      in
      IntMap.fold
        (fun k (_, v) acc ->
          match v with
          | Some d -> add_many d k acc
          | None -> acc)
        map
        IntListMap.empty
    in
    let () =
      let dom_to_vars = classify vars in
      Format.printf "{| ";
      dom_to_vars
      |> IntListMap.iter (fun d vars ->
             let open Format in
             printf
               "{%a} ∈ {%a}"
               (pp_print_list ~pp_sep:pp_print_comma pp_print_int)
               vars
               (pp_print_list ~pp_sep:pp_print_comma pp_print_int)
               d);
      Format.printf " |}.\n%!"
    in
    Format.printf "%a\n%!" (GT.fmt GT.list pp_phormula)
    @@ List.of_seq
    @@ PhSet.to_seq
    @@ PhSet.filter
         (function
           | FMDom _ -> false
           | _ -> true)
         phs;
    Format.printf "\027[0m"
  ;;

  let pp ppf { phs } =
    Format.fprintf ppf "{| ";
    PhSet.iter (Format.fprintf ppf "%a; " pp_phormula) phs;
    Format.fprintf ppf "|}"
  ;;

  let is_interesting_var { vars } idx =
    match IntMap.find idx vars with
    | exception Not_found -> false
    | _ -> true
  ;;

  let mk solver vars sorts phs = { solver; vars; sorts; phs }

  module Layer = struct
    let mk_sort ctx name ints =
      (* printf "\t\tEnumeration.mk_sort '%s' <domain>\n%!" name; *)
      Enumeration.mk_sort
        ctx
        (Symbol.mk_string ctx name)
        (Caml.List.map (Symbol.mk_int ctx) ints)
    ;;

    let mk_fresh_const ctx name sort =
      (* printf "\t\tExpr.mk_fresh_const '%s' of '%s'\n%!" name (Sort.to_string sort); *)
      Expr.mk_fresh_const ctx name sort
    ;;

    let add1 solver ph =
      (* printf "\t\tadd '%s'\n%!" (Expr.to_string ph); *)
      Solver.add solver [ ph ]
    ;;

    let check solver = Z3.Solver.check solver []
  end

  let check { vars; solver } =
    match Layer.check solver with
    | Z3.Solver.SATISFIABLE ->
      (match Z3.Solver.get_model solver with
      | None ->
        Format.printf "SAT but can't get a model\n%!";
        true
      | Some m ->
        let () =
          if trace_models
          then
            trace_a_model m (fun m ->
                Format.printf "\027[%dm" 36;
                Format.printf "model =";
                IntMap.iter
                  (fun k (ve, _) ->
                    Format.printf
                      "%s -> %s "
                      (Z3.Expr.to_string ve)
                      (Z3.Model.eval m ve false |> Stdlib.Option.get |> Z3.Expr.to_string))
                  vars;
                Format.printf "\027[0m";
                Format.printf "\n%!")
          else ()
        in
        true)
    | Z3.Solver.UNSATISFIABLE ->
      (* Format.printf "UNSAT\n%!"; *)
      false
    | Z3.Solver.UNKNOWN -> assert false
  ;;

  let make () =
    mk (Z3.Solver.mk_simple_solver ctx) IntMap.empty IntListMap.empty PhSet.empty
  ;;

  let clone { solver; vars; sorts; phs } =
    (* TODO: maybe we neeed a new context here *)
    (* TODO: maybe we should clone sorts too ? *)
    mk (Z3.Solver.translate solver ctx) vars sorts phs
  ;;

  let list_find_index v xs =
    (* Format.printf
      "list_find_index %d in %a\n%!"
      v
      (Format.pp_print_list
         ~pp_sep:(fun ppf () -> Format.fprintf ppf " ")
         Format.pp_print_int)
      xs; *)
    let rec helper idx = function
      | [] -> raise Not_found
      | h :: _ when h = v -> idx
      | _ :: tl -> helper (1 + idx) tl
    in
    helper 0 xs
  ;;

  let extend ({ solver; vars; sorts; phs } as s) ph0 =
    log "MYSOLVER.extend: trying to extend by %a" (GT.fmt phormula0) ph0;
    let makef = function
      | EQ -> Boolean.mk_eq
      | NEQ -> fun ctx l r -> Boolean.mk_not ctx (Boolean.mk_eq ctx l r)
    in
    let on_phormula _s = function
      | FMDom (vidx, ints) ->
        (* printf "\tTrying to add domain\n%!"; *)
        (match IntMap.find vidx vars with
        | vexpr, None ->
          let sort =
            try IntListMap.find ints sorts with
            | Not_found -> Layer.mk_sort ctx (Printf.sprintf "sort_%d" vidx) ints
          in
          mk
            solver
            (IntMap.add vidx (vexpr, Some ints) vars)
            (IntListMap.add ints sort sorts)
            phs
        | _, Some ints_old when ints_old = ints -> _s
        | _, Some ints_old ->
          failwith
            Format.(
              asprintf
                "Trying to assign domain %a to var _.%d when domain %a is already \
                 assigned"
                (pp_print_list ~pp_sep:pp_print_space pp_print_int)
                ints
                vidx
                (pp_print_list ~pp_sep:pp_print_space pp_print_int)
                ints_old)
        | exception Not_found ->
          let sort =
            try IntListMap.find ints sorts with
            | Not_found -> Layer.mk_sort ctx (Printf.sprintf "sort_%d" vidx) ints
          in
          let v = Layer.mk_fresh_const ctx (sprintf "v%d" vidx) sort in
          let __ () =
            Format.(
              printf
                "Assigning domain %a to variable _.%d\n%!"
                (pp_print_list ~pp_sep:pp_print_space pp_print_int)
                ints
                vidx)
          in
          mk
            solver
            (IntMap.add vidx (v, Some ints) vars)
            (IntListMap.add ints sort sorts)
            (PhSet.add ph0 phs))
      | FMBinop (op, Var v1, Var v2) as ph ->
        let new_vars =
          match IntMap.find_opt v1 vars, IntMap.find_opt v2 vars with
          | Some (e1, dom1), Some (e2, dom2) ->
            (* printf
              "== Adding binop between two known variables: '%s' and '%s'\n%!"
              (Expr.to_string e1)
              (Expr.to_string e2); *)
            Layer.add1 solver (makef op ctx e1 e2);
            vars
          | Some (e1, Some dom1), None ->
            let sort = IntListMap.find dom1 sorts in
            let e2 = Layer.mk_fresh_const ctx (sprintf "v%d" v2) sort in
            (* printf
              "== Left var is known, right is new: '%s' and '%s'\n%!"
              (Expr.to_string e1)
              (Expr.to_string e2); *)
            Layer.add1 solver (makef op ctx e1 e2);
            IntMap.add v2 (e2, Some dom1) vars
            (* Solver.add solver [ makef op ctx e1 e2 ] *)
          | None, Some (e2, Some dom2) ->
            let sort = IntListMap.find dom2 sorts in
            let e1 = Expr.mk_fresh_const ctx (sprintf "v%d" v1) sort in
            Layer.add1 solver (makef op ctx e1 e2);
            vars
            (* Solver.add solver [ makef op ctx e1 e2 ] *)
          | None, _ | _, None ->
            Format.eprintf "Can't add to Z3 phormula %a\n%!" (GT.fmt phormula0) ph;
            vars
        in
        mk s.solver new_vars s.sorts (PhSet.add ph0 s.phs)
      | FMBinop (op, Const v1, Const _) -> assert false
      | FMBinop (op, Const n, Var v) | FMBinop (op, Var v, Const n) ->
        let vexpr, ints =
          match IntMap.find v vars with
          | vexpr, Some ints -> vexpr, ints
          | _, None -> failwith "should not happen"
        in
        let vsort = Expr.get_sort vexpr in
        let rhs = Enumeration.get_const vsort (list_find_index n ints) in
        Solver.add solver [ makef op ctx vexpr rhs ];
        { s with phs = PhSet.add ph0 s.phs }
    in
    on_phormula s ph0
  ;;

  let extend_and_check so ph0 =
    let s = extend so ph0 in
    if check s
    then Some s
    else (
      let () = log "extend_and_check failed %s %d" __FILE__ __LINE__ in
      None)
  ;;
end

module MYSOLVER = MYZ3

module type STORE = sig
  type t = MYSOLVER.state

  val empty : unit -> t
  val is_var_interesting : t -> Term.Var.t -> bool
  val check : unit -> bool
  val get : unit -> t
  val load : t -> unit
  val extend : (term0 -> term0 -> phormula0) -> 'a -> 'b -> unit
  val extend_and_check : (term0 -> term0 -> phormula0) -> 'a -> 'b -> t -> t option
  val add_domain : Term.Var.t -> int list -> t -> t option
  val trace : t -> unit
end

module Store = struct
  type t = MYSOLVER.state

  let empty () = MYSOLVER.make ()
  let trace = MYSOLVER.trace

  let check store =
    match MYSOLVER.check store with
    | false -> false
    | true -> true
  ;;

  let add_domain var dom state =
    (* printf "%s %d\n%!" __FILE__ __LINE__; *)
    (* TODO: if the same domain is already assigned, maybe we can skip cloning *)
    let state = MYSOLVER.clone state in
    let state = MYSOLVER.extend state (FMDom (var.Term.Var.index, dom)) in
    match MYSOLVER.check state with
    | false -> None
    | true ->
      (* Format.printf "YES, add_domain said true\n%!"; *)
      Some state
  ;;

  let clone = MYSOLVER.clone

  let on_var_and_term solver op v term =
    let idx = v.Term.Var.index in
    if MYSOLVER.is_interesting_var solver idx
    then MYSOLVER.extend solver (op (Var idx) (Const term))
    else solver
  ;;

  let on_two_vars solver op v1 v2 =
    let idx1 = v1.Term.Var.index in
    let idx2 = v2.Term.Var.index in
    if MYSOLVER.is_interesting_var solver idx1 || MYSOLVER.is_interesting_var solver idx2
    then MYSOLVER.extend solver (op (Var idx1) (Var idx2))
    else solver
  ;;

  let extend ~clone solver op a b =
    let solver = if clone then MYSOLVER.clone solver else solver in
    let open Subst in
    (* We should iter prefix and see if some new substitution affect
      our constraints.
      In some cases our constraints can be merged
    *)
    (* let () = printf "a  = %s\n" (Term.show !!!a) in
    let () = printf "b  = %s\n" (Term.show !!!b) in *)
    match Term.(var a, var b) with
    | None, None when !!!a = !!!b -> solver
    | None, None -> solver
    | Some v1, Some v2 -> on_two_vars solver op v1 v2
    | Some v, _ -> on_var_and_term solver op v (!!!b : int)
    | _, Some v -> on_var_and_term solver op v (!!!a : int)
  ;;

  let extend_and_check ~clone op a b store =
    let store = extend ~clone store op a b in
    log "after extension: %a\n%!" MYSOLVER.pp store;
    match check store with
    | false ->
      log "Z3 failed";
      None
    | true ->
      log "Z3 returned a model";
      Some store
  ;;

  type store_rez =
    | Extended of t
    | Old
    | UnsatFound

  let extend_list store prefix =
    let exception Unsat in
    try
      ListLabels.fold_left
        prefix
        ~init:(false, store)
        ~f:(fun ((was_extended, store) as acc) bin ->
          let a = bin.Subst.Binding.var in
          let b = bin.Subst.Binding.term in
          match Term.(var a, var b) with
          | None, None when !!!a = !!!b -> acc
          | None, None -> raise Unsat
          | Some v1, Some v2 ->
            let idx1 = v1.Term.Var.index in
            let idx2 = v2.Term.Var.index in
            if MYSOLVER.is_interesting_var store idx1
               || MYSOLVER.is_interesting_var store idx2
            then (
              let store = if was_extended then store else MYSOLVER.clone store in
              true, MYSOLVER.extend store (fmeq (Var idx1) (Var idx2)))
            else false, store
          | Some v, _ ->
            let idx = v.Term.Var.index in
            if MYSOLVER.is_interesting_var store idx
            then (
              let store = if was_extended then store else MYSOLVER.clone store in
              true, MYSOLVER.extend store (fmeq (Var idx) (Const !!!b)))
            else false, store
          | _, Some v ->
            let idx = v.Term.Var.index in
            if MYSOLVER.is_interesting_var store idx
            then (
              let store = if was_extended then store else MYSOLVER.clone store in
              true, MYSOLVER.extend store (fmeq (Var idx) (Const !!!a)))
            else false, store)
      |> function
      | true, store -> Extended store
      | false, store -> Old
    with
    | Unsat -> UnsatFound
  ;;
end

type t = Store.t

let trace = Store.trace
let empty () = Store.empty ()

let recheck_helper op (store : Store.t) (_prefix : Subst.Binding.t list) =
  match Store.extend_list store _prefix with
  | Store.UnsatFound -> None
  | Store.Old -> Some store
  | Store.Extended store ->
    (match Store.check store with
    | false -> None
    | true -> Some store)
;;

let recheck _env _subst (store : Store.t) (_prefix : Subst.Binding.t list) =
  (* printf "%s %d length of _prefix=%d\n" __FILE__ __LINE__ (Stdlib.List.length _prefix); *)
  recheck_helper fmeq store _prefix
;;

let check store = if Store.check store then Some store else None
let neq eta = Store.extend_and_check ~clone:true fmneq eta
let eq eta = Store.extend_and_check ~clone:true fmeq eta

(* let lt x = Store.extend_and_check ~clone:true fmlt x *)
let ( =/= ) = neq

let domain (v : inti) ints store =
  let v =
    match Term.var !!!v with
    | None -> failwith "should not happen"
    | Some v -> v
  in
  Store.add_domain v ints store
;;

(*
  try
    fold_cps ~init:[] store ~f:(fun acc (set,is) tl k ->
      if VarSet.mem v set
      then begin
        let d = FMDom (v.Term.Var.index, ints) in
        let is = d::is in
        if Store.check_item_list is
        then (VarSet.add v set, is) :: (acc @ tl)
        else raise Bad
      end else
        k ((set,is)::acc)
    ) |> (fun x -> Some x)
  with Bad -> None *)

let is_interesting_var v store = MYSOLVER.is_interesting_var store v.Term.Var.index
