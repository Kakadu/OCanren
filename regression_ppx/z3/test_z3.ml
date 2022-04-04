open Format
open Z3

let mk_sort ctx name ints =
  Enumeration.mk_sort
    ctx
    (Symbol.mk_string ctx name)
    (Caml.List.map (Symbol.mk_int ctx) ints)
;;

let%expect_test "?" =
  let ctx = Z3.mk_context [] in
  let solver = Z3.Solver.mk_simple_solver ctx in
  let sort = mk_sort ctx (Printf.sprintf "sort_%d" 10) [ 2; 3 ] in
  let q = Expr.mk_fresh_const ctx (sprintf "v%d" 10) sort in
  let r = Expr.mk_fresh_const ctx (sprintf "v%d" 11) sort in
  Solver.add solver [ Boolean.mk_not ctx (Boolean.mk_eq ctx q r) ];
  let s = Expr.mk_fresh_const ctx (sprintf "v%d" 12) sort in
  Solver.add solver [ Boolean.mk_not ctx (Boolean.mk_eq ctx q s) ];
  Solver.add solver [ Boolean.mk_not ctx (Boolean.mk_eq ctx s r) ];
  let () =
    match Z3.Solver.check solver [] with
    | Z3.Solver.SATISFIABLE -> printf "sat"
    | UNSATISFIABLE -> printf "unsat"
    | UNKNOWN -> printf "unk"
  in
  [%expect {xxx|

      	unsat
    |xxx}]
;;
