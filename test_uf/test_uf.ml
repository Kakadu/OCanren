let%expect_test _ =
  print_int 52;
  [%expect "52"]

open UnionFind

type data = Var of string | F of data
let%expect_test "test forests" =
  let xkey = UnionFind.make "x" in
  let ykey = UnionFind.make "y" in
  Printf.printf "%b\n" (UnionFind.eq xkey ykey);
  [%expect "false"];
  let xykey = UnionFind.merge Fun.const xkey ykey in
  Printf.printf "%b\n" (UnionFind.eq xkey ykey);
  [%expect "true"];
  Printf.printf "%b\n" (UnionFind.eq xkey xykey);
  [%expect "true"];
  ()



let%expect_test "test forests 2" =
  let xkey = UnionFind.make "x" in
  let ykey = UnionFind.make "x" in
  Printf.printf "%b\n" (UnionFind.eq xkey ykey);
  [%expect "false"];
  ()
