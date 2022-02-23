These are tests for OCanren-spefici `ocanren { ... }` syntax extension
  $ echo 'let _ = ocanren { fresh h, tl in Nat.(<=) 0 & (Nat.(<=) n 0) & n == Nat.zero}' > test0.ml
  $ camlp5o -I . pa_o.cmo pr_o.cmo pa_ocanren.cma test0.ml
  let _ =
    OCanren.Fresh.two
      (fun h tl ->
         OCanren.conj (Nat.(<=) (OCanren.Std.nat 0))
           (OCanren.conj (Nat.(<=) n (OCanren.Std.nat 0))
              (OCanren.unify n Nat.zero)))
  $ echo 'let _ = ocanren { fresh h, tl in  q == __::__ }' > test1.ml
  $ camlp5o -I . pa_o.cmo pr_o.cmo pa_ocanren.cma test1.ml
  let _ =
    OCanren.Fresh.two
      (fun h tl ->
         OCanren.Fresh.two
           (fun __1 __2 -> OCanren.unify q (OCanren.Std.List.cons __1 __2)))
# expanding wildcards in standart miniKanren syntax extension is not yet implemented
  $ echo 'let __ q  =  q === (__ %__)' > test2.ml
  $ camlp5o -I . pa_o.cmo pr_o.cmo pa_ocanren.cma test2.ml
  let __ q = q === __ % __
