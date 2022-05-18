open OCanren
open Tester
(*
let rel1 x =
  fresh (temp)
    (FD.domain x [1;2])
    (FD.neq x !!1)
    (FD.neq x !!2)*)


let runL eta = run_r OCanren.reify GT.(show logic @@ show int) eta

let rel3 dom a b c d =
  fresh (_temp)
    (FD.domain a dom)
    (FD.domain b dom)
    (FD.domain c dom)
    (FD.domain d dom)
    (FD.neq a b)
    (FD.neq a c)
    (FD.neq a d)
    (FD.neq b c)
    (FD.neq b d)
    (FD.neq c d)

let _freeVars =
  runL   1  q     qh (REPR (fun x -> (FD.domain x [1;2])  ));
  flush stdout;
  runL   1  q     qh (REPR (fun x -> (FD.domain x [1;2]) &&&  (FD.neq x !!1)  ));
  runL   1  q     qh (REPR (fun x -> (FD.domain x [1;2]) &&&  (FD.neq x !!1) &&& (FD.neq x !!2) ));
  runL   1  q     qh (REPR (fun x -> (FD.domain x [1;2]) &&&  (FD.neq x !!1) ));
  runL   1  qrst  qrsth (REPR (rel3 [1;2;3]));
  runL   1  qrst  qrsth (REPR (rel3 [1;2;3;4]));
  ()

let _ =
  runL   1  qrs  qrsh (REPR (fun q r s -> fresh ()
    (* One of domains should be known beforehand*)
    (FD.domain q [2;3])
    (FD.neq q r)
    (FD.neq r s)
    (FD.neq q s)
    (FD.domain r [2;3])
    (FD.domain s [2;3])

  ))
