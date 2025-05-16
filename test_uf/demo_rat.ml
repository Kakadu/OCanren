open OCanren
open Tester

let demo1 () =
  run_r Std.Nat.reify Std.Nat.rat_show 1 qr qrh
    (REPR
       (fun x y ->
         fresh (v u)
           (rat_unify x (Std.Nat.succ v))
           (rat_unify v (Std.Nat.succ y))
           (rat_unify y (Std.Nat.succ u))
           (rat_unify u (Std.Nat.succ x))
           (debug_var !!1 OCanren.reify (fun _ ->
                print_endline "";
                success))
           (rat_unify x (Std.Nat.succ y))))

let run_nat2 n (desc, rel) =
  let answers =
    OCanren.(run qr) rel (fun q1 q2 ->
        (q1#reify Std.Nat.reify, q2#reify Std.Nat.reify))
    |> Stream.take ~n
  in
  Printf.printf "%s {\n" desc;
  List.iter
    (fun (q, r) ->
      Printf.printf "q = %s; r=%s" (Std.Nat.rat_show q) (Std.Nat.rat_show r))
    answers;
  Printf.printf "}\n"

let demo2 () =
  run_nat2 1
    (REPR
       (fun x y ->
         fresh ()
           (rat_unify x (Std.Nat.succ (Std.Nat.succ y)))
           (rat_unify y (Std.Nat.succ (Std.Nat.succ x)))
           (debug_var !!1 OCanren.reify (fun _ ->
                print_endline "";
                success))
           (rat_unify x (Std.Nat.succ y))))

let () =
  Arg.parse
    [
      (* *** *** *** *** *)
      ("-demo1", Arg.Unit demo1, "");
      ("-demo2", Arg.Unit demo2, "");
    ]
    (fun _ -> assert false)
    "help"
