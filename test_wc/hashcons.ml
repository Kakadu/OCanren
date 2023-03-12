open OCanren
open OCanren.Std
open Tester

let show_int = GT.show GT.int
let show_intl = GT.show logic (GT.show GT.int)
let run_list eta = run_r (List.reify OCanren.reify) (GT.show List.logic show_intl) eta
let tbl : OCanren.tbl = Hashtbl.create 10

let foo () =
  OCanren.(run q)
    (fun q ->
      fresh
        (a b c)
        (c === !!2 % nil ())
        (b === !!1 % c)
        (a === !!0 % b)
        (q === a)
        (hashcons tbl q))
    (fun rr -> rr#reify (Std.List.prj_exn_hacky OCanren.prj_exn))
  |> Stream.iter (fun x ->
       (* ***  ***  ***  ***  ***  ***  ***  ***  ***  *** *)
       print_endline (GT.show List.ground (GT.show GT.int) x);
       Format.printf "Pointer to the rezult is\n\t%d\n%!" (Obj.magic x));
  Format.printf "Hashtable:\n%!";
  Hashtbl.iter
    (fun k _ -> Format.printf "\t%d -> %s\n%!" (Obj.magic k) (OCanren.Term.show k))
    tbl
;;

let () =
  foo ();
  foo ()
;;
