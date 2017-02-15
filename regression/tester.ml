open Printf
open MiniKanren

let qh    = fun qs          -> ["q", qs]
let qrh   = fun qs rs       -> ["q", qs; "r", rs]
let qrsh  = fun qs rs ss    -> ["q", qs; "r", rs; "s", ss]
let qrsth = fun qs rs ss ts -> ["q", qs; "r", rs; "s", ss; "t", ts]

let make_title n msg =
  printf "%s, %s answer%s {\n%!"
    msg
    (if n = (-1) then "all" else string_of_int n)
    (if n <>  1  then "s" else "")

exception NoMoreAnswers

let run_gen onOK (onFree: _ -> _ -> var_checker -> _) n num handler (repr, goal)  =
  make_title n repr;
  let rec loop pairs = function
  | 0 -> ()
  | k ->
    let new_pairs =
      List.mapi (fun i (name,st) ->
        (* TODO: invent retrieve_hd function *)
        let (_: ('a,'b) fancy reification_rez Stream.t) = st in
        match Stream.retrieve ~n:1 st with
        | [],_ -> raise NoMoreAnswers
        | [Final x],tl ->
          onOK i name (Obj.magic x : 'a);
          (name,tl)
        | [HasFreeVars (f,x)],tl ->
          onFree i name
            (object method isVar: 'a . 'a -> bool = fun x -> f @@ Obj.repr x end)
            ((Obj.obj x) : ('a,'b) fancy);
          (name,tl)
        | _ -> assert false
      ) pairs
    in
    printf "\n%!";
    loop new_pairs (k-1)
  in
  let () = try loop (MiniKanren.run num goal handler) n with NoMoreAnswers -> () in
  printf "}\n%!"

(* Without free vars and reification *)
let run_exn printer = run_gen
  (fun i name x -> printf "%s%s=%s;%!" (if i<>0 then " " else "") name (printer x) )
  (fun _ _ _ -> failwith "Free logic variables in the answer")

let runR reifier printerNoFree printerR = run_gen
  (fun i name x -> printf "%s%s=%s;%!" (if i<>0 then " " else "") name (printerNoFree x) )
  (fun i name isVar obj ->
    let ans = reifier isVar obj in
    printf "%s%s=%s;%!" (if i<>0 then " " else "") name (printerR ans)
    )
