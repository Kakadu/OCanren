(* Testing Option.t and Result.t here *)
open OCanren
open OCanren.Std
open Tester
open Printf

let show_int       = GT.show(GT.int)
let show_int_opt   = GT.show(GT.option) (GT.show(GT.int))
let show_intl      = GT.show(logic)  (GT.show(GT.int))
let show_intl_optl = GT.show(logic)  (GT.show(GT.option) (GT.show(logic) (GT.show(GT.int))))

let run_opt eta = run_r (Option.reify OCanren.reify) show_intl_optl eta
let run_int eta = run_r OCanren.prj_exn show_int eta

let (!!) x = inj (lift x)

let _ = Option.(
    run_int 1 q qh (REPR(fun q -> q === !!5));
    run_opt 1 q qh (REPR(fun q -> q === some !!5));
    run_opt 1 q qh (REPR(fun q -> q === none ()));
    run_int 1 q qh (REPR(fun q -> some q === some !!5 ));
    run_opt 1 q qh (REPR(fun q -> fresh (w) (q === some w) ))
  )

module Result = struct
  @type ('a, 'b) t = ('a, 'b) Result.t =
    | Ok of 'a | Error of 'b
    with gmap,show
  let fmap eta = GT.gmap t eta;;

  @type ('a, 'b) logic = ('a, 'b)  t OCanren.logic
    with gmap,show
  module A = OCanren.Fmap2(struct
    type ('a, 'b) t = ('a, 'b) Result.t
    let fmap = fmap
  end )
  include A

  type ('a, 'b, 'c, 'd) i = (('a, 'b) Result.t, ('c,'d) Result.t OCanren.logic) injected
  let ok x    : _ i = inj @@ distrib(Ok x)
  let error : _ -> _ i = fun x -> inj @@ distrib (Error x)
  let _1 : unit -> ((int, int) Result.t, (int OCanren.logic, int OCanren.logic) Result.t OCanren.logic) Reifier.t = fun () ->
    reify OCanren.reify OCanren.reify
end
(*
include struct
  let () =
    print_endline "AAA";
    let run_option rel =
      OCanren.(run q) rel (fun rr ->
        rr#reify (Option.reify OCanren.reify))
        |> OCanren.Stream.iter (fun x ->
          print_endline @@ GT.show(logic) (GT.show(Option.t)
          (GT.show(logic) (GT.show GT.int))) x )
    in
    run_option (fun q -> q === q);
    run_option (fun q -> q === Option.some !!1);
    run_option (fun q -> q === Option.none ());
    ()

    let () =
    print_endline "BBB";
    let run_option rel =
      OCanren.(run q) rel (fun rr ->
        rr#reify (Option.prj_exn OCanren.prj_exn))
        |> OCanren.Stream.iter (fun x ->
          print_endline @@ (GT.show(Option.t) (GT.show GT.int)) x)
    in
    run_option (fun q -> q === Option.some !!1);
    run_option (fun q -> q === Option.none ());
    ()
  let () =
    print_endline "CCC";
    let run_option rel =
      let show = GT.show(logic) (GT.show(Result.t)
                  (GT.show(logic) (GT.show GT.int))
                  (GT.show(logic) (GT.show GT.int))
                  )
      in
      OCanren.(run q) rel (fun rr ->
        rr#reify (Result.reify OCanren.reify OCanren.reify))
        |> OCanren.Stream.iter (fun x ->
          print_endline @@ show x)
    in
    run_option (fun q -> q === Result.ok !!1);
    run_option (fun q -> q === Result.error !!2);
    ()
end *)

let show1 = GT.show(Result.t) (GT.show(GT.int)) (GT.show(GT.option) (GT.show(GT.int)))
let show1logic =
  GT.show(logic) (GT.show(Result.t)
    (GT.show(logic) (GT.show GT.int))
    (GT.show(logic) (GT.show GT.int)) )

let runResult n =
  run_r (Result.reify OCanren.reify OCanren.reify) show1logic n

let _ =
  runResult     1  q qh (REPR(fun q -> q === Result.ok !!5 ));
  runResult   (-1) q qh (REPR(fun q ->
    fresh (r)
      (q === Result.ok r)
      (conde [r === !!5; success])
    ));
  runResult   (-1) q qh (REPR(fun q -> fresh (r s)
    (conde
      [ (q === Result.ok    s) &&& (s =/= !!4)
      ; (q === Result.error r)
      ])
  ))
