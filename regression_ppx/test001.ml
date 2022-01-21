open OCanren
open Tester
(*
module _ = struct
  include struct
    type nonrec 'a t =
      | Z
      | S of 'a
    [@@deriving gt ~options:{ gmap; show }]

    type ground = ground t [@@deriving gt ~options:{ gmap; show }]
    type logic = logic t OCanren.logic [@@deriving gt ~options:{ gmap; show }]
    type injected = injected t OCanren.ilogic

    let (prj_exn : (_, ground t) Reifier.t) =
      let open Env.Monad.Syntax in
      Reifier.fix (fun rself ->
          let* self = rself in
          let* _shallowr = OCanren.prj_exn in
          let rec foo x = (GT.gmap t self) (_shallowr x) in
          Env.Monad.return foo)
    ;;

    let (reify : (injected, logic) Reifier.t) =
      let open Env.Monad.Syntax in
      Reifier.fix (fun rself ->
          let* self = rself in
          let* _shallowr = OCanren.reify in
          let rec foo smth =
            match _shallowr smth with
            | Var (v, xs) ->
              let (_ : injected t OCanren.logic list) = xs in
              Var (v, Stdlib.List.map (GT.gmap OCanren.logic (GT.gmap t self)) xs)
            | Value x as subj ->
              let (_ : injected t OCanren.logic) = subj in
              Value ((GT.gmap t self) x)
          in
          Env.Monad.return foo)
    ;;

    let z () = OCanren.inji Z
    let s _x__001_ = OCanren.inji (S _x__001_)
  end

  let run_peano_exn n = run_new prj_exn (GT.show ground) n
  let run_peano n = run_new reify (GT.show logic) n

  let () =
    run_peano 1 q qh (REPR (fun q -> q === z ()));
    run_peano 1 q qh (REPR (fun q -> q === s (z ())))
  ;;
end *)

module _ = struct
  [%%distrib
  type nonrec 'a t =
    | Z
    | S of 'a
  [@@deriving gt ~options:{ gmap; show }]

  type ground = ground t]

  let run_peano_exn n = run_new prj_exn (GT.show ground) n
  let run_peano n = run_new reify (GT.show logic) n

  let () =
    run_peano 1 q qh (REPR (fun q -> q === z ()));
    run_peano 1 q qh (REPR (fun q -> q === s (z ())))
  ;;
end

module _ = struct
  [%%distrib
  type nonrec 'a t =
    | None
    | Some of 'a
  [@@deriving gt ~options:{ gmap; show }]

  type nonrec 'a ground = 'a t]

  (* let reify : 'a 'b. ('a, 'b) Reifier.t -> ('a injected, 'b logic) Reifier.t =
   fun ra ->
    let open Env.Monad.Syntax in
    Reifier.fix (fun _ ->
        (* let* self = rself in *)
        let* _shallowr = OCanren.reify in
        let* a = ra in
        let rec foo smth =
          match _shallowr smth with
          | Var (v, xs) ->
            Var (v, Stdlib.List.map (GT.gmap OCanren.logic (GT.gmap t foo)) xs)
          | Value x -> Value ((GT.gmap t a) x)
        in
        Env.Monad.return foo)
 ;; *)

  let (_ :
        (('a t ilogic as 'a), ('b t OCanren__Logic.logic as 'b)) Reifier.t
        -> ('a injected, 'b logic) Reifier.t)
    =
    reify
  ;;

  (* OCanren.reify *)

  let run_option n =
    run_new
      [%reify: GT.int ground]
      (GT.show logic (GT.show OCanren.logic (GT.show GT.int)))
      n
  ;;

  let () =
    run_option 1 q qh (REPR (fun q -> q === none ()));
    run_option 1 q qh (REPR (fun q -> fresh x (q === some x)));
    run_option 1 q qh (REPR (fun q -> fresh x (q === some !!42)))
  ;;
end

module _ = struct
  [%%distrib
  type nonrec ('a, 'b) t =
    | [] [@name "nil"]
    | ( :: ) of 'a * 'b [@name "cons"]
  [@@deriving gt ~options:{ gmap; show }]

  type 'a ground = ('a, 'a ground) t]

  let run_list n =
    run_new
      [%reify: GT.int ground]
      (GT.show logic (GT.show OCanren.logic (GT.show GT.int)))
      n
  ;;

  let () =
    run_list 1 q qh (REPR (fun q -> q === nil ()));
    run_list 1 q qh (REPR (fun q -> fresh x (q === cons x (nil ()))))
  ;;
end
(*
module Moves = struct
  type nonrec 'nat t =
    | Forward of 'nat
    | Backward of 'nat
    | Unload of 'nat
    | Fill of 'nat
  [@@deriving gt ~options:{ gmap; show }]

  type nonrec ground = GT.int t
  type nonrec logic = GT.int OCanren.logic t OCanren.logic
  type nonrec injected = GT.int OCanren.ilogic t OCanren.ilogic

  let prj_exn : (injected, ground) Reifier.t =
    let open Env.Monad.Syntax in
    Reifier.fix (fun rself ->
        let* self = rself in
        let* _shallowr = OCanren.prj_exn in
        let* int_shallowr = OCanren.prj_exn in
        let rec foo x = (GT.gmap t int_shallowr) (_shallowr x) in
        Env.Monad.return foo)
  ;;

  let reify : (injected, logic) Reifier.t =
    let open Env.Monad.Syntax in
    Reifier.fix (fun rself ->
        let* self = rself in
        let* _shallowr = OCanren.reify in
        let* int_shallowr = OCanren.reify in
        let rec foo x =
          match _shallowr x with
          | Var (v, xs) ->
            Var (v, Stdlib.List.map (GT.gmap OCanren.logic (GT.gmap t int_shallowr)) xs)
          | Value x -> Value (GT.gmap t int_shallowr x)
        in
        Env.Monad.return foo)
  ;;
end
*)

module Moves = struct
  [%%distrib
  type nonrec 'nat t =
    | Forward of 'nat
    | Backward of 'nat
    | Unload of 'nat
    | Fill of 'nat
  [@@deriving gt ~options:{ gmap; show }]

  type nonrec ground = GT.int t]
end
