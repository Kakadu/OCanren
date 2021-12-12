  $ ../ppx/pp_distrib.exe test001.ml | ocamlformat --impl --enable-outside-detected-project --profile=janestreet -
  open OCanren
  open Tester
  
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
        let* _shallowr = OCanren.prj_exn in
        Reifier.fix (fun rself ->
            Reifier.compose
              OCanren.prj_exn
              (let* self = rself in
               Env.Monad.return (GT.gmap t self)))
      ;;
  
      let (reify : (_, logic t OCanren.logic) Reifier.t) =
        let open Env.Monad.Syntax in
        let* _shallowr = OCanren.reify in
        Reifier.fix (fun rself ->
            Reifier.compose
              OCanren.reify
              (let* self = rself in
               let rec foo = function
                 | Var (v, xs) -> Var (v, Stdlib.List.map foo xs)
                 | Value x -> Value ((GT.gmap t self) x)
               in
               Env.Monad.return foo))
      ;;
  
      let z () = OCanren.inji Z
      let s _x__001_ = OCanren.inji (S _x__001_)
    end
  
    let run_peano n = run_new reify (GT.show logic) n
  
    let () =
      run_peano 1 q qh (REPR (fun q -> q === z ()));
      run_peano 1 q qh (REPR (fun q -> q === s (z ())))
    ;;
  end
  
  module _ = struct
    include struct
      type nonrec 'a t =
        | None
        | Some of 'a
      [@@deriving gt ~options:{ gmap; show }]
  
      type nonrec 'a ground = 'a t [@@deriving gt ~options:{ gmap; show }]
      type nonrec 'a logic = 'a t OCanren.logic [@@deriving gt ~options:{ gmap; show }]
      type nonrec 'a injected = 'a t OCanren.ilogic
  
      let prj_exn ra =
        let open Env.Monad.Syntax in
        let* _shallowr = OCanren.prj_exn in
        Reifier.compose
          OCanren.prj_exn
          (let* a = ra in
           Env.Monad.return (GT.gmap t a))
      ;;
  
      let reify ra =
        let open Env.Monad.Syntax in
        let* _shallowr = OCanren.reify in
        Reifier.compose
          OCanren.reify
          (let* a = ra in
           let rec foo = function
             | Var (v, xs) -> Var (v, Stdlib.List.map foo xs)
             | Value x -> Value ((GT.gmap t a) x)
           in
           Env.Monad.return foo)
      ;;
  
      let none () = OCanren.inji None
      let some _x__002_ = OCanren.inji (Some _x__002_)
    end
  
    let run_option n =
      run_new
        (reify OCanren.reify)
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
    include struct
      type nonrec ('a, 'b) t =
        | [] [@name "nil"]
        | ( :: ) of 'a * 'b [@name "cons"]
      [@@deriving gt ~options:{ gmap; show }]
  
      type 'a ground = ('a, 'a ground) t [@@deriving gt ~options:{ gmap; show }]
      type 'a logic = ('a, 'a logic) t OCanren.logic [@@deriving gt ~options:{ gmap; show }]
      type 'a injected = ('a, 'a injected) t OCanren.ilogic
  
      let prj_exn ra =
        let open Env.Monad.Syntax in
        let* _shallowr = OCanren.prj_exn in
        Reifier.fix (fun rself ->
            Reifier.compose
              OCanren.prj_exn
              (let* self = rself in
               let* a = ra in
               Env.Monad.return (GT.gmap t a self)))
      ;;
  
      let reify ra =
        let open Env.Monad.Syntax in
        let* _shallowr = OCanren.reify in
        Reifier.fix (fun rself ->
            Reifier.compose
              OCanren.reify
              (let* self = rself in
               let* a = ra in
               let rec foo = function
                 | Var (v, xs) -> Var (v, Stdlib.List.map foo xs)
                 | Value x -> Value ((GT.gmap t a self) x)
               in
               Env.Monad.return foo))
      ;;
  
      let nil () = OCanren.inji []
      let cons _x__003_ _x__004_ = OCanren.inji (_x__003_ :: _x__004_)
    end
  
    let run_list n =
      run_new
        (reify OCanren.reify)
        (GT.show logic (GT.show OCanren.logic (GT.show GT.int)))
        n
    ;;
  
    let () =
      run_list 1 q qh (REPR (fun q -> q === nil ()));
      run_list 1 q qh (REPR (fun q -> fresh x (q === cons x (nil ()))))
    ;;
  end
  
  module Moves = struct
    include struct
      type nonrec 'nat t =
        | Forward of 'nat
        | Backward of 'nat
        | Unload of 'nat
        | Fill of 'nat
      [@@deriving gt ~options:{ gmap; show }]
  
      type nonrec ground = GT.int t [@@deriving gt ~options:{ gmap; show }]
  
      type nonrec logic = GT.int OCanren.logic t OCanren.logic
      [@@deriving gt ~options:{ gmap; show }]
  
      type nonrec injected = GT.int OCanren.ilogic t OCanren.ilogic
  
      let (prj_exn : (_, GT.int t) Reifier.t) =
        let open Env.Monad.Syntax in
        let* _shallowr = OCanren.prj_exn in
        Reifier.compose OCanren.prj_exn (Env.Monad.return (GT.gmap t _shallowr))
      ;;
  
      let (reify : (_, GT.int OCanren.logic t OCanren.logic) Reifier.t) =
        let open Env.Monad.Syntax in
        let* _shallowr = OCanren.reify in
        Reifier.compose
          OCanren.reify
          (let rec foo = function
             | Var (v, xs) -> Var (v, Stdlib.List.map foo xs)
             | Value x -> Value ((GT.gmap t _shallowr) x)
           in
           Env.Monad.return foo)
      ;;
  
      let forward _x__005_ = OCanren.inji (Forward _x__005_)
      let backward _x__006_ = OCanren.inji (Backward _x__006_)
      let unload _x__007_ = OCanren.inji (Unload _x__007_)
      let fill _x__008_ = OCanren.inji (Fill _x__008_)
  
      type nonrec moves = ground GT.list [@@deriving reify]
      type nonrec t1 = (int * int) Std.List.ground [@@deriving reify]
    end
  end
  
  type xxxx = int Moves.t
  $ ./test001.exe
  fun q -> q === (z ()), 1 answer {
  q=Z;
  }
  fun q -> q === (s (z ())), 1 answer {
  q=S (Z);
  }
  fun q -> q === (none ()), 1 answer {
  q=None;
  }
  fun q -> fresh x (q === (some x)), 1 answer {
  q=Some (_.11);
  }
  fun q -> fresh x (q === (some (!! 42))), 1 answer {
  q=Some (42);
  }
  fun q -> q === (nil ()), 1 answer {
  q=[];
  }
  fun q -> fresh x (q === (cons x (nil ()))), 1 answer {
  q=:: (_.11, []);
  }
