  $ ../ppx/pp_distrib.exe test001.ml | ocamlformat --impl --enable-outside-detected-project --profile=compact -
  open OCanren
  open Tester
  
  module _ = struct
    include struct
      type nonrec 'a t = Z | S of 'a [@@deriving gt ~options:{gmap; show}]
      type ground = ground t [@@deriving gt ~options:{gmap; show}]
      type logic = logic t OCanren.logic [@@deriving gt ~options:{gmap; show}]
      type injected = injected t OCanren.ilogic
  
      let reify =
        let open Env.Monad.Syntax in
        Reifier.fix (fun rself ->
            Reifier.compose Reifier.reify
              (let* self = rself in
               let rec foo = function
                 | Var (v, xs) -> Var (v, Stdlib.List.map foo xs)
                 | Value x -> Value ((GT.gmap t self) x) in
               Env.Monad.return foo ) )
  
      let z () = OCanren.inji Z
      let s _x__001_ = OCanren.inji (S _x__001_)
    end
  
    let run_peano n = run_new reify (GT.show logic) n
  
    let () =
      run_peano 1 q qh (REPR (fun q -> q === z ())) ;
      run_peano 1 q qh (REPR (fun q -> q === s (z ())))
  end
  
  module _ = struct
    include struct
      type nonrec 'a t = None | Some of 'a [@@deriving gt ~options:{gmap; show}]
      type nonrec 'a ground = 'a t [@@deriving gt ~options:{gmap; show}]
  
      type nonrec 'a logic = 'a t OCanren.logic
      [@@deriving gt ~options:{gmap; show}]
  
      type nonrec 'a injected = 'a t OCanren.ilogic
  
      let reify ra =
        let open Env.Monad.Syntax in
        Reifier.compose Reifier.reify
          (let* a = ra in
           let rec foo = function
             | Var (v, xs) -> Var (v, Stdlib.List.map foo xs)
             | Value x -> Value ((GT.gmap t a) x) in
           Env.Monad.return foo )
  
      let none () = OCanren.inji None
      let some _x__002_ = OCanren.inji (Some _x__002_)
    end
  
    let run_option n =
      run_new (reify OCanren.reify)
        (GT.show logic (GT.show OCanren.logic (GT.show GT.int)))
        n
  
    let () =
      run_option 1 q qh (REPR (fun q -> q === none ())) ;
      run_option 1 q qh (REPR (fun q -> fresh x (q === some x))) ;
      run_option 1 q qh (REPR (fun q -> fresh x (q === some !!42)))
  end
  
  module _ = struct
    include struct
      type nonrec ('a, 'b) t =
        | [] [@name "nil"]
        | ( :: ) of 'a * 'b [@name "cons"]
      [@@deriving gt ~options:{gmap; show}]
  
      type 'a ground = ('a, 'a ground) t [@@deriving gt ~options:{gmap; show}]
  
      type 'a logic = ('a, 'a logic) t OCanren.logic
      [@@deriving gt ~options:{gmap; show}]
  
      type 'a injected = ('a, 'a injected) t OCanren.ilogic
  
      let reify ra =
        let open Env.Monad.Syntax in
        Reifier.fix (fun rself ->
            Reifier.compose Reifier.reify
              (let* self = rself in
               let* a = ra in
               let rec foo = function
                 | Var (v, xs) -> Var (v, Stdlib.List.map foo xs)
                 | Value x -> Value ((GT.gmap t a self) x) in
               Env.Monad.return foo ) )
  
      let nil () = OCanren.inji []
      let cons _x__003_ _x__004_ = OCanren.inji (_x__003_ :: _x__004_)
    end
  
    let run_list n =
      run_new (reify OCanren.reify)
        (GT.show logic (GT.show OCanren.logic (GT.show GT.int)))
        n
  
    let () =
      run_list 1 q qh (REPR (fun q -> q === nil ())) ;
      run_list 1 q qh (REPR (fun q -> fresh x (q === cons x (nil ()))))
  end
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
