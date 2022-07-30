open OCanren
open Tester
open OCanren.Std

let bool_dom l = conde [ l === !!false; l === !!true ]
let run_int eta = run_r OCanren.reify ([%show: GT.int logic] ()) eta

module _ = struct
  let source = {|
    match ... with
    | t,_ -> 1
    | _,_ -> 2
  |}

  let () = Printf.printf "Pseudecode:\n%s\n" source

  let run_m eta =
    run_r
      (Pair.reify (Pair.reify OCanren.reify OCanren.reify) OCanren.reify)
      ([%show:
         ((GT.bool logic, GT.bool logic) Std.Pair.logic, GT.int logic) Std.Pair.logic]
         ())
      eta
  ;;

  let test rel =
    [%tester
      run_m (-1) (fun q ->
        fresh
          (scru rhs)
          (q === pair scru rhs)
          (rel scru rhs)
          (fresh (l r) (scru === Std.pair l r) (bool_dom l) (bool_dom r)))]
  ;;

  let naive_rel q rez =
    conde
      [ fresh () (q === Std.pair !!true __) (rez === !!1)
      ; fresh temp (q =/= Std.pair !!true temp) (rez === !!2)
      ]
  ;;

  let () =
    print_endline "Naive with diseq constraints (6 answers instead of 4): ";
    test naive_rel
  ;;

  let smart_rel q rez =
    conde
      [ fresh () (q === Std.pair !!true __) (rez === !!1)
      ; fresh () (q =/= Std.pair !!true __) (rez === !!2)
      ]
  ;;

  let () =
    print_endline "With wildcards: ";
    test smart_rel
  ;;
end

module _ = struct
  let () = Printf.printf "*******\n\nLonger example for Luc's Maranget paper\n"

  let source =
    {|
    match ... with
    | _,f,t -> 1
    | f,t,_ -> 2
    | _,_,f -> 3
    | _,_,t -> 4
  |}
  ;;

  let () = Printf.printf "Pseudecode:\n%s\n" source

  let run_m eta =
    run_r
      (Pair.reify (Triple.reify OCanren.reify OCanren.reify OCanren.reify) OCanren.reify)
      ([%show:
         ( (GT.bool logic, GT.bool logic, GT.bool logic) Std.Triple.logic
         , GT.int logic )
         Std.Pair.logic]
         ())
      eta
  ;;

  let test rel =
    [%tester
      run_m (-1) (fun q ->
        fresh
          (scru rhs l m r)
          (q === pair scru rhs)
          (rel scru rhs)
          (scru === Std.triple l m r)
          (bool_dom l)
          (bool_dom m)
          (bool_dom r))]
  ;;

  let smart_rel q rez =
    let _T = !!true in
    let _F = !!false in
    let w = Std.triple in
    conde
      [ fresh () (rez === !!1) (q === w __ _F _T)
      ; fresh () (rez === !!2) (q === w _F _T __) (q =/= w __ _F _T)
      ; fresh () (rez === !!3) (q === w __ __ _F) (q =/= w __ _F _T) (q =/= w _F _T __)
      ; fresh
          ()
          (rez === !!4)
          (q =/= w __ _F _T)
          (q =/= w _F _T __)
          (q =/= w __ __ _F)
          (q === w __ __ _T)
      ]
  ;;

  let () =
    print_endline "With wildcards: ";
    test smart_rel
  ;;

  let () =
    [%tester
      run_int (-1) (fun rhs -> fresh s (s === Std.triple !!true __ __) (smart_rel s rhs))]
  ;;

  let hack q rez =
    let _T = !!true in
    let _F = !!false in
    let w = Std.triple in
    conde
      [ failure
        (* ; fresh () (rez === !!1) (q === w __ _F _T) *)
        (* ; fresh () (rez === !!2) (q === w _F _T __) (q =/= w __ _F _T) *)
        (* ; fresh () (rez === !!3) (q === w __ __ _F) (q =/= w __ _F _T) (q =/= w _F _T __) *)
      ; fresh
          ()
          (rez === !!4)
          (* (q === w __ __ __) *)
          (q =/= w __ _F _T)
          (q =/= w _F _T __)
          (q =/= w __ __ _F)
          (debug_var !!1 OCanren.reify (fun _ ->
             (* OCanren.set_diseq_logging true; *)
             success))
          (q === w __ __ _T)
      ]
  ;;

  let () =
    print_endline "HACK";
    [%tester
      run_m (-1) (fun q ->
        fresh
          (scru rhs l m r)
          (q === pair scru rhs)
          (* (scru === Std.triple l m r) *)
          (hack scru rhs)
          (* (bool_dom l) *)
          (* (bool_dom m) *)
          (* (bool_dom r) *)
          success)]
  ;;
end
