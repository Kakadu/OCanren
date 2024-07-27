open OCanren

let rec binary_of_int xlen n =
  assert (n >= 0);
  if xlen > 0 then binary_of_int (xlen - 1) (n / 2) @ [ n mod 2 ] else []

let print_matrix =
  List.iter (fun n -> Printf.printf "\t%s\n" @@ [%show: GT.int GT.list] () n)

let inj_matrix = Std.list (Std.list ( !! ))

let rec list_of_empty_lists xs =
  let open Std in
  conde
    [
      xs === Std.nil ();
      fresh tl (xs === Std.nil () % tl) (list_of_empty_lists tl);
    ]

type bvi = int ilogic Std.List.injected
type matrixi = bvi Std.List.injected
type counti = Std.Nat.injected

module Matrix = struct
  type injected = bvi Std.List.injected

  let reify : (matrixi, _) Reifier.t =
    Std.List.reify (Std.List.reify OCanren.reify)

  let show_logic = [%show: GT.int OCanren.logic Std.List.logic Std.List.logic]
end

let rec list_of_same : 'a. xs:'a Std.List.injected -> 'a -> goal =
 fun ~xs el ->
  let open Std in
  conde [ xs === nil (); fresh tl (xs === el % tl) (list_of_same el ~xs:tl) ]

let rec list_of_singletons_helper : matrixi -> found0:_ -> found1:_ -> goal =
  let open Std in
  fun xs ~found0 ~found1 ->
    conde
      [
        xs === nil () &&& (found0 === !!false) &&& (found1 === !!false);
        found0 === !!false &&& (found1 === !!true) &&& list_of_same ~xs !<(!!1);
        found1 === !!false &&& (found0 === !!true) &&& list_of_same ~xs !<(!!0);
        found0 === !!true &&& (found1 === !!true)
        &&& fresh (tl tmp)
              (conde
                 [
                   xs === !<(!!0) % (!<(!!1) % tl);
                   xs === !<(!!1) % (!<(!!0) % tl);
                   xs
                   === !<(!!1) % (!<(!!1) % tl)
                   &&& list_of_singletons_helper tl ~found1:tmp ~found0;
                   xs
                   === !<(!!0) % (!<(!!0) % tl)
                   &&& list_of_singletons_helper tl ~found0:tmp ~found1;
                 ]);
      ]

let test_list_of_singletons_helper_fwd ?msg matrix =
  let inj_matrix = Std.list (Std.list ( !! )) in
  Option.iter print_endline msg;
  let open Tester in
  [%tester
    run_r
      (Std.Pair.reify OCanren.reify OCanren.reify)
      ([%show: (GT.bool OCanren.logic, GT.bool OCanren.logic) Std.Pair.logic] ())
      1
      (fun p ->
        fresh (found0 found1)
          (p === Std.pair found0 found1)
          (list_of_singletons_helper (inj_matrix matrix) ~found0 ~found1))]

let list_of_singletons =
  let open Std in
  (fun xss count ->
     fresh (has0 has1)
       (list_of_singletons_helper xss ~found0:has0 ~found1:has1)
       (conde
          [
            has0 === !!false &&& (has1 === !!false) &&& (count === Nat.zero);
            has0 === !!true &&& (has1 === !!false) &&& (count === Nat.one);
            has0 === !!false &&& (has1 === !!true) &&& (count === Nat.one);
            has0 === !!true &&& (has1 === !!true) &&& (count === Nat.(succ one));
          ])
    : matrixi -> counti -> goal)

let test_list_of_singletons_fwd matrix =
  let inj_matrix = Std.list (Std.list ( !! )) in

  print_endline ([%show: GT.int GT.list GT.list] () matrix);
  let open Tester in
  [%tester
    run_r Std.Nat.reify
      ([%show: Std.Nat.logic] ())
      1
      (fun found0 -> list_of_singletons (inj_matrix matrix) found0)]

let rec groupo : matrixi -> head1:matrixi -> matrixi -> goal =
  let open Std in
  fun xss ~head1 head0 ->
    conde
      [
        xss === nil () &&& (head0 === Std.nil ()) &&& (head0 === head1);
        fresh (h tl rest rest0 rest1)
          (xss === h % rest)
          (conde
             [
               h === !!0 % tl
               &&& (head0 === tl % rest0)
               &&& groupo rest ~head1 rest0;
               h === !!1 % tl
               &&& (head1 === tl % rest1)
               &&& groupo rest ~head1:rest1 head0;
             ]);
      ]

let test_groupo_fwd matrix =
  let inj_matrix = Std.list (Std.list ( !! )) in
  print_endline ([%show: GT.int GT.list GT.list] () matrix);
  let open Tester in
  [%tester
    run_r Matrix.reify (Matrix.show_logic ()) 1 (fun head0 head1 ->
        groupo (inj_matrix matrix) ~head1 head0)]

(* All xss are lists of the same length *)
let rec counto_distincto =
  let open Std in
  let rec helper ?(verbose = false) (xss : matrixi) (count : counti) =
    conde
      [
        xss === nil () &&& (count === Nat.zero);
        xss =/= nil ()
        &&& conde
              [
                (* list_of_singletons xss count; *)
                list_of_same ~xs:xss (Std.nil ()) &&& (count === Nat.one);
                fresh
                  (head0 head1 count0 count1)
                  (groupo xss ~head1 head0) (helper head0 count0)
                  (helper head1 count1)
                  (if verbose then
                     debug_var (Std.pair count0 count1)
                       [%reify: (Nat.logic, Nat.logic) Std.Pair.logic] (function
                       | [ Value (count0, count1) ] ->
                           Printf.printf "count0 = %s, count1 = %s\n"
                             ([%show: Nat.logic] () count0)
                             ([%show: Nat.logic] () count1);
                           success
                       | _ -> assert false)
                   else success)
                  (Nat.addo count0 count1 count);
              ];
      ]
  in
  fun ?(verbose = false) submatrix count ->
    (if verbose then
       debug_var (Std.pair submatrix count)
         (Std.Pair.reify Matrix.reify Std.Nat.reify) (function
         | [ Value (m, c) ] ->
             Printf.printf "%s count=%s:\n" __FUNCTION__ (Std.Nat.show_logic c);
             Printf.printf "%s\n" (Matrix.show_logic () m);
             success
         | _ -> success)
     else success)
    &&& helper ~verbose submatrix count
    &&&
    if verbose then
      debug_var (Std.pair submatrix count)
        (Std.Pair.reify Matrix.reify Std.Nat.reify) (function
        | [ Value (m, c) ] ->
            Printf.printf "%s FINISHED count=%s:\n" __FUNCTION__
              (Std.Nat.show_logic c);
            Printf.printf "%s\n" (Matrix.show_logic () m);
            success
        | _ -> success)
    else success

let test_counto_distincto_full_ground ?(verbose = false) ?(n = 1) ~xlen numbers
    distinct_count =
  let inj_matrix = Std.list (Std.list ( !! )) in
  let matrix = List.map (binary_of_int xlen) numbers in
  print_matrix matrix;
  let open Tester in
  [%tester
    run_r OCanren.reify
      ([%show: GT.int OCanren.logic] ())
      n
      (fun _ ->
        counto_distincto ~verbose (inj_matrix matrix) (Std.nat distinct_count))]

let test_counto_distincto_fwd matrix =
  let inj_matrix = Std.list (Std.list ( !! )) in

  print_endline ([%show: GT.int GT.list GT.list] () matrix);
  let open Tester in
  [%tester
    run_r Std.Nat.reify
      ([%show: Std.Nat.logic] ())
      1
      (fun c -> counto_distincto (inj_matrix matrix) c)]

let test_list_of_singletons_fwd matrix =
  let inj_matrix = Std.list (Std.list ( !! )) in
  print_endline ([%show: GT.int GT.list GT.list] () matrix);
  let open Tester in
  [%tester
    run_r Std.Nat.reify
      ([%show: Std.Nat.logic] ())
      1
      (fun c -> list_of_singletons (inj_matrix matrix) c)]

let rec split_first_column : matrixi -> bvi -> matrixi -> goal =
 fun matrix col rest ->
  let open Std in
  conde
    [
      matrix === Std.nil () &&& (rest === Std.nil ()) &&& (col === Std.nil ());
      fresh
        (string1 rest_strings col1 col_tl rest1 rest_tl)
        (matrix === string1 % rest_strings)
        (string1 === col1 % rest1)
        (col === col1 % col_tl)
        (rest === rest1 % rest_tl)
        (split_first_column rest_strings col_tl rest_tl);
    ]

let test_split_first_column_fwd matrix =
  let inj_matrix = Std.list (Std.list ( !! )) in

  print_endline ([%show: GT.int GT.list GT.list] () matrix);
  let open Tester in
  [%tester
    run_r
      (Std.Pair.reify (Std.List.reify OCanren.reify) Matrix.reify)
      ((GT.show Std.Pair.logic)
         ([%show: GT.int OCanren.logic Std.List.logic] ())
         (Matrix.show_logic ()))
      1
      (fun pair ->
        fresh (c rest)
          (pair === Std.pair c rest)
          (split_first_column (inj_matrix matrix) c rest))]

let empty_column (matrix : Matrix.injected) (rez : Matrix.injected) =
  Std.List.mapo (fun _ rez -> rez === Std.nil ()) matrix rez

let rec cons_column c m rez =
  let open Std in
  conde
    [
      c === nil () &&& (m === nil ()) &&& (rez === m);
      fresh (ch ctl mh mtl rezh reztl)
        (c === ch % ctl)
        (m === mh % mtl)
        (rez === rezh % reztl)
        (rezh === ch % mh)
        (cons_column ctl mtl reztl);
    ]

let rec choose ?(verbose = false) matrix index_count rez =
  (if false then
     debug_var index_count Std.Nat.reify (function xs ->
         Printf.printf "index_count = %s\n"
           ([%show: Std.Nat.logic] () (Stdlib.List.hd xs));
         success)
   else success)
  &&& conde
        [
          index_count === Std.Nat.zero &&& empty_column matrix rez;
          conde
            [
              (* empty_column matrix matrix
                 &&& (index_count =/= Std.Nat.zero)
                 &&& failure; *)
              (* cut first column *)
              fresh (iprev col m_rest ans)
                (index_count === Std.Nat.succ iprev)
                (split_first_column matrix col m_rest)
                (choose ~verbose m_rest iprev ans)
                (cons_column col ans rez);
              (* pass 1st column *)
              fresh (iprev col m_rest)
                (index_count === Std.Nat.succ iprev)
                (split_first_column matrix col m_rest)
                (choose ~verbose m_rest index_count rez);
            ];
        ]

let test_choose_fwd ?(n = 1) ~xlen numbers =
  let matrix = List.map (binary_of_int xlen) numbers in
  print_matrix matrix;
  let open Tester in
  [%tester
    run_r [%reify: (Std.Nat.t, Matrix.t) Std.Pair.t]
      (GT.show Std.Pair.logic
         ([%show: Std.Nat.logic] ())
         (Matrix.show_logic ()))
      n
      (fun pair ->
        fresh (index_count rez)
          (pair === Std.pair index_count rez)
          (index_count =/= Std.Nat.zero)
          (choose (inj_matrix matrix) index_count rez))]

let main_rel :
    ?verbose:bool ->
    Matrix.injected ->
    index_count:Std.Nat.injected ->
    Matrix.injected ->
    Std.Nat.injected ->
    goal =
  let open Std in
  (* let  first_column matrix rez = List.mapo List.hdo matrix rez in *)
  fun ?(verbose = false) matrix ~index_count submatrix count ->
    fresh ()
      (choose ~verbose matrix index_count submatrix)
      (if verbose then
         debug_var (Std.pair submatrix count)
           (Std.Pair.reify Matrix.reify Std.Nat.reify) (function
           | [ Value (m, c) ] ->
               Printf.printf "Trying to fit matrix ot count %s:\n"
                 (Std.Nat.show_logic c);
               Printf.printf "%s\n" (Matrix.show_logic () m);
               success
           | _ -> success)
       else success)
      (counto_distincto ~verbose submatrix count)
      (if verbose then
         debug_var (Std.pair submatrix count)
           (Std.Pair.reify Matrix.reify Std.Nat.reify) (function
           | [ Value (m, c) ] ->
               Printf.printf "counto_distincto succeeded for count %s:\n"
                 (Std.Nat.show_logic c);
               Printf.printf "%s\n\n" (Matrix.show_logic () m);
               success
           | _ -> success)
       else success)

let test_main_fwd ?(n = 1) matrix ~col_count =
  let inj_matrix = Std.list (Std.list ( !! )) in
  Printf.printf "\nColumns count = %d\n" col_count;
  print_matrix matrix;
  let open Tester in
  [%tester
    run_r [%reify: (Matrix.t, Std.Nat.t) Std.Pair.t]
      ((GT.show Std.Pair.logic) (Matrix.show_logic ())
         ([%show: Std.Nat.logic] ()))
      n
      (fun pair ->
        fresh (submatrix distinct_count)
          (pair === Std.pair submatrix distinct_count)
          (main_rel (inj_matrix matrix) ~index_count:(Std.nat col_count)
             submatrix distinct_count))]

let test_main_submatrix ?(n = 1) ?(verbose = false) ~xlen numbers ~index_count
    distinct_count =
  let inj_matrix = Std.list (Std.list ( !! )) in
  Printf.printf "\nDistinct count = %d, index count = %d\n" distinct_count
    index_count;

  let matrix = List.map (binary_of_int xlen) numbers in
  print_matrix matrix;
  let open Tester in
  [%tester
    run_r [%reify: Matrix.t] (Matrix.show_logic ()) n (fun submatrix ->
        main_rel ~verbose (inj_matrix matrix) ~index_count:(Std.nat index_count)
          submatrix (Std.nat distinct_count))]

let test1 xlen numbers ~distinct_count =
  assert (distinct_count > 0);
  let matrix = List.map (binary_of_int xlen) numbers in

  List.iter (fun n -> print_endline @@ [%show: GT.int GT.list] () n) matrix;
  test_main_fwd ~n:3 matrix ~col_count:2;
  test_main_submatrix ~n:1 ~xlen numbers ~index_count:2 distinct_count;
  ()

let test_main_anyindex_anysubmatrix ?(verbose = false) ?(n = 1) xlen numbers
    distinct_count =
  Printf.printf "\nDistinct count = %d, xlen = %d\n" distinct_count xlen;

  assert (distinct_count > 0);
  let matrix = List.map (binary_of_int xlen) numbers in
  print_matrix matrix;
  let open Tester in
  [%tester
    run_r [%reify: (Std.Nat.t, Matrix.t) Std.Pair.t]
      (GT.show Std.Pair.logic (GT.show Std.Nat.logic) (Matrix.show_logic ()))
      n
      (fun pair ->
        fresh (index_count submatrix)
          (pair === Std.pair index_count submatrix)
          (main_rel ~verbose (inj_matrix matrix) ~index_count submatrix
             (Std.nat distinct_count)))]
