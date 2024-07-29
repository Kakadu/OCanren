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

let test_groupo_fwd ?(n = 1) matrix =
  let inj_matrix = Std.list (Std.list ( !! )) in
  print_endline ([%show: GT.int GT.list GT.list] () matrix);
  let open Tester in
  [%tester
    run_r Matrix.reify (Matrix.show_logic ()) n (fun head0 head1 ->
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
  fun ?(verbose = false) matrix ~index_count submatrix count ->
    fresh ()
      (choose ~verbose matrix index_count submatrix)
      (counto_distincto ~verbose submatrix count)

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

include struct
  let reconstruct_submatrix :
      ?verbose:bool ->
      Std.Nat.injected Std.List.injected ->
      Matrix.injected ->
      Matrix.injected ->
      goal =
   fun ?(verbose = false) ->
    let open Std in
    let rec helper curidx indexes matrix rez =
      (if verbose then
         debug_var curidx Std.Nat.reify (function
           | [ h ] ->
               Printf.printf "curidx = %s\n" ([%show: Std.Nat.logic] () h);
               success
           | _ -> assert false)
         &&& debug_var indexes [%reify: Std.Nat.t Std.List.t] (function
               | [ h ] ->
                   Printf.printf "indexes = %s\n"
                     ([%show: Std.Nat.logic Std.List.logic] () h);
                   success
               | _ -> assert false)
       else success)
      &&& conde
            [
              indexes === Std.nil () &&& empty_column matrix rez;
              fresh (ih itl col m_rest)
                (indexes === ih % itl)
                (split_first_column matrix col m_rest)
                (conde
                   [
                     fresh rez_rest (ih === curidx)
                       (cons_column col rez_rest rez)
                       (helper (Std.Nat.succ curidx) itl m_rest rez_rest);
                     fresh ()
                       (* (Std.Nat.lto curidx ih !!true) *)
                       (ih =/= curidx)
                       (helper (Std.Nat.succ curidx) indexes m_rest rez);
                   ]);
            ]
    in
    fun eta -> helper Std.Nat.one eta

  let rec well_founded_matrix m =
    let open Std in
    conde
      [
        m === Std.nil (); fresh (h tl) (m === !<h % tl) (well_founded_matrix tl);
      ]

  let rec eval ?(verbose = false) matrix cur_idx all_indexes total_count
      ~empty_column : goal =
    let open Std in
    (if false then
       debug_var (Std.pair total_count cur_idx)
         [%reify: (Std.Nat.t, Std.Nat.t) Std.Pair.t] (function
         | [ Value (total, cur) ] ->
             Printf.printf "eval.total_count = %s, curidx = %s\n"
               ([%show: Std.Nat.logic] () total)
               ([%show: Std.Nat.logic] () cur);
             success
         | _ -> assert false)
       &&& debug_var matrix [%reify: Matrix.t] (function
             | [ h ] ->
                 Printf.printf "matrix = %s\n" (Matrix.show_logic () h);
                 success
             | _ -> assert false)
     else success)
    &&& well_founded_matrix matrix
    &&& conde
          [
            all_indexes === Std.nil () &&& failure;
            matrix === Std.nil () &&& failure;
            matrix === !<(Std.nil ()) &&& failure;
            fresh last_index
              (all_indexes === !<last_index)
              (conde
                 [
                   list_of_empty_lists matrix &&& failure;
                   (* Not ntake 1st column *)
                   fresh (matrix col m_rest)
                     (split_first_column matrix col m_rest)
                     (m_rest =/= empty_column)
                     (eval ~empty_column ~verbose m_rest (Nat.succ cur_idx)
                        all_indexes total_count);
                   (* take first column *)
                   fresh
                     (head0 head1 count0 count1 count01)
                     (last_index === cur_idx)
                     (groupo matrix ~head1 head0)
                     (conde
                        [
                          head0 === nil () &&& (count0 === Nat.zero);
                          head0 =/= nil () &&& (count0 === Nat.one);
                        ])
                     (conde
                        [
                          head1 === nil () &&& (count1 === Nat.zero);
                          head1 =/= nil () &&& (count1 === Nat.one);
                        ])
                     (debug_var (Std.triple count0 count1 total_count)
                        [%reify: (Std.Nat.t, Std.Nat.t, Std.Nat.t) Std.Triple.t]
                        (function
                       | [ Value (c0, c1, tot) ] ->
                           Printf.printf "c0 = %s, c1 = %s, total = %s\n"
                             ([%show: Std.Nat.logic] () c0)
                             ([%show: Std.Nat.logic] () c1)
                             ([%show: Std.Nat.logic] () tot);
                           success
                       | _ -> assert false))
                     (debug_var (Std.triple matrix head0 head1)
                        [%reify: (Matrix.t, Matrix.t, Matrix.t) Std.Triple.t]
                        (function
                       | [ Value (m, c0, c1) ] ->
                           Printf.printf "head0 = %s, head1 = %s , m = %s\n"
                             (Matrix.show_logic () c0) (Matrix.show_logic () c1)
                             (Matrix.show_logic () m);
                           success
                       | _ -> assert false))
                     (Nat.addo count0 count1 count01)
                     (count01 === total_count)
                     (debug_var !!1 OCanren.reify (fun _ ->
                          print_endline "HERR";
                          success));
                 ]);
            conde
              [
                (* skip first column *)
                fresh
                  (next_idx col m_rest all_indexes_rest tmp0 tmp1)
                  (all_indexes === cur_idx % all_indexes_rest)
                  (all_indexes_rest === tmp0 % tmp1)
                  (next_idx === Std.Nat.succ cur_idx)
                  (split_first_column matrix col m_rest)
                  (eval ~empty_column ~verbose m_rest next_idx all_indexes
                     total_count);
                (* pass 1st column *)
                fresh
                  (all_indexes_rest head0 head1 tmp0 tmp1)
                  (all_indexes === cur_idx % all_indexes_rest)
                  (all_indexes_rest === tmp0 % tmp1)
                  (groupo matrix ~head1 head0)
                  (conde
                     [
                       head0 === Std.nil ()
                       &&& eval ~empty_column head1 (Nat.succ cur_idx)
                             all_indexes_rest total_count;
                       head1 === Std.nil ()
                       &&& eval ~empty_column head0 (Nat.succ cur_idx)
                             all_indexes_rest total_count;
                       fresh (count0 count1)
                         (head0 =/= Std.nil ())
                         (head1 =/= Std.nil ())
                         (eval ~empty_column head0 (Nat.succ cur_idx)
                            all_indexes_rest count0)
                         (Std.Nat.addo count0 count1 total_count)
                         (eval ~empty_column head1 (Nat.succ cur_idx)
                            all_indexes_rest count1)
                         (if verbose then
                            debug_var (Std.pair count0 count1)
                              [%reify: (Std.Nat.t, Std.Nat.t) Std.Pair.t]
                              (function
                              | [ Value (c0, c1) ] ->
                                  Printf.printf "count0 = %s, count1 = %s\n"
                                    ([%show: Std.Nat.logic] () c0)
                                    ([%show: Std.Nat.logic] () c1);
                                  success
                              | _ -> assert false)
                          else success)
                         (if verbose then
                            debug_var head0 [%reify: Matrix.t] (function
                              | [ h ] ->
                                  Printf.printf "  head0 = %s\n"
                                    (Matrix.show_logic () h);
                                  success
                              | _ -> assert false)
                          else success)
                         (if verbose then
                            debug_var head1 [%reify: Matrix.t] (function
                              | [ h ] ->
                                  Printf.printf "  head1 = %s\n"
                                    (Matrix.show_logic () h);
                                  success
                              | _ -> assert false)
                          else success);
                     ]);
              ];
          ]

  (* fuse choose and count *)
  let main2 :
      ?verbose:bool ->
      Matrix.injected ->
      Std.Nat.injected Std.List.injected ->
      submatrix:Matrix.injected ->
      Std.Nat.injected ->
      goal =
    let open Std in
    fun ?(verbose = false) matrix all_indexes ~submatrix count ->
      fresh empty_column
        (List.mapo (fun _ rez -> rez === Std.nil ()) matrix empty_column)
        (eval ~empty_column ~verbose matrix Std.Nat.one all_indexes count)
        (reconstruct_submatrix all_indexes matrix submatrix)
end

let test_reconstruct_submatrix ?(verbose = false) ?(n = 1) xlen numbers indices
    =
  let _ = verbose in
  assert (List.for_all (fun x -> x > 0) indices);
  Printf.printf "\nxlen = %d\n" xlen;
  Printf.printf "indicies = %s\n" (GT.show GT.list (GT.show GT.int) indices);

  let matrix = List.map (binary_of_int xlen) numbers in
  print_matrix matrix;
  let open Tester in
  [%tester
    run_r [%reify: Matrix.t] (Matrix.show_logic ()) n (fun submatrix ->
        reconstruct_submatrix ~verbose (Std.list Std.nat indices)
          (inj_matrix matrix) submatrix)]

let test_main2 ?(verbose = false) ?(n = 1) xlen numbers distinct_count =
  assert (distinct_count > 0);
  Printf.printf "\nxlen = %d, distinct_count = %d\n" xlen distinct_count;

  let matrix = List.map (binary_of_int xlen) numbers in
  print_matrix matrix;
  let open Tester in
  [%tester
    run_r [%reify: (Matrix.t, Std.Nat.t Std.List.t) Std.Pair.t]
      (GT.show Std.Pair.logic (Matrix.show_logic ())
         ([%show: Std.Nat.logic Std.List.logic] ()))
      n
      (fun pair ->
        fresh (submatrix indicies)
          (pair === Std.pair submatrix indicies)
          (main2 ~verbose (inj_matrix matrix) indicies ~submatrix
             (Std.nat distinct_count)))]

include struct
  module List1 = struct
    [%%distrib
    type 'a ground = Last of 'a | Cons of 'a * 'a ground
    [@@deriving gt ~options:{ gmap }]]

    let rec of_list = function
      | [] -> failwith "bad argument"
      | [ h ] -> Last h
      | h :: tl -> Cons (h, of_list tl)

    let rec inj_list f : _ -> _ injected = function
      | [] -> failwith "bad argument"
      | [ h ] -> last (f h)
      | h :: tl -> cons (f h) (inj_list f tl)

    let rec of_binary_int ~xlen n =
      assert (n >= 0);
      assert (xlen > 0);
      let rec loop acc curi n =
        if curi > xlen then acc
        else loop (Cons (n mod 2, acc)) (curi + 1) (n / 2)
      in

      loop (Last (n mod 2)) 2 (n / 2)

    let rec inj f = function
      | Last x -> last (f x)
      | Cons (x, xs) -> cons (f x) (inj f xs)

    let rec ground_to_normal_list = function
      | Cons (h, tl) -> h :: ground_to_normal_list tl
      | Last h -> [ h ]

    let rec logic_to_normal_list_exn fcast_exn : _ logic -> _ list = function
      | Value (Cons (h, tl)) ->
          fcast_exn h :: logic_to_normal_list_exn fcast_exn tl
      | Value (Last h) -> [ fcast_exn h ]
      | Var _ -> failwith "bad arg"

    let show_ground f xs = GT.show GT.list f (ground_to_normal_list xs)

    let show_logic_int_list xs =
      let l =
        logic_to_normal_list_exn
          (function Value x -> x | Var _ -> assert false)
          xs
      in
      [%show: GT.int GT.list] () l
  end

  module Split_rez : sig
    type ('a, 'a0) t = Last_col of 'a0 | Many_cols of 'a0 * 'a
    [@@deriving gt ~options:{ gmap }]

    type nonrec 'a ground = ('a, int list) t [@@deriving gt ~options:{ gmap }]

    type nonrec 'a logic =
      ('a, int OCanren.logic Std.List.logic) t OCanren.logic
    [@@deriving gt ~options:{ gmap }]

    type nonrec 'a injected = ('a, int ilogic Std.List.injected) t ilogic

    val prj_exn : ('a, 'a_2) Reifier.t -> ('a injected, 'a_2 ground) Reifier.t
    val reify : ('a, 'a_2) Reifier.t -> ('a injected, 'a_2 logic) Reifier.t
    val last_col : 'a -> ('b, 'a) t ilogic
    val many_cols : 'col -> 'm -> ('m, 'col) t ilogic
  end = struct
    [%%distrib
    type nonrec 'a ground =
      | Last_col of GT.int Std.List.ground
      | Many_cols of GT.int Std.List.ground * 'a
    [@@deriving gt ~options:{ gmap }]]
  end

  module rec Matrix1 : sig
    type nonrec ground = GT.int List1.ground GT.list
    [@@deriving gt ~options:{ gmap }]

    type nonrec logic = GT.int OCanren.logic List1.logic Std.List.logic
    [@@deriving gt ~options:{ gmap }]

    type injected = int ilogic List1.injected Std.List.injected

    val prj_exn : (injected, int List1.ground list) Reifier.t
    val reify : (injected, logic) Reifier.t
    val make : int list list -> injected

    val split_1_col :
      injected ->
      (injected, int ilogic Std.List.injected) Split_rez.t ilogic ->
      goal

    val groupo : injected -> head1:injected -> injected -> goal
    val inj_numbers : xlen:int -> int list -> injected
    val show_logic : logic -> string
  end = struct
    [%%distrib
    type nonrec ground = GT.int List1.ground GT.list
    [@@deriving gt ~options:{ gmap }]]

    let make xs = Std.list (List1.inj_list ( !! )) xs

    let inj_numbers ~xlen xs : injected =
      make @@ List.map (binary_of_int xlen) xs

    let show_logic : logic -> string =
     fun m -> GT.show Std.List.logic List1.show_logic_int_list m

    let split_1_col matrix rez =
      conde
        [
          fresh col1
            (rez === Split_rez.last_col col1)
            (Std.List.mapo (fun a b -> a === List1.last b) matrix col1);
          fresh (col1 m2)
            (rez === Split_rez.many_cols col1 m2)
            (Std.List.mapo
               (fun a b -> fresh tl (a === List1.cons b tl))
               matrix col1)
            (Std.List.mapo
               (fun a b -> fresh tl (a === List1.cons tl b))
               matrix m2);
        ]

    let rec groupo : injected -> head1:injected -> injected -> goal =
      let open Std in
      fun xss ~head1 head0 ->
        conde
          [
            xss === nil () &&& (head0 === Std.nil ()) &&& (head0 === head1);
            fresh (h tl rest rest0 rest1)
              (xss === h % rest)
              (conde
                 [
                   h === List1.cons !!0 tl
                   &&& (head0 === tl % rest0)
                   &&& groupo rest ~head1 rest0;
                   h === List1.cons !!1 tl
                   &&& (head1 === tl % rest1)
                   &&& groupo rest ~head1:rest1 head0;
                 ]);
          ]
  end

  let reconstruct_submatrix3 :
      ?verbose:bool ->
      Std.Nat.injected List1.injected ->
      Matrix1.injected ->
      Matrix1.injected ->
      goal =
   fun ?(verbose = false) ->
    let open Std in
    let _ = verbose in
    let rec helper curidx indexes (matrix : Matrix1.injected)
        (rez : Matrix1.injected) =
      conde
        [
          fresh mrest
            (* Last index === current, take first column *)
            (indexes === List1.last curidx)
            (conde
               [
                 (* matrix is big *)
                 fresh col1
                   (Matrix1.split_1_col matrix (Split_rez.many_cols col1 mrest))
                   (List.mapo (fun e x -> x === List1.last e) col1 rez);
                 fresh col1
                   (Matrix1.split_1_col matrix (Split_rez.last_col col1))
                   (List.mapo (fun e x -> x === List1.last e) col1 rez);
               ]);
          fresh (lasti col1 mrest)
            (* Last index, NOT a current index *)
            (indexes === List1.last lasti)
            (lasti =/= curidx)
            (Matrix1.split_1_col matrix (Split_rez.many_cols col1 mrest))
            (helper (Nat.succ curidx) indexes mrest rez);
          fresh (ihead itl col1 mrest)
            (* NOT Last index, NOT a current index *)
            (* If matrix has only 1 column --- fail (not written here) *)
            (indexes === List1.cons ihead itl)
            (ihead =/= curidx)
            (Matrix1.split_1_col matrix (Split_rez.many_cols col1 mrest))
            (helper (Nat.succ curidx) indexes mrest rez);
          fresh (ih itl mrest col1 rez_tl)
            (* NOT Last index, starts with a CURRENT index *)
            (indexes === List1.cons ih itl)
            (ih === curidx)
            (Matrix1.split_1_col matrix (Split_rez.many_cols col1 mrest))
            (Matrix1.split_1_col rez (Split_rez.many_cols col1 rez_tl))
            (helper (Nat.succ curidx) itl mrest rez_tl);
        ]
    in
    fun eta -> helper Std.Nat.one eta

  let rec well_founded_matrix m =
    let open Std in
    conde
      [
        m === Std.nil (); fresh (h tl) (m === !<h % tl) (well_founded_matrix tl);
      ]

  let counto01 lst rez =
    conde
      [
        rez === Std.Nat.zero &&& (lst === Std.nil ());
        Std.List.mapo (fun _ r -> r === !!0) lst lst &&& (rez === Std.Nat.one);
        Std.List.mapo (fun _ r -> r === !!1) lst lst &&& (rez === Std.Nat.one);
        rez === Std.nat 2;
      ]

  let rec eval3 ?(verbose = false) matrix cur_idx all_indexes total_count
      ~empty_column : goal =
    let open Std in
    let _ : Matrix1.injected = matrix in
    let _ : _ List1.injected = all_indexes in
    conde
      [
        matrix === Std.nil () &&& failure;
        fresh (col last_idx)
          (Matrix1.split_1_col matrix (Split_rez.last_col col))
          (all_indexes === List1.last last_idx)
          (cur_idx === last_idx) (counto01 col total_count);
        fresh (col last_idx m2)
          (Matrix1.split_1_col matrix (Split_rez.many_cols col m2))
          (all_indexes === List1.last last_idx)
          (conde
             [
               fresh () (* take *)
                 (cur_idx === last_idx) (counto01 col total_count);
               (* omit *)
               eval3 ~verbose m2 (Std.Nat.succ cur_idx) all_indexes total_count
                 ~empty_column;
             ]);
        fresh (col idx_h idx_tl m2)
          (Matrix1.split_1_col matrix (Split_rez.many_cols col m2))
          (all_indexes === List1.cons idx_h idx_tl)
          (conde
             [
               fresh (head0 head1) (* take *)
                 (cur_idx === idx_h)
                 (Matrix1.groupo matrix head0 ~head1)
                 (conde
                    [
                      fresh ()
                        (head0 === nil ())
                        (eval3 ~verbose head1 (Std.Nat.succ cur_idx) idx_tl
                           total_count ~empty_column);
                      fresh ()
                        (head1 === nil ())
                        (eval3 ~verbose head0 (Std.Nat.succ cur_idx) idx_tl
                           total_count ~empty_column);
                      fresh (count0 count1)
                        (head0 =/= nil ())
                        (head1 =/= nil ())
                        (eval3 ~verbose head0 (Std.Nat.succ cur_idx) idx_tl
                           count0 ~empty_column)
                        (eval3 ~verbose head1 (Std.Nat.succ cur_idx) idx_tl
                           count1 ~empty_column)
                        (Nat.addo count0 count1 total_count);
                    ]);
               (* omit *)
               eval3 ~verbose m2 (Std.Nat.succ cur_idx) all_indexes total_count
                 ~empty_column;
             ]);
      ]

  (* fuse choose and count *)
  let main3 :
      ?verbose:bool ->
      Matrix1.injected ->
      Std.Nat.injected List1.injected ->
      submatrix:Matrix1.injected ->
      Std.Nat.injected ->
      goal =
    let open Std in
    fun ?(verbose = false) matrix all_indexes ~submatrix count ->
      fresh empty_column
        (List.mapo (fun _ rez -> rez === Std.nil ()) matrix empty_column)
        (eval3 ~empty_column ~verbose matrix Std.Nat.one all_indexes count)
        (reconstruct_submatrix3 all_indexes matrix submatrix)
end
