(* open OCanren
   open Bits

   let __ =
     print_endline "\n*** *** *** *** *** *** *** Test count_distincto";
     let open Tester in
     test_counto_distincto_fwd [];
     let matrix = [ [ 1 ]; [ 0 ]; [ 1 ]; [ 0 ] ] in
     test_counto_distincto_fwd matrix;
     let matrix = [ [ 1; 1 ]; [ 0; 1 ]; [ 1; 0 ]; [ 0; 1 ] ] in
     test_counto_distincto_fwd matrix;
     let matrix = [ [ 1; 0 ]; [ 0; 0 ]; [ 0; 1 ]; [ 1; 0 ] ] in
     test_counto_distincto_fwd matrix;
     let matrix = [ [ 0; 0 ]; [ 0; 0 ]; [ 0; 0 ]; [ 0; 0 ] ] in
     test_counto_distincto_fwd matrix

   let test_list_of_singletons_fwd matrix =
     let inj_matrix = Std.list (Std.list ( !! )) in
     print_endline ([%show: GT.int GT.list GT.list] () matrix);
     let open Tester in
     [%tester
       run_r Std.Nat.reify
         ([%show: Std.Nat.logic] ())
         1
         (fun c -> list_of_singletons (inj_matrix matrix) c)]

   let __ _ =
     print_endline "\n*** *** *** *** *** *** *** Test list_of_singletons";
     let open Tester in
     test_list_of_singletons_fwd [];

     let matrix = [ [ 1 ]; [ 0 ]; [ 1 ]; [ 0 ] ] in
     test_list_of_singletons_fwd matrix

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

   let __ _ =
     let open Tester in
     let matrix = [ [ 1 ]; [ 0 ]; [ 1 ]; [ 0 ] ] in
     test_split_first_column_fwd matrix;
     let matrix = [ [ 1; 0 ]; [ 0; 0 ]; [ 1; 0 ]; [ 0; 1 ] ] in
     test_split_first_column_fwd matrix;
     let matrix = [ [ 1; 0; 1 ]; [ 0; 0; 1 ]; [ 1; 0; 1 ]; [ 0; 1; 1 ] ] in
     test_split_first_column_fwd matrix;
     ()

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

   let rec choose matrix index_count rez =
     debug_var index_count Std.Nat.reify (function xs ->
         Printf.printf "index_count = %s\n"
           ([%show: Std.Nat.logic] () (Stdlib.List.hd xs));
         success)
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
                   (choose m_rest iprev ans) (cons_column col ans rez);
                 (* pass 1st column *)
                 fresh (iprev col m_rest)
                   (index_count === Std.Nat.succ iprev)
                   (split_first_column matrix col m_rest)
                   (choose m_rest index_count rez);
               ];
           ]

   let test_choose_fwd ?(n = 1) ~xlen numbers =
     Printf.printf "************************* %s\n" __FUNCTION__;
     let inj_matrix = Std.list (Std.list ( !! )) in
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

   let () = test_choose_fwd ~n:6 ~xlen:5 [ 5; 3; 0; 0; 0 ]

   let main_rel :
       Matrix.injected ->
       index_count:Std.Nat.injected ->
       Matrix.injected ->
       Std.Nat.injected ->
       goal =
     let open Std in
     (* let  first_column matrix rez = List.mapo List.hdo matrix rez in *)
     fun matrix ~index_count submatrix count ->
       fresh ()
         (choose matrix index_count submatrix)
         (counto_distincto submatrix count)

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

   let __ _ =
     print_endline "\n*** *** *** *** *** *** *** Test main";
     let matrix = [ [ 1 ]; [ 0 ]; [ 1 ]; [ 0 ] ] in
     test_main_fwd ~n:(-1) matrix ~col_count:1;
     let matrix = [ [ 1 ]; [ 0 ]; [ 1 ]; [ 0 ] ] in
     test_main_fwd ~n:(-1) matrix ~col_count:0;
     let matrix = [ [ 1; 0 ]; [ 0; 0 ]; [ 0; 1 ]; [ 1; 0 ] ] in
     test_main_fwd ~n:(-1) matrix ~col_count:1;
     Printf.printf " ===== %s %d\n%!" __FILE__ __LINE__;
     let matrix =
       [
         [ 1; 0; 0; 0; 1 ];
         [ 0; 1; 0; 0; 1 ];
         [ 0; 0; 1; 0; 1 ];
         [ 0; 0; 0; 1; 1 ];
         [ 0; 0; 0; 0; 1 ];
       ]
     in
     (* When we ask more than 5 solutions -- it hangs *)
     test_main_fwd ~n:5 matrix ~col_count:1;
     Printf.printf " ===== %s %d\n%!" __FILE__ __LINE__;
     let matrix = [ [ 1; 0 ]; [ 0; 0 ]; [ 0; 1 ]; [ 1; 0 ] ] in

     test_main_fwd ~n:1 matrix ~col_count:2;
     test_main_fwd ~n:2
       (Stdlib.List.map (binary_of_int 4) [ 3; 1; 0; 0; 0 ])
       ~col_count:2;
     ()

   let test_main_submatrix ?(n = 1) ~xlen numbers ~index_count distinct_count =
     let inj_matrix = Std.list (Std.list ( !! )) in
     Printf.printf "************************* %s\n" __FUNCTION__;
     Printf.printf "\nDistinct count = %d, index count = %d\n" distinct_count
       index_count;

     let matrix = List.map (binary_of_int xlen) numbers in
     print_matrix matrix;
     let open Tester in
     [%tester
       run_r [%reify: Matrix.t]
         (* (Std.Pair.reify Matrix.reify Std.Nat.reify) *)
         (Matrix.show_logic ()) n (fun submatrix ->
           main_rel (inj_matrix matrix) ~index_count:(Std.nat index_count)
             submatrix (Std.nat distinct_count))]

   let test1 xlen numbers ~distinct_count =
     Printf.printf "************************* %s\n" __FUNCTION__;
     assert (distinct_count > 0);
     let matrix = List.map (binary_of_int xlen) numbers in

     List.iter (fun n -> print_endline @@ [%show: GT.int GT.list] () n) matrix;
     test_main_fwd ~n:3 matrix ~col_count:2;
     test_main_submatrix ~n:1 ~xlen numbers ~index_count:2 distinct_count;
     ()

   let __ =
     (* test1 8 [ 255; 127; 16; 8; 7 ] 2;
        print_endline "Looking for 3 distinct values";
        test1 8 [ 255; 127; 16; 8; 7 ] 3;
        test1 3 [ 7; 5; 0; 0; 0 ] 3; *)
     let xlen = 5 in
     let numbers = [ 5; 3; 0; 0; 0 ] in
     test_choose_fwd ~n:6 ~xlen numbers;
     test_main_submatrix ~n:5 ~xlen numbers ~index_count:2 2;
     ()

   let test_main_anyindex_anysubmatrix ?(n = 1) matrix distinct_count =
     let inj_matrix = Std.list (Std.list ( !! )) in
     Printf.printf "\nDistinct count = %d \n" distinct_count;
     List.iter
       (fun n -> Printf.printf "\t%s\n" @@ [%show: GT.int GT.list] () n)
       matrix;
     let open Tester in
     [%tester
       run_r [%reify: (Std.Nat.t, Matrix.t) Std.Pair.t]
         (GT.show Std.Pair.logic (GT.show Std.Nat.logic) (Matrix.show_logic ()))
         n
         (fun pair ->
           fresh (index_count submatrix)
             (pair === Std.pair index_count submatrix)
             (main_rel (inj_matrix matrix) ~index_count submatrix
                (Std.nat distinct_count)))]

   let run_anyindex_anysubmatrix ?(n = 1) xlen numbers distinct_count =
     assert (distinct_count > 0);
     let matrix = List.map (binary_of_int xlen) numbers in

     List.iter
       (fun n -> Printf.printf "\t%s\n" @@ [%show: GT.int GT.list] () n)
       matrix;
     test_main_anyindex_anysubmatrix ~n matrix distinct_count;
     ()

   let __ _ =
     run_anyindex_anysubmatrix ~n:1 4 [ 3; 1; 0; 0; 0 ] 3;
     () *)
