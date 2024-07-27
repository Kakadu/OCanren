open OCanren
open Bits

let%expect_test _ =
  let open Tester in
  test_list_of_singletons_helper_fwd [];
  [%expect
    {|
    fun p ->
      fresh (found0 found1) (p === (Std.pair found0 found1))
        (list_of_singletons_helper (inj_matrix matrix) ~found0 ~found1), 1 answer {
    q=(false, false);
    } |}];
  test_list_of_singletons_helper_fwd [ [ 1 ] ];
  [%expect
    {|
    fun p ->
      fresh (found0 found1) (p === (Std.pair found0 found1))
        (list_of_singletons_helper (inj_matrix matrix) ~found0 ~found1), 1 answer {
    q=(false, true);
    } |}];
  let matrix = [ [ 1 ]; [ 0 ]; [ 1 ]; [ 0 ] ] in
  test_list_of_singletons_helper_fwd matrix;
  [%expect
    {|
    fun p ->
      fresh (found0 found1) (p === (Std.pair found0 found1))
        (list_of_singletons_helper (inj_matrix matrix) ~found0 ~found1), 1 answer {
    q=(true, true);
    } |}]

let%expect_test _ =
  print_endline "\n*** *** *** *** *** *** *** Test list_of_singletons";
  let open Tester in
  let matrix = [ [ 0 ]; [ 1 ] ] in
  test_list_of_singletons_fwd matrix;
  let matrix = [ [ 0 ]; [ 0 ] ] in
  test_list_of_singletons_fwd matrix;
  [%expect
    {|
  *** *** *** *** *** *** *** Test list_of_singletons
  [[0]; [1]]
  fun c -> list_of_singletons (inj_matrix matrix) c, 1 answer {
  q=S (S (O));
  }
  [[0]; [0]]
  fun c -> list_of_singletons (inj_matrix matrix) c, 1 answer {
  q=S (O);
  } |}]

let%expect_test _ =
  let open Tester in
  let matrix = [ [ 1 ]; [ 0 ]; [ 1 ]; [ 0 ] ] in
  test_groupo_fwd matrix;
  [%expect
    {|
    [[1]; [0]; [1]; [0]]
    fun head0 -> fun head1 -> groupo (inj_matrix matrix) ~head1 head0, 1 answer {
    q=[[]; []]; r=[[]; []];
    } |}];
  let matrix = [ [ 1; 1 ]; [ 0; 1 ]; [ 1; 0 ]; [ 0; 1 ] ] in
  test_groupo_fwd matrix;
  [%expect
    {|
    [[1; 1]; [0; 1]; [1; 0]; [0; 1]]
    fun head0 -> fun head1 -> groupo (inj_matrix matrix) ~head1 head0, 1 answer {
    q=[[1]; [1]]; r=[[1]; [0]];
    } |}];
  let matrix = [ [ 1; 1; 0 ]; [ 0; 1; 0 ]; [ 1; 0; 1 ]; [ 0; 1; 1 ] ] in
  test_groupo_fwd matrix;
  [%expect
    {|
    [[1; 1; 0]; [0; 1; 0]; [1; 0; 1]; [0; 1; 1]]
    fun head0 -> fun head1 -> groupo (inj_matrix matrix) ~head1 head0, 1 answer {
    q=[[1; 0]; [1; 1]]; r=[[1; 0]; [0; 1]];
    } |}];
  let matrix = [ [ 1; 0 ]; [ 0; 0 ]; [ 0; 1 ]; [ 1; 0 ] ] in
  test_groupo_fwd matrix;
  [%expect
    {|
      [[1; 0]; [0; 0]; [0; 1]; [1; 0]]
      fun head0 -> fun head1 -> groupo (inj_matrix matrix) ~head1 head0, 1 answer {
      q=[[0]; [1]]; r=[[0]; [0]];
      } |}];
  let matrix = [ [ 0; 0 ]; [ 0; 0 ]; [ 0; 0 ]; [ 0; 0 ]; [ 0; 0 ] ] in
  test_groupo_fwd matrix;
  [%expect
    {|
    [[0; 0]; [0; 0]; [0; 0]; [0; 0]; [0; 0]]
    fun head0 -> fun head1 -> groupo (inj_matrix matrix) ~head1 head0, 1 answer {
    q=[[0]; [0]; [0]; [0]; [0]]; r=[];
    }
         |}];
  ()

let%expect_test _ =
  let open Tester in
  test_counto_distincto_full_ground ~n:2 ~xlen:2 [ 0; 0; 0; 0; 0 ] 2;
  [%expect
    {|
      	[0; 0]
      	[0; 0]
      	[0; 0]
      	[0; 0]
      	[0; 0]
      fun _ -> counto_distincto (inj_matrix matrix) (Std.nat distinct_count), 2 answers {
      count0 = S (O), count1 = O
      count0 = S (O), count1 = S (O)
      q=_.10;
      count0 = S (O), count1 = S (O)
      q=_.10;
      } |}]

let%expect_test _ =
  let open Tester in
  test_counto_distincto_fwd [];
  [%expect
    {|
    []
    fun c -> counto_distincto (inj_matrix matrix) c, 1 answer {
    q=O;
    } |}];
  let matrix = [ [ 1 ]; [ 0 ]; [ 1 ]; [ 0 ] ] in
  test_counto_distincto_fwd matrix;
  [%expect
    {|
    [[1]; [0]; [1]; [0]]
    fun c -> counto_distincto (inj_matrix matrix) c, 1 answer {
    q=S (S (O));
    } |}];
  let matrix = [ [ 1; 1 ]; [ 0; 1 ]; [ 1; 0 ]; [ 0; 1 ] ] in
  test_counto_distincto_fwd matrix;
  [%expect
    {|
    [[1; 1]; [0; 1]; [1; 0]; [0; 1]]
    fun c -> counto_distincto (inj_matrix matrix) c, 1 answer {
    count0 = S (O), count1 = S (S (O))
    q=S (S (S (O)));
    } |}];
  let matrix = [ [ 1; 0 ]; [ 0; 0 ]; [ 0; 1 ]; [ 1; 0 ] ] in
  test_counto_distincto_fwd matrix;
  [%expect
    {|
    [[1; 0]; [0; 0]; [0; 1]; [1; 0]]
    fun c -> counto_distincto (inj_matrix matrix) c, 1 answer {
    count0 = S (S (O)), count1 = S (O)
    q=S (S (S (O)));
    } |}];
  let matrix = [ [ 0; 0 ]; [ 0; 0 ]; [ 0; 0 ]; [ 0; 0 ] ] in
  test_counto_distincto_fwd matrix;
  [%expect
    {|
    [[0; 0]; [0; 0]; [0; 0]; [0; 0]]
    fun c -> counto_distincto (inj_matrix matrix) c, 1 answer {
    count0 = S (O), count1 = O
    q=S (O);
    } |}]

let test_list_of_singletons_fwd matrix =
  let inj_matrix = Std.list (Std.list ( !! )) in
  print_endline ([%show: GT.int GT.list GT.list] () matrix);
  let open Tester in
  [%tester
    run_r Std.Nat.reify
      ([%show: Std.Nat.logic] ())
      1
      (fun c -> list_of_singletons (inj_matrix matrix) c)]

let%expect_test _ =
  print_endline "\n*** *** *** *** *** *** *** Test list_of_singletons";
  let open Tester in
  test_list_of_singletons_fwd [];
  [%expect
    {|
    *** *** *** *** *** *** *** Test list_of_singletons
    []
    fun c -> list_of_singletons (inj_matrix matrix) c, 1 answer {
    q=O;
    } |}];

  let matrix = [ [ 1 ]; [ 0 ]; [ 1 ]; [ 0 ] ] in
  test_list_of_singletons_fwd matrix;
  [%expect
    {|
    [[1]; [0]; [1]; [0]]
    fun c -> list_of_singletons (inj_matrix matrix) c, 1 answer {
    q=S (S (O));
    } |}]

let%expect_test _ =
  let open Tester in
  let matrix = [ [ 1 ]; [ 0 ]; [ 1 ]; [ 0 ] ] in
  test_split_first_column_fwd matrix;
  [%expect
    {|
    [[1]; [0]; [1]; [0]]
    fun pair ->
      fresh (c rest) (pair === (Std.pair c rest))
        (split_first_column (inj_matrix matrix) c rest), 1 answer {
    q=([1; 0; 1; 0], [[]; []; []; []]);
    } |}];
  let matrix = [ [ 1; 0 ]; [ 0; 0 ]; [ 1; 0 ]; [ 0; 1 ] ] in
  test_split_first_column_fwd matrix;
  [%expect
    {|
    [[1; 0]; [0; 0]; [1; 0]; [0; 1]]
    fun pair ->
      fresh (c rest) (pair === (Std.pair c rest))
        (split_first_column (inj_matrix matrix) c rest), 1 answer {
    q=([1; 0; 1; 0], [[0]; [0]; [0]; [1]]);
    } |}];
  let matrix = [ [ 1; 0; 1 ]; [ 0; 0; 1 ]; [ 1; 0; 1 ]; [ 0; 1; 1 ] ] in
  test_split_first_column_fwd matrix;
  [%expect
    {|
    [[1; 0; 1]; [0; 0; 1]; [1; 0; 1]; [0; 1; 1]]
    fun pair ->
      fresh (c rest) (pair === (Std.pair c rest))
        (split_first_column (inj_matrix matrix) c rest), 1 answer {
    q=([1; 0; 1; 0], [[0; 1]; [0; 1]; [0; 1]; [1; 1]]);
    } |}];
  ()

let%expect_test _ =
  test_choose_fwd ~n:6 ~xlen:5 [ 5; 3; 0; 0; 0 ];
  [%expect
    {|
    	[0; 0; 1; 0; 1]
    	[0; 0; 0; 1; 1]
    	[0; 0; 0; 0; 0]
    	[0; 0; 0; 0; 0]
    	[0; 0; 0; 0; 0]
    fun pair ->
      fresh (index_count rez) (pair === (Std.pair index_count rez))
        (index_count =/= Std.Nat.zero)
        (choose (inj_matrix matrix) index_count rez), 6 answers {
    q=(S (O), [[0]; [0]; [0]; [0]; [0]]);
    q=(S (O), [[0]; [0]; [0]; [0]; [0]]);
    q=(S (S (O)), [[0; 0]; [0; 0]; [0; 0]; [0; 0]; [0; 0]]);
    q=(S (O), [[1]; [0]; [0]; [0]; [0]]);
    q=(S (S (O)), [[0; 1]; [0; 0]; [0; 0]; [0; 0]; [0; 0]]);
    q=(S (S (O)), [[0; 1]; [0; 0]; [0; 0]; [0; 0]; [0; 0]]);
    } |}]

let%expect_test _ =
  let matrix = [ [ 1 ]; [ 0 ]; [ 1 ]; [ 0 ] ] in
  test_main_fwd ~n:(-1) matrix ~col_count:1;
  [%expect
    {|
    Columns count = 1
    	[1]
    	[0]
    	[1]
    	[0]
    fun pair ->
      fresh (submatrix distinct_count)
        (pair === (Std.pair submatrix distinct_count))
        (main_rel (inj_matrix matrix) ~index_count:(Std.nat col_count) submatrix
           distinct_count), all answers {
    q=([[1]; [0]; [1]; [0]], S (S (O)));
    } |}];

  (* let matrix = [ [ 1 ]; [ 0 ]; [ 1 ]; [ 0 ] ] in
     test_main_fwd ~n:(-1) matrix ~col_count:0; *)
  let matrix = [ [ 1; 0 ]; [ 0; 0 ]; [ 0; 1 ]; [ 1; 0 ] ] in
  test_main_fwd ~n:(-1) matrix ~col_count:1;
  [%expect
    {|
    Columns count = 1
    	[1; 0]
    	[0; 0]
    	[0; 1]
    	[1; 0]
    fun pair ->
      fresh (submatrix distinct_count)
        (pair === (Std.pair submatrix distinct_count))
        (main_rel (inj_matrix matrix) ~index_count:(Std.nat col_count) submatrix
           distinct_count), all answers {
    q=([[1]; [0]; [0]; [1]], S (S (O)));
    q=([[0]; [0]; [1]; [0]], S (S (O)));
    } |}];
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
  [%expect
    {|
    Columns count = 1
    	[1; 0; 0; 0; 1]
    	[0; 1; 0; 0; 1]
    	[0; 0; 1; 0; 1]
    	[0; 0; 0; 1; 1]
    	[0; 0; 0; 0; 1]
    fun pair ->
      fresh (submatrix distinct_count)
        (pair === (Std.pair submatrix distinct_count))
        (main_rel (inj_matrix matrix) ~index_count:(Std.nat col_count) submatrix
           distinct_count), 5 answers {
    q=([[1]; [0]; [0]; [0]; [0]], S (S (O)));
    q=([[0]; [1]; [0]; [0]; [0]], S (S (O)));
    q=([[0]; [0]; [1]; [0]; [0]], S (S (O)));
    q=([[0]; [0]; [0]; [1]; [0]], S (S (O)));
    q=([[1]; [1]; [1]; [1]; [1]], S (O));
    } |}];
  let matrix = [ [ 1; 0 ]; [ 0; 0 ]; [ 0; 1 ]; [ 1; 0 ] ] in

  test_main_fwd ~n:1 matrix ~col_count:2;
  [%expect
    {|
    Columns count = 2
    	[1; 0]
    	[0; 0]
    	[0; 1]
    	[1; 0]
    fun pair ->
      fresh (submatrix distinct_count)
        (pair === (Std.pair submatrix distinct_count))
        (main_rel (inj_matrix matrix) ~index_count:(Std.nat col_count) submatrix
           distinct_count), 1 answer {
    count0 = S (S (O)), count1 = S (O)
    q=([[1; 0]; [0; 0]; [0; 1]; [1; 0]], S (S (S (O))));
    } |}];
  test_main_fwd ~n:2
    (Stdlib.List.map (binary_of_int 4) [ 3; 1; 0; 0; 0 ])
    ~col_count:2;
  ();
  [%expect
    {|
    Columns count = 2
    	[0; 0; 1; 1]
    	[0; 0; 0; 1]
    	[0; 0; 0; 0]
    	[0; 0; 0; 0]
    	[0; 0; 0; 0]
    fun pair ->
      fresh (submatrix distinct_count)
        (pair === (Std.pair submatrix distinct_count))
        (main_rel (inj_matrix matrix) ~index_count:(Std.nat col_count) submatrix
           distinct_count), 2 answers {
    count0 = S (O), count1 = O
    q=([[0; 0]; [0; 0]; [0; 0]; [0; 0]; [0; 0]], S (O));
    count0 = S (O), count1 = S (O)
    q=([[0; 0]; [0; 0]; [0; 0]; [0; 0]; [0; 0]], S (S (O)));
    } |}]

let%expect_test _ =
  (* test1 8 [ 255; 127; 16; 8; 7 ] 2;
     print_endline "Looking for 3 distinct values";
     test1 8 [ 255; 127; 16; 8; 7 ] 3;
     test1 3 [ 7; 5; 0; 0; 0 ] 3; *)
  let xlen = 5 in
  let numbers = [ 5; 3; 0; 0; 0 ] in
  test_choose_fwd ~n:8 ~xlen numbers;
  [%expect
    {|
    	[0; 0; 1; 0; 1]
    	[0; 0; 0; 1; 1]
    	[0; 0; 0; 0; 0]
    	[0; 0; 0; 0; 0]
    	[0; 0; 0; 0; 0]
    fun pair ->
      fresh (index_count rez) (pair === (Std.pair index_count rez))
        (index_count =/= Std.Nat.zero)
        (choose (inj_matrix matrix) index_count rez), 8 answers {
    q=(S (O), [[0]; [0]; [0]; [0]; [0]]);
    q=(S (O), [[0]; [0]; [0]; [0]; [0]]);
    q=(S (S (O)), [[0; 0]; [0; 0]; [0; 0]; [0; 0]; [0; 0]]);
    q=(S (O), [[1]; [0]; [0]; [0]; [0]]);
    q=(S (S (O)), [[0; 1]; [0; 0]; [0; 0]; [0; 0]; [0; 0]]);
    q=(S (S (O)), [[0; 1]; [0; 0]; [0; 0]; [0; 0]; [0; 0]]);
    q=(S (S (S (O))), [[0; 0; 1]; [0; 0; 0]; [0; 0; 0]; [0; 0; 0]; [0; 0; 0]]);
    q=(S (O), [[0]; [1]; [0]; [0]; [0]]);
    } |}];
  test_main_submatrix ~verbose:true ~n:5 ~xlen numbers ~index_count:2 2;
  ();
  [%expect
    {|
    Distinct count = 2, index count = 2
    	[0; 0; 1; 0; 1]
    	[0; 0; 0; 1; 1]
    	[0; 0; 0; 0; 0]
    	[0; 0; 0; 0; 0]
    	[0; 0; 0; 0; 0]
    fun submatrix ->
      main_rel ~verbose (inj_matrix matrix) ~index_count:(Std.nat index_count)
        submatrix (Std.nat distinct_count), 5 answers {
    Trying to fit matrix ot count S (S (O)):
    [[0; 0]; [0; 0]; [0; 0]; [0; 0]; [0; 0]]
    Bits.counto_distincto.(fun) count=S (S (O)):
    [[0; 0]; [0; 0]; [0; 0]; [0; 0]; [0; 0]]
    count0 = S (O), count1 = O
    count0 = S (O), count1 = S (O)
    Bits.counto_distincto.(fun) FINISHED count=S (S (O)):
    [[0; 0]; [0; 0]; [0; 0]; [0; 0]; [0; 0]]
    counto_distincto succeeded for count S (S (O)):
    [[0; 0]; [0; 0]; [0; 0]; [0; 0]; [0; 0]]

    q=[[0; 0]; [0; 0]; [0; 0]; [0; 0]; [0; 0]];
    count0 = S (O), count1 = S (O)
    Bits.counto_distincto.(fun) FINISHED count=S (S (O)):
    [[0; 0]; [0; 0]; [0; 0]; [0; 0]; [0; 0]]
    counto_distincto succeeded for count S (S (O)):
    [[0; 0]; [0; 0]; [0; 0]; [0; 0]; [0; 0]]

    q=[[0; 0]; [0; 0]; [0; 0]; [0; 0]; [0; 0]];
    Trying to fit matrix ot count S (S (O)):
    [[0; 1]; [0; 0]; [0; 0]; [0; 0]; [0; 0]]
    Bits.counto_distincto.(fun) count=S (S (O)):
    [[0; 1]; [0; 0]; [0; 0]; [0; 0]; [0; 0]]
    count0 = O, count1 = O
    count0 = S (O), count1 = O
    count0 = O, count1 = S (O)
    count0 = S (O), count1 = S (O)
    Bits.counto_distincto.(fun) FINISHED count=S (S (O)):
    [[0; 0]; [0; 0]; [0; 0]; [0; 0]; [0; 0]]
    counto_distincto succeeded for count S (S (O)):
    [[0; 0]; [0; 0]; [0; 0]; [0; 0]; [0; 0]]

    q=[[0; 0]; [0; 0]; [0; 0]; [0; 0]; [0; 0]];
    count0 = O, count1 = S (O)
    count0 = S (O), count1 = O
    count0 = S (O), count1 = S (O)
    Bits.counto_distincto.(fun) FINISHED count=S (S (O)):
    [[0; 0]; [0; 0]; [0; 0]; [0; 0]; [0; 0]]
    counto_distincto succeeded for count S (S (O)):
    [[0; 0]; [0; 0]; [0; 0]; [0; 0]; [0; 0]]

    q=[[0; 0]; [0; 0]; [0; 0]; [0; 0]; [0; 0]];
    count0 = S (O), count1 = S (O)
    Bits.counto_distincto.(fun) FINISHED count=S (S (O)):
    [[0; 0]; [0; 0]; [0; 0]; [0; 0]; [0; 0]]
    counto_distincto succeeded for count S (S (O)):
    [[0; 0]; [0; 0]; [0; 0]; [0; 0]; [0; 0]]

    q=[[0; 0]; [0; 0]; [0; 0]; [0; 0]; [0; 0]];
    } |}]

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

let%expect_test _ =
  run_anyindex_anysubmatrix ~n:1 4 [ 3; 1; 0; 0; 0 ] 3;
  [%expect
    {|
    	[0; 0; 1; 1]
    	[0; 0; 0; 1]
    	[0; 0; 0; 0]
    	[0; 0; 0; 0]
    	[0; 0; 0; 0]

    Distinct count = 3
    	[0; 0; 1; 1]
    	[0; 0; 0; 1]
    	[0; 0; 0; 0]
    	[0; 0; 0; 0]
    	[0; 0; 0; 0]
    fun pair ->
      fresh (index_count submatrix) (pair === (Std.pair index_count submatrix))
        (main_rel (inj_matrix matrix) ~index_count submatrix
           (Std.nat distinct_count)), 1 answer {
    count0 = S (O), count1 = O
    count0 = S (O), count1 = S (O)
    count0 = S (O), count1 = S (O)
    count0 = O, count1 = O
    count0 = S (O), count1 = O
    count0 = O, count1 = S (O)
    count0 = S (O), count1 = S (O)
    count0 = O, count1 = S (O)
    count0 = S (O), count1 = O
    count0 = S (O), count1 = S (O)
    count0 = S (O), count1 = S (O)
    count0 = S (O), count1 = S (O)
    count0 = S (O), count1 = S (S (O))
    q=(S (S (O)), [[0; 0]; [0; 0]; [0; 0]; [0; 0]; [0; 0]]);
    } |}];
  ()
