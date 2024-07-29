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
  test_counto_distincto_full_ground ~verbose:false ~n:2 ~xlen:2
    [ 0; 0; 0; 0; 0 ] 1;
  [%expect
    {|
      	[0; 0]
      	[0; 0]
      	[0; 0]
      	[0; 0]
      	[0; 0]
      fun _ ->
        counto_distincto ~verbose (inj_matrix matrix) (Std.nat distinct_count), 2 answers {
      q=_.10;
      } |}];
  test_counto_distincto_full_ground ~verbose:false ~n:2 ~xlen:2
    [ 0; 0; 0; 0; 0 ] 2;
  [%expect
    {|
          	[0; 0]
          	[0; 0]
          	[0; 0]
          	[0; 0]
          	[0; 0]
          fun _ ->
            counto_distincto ~verbose (inj_matrix matrix) (Std.nat distinct_count), 2 answers {
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
    q=S (S (S (O)));
    } |}];
  let matrix = [ [ 1; 0 ]; [ 0; 0 ]; [ 0; 1 ]; [ 1; 0 ] ] in
  test_counto_distincto_fwd matrix;
  [%expect
    {|
    [[1; 0]; [0; 0]; [0; 1]; [1; 0]]
    fun c -> counto_distincto (inj_matrix matrix) c, 1 answer {
    q=S (S (S (O)));
    } |}];
  let matrix = [ [ 0; 0 ]; [ 0; 0 ]; [ 0; 0 ]; [ 0; 0 ] ] in
  test_counto_distincto_fwd matrix;
  [%expect
    {|
    [[0; 0]; [0; 0]; [0; 0]; [0; 0]]
    fun c -> counto_distincto (inj_matrix matrix) c, 1 answer {
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
    q=([[0; 0]; [0; 0]; [0; 0]; [0; 0]; [0; 0]], S (O));
    q=([[0; 1]; [0; 0]; [0; 0]; [0; 0]; [0; 0]], S (S (O)));
    } |}]

let%expect_test _ =
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
  test_main_submatrix ~verbose:false ~n:5 ~xlen numbers ~index_count:2 2;
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
    q=[[0; 1]; [0; 0]; [0; 0]; [0; 0]; [0; 0]];
    q=[[0; 1]; [0; 0]; [0; 0]; [0; 0]; [0; 0]];
    q=[[0; 0]; [0; 1]; [0; 0]; [0; 0]; [0; 0]];
    q=[[0; 1]; [0; 1]; [0; 0]; [0; 0]; [0; 0]];
    q=[[0; 0]; [0; 1]; [0; 0]; [0; 0]; [0; 0]];
    } |}]

let%expect_test _ =
  test_main_anyindex_anysubmatrix ~n:1 4 [ 3; 1; 0; 0; 0 ] 3;
  [%expect
    {|
    Distinct count = 3, xlen = 4
    	[0; 0; 1; 1]
    	[0; 0; 0; 1]
    	[0; 0; 0; 0]
    	[0; 0; 0; 0]
    	[0; 0; 0; 0]
    fun pair ->
      fresh (index_count submatrix) (pair === (Std.pair index_count submatrix))
        (main_rel ~verbose (inj_matrix matrix) ~index_count submatrix
           (Std.nat distinct_count)), 1 answer {
    q=(S (S (O)), [[1; 1]; [0; 1]; [0; 0]; [0; 0]; [0; 0]]);
    } |}];
  (* test1 8 [ 255; 127; 16; 8; 7 ] 2;
     print_endline "Looking for 3 distinct values";
     test1 8 [ 255; 127; 16; 8; 7 ] 3;
     test1 3 [ 7; 5; 0; 0; 0 ] 3; *)
  test_main_anyindex_anysubmatrix ~n:5 8 [ 223; 93; 18; 10; 5 ] 5;

  [%expect
    {|
    Distinct count = 5, xlen = 8
    	[1; 1; 0; 1; 1; 1; 1; 1]
    	[0; 1; 0; 1; 1; 1; 0; 1]
    	[0; 0; 0; 1; 0; 0; 1; 0]
    	[0; 0; 0; 0; 1; 0; 1; 0]
    	[0; 0; 0; 0; 0; 1; 0; 1]
    fun pair ->
      fresh (index_count submatrix) (pair === (Std.pair index_count submatrix))
        (main_rel ~verbose (inj_matrix matrix) ~index_count submatrix
           (Std.nat distinct_count)), 5 answers {
    q=(S (S (S (O))), [[1; 1; 1]; [0; 1; 1]; [0; 1; 0]; [0; 0; 1]; [0; 0; 0]]);
    q=(S (S (S (S (O)))), [[1; 1; 1; 1]; [0; 1; 1; 1]; [0; 0; 1; 0]; [0; 0; 0; 1]; [0; 0; 0; 0]]);
    q=(S (S (S (S (O)))), [[1; 0; 1; 1]; [0; 0; 1; 1]; [0; 0; 1; 0]; [0; 0; 0; 1]; [0; 0; 0; 0]]);
    q=(S (S (S (S (S (O))))), [[1; 1; 0; 1; 1]; [0; 1; 0; 1; 1]; [0; 0; 0; 1; 0]; [0; 0; 0; 0; 1]; [0; 0; 0; 0; 0]]);
    q=(S (S (S (O))), [[1; 1; 1]; [0; 1; 1]; [0; 1; 0]; [0; 0; 0]; [0; 0; 1]]);
    } |}];
  ()

let%expect_test _ =
  let xlen = 5 in
  let numbers = [ 5; 3 ] in
  test_reconstruct_submatrix xlen numbers [];
  [%expect
    {|

  xlen = 5
  indicies = []
  	[0; 0; 1; 0; 1]
  	[0; 0; 0; 1; 1]
  fun submatrix ->
    reconstruct_submatrix ~verbose (Std.list Std.nat indices)
      (inj_matrix matrix) submatrix, 1 answer {
  q=[[]; []];
  }|}];

  test_reconstruct_submatrix ~n:2 3 numbers [ 1; 2; 3 ];
  [%expect
    {|
    xlen = 3
    indicies = [1; 2; 3]
    	[1; 0; 1]
    	[0; 1; 1]
    fun submatrix ->
      reconstruct_submatrix ~verbose (Std.list Std.nat indices)
        (inj_matrix matrix) submatrix, 2 answers {
    q=[[1; 0; 1]; [0; 1; 1]];
    } |}];
  test_reconstruct_submatrix ~n:2 3 numbers [ 1; 3 ];
  [%expect
    {|
      xlen = 3
      indicies = [1; 3]
      	[1; 0; 1]
      	[0; 1; 1]
      fun submatrix ->
        reconstruct_submatrix ~verbose (Std.list Std.nat indices)
          (inj_matrix matrix) submatrix, 2 answers {
      q=[[1; 1]; [0; 1]];
      } |}];
  ()

let%expect_test _ =
  test_main2 ~verbose:true ~n:2 2 [ 2; 1 ] 2;
  [%expect
    {|
    xlen = 2, distinct_count = 2
    	[1; 0]
    	[0; 1]
    fun pair ->
      fresh (submatrix indicies) (pair === (Std.pair submatrix indicies))
        (main2 ~verbose (inj_matrix matrix) indicies ~submatrix
           (Std.nat distinct_count)), 2 answers {
    } |}];
  (* test_main2 ~n:1 8 [ 223; 93; 18; 10; 5 ] 4; *)
  (* *)
  test_main2 ~verbose:true ~n:1 1 [ 1 ] 1;
  [%expect
    {|
    xlen = 1, distinct_count = 1
    	[1]
    fun pair ->
      fresh (submatrix indicies) (pair === (Std.pair submatrix indicies))
        (main2 ~verbose (inj_matrix matrix) indicies ~submatrix
           (Std.nat distinct_count)), 1 answer {
    c0 = O, c1 = S (O), total = S (O)
    head0 = [], head1 = [[]] , m = [[1]]
    HERR
    q=([[1]], [S (O)]);
    } |}];
  test_main2 ~verbose:true ~n:1 2 [ 3; 1; 0 ] 1;
  [%expect
    {|
    xlen = 2, distinct_count = 1
    	[1; 1]
    	[0; 1]
    	[0; 0]
    fun pair ->
      fresh (submatrix indicies) (pair === (Std.pair submatrix indicies))
        (main2 ~verbose (inj_matrix matrix) indicies ~submatrix
           (Std.nat distinct_count)), 1 answer {
    } |}];
  (* let matrix = [ [ 1 ] ] in *)
  (* test_groupo_fwd ~n:1 matrix;
     [%expect {|

       } |}]; *)
  (* let open Tester in
     [%tester
       run_r Std.Nat.reify (GT.show Std.Nat.logic) 2 (fun count0 count1 ->
           let open Std in
           fresh (head0 head1)
             (groupo (inj_matrix matrix) ~head1 head0)
             (conde
                [
                  head0 === Std.nil () &&& (count0 === Nat.zero);
                  head0 =/= nil () &&& (count0 === Nat.one);
                ])
             (conde
                [
                  head1 === nil () &&& (count1 === Nat.zero);
                  head1 =/= nil () &&& (count1 === Nat.one);
                ])
             (Nat.addo count0 count1 (Std.nat 2)))]; *)
  [%expect {| |}];
  ()

let test_reconstruct_submatrix3 ?(verbose = false) ?(n = 1) ~xlen numbers
    indices =
  let _ = verbose in
  assert (List.for_all (fun x -> x > 0) indices);
  Printf.printf "\nxlen = %d\n" xlen;
  Printf.printf "indicies = %s\n" (GT.show GT.list (GT.show GT.int) indices);

  let matrix = Matrix1.inj_numbers ~xlen numbers in
  let indices = List1.inj_list Std.nat indices in
  (* print_matrix matrix; *)
  let open Tester in
  [%tester
    run_r [%reify: Matrix1.t] Matrix1.show_logic n (fun submatrix ->
        reconstruct_submatrix3 ~verbose indices matrix submatrix)]

let%expect_test "reconstruct submatrix 3" =
  print_endline "asdf";
  [%expect {| asdf |}];
  test_reconstruct_submatrix3 ~xlen:3 [ 5; 3; 1 ] [ 1 ];
  [%expect {| asdf |}];
  [%expect {| asdf |}];
  [%expect {| asdf |}];
  [%expect {| asdf |}]
