  $ ./debug_var.exe
  fun q -> trace_int q, all answers {
  _.10
  q=_.10;
  }
  fun q -> (q === (!! 1)) &&& (trace_int q), all answers {
  1
  q=1;
  }
  fun q -> (q =/= (!! 1)) &&& (trace_int q), all answers {
  _.10 [=/= 1]
  q=_.10 [=/= 1];
  }
  fun q -> (q =/= (Std.pair (!! 1) (!! 2))) &&& (trace_pair q), all answers {
  _.10 [=/= (1, 2)]
  q=_.10 [=/= (1, 2)];
  }
  fun q ->
    fresh (x y) (q =/= (Std.pair x y)) (x =/= (!! 1)) (y =/= (!! 2))
      (trace_pair q), all answers {
  _.10 [=/= (_.11 [=/= 1], _.12 [=/= 2])]
  q=_.10 [=/= (_.11 [=/= 1], _.12 [=/= 2])];
  }
