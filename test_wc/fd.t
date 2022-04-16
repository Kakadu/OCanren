  $ ./fd.exe
  fun q -> fresh x (q =/= (pair __ (!! 1))) (q === (pair (!! 1) __)), all answers {
  q=(1, _.12 [=/= 1]);
  }
  fun q -> fresh () (FD.domain q [1; 2]), all answers {
  q=_.10;
  }
  fun q -> fresh () (FD.domain q [1; 2]) (q =/= (!! 1)), all answers {
  q=_.10 [=/= 1];
  }
  fun q -> fresh () (FD.domain q [1; 2]) (q =/= (!! 1)) (q =/= (!! 2)), all answers {
  }
  fun q -> fresh () (FD.domain q [1; 2]) (FD.neq q (!! 1)) (FD.neq q (!! 2)), all answers {
  }
  fun q -> fresh x (q =/= (Option.some __)) (q === (Option.some x)), all answers {
  q=Some (_.11);
  }
  fun q ->
    fresh x (q =/= (Option.some __)) (q === (Option.some x))
      cut_off_wc_diseq_without_domain, all answers {
  }
  fun q ->
    fresh x (q =/= (Option.some __)) (FD.domain x [1; 2]) (x =/= (!! 1))
      (x =/= (!! 2)) (q === (Option.some x)), all answers {
  }
  	To repair the next example we should decide existance of the answer in the moment of reification 
  fun q ->
    fresh x (q =/= (Option.some __)) (FD.domain x [1; 2; 3]) (x =/= (!! 1))
      (x =/= (!! 2)) (q === (Option.some x)), all answers {
  q=Some (_.11 [=/= 1; =/= 2]);
  }
  fun q ->
    fresh _11 (FD.domain _11 [1; 2]) (_11 =/= (!! 2)) (q =/= (pair _11 __))
      (q === (pair (!! 1) (!! 1))), all answers {
  }
  fun q ->
    fresh _11 (FD.domain _11 [1; 2]) (_11 =/= (!! 2)) (q === (pair _11 __))
      (q =/= (pair (!! 1) __)), all answers {
  }
  fun q ->
    fresh _11 (FD.domain _11 [1; 2]) (q =/= (pair _11 __))
      (q === (pair (!! 1) (!! 1))) (_11 =/= (!! 2)), all answers {
  }
  fun q ->
    fresh () (q =/= (!! 1)) (FD.domain q [1; 2]) trace_domain_constraints
      (q =/= (!! 2)) success, all answers {
  {| {10} ∈ {1, 2} |}.
  []
  }
  fun q -> fresh () (q =/= (!! 1)) (q =/= (!! 2)) (FD.domain q [1; 2]) success, all answers {
  }
