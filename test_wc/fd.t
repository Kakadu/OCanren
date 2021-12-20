  $ ./fd.exe
  fun q -> fresh () (FD.domain q [1; 2]), all answers {
  q=_.10;
  }
  fun q -> fresh () (FD.domain q [1; 2]) (q =/= (!! 1)), all answers {
  q=_.10 [=/= 1];
  }
  fun q -> fresh () (FD.domain q [1; 2]) (q =/= (!! 1)) (q =/= (!! 2)), all answers {
  }
