  $ ./main.exe
  fun q -> q === __, all answers {
  q=_.11;
  }
  fun q -> q =/= __, all answers {
  }
  fun q -> (pair (!! 2) __) =/= (pair __ (!! 2)), all answers {
  }
  fun q -> fresh () (q =/= (pair __ (!! 1))) (q === (pair (!! 1) __)), all answers {
  q=(1, _.11 [=/= 1]);
  }
