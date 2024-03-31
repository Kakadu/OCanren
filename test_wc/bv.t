  $ ./bv.exe
  fun ph -> evalo ph (!! true), 10 answers {
  q=LE (Const ([1; 0]), Const ([1; 0]));
  q=LE (Const ([1; 0]), Const ([0; 1]));
  q=LE (Const ([1; 0]), Const ([1; 1]));
  q=Not (LE (Const ([0; 1]), Const ([1; 0])));
  q=Not (LE (Const ([1; 1]), Const ([1; 0])));
  q=LE (Const ([0; 1]), Const ([0; 1]));
  q=Not (LE (Const ([1; 1]), Const ([0; 1])));
  q=LE (Const ([0; 1]), Const ([1; 1]));
  q=LE (Const ([1; 1]), Const ([1; 1]));
  }
