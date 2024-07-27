$ ls
  $ ./bits_run.exe
  
  Distinct count = 2, xlen = 16
  	[0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0]
  	[0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 1]
  fun pair ->
    fresh (index_count submatrix) (pair === (Std.pair index_count submatrix))
      (main_rel ~verbose (inj_matrix matrix) ~index_count submatrix
         (Std.nat distinct_count)), 1 answer {
  q=(S (O), [[0]; [1]]);
  }
  total 19.671508 seconds
