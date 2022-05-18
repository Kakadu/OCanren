  $ ./test031wc.exe
  line 96
  fun q ->
    wc
      (fun __ ->
         delay
           (fun () ->
              conj (conj (q === pair __ !!1) (q === pair !!1 __))
                (q === pair !!2 !!1))), all answers {
  q=(_.-42, 1);
  }
