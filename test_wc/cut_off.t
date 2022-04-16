  $ ./cut_off.exe
  fun q -> (q =/= __) &&& trace_diseq_constraints, all answers {
  All disjuncts (1)
  	0: [  ] {| 10; |}
  
  q=_.10;
  }
  fun q -> (q =/= __) &&& cut_off_wc_diseq_without_domain, all answers {
  }
  fun q ->
    fresh eargs (q =/= (Expr.pair true_ __)) (q === (e (!! "pair") eargs))
      (eargs === (__ % (__ % (nil ())))) trace_diseq_constraints, all answers {
  All disjuncts (2)
  	0: [  ] {| 13; |}
  	1: [ { _.12 <> 'boxed 0 <string<true>, int<0>>' } ] {| |}
  
  q=E ("pair", [_.12 [=/= E ("true", [])]; _.13]);
  }
