  $ ./match.exe
  Pseudecode:
  
      match ... with
      | t,_ -> 1
      | _,_ -> 2
    
  Naive with diseq constraints (6 answers instead of 4): 
  fun q ->
    fresh (scru rhs) (q === (pair scru rhs)) (rel scru rhs)
      (fresh (l r) (scru === (Std.pair l r)) (bool_dom l) (bool_dom r)), all answers {
  q=((true, false), 1);
  q=((true, true), 1);
  q=((false, false), 2);
  q=((true, false), 2);
  q=((false, true), 2);
  q=((true, true), 2);
  }
  With wildcards: 
  fun q ->
    fresh (scru rhs) (q === (pair scru rhs)) (rel scru rhs)
      (fresh (l r) (scru === (Std.pair l r)) (bool_dom l) (bool_dom r)), all answers {
  q=((true, false), 1);
  q=((false, false), 2);
  q=((true, true), 1);
  q=((false, true), 2);
  }
  *******
  
  Longer example for Luc's Maranget paper
  Pseudecode:
  
      match ... with
      | _,f,t -> 1
      | f,t,_ -> 2
      | _,_,f -> 3
      | _,_,t -> 4
    
  With wildcards: 
  fun q ->
    fresh (scru rhs l m r) (q === (pair scru rhs)) (rel scru rhs)
      (scru === (Std.triple l m r)) (bool_dom l) (bool_dom m) (bool_dom r), all answers {
  q=((false, false, true), 1);
  q=((true, false, true), 1);
  q=((false, true, false), 2);
  q=((false, true, true), 2);
  q=((false, false, false), 3);
  q=((true, false, false), 3);
  q=((true, true, true), 4);
  q=((true, true, false), 3);
  }
  fun rhs -> fresh s (s === (Std.triple (!! true) __ __)) (smart_rel s rhs), all answers {
  q=1;
  q=3;
  q=4;
  }
  HACK
  fun q ->
    fresh (scru rhs l m r) (q === (pair scru rhs)) (hack scru rhs) success, all answers {
  q=((_.16 [=/= false], _.17 [=/= false], true), 4);
  q=((_.16, _.17 [=/= false; =/= true], true), 4);
  }
