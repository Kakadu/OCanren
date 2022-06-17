  $ ./unique.exe
  fun q -> let g _ = failure in Unique.unique_answers g q, all answers {
  q=NoAnswer;
  }
  fun q -> let g x = x === (!! 1) in Unique.unique_answers g q, all answers {
  q=Unique (1);
  }
  fun q -> let g x = conde [x === (!! 1)] in Unique.unique_answers g q, all answers {
  q=Unique (1);
  }
  fun q ->
    let g x = conde [x === (!! 3); x === (!! 4)] in Unique.unique_answers g q, all answers {
  q=DifferentAnswers;
  }
  fun q -> fresh u (is_free u (q === (!! "free")) (q === (!! "nonfree"))), all answers {
  q="free";
  }
  fun q -> all_give_same_answer_or_fail q [(fun q -> q === (!! 1))], all answers {
  q=1;
  }
  fun q ->
    let g1 q = q === (!! 1) in
    let g2 q = conde [q === (!! 1); q === (!! 1)] in
    all_give_same_answer_or_fail q [g1; g2], all answers {
  q=1;
  }
  fun q ->
    let g1 q = q === (!! 1) in
    let g2 q = conde [q === (!! 1); q === (!! 2)] in
    all_give_same_answer_or_fail q [g1; g2], all answers {
  }
  fun q ->
    let g1 q = q === (!! 1) in
    let g2 q = conde [q === (!! 1); q === (!! 1)] in
    let g3 _ = failure in all_give_same_answer_or_fail q [g1; g2; g3], all answers {
  q=1;
  }
  fun q ->
    let g1 q = q === (!! 2) in
    let g2 q = q === (!! 3) in all_give_same_answer_or_fail q [g1; g2], all answers {
  }
  fun q ->
    let g x = conde [x === (!! 1); x === (!! 2)] in
    (q === (Unique.unique (!! 2))) &&& (Unique.unique_answers g q), all answers {
  q=Unique (2);
  }
