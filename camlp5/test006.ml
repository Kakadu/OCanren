
[%%ocanren_inject
  type aa = A of bb
  and bb = aa GT.list
  [@@deriving gt ~options:{gmap}]
]


(* let () = print_endline "test007" *)
