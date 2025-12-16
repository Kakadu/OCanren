module _ = struct

  [%%ocanren_inject
    type aa = A of bb
    and bb = aa GT.list
  ]
end

let () = print_endline "test007"
