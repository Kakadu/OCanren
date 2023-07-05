  $ ../ppx/pp_ocanren_all.exe  test012mutual.ml -pretty -new-typenames
  let () = print_endline "test012"
  type nonrec ('a, 'a0) targ_fuly =
    | T of 'a0 * 'a [@@deriving gt ~options:{ gmap }]
  type nonrec ('a, 'a1, 'a0) jtyp_fuly =
    | Array of 'a1 
    | V of 'a0 [@@deriving gt ~options:{ gmap }]
  type 'a targ_logic = ('a, 'a jtyp_logic) targ_fuly OCanren.logic
  and 'a jtyp_logic =
    ('a, 'a jtyp_logic, 'a targ_logic) jtyp_fuly OCanren.logic[@@deriving
                                                                gt
                                                                  ~options:
                                                                  { gmap
                                                                  }]
  let __ (type a) (type b) =
    (fun eta -> GT.gmap jtyp_logic eta : (a -> b) ->
                                           a jtyp_logic -> b jtyp_logic)

  $ ./test012mutual.exe
  test012
