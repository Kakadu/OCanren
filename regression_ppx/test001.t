  $ ../ppx/pp_distrib.exe test001.ml | ocamlformat --impl --enable-outside-detected-project --profile=compact -
  include
    struct
      type nonrec 'a t =
        | Z
        | S of 'a [@@deriving gt ~options:{ gmap }]
      module Distribs_t =
        (Fmap1)(struct
                  let rec fmap _eta = GT.gmap t _eta
                  type nonrec 'a t = 'a t
                end)
      let z () = inj (Distribs_t.distrib Z)
      let s a0 = inj (Distribs_t.distrib (S a0))
      type ground = ground t[@@deriving gt ~options:{ gmap }]
      type logic = logic t OCanren.logic[@@deriving gt ~options:{ gmap }]
      let rec reify eta = (Distribs_t.reify reify) eta
    end
$ OCAMLRUNPARAM=b ./test001.exe
  $ ./test001.exe
