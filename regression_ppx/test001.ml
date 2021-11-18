open OCanren
module Fmap1(X:sig end) = struct
  let distrib _ = Obj.magic ()
  let reify _ = Obj.magic ()
end

[%%distrib
  type nonrec 'a t = Z | S of 'a [@@deriving gt ~options:{gmap}]
  type ground = ground t
]
