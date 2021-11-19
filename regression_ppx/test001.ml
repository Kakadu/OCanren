open OCanren
open Tester

module _ = struct
  [%%distrib
    type nonrec 'a t = Z | S of 'a [@@deriving gt ~options:{gmap; show}]
    type ground = ground t
  ]

  let run_peano n = run_new reify  (GT.show logic) n

  let s x  = inji (S x)
  let z () = inji Z
  let () =
    run_peano 1 q qh (REPR(fun q -> q === z ()));
    run_peano 1 q qh (REPR(fun q -> q === s (z ())));
end

module _ = struct
  (* [%%distrib
    type nonrec 'a t = None | Some of 'a [@@deriving gt ~options:{gmap}]
    type 'a ground = 'a t
  ] *)
end
