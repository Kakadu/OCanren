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
  [%%distrib
    type nonrec 'a t = None | Some of 'a [@@deriving gt ~options:{gmap;show}]
    type nonrec  'a ground = 'a t
  ]

  let some x  = inji (Some x)
  let none  () = inji None

  let run_option n = run_new (reify OCanren.reify)  (GT.show logic (GT.show OCanren.logic (GT.show GT.int))) n
  let () =
    run_option 1 q qh (REPR(fun q -> q === none ()));
    run_option 1 q qh (REPR(fun q -> fresh (x) (q === some x) ));
    run_option 1 q qh (REPR(fun q -> fresh (x) (q === some !!42) ));
end

module _ = struct
  [%%distrib
    type nonrec ('a,'b) t = [] | (::) of 'a * 'b [@@deriving gt ~options:{gmap;show}]
    type   'a ground = ('a, 'a ground) t
  ]

  let cons x xs = inji (x::xs)
  let nil () = inji []

  let run_list n = run_new (reify OCanren.reify) (GT.show logic (GT.show OCanren.logic (GT.show GT.int))) n
  let () =
    run_list 1 q qh (REPR(fun q -> q === nil ()));
    run_list 1 q qh (REPR(fun q -> fresh (x) (q === cons x (nil())) ));

end
