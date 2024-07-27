open Bits

let measure f x =
  let start = Mtime_clock.elapsed () in
  let rez = f x in
  let span = Mtime.Span.abs_diff (Mtime_clock.elapsed ()) start in
  (Mtime.Span.to_float_ns span /. 1e9, rez)

let () =
  let sec, () =
    measure (fun () -> test_main_anyindex_anysubmatrix ~n:1 16 [ 0; 1 ] 2) ()
  in
  Printf.printf "total %f seconds\n" sec;
  ()
