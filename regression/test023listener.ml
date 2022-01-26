open OCanren
open OCanren.Std
(* open GT *)

let show_llist =
  (* [%show: int OCanren.logic Std.List.logic] *)
  GT.show(List.logic) (GT.show(logic) (string_of_int))

let p : (int List.ground, int logic List.logic) printer = fun rr ->
  show_llist @@ rr#reify (List.reify OCanren.reify)

let rec appendo a b ab =
  let trace_answ = ((Trace.(trace three)) (fun q r s -> Listener.Answer ("appendo", [p q; p r; p s])) a b ab success) in
  Trace.(trace three) (fun q r s -> Listener.Goal ("appendo", [p q; p r; p s])) a b ab
  (conde
    [ ((unify ~p a @@ nil ()) &&& (unify ~p b ab)) (*&&& trace_answ*)
    ; fresh (h t ab')
        (unify ~p a (h%t))
        (unify ~p (h%ab') ab)
        (appendo t b ab')
        (* (trace_answ) *)
    ]
    &&&
      (trace_answ)
  )

let rec reverso a b =
  let trace_answ = ((Trace.(trace two)) (fun q r -> Listener.Answer ("reverso", [p q; p r])) a b success) in
  Trace.(trace two) (fun q r -> Listener.Goal ("reverso", [p q; p r])) a b
  (conde
    [ ((unify ~p a @@ nil ()) &&& (unify ~p b @@ nil ())) (*&&& trace_answ*)
    ; fresh (h t a')
        (unify ~p a (h%t))
        (appendo a' !<h b)
        (defer (reverso t a'))
        (* (trace_answ) *)
    ]
    &&&
      (trace_answ)
  )

let rec appendo a b ab =
  let trace_answ =
    (Trace.(trace three))
      (fun q r s -> Listener.Answer ("appendo", [p q; p r; p s ]))
      a b ab success in
  Trace.(trace three)
    (fun q r s -> Listener.Goal ("appendo rec", [p q; p r; p s]))
    a b ab
    (let (===) eta = unify ~p eta in
      conde
      [ (( a === nil ()) &&& (b === ab))
      ; fresh (h t ab2)
          (debug_lino __FILE__ __LINE__)
          (a === (h%t))
          (appendo t b ab2)
          (defer (ab === (h % ab2)))
          (trace_answ)
      ]
      &&&
        (trace_answ)
    )

let f a b = (a === b) &&& (b === !!1)

let g a b = ?& [(a === b); (b === !!1); (a === !!2)]

(* let filter = function
  | "reverso" -> true
  | _ -> false *)

let () =
  let logger = TreeLogger.create () in
  let stream = run ~listener:(logger :> Listener.t) q (fun q -> reverso q q) (fun qs -> qs) in
  let _ = Stream.take ~n:4 stream in
  logger#print Format.std_formatter

let () =
  let logger = TreeLogger.create () in
  let stream =
    run ~listener:(logger :> Listener.t) qr
      (fun q r -> appendo q r (Std.List.list [!!1; !!2 ])) (fun qs rs  -> qs,rs)
  in
  let _ = Stream.take ~n:1 stream in
  logger#print Format.std_formatter
