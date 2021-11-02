open OCanren

(* example of reifiers for custom types *)
module TestOption = struct
  open OCanren.Std

  (* test projection *)
  let%test _ =
    let goal q = q === inji @@ Some (inji 42) in
    let xs : int option Stream.t =
      OCanren.(run q) goal (fun rr -> rr#reify (Std.Option.prj Reifier.prj_exn))
    in
    match Stream.take xs with
    | [ Some 42 ] -> true
    | _ -> false
  ;;

  (* test reification *)
  let%test _ =
    let goal q = q === inji @@ Some (inji 42) in
    let xs : int logic Option.logic Stream.t =
      OCanren.(run q) goal (fun rr -> rr#reify (Option.reify Reifier.reify))
    in
    match Stream.take xs with
    | [ Value (Some (Value 42)) ] -> true
    | _ -> false
  ;;

  let%test _ =
    let goal q = success in
    let xs : int logic Option.logic Stream.t =
      OCanren.(run q) goal (fun rr -> rr#reify (Option.reify Reifier.reify))
    in
    match Stream.take xs with
    | [ Var (_, _) ] -> true
    | _ -> false
  ;;

  let%test _ =
    let goal q = fresh x (q === inji @@ Some x) in
    let xs : int logic Option.logic Stream.t =
      OCanren.(run q) goal (fun rr -> rr#reify (Option.reify Reifier.reify))
    in
    match Stream.take xs with
    | [ Value (Some (Var (_, _))) ] -> true
    | _ -> false
  ;;
end
