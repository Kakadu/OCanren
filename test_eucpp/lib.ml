open OCanren

(* example of reifiers for custom types *)
module TestOption = struct
  module Maybe = struct
    type 'a t = 'a option
    type 'a ground = 'a t
    type nonrec 'a logic = 'a t logic
    type nonrec 'a ilogic = 'a t ilogic

    let fmap : 'a 'b. ('a -> 'b) -> 'a t -> 'b t =
     fun f a ->
      match a with
      | Some a -> Some (f a)
      | None -> None
   ;;

    let reify : 'a 'b. ('a, 'b) Reifier.t -> ('a ilogic, 'b logic) Reifier.t =
     fun ra ->
      let ( >>= ) = Env.Monad.bind in
      Reifier.reify
      >>= fun r ->
      ra
      >>= fun fa ->
      Env.Monad.return (fun x ->
          match r x with
          | Var (v, c) -> Var (v, [])
          | Value t -> Value (fmap fa t))
   ;;

    let prj_exn : 'a 'b. ('a, 'b) Reifier.t -> ('a ilogic, 'b ground) Reifier.t =
     fun ra ->
      let ( >>= ) = Env.Monad.bind in
      Reifier.prj_exn
      >>= fun r -> ra >>= fun fa -> Env.Monad.return (fun x -> fmap fa (r x))
   ;;
  end

  (* test projection *)
  let%test _ =
    let goal q = q === inji @@ Some (inji 42) in
    let xs : int option Stream.t =
      OCanren.(run q) goal (fun rr -> rr#reify (Maybe.prj_exn Reifier.prj_exn))
    in
    match Stream.take xs with
    | [ Some 42 ] -> true
    | _ -> false
  ;;

  (* test reification *)
  let%test _ =
    let goal q = q === inji @@ Some (inji 42) in
    let xs : int logic Maybe.logic Stream.t =
      OCanren.(run q) goal (fun rr -> rr#reify (Maybe.reify Reifier.reify))
    in
    match Stream.take xs with
    | [ Value (Some (Value 42)) ] -> true
    | _ -> false
  ;;

  let%test _ =
    let goal q = success in
    let xs : int logic Maybe.logic Stream.t =
      OCanren.(run q) goal (fun rr -> rr#reify (Maybe.reify Reifier.reify))
    in
    match Stream.take xs with
    | [ Var (_, _) ] -> true
    | _ -> false
  ;;

  let%test _ =
    let goal q = fresh x (q === inji @@ Some x) in
    let xs : int logic Maybe.logic Stream.t =
      OCanren.(run q) goal (fun rr -> rr#reify (Maybe.reify Reifier.reify))
    in
    match Stream.take xs with
    | [ Value (Some (Var (_, _))) ] -> true
    | _ -> false
  ;;
end
