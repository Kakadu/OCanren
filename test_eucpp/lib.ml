open OCanren

(* example of reifiers for custom types *)
module TestOption = struct
  open OCanren.Std

  (* test projection *)
  let%test _ =
    let goal q = q === inji @@ Some (inji 42) in
    let xs : int option Stream.t =
      OCanren.(run q) goal (fun rr -> rr#reify (Std.Option.prj_exn Reifier.prj_exn))
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

module TestNestedOption = struct
  type 'a t = 'a option
  type ground = ground t
  type logic = logic t OCanren.logic
  type ilogic = ilogic t OCanren.ilogic

  let reify_with_compose : (ilogic, logic) Reifier.t =
    let open Env.Monad.Syntax in
    Reifier.fix (fun self ->
        (* Format.printf "%s %d\n%!" __FILE__ __LINE__; *)
        let* rself = self in
        (* Format.printf "%s %d\n%!" __FILE__ __LINE__; *)
        Reifier.compose
          Reifier.reify
          (let rec foo = function
             | Var (v, xs) -> Var (v, Stdlib.List.map foo xs)
             | Value t -> Value (Option.map rself t)
           in
           Env.Monad.return foo))
  ;;

  let reify : (ilogic, logic) Reifier.t =
    let open Env.Monad.Syntax in
    Reifier.fix (fun self ->
        (* Format.printf "%s %d\n%!" __FILE__ __LINE__; *)
        let* rself = self in
        (* Format.printf "%s %d\n%!" __FILE__ __LINE__; *)
        let* r = Reifier.reify in
        let rec foo x =
          match r x with
          | Var (v, xs) ->
            let (_ : 'a OCanren.logic list) = xs in
            Var
              (v, Stdlib.List.map (GT.gmap OCanren.logic (GT.gmap Std.Option.t rself)) xs)
            (* Var (v, []) *)
          | Value t -> Value (Option.map rself t)
        in
        Env.Monad.return foo)
  ;;

  let test reifier =
    let goal q = fresh x (q === inji @@ Some x) in
    let xs : logic Stream.t = OCanren.(run q) goal (fun rr -> rr#reify reifier) in
    match Stream.take xs with
    | [ Value (Some (Var (_, _))) ] -> true
    | _ -> false
  ;;

  let%test _ = test reify_with_compose
  let%test _ = test reify
end

module TestNat = struct
  open Std.Nat

  let reify_with_compose : (groundi, Std.Nat.logic) Reifier.t =
    let open Env.Monad.Syntax in
    Reifier.fix (fun self ->
        Reifier.compose
          Reifier.reify
          (let* fr = self in
           let rec foo = function
             | Var (v, xs) -> Var (v, Stdlib.List.map foo xs)
             | Value x -> Value (GT.gmap t fr x)
           in
           Env.Monad.return foo))
  ;;

  (* works, but we can't move let* fr = self in higher *)
  let reify : (groundi, Std.Nat.logic) Reifier.t =
    let open Env.Monad.Syntax in
    Reifier.fix (fun self ->
        let* fr = self in
        let* r = OCanren.reify in
        let rec foo x =
          match r x with
          | Value x -> Value (GT.gmap t fr x)
          | Var (v, xs) ->
            let (_ : 'a logic' list) = xs in
            Var (v, Stdlib.List.map (GT.gmap logic' (GT.gmap t foo)) xs)
        in
        Env.Monad.return foo)
  ;;

  let test () =
    let goal q = fresh x (q === inji @@ S x) in
    let xs : logic Stream.t = OCanren.(run q) goal (fun rr -> rr#reify reify) in
    match Stream.take xs with
    | [ Value (S (Var (_, _))) ] -> true
    | _ -> false
  ;;

  let%test _ = test ()
end

(* Natural numbers not being tied-in-the-knot *)
module TestNat2 = struct
  type 'a t =
    | O
    | S of 'a
  [@@deriving gt ~options:{ gmap }]

  type 'a ground = 'a t
  type 'a logic = 'a t OCanren.logic
  type 'a injected = 'a t ilogic

  let reify_open : 'a 'b. ('a, 'b) Reifier.t -> ('a injected, 'b logic) Reifier.t =
   fun fa ->
    let open Env.Monad.Syntax in
    Reifier.fix (fun _self ->
        let* (ra : 'a -> 'b) = fa in
        let* r = OCanren.reify in
        let rec foo x =
          match r x with
          | Value x -> Value (GT.gmap t ra x)
          | Var (v, xs) ->
            Var (v, Stdlib.List.map (GT.gmap OCanren.logic (GT.gmap t ra)) xs)
        in
        Env.Monad.return foo)
 ;;

  let test () =
    let goal q = fresh x (q === inji @@ S x) in
    let xs : _ Stream.t =
      OCanren.(run q) goal (fun rr -> rr#reify (reify_open OCanren.reify))
    in
    match Stream.take xs with
    | [ Value (S (Var (_, _))) ] -> true
    | _ -> false
  ;;

  let%test _ = test ()

  let reify : (('a injected as 'a), ('b logic as 'b)) Reifier.t =
    let open Env.Monad.Syntax in
    Reifier.fix (fun self ->
        let* r = OCanren.reify in
        let* rself = self in
        let rec foo x =
          match r x with
          | Value x -> Value (GT.gmap t rself x)
          | Var (v, xs) ->
            Var (v, Stdlib.List.map (GT.gmap OCanren.logic (GT.gmap t rself)) xs)
        in
        Env.Monad.return foo)
  ;;

  let test () =
    let goal q = fresh x (q === inji @@ S x) in
    let xs : _ Stream.t = OCanren.(run q) goal (fun rr -> rr#reify reify) in
    match Stream.take xs with
    | [ Value (S (Var (_, _))) ] -> true
    | _ -> false
  ;;

  let%test _ = test ()
end
