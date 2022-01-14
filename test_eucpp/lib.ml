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

  let reify : (ilogic, logic) Reifier.t =
    let open Env.Monad.Syntax in
    Reifier.fix (fun self ->
        Format.printf "%s %d\n%!" __FILE__ __LINE__;
        let* rself = self in
        Format.printf "%s %d\n%!" __FILE__ __LINE__;
        Reifier.compose
          Reifier.reify
          (let rec foo = function
             | Var (v, xs) -> Var (v, Stdlib.List.map foo xs)
             | Value t -> Value (Option.map rself t)
           in
           Env.Monad.return foo))
  ;;

  let test () =
    let goal q = fresh x (q === inji @@ Some x) in
    let xs : logic Stream.t = OCanren.(run q) goal (fun rr -> rr#reify reify) in
    match Stream.take xs with
    | [ Value (Some (Var (_, _))) ] -> true
    | _ -> false
  ;;

  (* let%test _ = test () *)
end

module TestNat = struct
  open Std.Nat

  let reify : (groundi, Std.Nat.logic) Reifier.t =
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
  let reify0 : (groundi, Std.Nat.logic) Reifier.t =
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

  let reify0 =
    let rec self : (groundi, Std.Nat.logic) Reifier.t Lazy.t =
      let open Env.Monad.Syntax in
      lazy
        (let* r = OCanren.reify in
         let open Env.Monad in
         self
         >>>= fun fr ->
         let rec foo : Std.Nat.injected -> Std.Nat.logic =
          fun x ->
           match r x with
           | Var (v, xs) ->
             Var (v, Stdlib.List.map (GT.gmap OCanren.logic (GT.gmap Std.Nat.t foo)) xs)
           | Value x -> Value (GT.gmap t (Lazy.force fr) x)
         in
         Env.Monad.return foo)
    in
    Lazy.force self
  ;;

  let test () =
    let goal q = fresh x (q === inji @@ S x) in
    let xs : logic Stream.t = OCanren.(run q) goal (fun rr -> rr#reify reify0) in
    match Stream.take xs with
    | [ Value (S (Var (_, _))) ] -> true
    | _ -> false
  ;;
end

module TestNat2 = struct
  type 'a t =
    | O
    | S of 'a
  [@@deriving gt ~options:{ gmap }]

  type 'a ground = 'a t
  type 'a logic = 'a t OCanren.logic
  type 'a injected = 'a t ilogic

  (*

 let rec reify =
  fun ra -> lazy
    (Reifier.reify >>= (fun r -> ra >>= (fun fa -> reify ra >>>= (fun fr ->
         Env.return (fun x -> match r x with
             | Var _ as v -> v
             | Value t -> Value (fmap fa (Lazy.force fr) t))))))

             *)
  (* let reify0 =
    let rec self : ('a, 'b) Reifier.t Lazy.t -> ('a injected, 'b logic) Reifier.t Lazy.t =
     fun ra ->
      let open Env.Monad.Syntax in
      lazy
        (let* r = OCanren.reify in
         let open Env.Monad in
         ra
         >>>= fun fa ->
         let rec foo : 'a injected -> 'b logic =
          fun x ->
           match r x with
           | Var (v, xs) ->
             Var (v, Stdlib.List.map (GT.gmap OCanren.logic (GT.gmap t foo)) xs)
           | Value x -> Value (GT.gmap t (Lazy.force fa) x)
         in
         Env.Monad.return foo)
    in
    fun ra -> Lazy.force (self (lazy ra))
  ;; *)

  (* let test () =
    let goal q = fresh x (q === inji @@ S x) in
    let xs : _ logic Stream.t =
      OCanren.(run q) goal (fun rr -> rr#reify (reify0 OCanren.reify))
    in
    match Stream.take xs with
    | [ Value (S (Var (_, _))) ] -> true
    | _ -> false
  ;; *)
end
