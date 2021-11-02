open GT
open OCanren
open Tester

module X = struct
  @type 'a t = A of 'a | Var1 of int with show,gmap
  type nonrec 'a logic = 'a t logic
  type nonrec 'a ilogic = 'a t ilogic

  let fmap f x = gmap(t) f x

  let prj : 'a 'b. ('a, 'b) Reifier.t -> ('a ilogic, 'b t) Reifier.t
        =
     fun ra ->
      let ( >>= ) = Env.Monad.bind in
      Reifier.prj_exn >>= fun r ->
      ra >>= fun fa ->
      Env.Monad.return (fun x -> GT.gmap t fa
        (try r x
         with Not_a_value -> Var1 5))


  let a x     = inj (A x)
end

module Y = struct
  @type 'a t = B of 'a | Var2 of int with show,gmap
  type nonrec 'a logic = 'a t logic
  type nonrec 'a ilogic = 'a t ilogic

  (* TODO: rewrite without exceptions *)
  let prj : 'a 'b. ('a, 'b) Reifier.t -> ('a ilogic, 'b t) Reifier.t =
     fun ra ->
      let ( >>= ) = Env.Monad.bind in
      Reifier.prj_exn >>= fun r ->
      ra >>= fun fa -> Env.Monad.return (fun x -> GT.gmap t fa
        (try r x
         with Not_a_value -> Var2 5))


  let b x = inj (B x)
end

let prjc_xy = X.prj (Y.prj OCanren.prj)
  (* X.prjc (Y.prjc (OCanren.prjc (fun _ -> assert false)) (fun n _ -> Y.Var2 n))
    (fun n _ -> X.Var1 n) h t
 *)
let showxy_int = show X.t @@ (show Y.t (show int))

let runResult n = run_new prjc_xy showxy_int n

let () =
  runResult     (-1) q qh (REPR(fun q -> Fresh.one (fun r -> q === q )));
  runResult     (-1) q qh (REPR(fun q -> Fresh.two (fun r s -> (r=/=s) &&& (q===(X.a r))) ));
  ()
