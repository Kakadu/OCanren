open Printf
open GT
open OCanren
open OCanren.Std
open Tester

@type token = Id | Add | Mul with show

let (!!) x = inj (lift x)
let show_token = show(token)

module GExpr = struct


  @type 'self t  = I | A of 'self * 'self | M of 'self * 'self
    with show, gmap

  include Fmap1(struct 
    type nonrec 'a t = 'a t
    let fmap f x = gmap(t) f x
  end)

  type ground = ground t
  type logic = logic t OCanren.logic
  type fexpr = (ground, logic) OCanren.injected

  let rec show_expr  e = show t show_expr e
  let rec show_lexpr e = show(logic) (show t show_lexpr) e

  let fmapt fa  subj =
    let open Env.Monad in
    Env.Monad.return (GT.gmap t) <*> fa <*> subj
  
  let reify: (ground, logic) Reifier.t =
    let open Env.Monad in
    Reifier.fix (fun self ->
      Reifier.reify <..>
        chain (Reifier.zed (Reifier.rework ~fv:(fmapt self))))

  let prj_exn : (ground, ground) Reifier.t =
    let open Env.Monad in
    Reifier.fix (fun self ->
      Reifier.prj_exn <..> chain (fmapt self))
  let i ()  : fexpr = inj @@ distrib I
  let a a b : fexpr = inj @@ distrib @@ A (a,b)
  let m a b : fexpr = inj @@ distrib @@ M (a,b)

end

open GExpr


let sym t i i' =
  fresh (x xs)
    (i === x%xs) (t === x) (i' === xs)

let eof i = i === nil ()

let (|>) x y = fun i i'' r'' ->
  fresh (i' r')
    (x i  i' r')
    (y r' i' i'' r'')

let (<|>) x y = fun i i' r ->
  conde [x i i' r; y i i' r]

let rec pId n n' r = (sym (inj (lift Id)) n n') &&& (r === i())
and pAdd i i' r = (pMulPlusAdd <|> pMul) i i' r
and pMulPlusAdd i i' r = (
      pMul |>
      (fun r i i'' r'' ->
         fresh (r' i')
           (sym !!Add i i')
           (r'' === (a r r'))
           (pAdd i' i'' r')
      )) i i' r
and pMul i i' r = (pIdAstMul <|> pId) i i' r
and pIdAstMul i i' r = (
      pId |>
      (fun r i i'' r'' ->
         fresh (r' i')
           (sym !!Mul i i')
           (r'' === (m r r'))
           (pMul i' i'' r')
      )) i i' r
and pTop i i' r = pAdd i i' r

let pExpr i r = fresh (i') (pTop i i' r) (eof i')

let runE_exn n = run_r GExpr.prj_exn GExpr.show_expr n
let show_stream xs = show(List.ground) show_token xs
let run_stream n = run_r (List.prj_exn OCanren.prj_exn) show_stream n

let _ =
  runE_exn   1   q   qh (REPR (fun q -> pExpr (list (!!) [Id]) q                  ));
  runE_exn   1   q   qh (REPR (fun q -> pExpr (list (!!) [Id; Mul; Id]) q         ));
  runE_exn   1   q   qh (REPR (fun q -> pExpr (list (!!) [Id; Mul; Id; Mul; Id]) q));
  runE_exn   1   q   qh (REPR (fun q -> pExpr (list (!!) [Id; Mul; Id; Add; Id]) q));
  runE_exn   1   q   qh (REPR (fun q -> pExpr (list (!!) [Id; Add; Id; Mul; Id]) q));
  runE_exn   1   q   qh (REPR (fun q -> pExpr (list (!!) [Id; Add; Id; Add; Id]) q));
  run_stream 1   q   qh (REPR (fun q -> pExpr q (m (i ()) (i ()))        ));
  ()
