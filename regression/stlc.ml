open Printf
open GT
open OCanren
open OCanren.Std

module GLam = struct
  @type ('varname, 'self) t =
        | V of 'varname
        | App of 'self * 'self
        | Abs of 'varname * 'self
    with show, gmap

  
  type ground = (string, ground) t
  type logic = (string OCanren.logic, logic) t OCanren.logic
  type injected = (ground, logic) OCanren.injected

  include Fmap2(struct 
    type nonrec ('a, 'b) t = ('a, 'b) t
    let fmap f g x = gmap(t) f g x
  end)
  let fmapt fa fb subj =
    let open Env.Monad in
    Env.Monad.return (GT.gmap t) <*> fa <*> fb <*> subj
  
  let v   s   = inj @@ distrib (V s)
  let app x y = inj @@ distrib @@ App (x,y)
  let abs x y = inj @@ distrib @@ Abs (x,y)

  let rec show_rlam term = show(t) (show(string)) show_rlam term
  let rec show_llam term = show(logic) (show(t) (show(logic) @@ show string)show_llam) term

  let reify: (ground, logic) Reifier.t =
    let open Env.Monad in
    Reifier.fix (fun self ->
      Reifier.reify <..>
        chain (Reifier.zed (Reifier.rework ~fv:(fmapt OCanren.reify self))))

  let prj_exn : (ground, ground) Reifier.t =
    let open Env.Monad in
    Reifier.fix (fun self ->
      Reifier.prj_exn <..> chain (fmapt OCanren.prj_exn self))
end

open GLam

let varX = inj @@ lift "x"
let varY = inj @@ lift "y"
let varF = inj @@ lift "f"
