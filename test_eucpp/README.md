#### Applicative reifiers

In the end of last year, @YueLiPicasso was checking usefullness of new reifiers more extensively. He discovered some issues and mde some changes (more details in the mail and [here](https://github.com/YueLiPicasso/intro_ocaml/tree/master/))

* Some problems with recursive reifiers were discovered.
  * An attempt to declare recursive reifiers with `lazy` keyword is done.
* There was an attempt to eliminate `compose` combinator (as Yue Li said: "Getting rid of the unreliable `Reifier.compose` that was used by Moiseenko to define recursive reifiers.")

At the same time I thought about reifiers in background, and was hacking compile-time generation of reifiers. This generation has some quirks (although, not too compicated) related to the naming. Let's look at the following piece of code.

````ocaml
  type 'a t =
    | O
    | S of 'a
  [@@deriving gt ~options:{ gmap }]

  type 'a ground = 'a t
  type 'a logic = 'a t OCanren.logic
  type 'a injected = 'a t ilogic

  let reify_old_style : (('a injected as 'a), ('b logic as 'b)) Reifier.t =
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
````

There I'm using a fancy syntax with `let*` which was introduced in OCaml 4.08 and basically is applicative+monadic do-notation (a concept highly popularized by Haskell).

This code has a few minor (or not) issues related to naming. We need to carefully invent names `r`, `rself`, `foo` which may hide some names declared above and carefully use them in reifier. Also, every reifier will have a special function `foo`, which does a shallow reification of provided values (called `x` here).

I discovered all these issues and kind of paused writing code for automatic generation of reifiers. I had a feeling that we could make everything simpler, better suited for automatic generation.

**Minor remark about fixpoint combinator**. (I'm not sure, TODO: recheck this) In original @eucpp's work on monadic combinators, he didn't use any fixpoint combinator and relied on `let rec`. In my original rework of the approach in `eucpp` branch this fix point combinator (I think) was flawed. It was a standard CBV fixpoint combinator, but we require a fix point combinator for reifiers, which are values of type `('a -> 'b) Reader.t` which is essentially `env -> 'a -> 'b`. To make this fix point combinator work as expected at some moment of hacking I added one more level for eta-expansion to make it work (not to hang).

The idea about fixing the approach was partially inspired by my frustration about names during generic programming, and partially by Yue Li's idea about getting rid of `compose` function. We need to generate new names when we use `bind` operator on our monadic reifiers. Yue Li tried to get rid of `compose` function and make "pure" monadic reifiers. So, maybe we should get rid of monadic reifiers and use only `compose` function? Which, occasionally or not is an `ap` operation if we will see our `_ Reader.t` as an *applicative functor*.
