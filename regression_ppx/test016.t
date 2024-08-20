
  $ ls
  test016.ml
Why this error?
  $ ../ppx/pp_distrib.exe   -pretty test016.ml
  [%%ocaml.error "\"t\" expected"]
  module _ =
    struct
      [%%ocanren_inject
        type nonrec ground =
          | Bad of GT.string GT.list [@@deriving gt ~options:{ gmap }]]
    end
  module _ =
    struct
      include
        struct
          type nonrec 'a0 t =
            | OK of 'a0 [@@deriving gt ~options:{ gmap }]
          type nonrec ground = GT.string Std.List.ground t[@@deriving
                                                            gt
                                                              ~options:
                                                              { gmap }]
          type nonrec logic =
            GT.string OCanren.logic OCanren.Std.List.logic t OCanren.logic
          [@@deriving gt ~options:{ gmap }]
          type nonrec injected =
            GT.string OCanren.ilogic OCanren.Std.List.injected t OCanren.ilogic
          let fmapt f__004_ subj__005_ =
            let open OCanren.Env.Monad in
              ((OCanren.Env.Monad.return (GT.gmap t)) <*> f__004_) <*>
                subj__005_
          let (prj_exn : (injected, ground) OCanren.Reifier.t) =
            let open OCanren.Env.Monad in
              OCanren.Reifier.fix
                (fun _ ->
                   OCanren.prj_exn <..>
                     (chain (fmapt (Std.List.prj_exn OCanren.prj_exn))))
          let (reify : (injected, logic) OCanren.Reifier.t) =
            let open OCanren.Env.Monad in
              OCanren.Reifier.fix
                (fun _ ->
                   OCanren.reify <..>
                     (chain
                        (OCanren.Reifier.zed
                           (OCanren.Reifier.rework
                              ~fv:(fmapt (Std.List.reify OCanren.reify))))))
          let oK _x__002_ = OCanren.inji (OK _x__002_)
        end
    end
