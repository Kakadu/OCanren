
  $ ../ppx/pp_ocanren_all.exe -help
  pp_ocanren_all.exe [extra_args] [<files>]
    -as-ppx                     Run as a -ppx rewriter (must be the first argument)
    --as-ppx                    Same as -as-ppx
    -as-pp                      Shorthand for: -dump-ast -embed-errors
    --as-pp                     Same as -as-pp
    -o <filename>               Output file (use '-' for stdout)
    -                           Read input from stdin
    -dump-ast                   Dump the marshaled ast to the output file instead of pretty-printing it
    --dump-ast                  Same as -dump-ast
    -dparsetree                 Print the parsetree (same as ocamlc -dparsetree)
    -embed-errors               Embed errors in the output AST (default: true when -as-pp, false otherwise)
    -null                       Produce no output, except for errors
    -impl <file>                Treat the input as a .ml file
    --impl <file>               Same as -impl
    -intf <file>                Treat the input as a .mli file
    --intf <file>               Same as -intf
    -debug-attribute-drop       Debug attribute dropping
    -print-transformations      Print linked-in code transformations, in the order they are applied
    -print-passes               Print the actual passes over the whole AST in the order they are applied
    -ite-check                  (no effect -- kept for compatibility)
    -pp <command>               Pipe sources through preprocessor <command> (incompatible with -as-ppx)
    -reconcile                  (WIP) Pretty print the output using a mix of the input source and the generated code
    -reconcile-with-comments    (WIP) same as -reconcile but uses comments to enclose the generated code
    -no-color                   Don't use colors when printing errors
    -diff-cmd                   Diff command when using code expectations (use - to disable diffing)
    -pretty                     Instruct code generators to improve the prettiness of the generated code
    -styler                     Code styler
    -output-metadata FILE       Where to store the output metadata
    -corrected-suffix SUFFIX    Suffix to append to corrected files
    -keywords <version+list>    Set keywords according to the version+list specification. Allows using a set of keywords different from the one of the current compiler for backward compatibility.
    --keywords <version+list>   Same as -keywords
    -loc-filename <string>      File name to use in locations
    -reserve-namespace <string> Mark the given namespace as reserved
    -no-check                   Disable checks (unsafe)
    -check                      Enable checks
    -no-check-on-extensions     Disable checks on extension point only
    -check-on-extensions        Enable checks on extension point only
    -no-locations-check         Disable locations check only
    -locations-check            Enable locations check only
    -apply <names>              Apply these transformations in order (comma-separated list)
    -dont-apply <names>         Exclude these transformations
    -no-merge                   Do not merge context free transformations (better for debugging rewriters). As a result, the context-free transformations are not all applied before all impl and intf.
    -cookie NAME=EXPR           Set the cookie NAME to EXPR
    --cookie                    Same as -cookie
    -new-typenames Mangle       type names by adding _logic/_ground suffix
    -no-new-typenames Old       naming scheme: creates types t, ground and logic. User types named t are forbidden
    -help                       Display this list of options
    --help                      Display this list of options

  $ ../ppx/pp_ocanren_all.exe -pp ../camlp5/pp5+ocanren+o.exe ./test023ulc.ml
  open GT
  open OCanren
  open OCanren.Std
  include
    struct
      type nonrec 'a0 t =
        | Str of 'a0 [@@deriving gt ~options:{ show }]
      type ground = GT.string t[@@deriving gt ~options:{ show }]
      type logic = GT.string OCanren.logic t OCanren.logic[@@deriving
                                                            gt
                                                              ~options:
                                                              { show }]
      type injected = GT.string OCanren.ilogic t OCanren.ilogic
      let fmapt f__003_ subj__004_ =
        let open OCanren.Env.Monad in
          ((OCanren.Env.Monad.return (GT.gmap t)) <*> f__003_) <*> subj__004_
      let (prj_exn : (injected, ground) OCanren.Reifier.t) =
        let open OCanren.Env.Monad in
          OCanren.Reifier.fix
            (fun self -> OCanren.prj_exn <..> (chain (fmapt OCanren.prj_exn)))
      let (reify : (injected, logic) OCanren.Reifier.t) =
        let open OCanren.Env.Monad in
          OCanren.Reifier.fix
            (fun self ->
               OCanren.reify <..>
                 (chain
                    (OCanren.Reifier.zed
                       (OCanren.Reifier.rework ~fv:(fmapt OCanren.reify)))))
      let str _x__001_ = OCanren.inj (Str _x__001_)
    end
