
module Cfg = Configurator.V1

(*** utility functions ***)

(* pretty dumb file reading *)
let read_file fn =
  let ichan = open_in fn in
  let rec helper lines =
    try
      let line = input_line ichan in
      helper (line :: lines)
    with End_of_file -> lines
  in
  let lines = List.rev @@ helper [] in
  String.concat "\n" lines

let extract_words = Cfg.Flags.extract_comma_space_separated_words

let string_match re s = Str.string_match re s 0

let match_fn_ext fn ext =
  String.equal ext @@ Filename.extension fn

(* scans `regression` folder looking for `test*.ml` files *)
let get_tests tests_dir =
  let re = Str.regexp "test*" in
  let check_fn fn =
       (string_match re fn)
    && (match_fn_ext fn ".ml")
    (* `dune` doesn't give us direct access to `source` folder, only to the `build` folder,
     * thus we have to exclude files generated by the preprocessor
     *)
    && (not @@ match_fn_ext (Filename.remove_extension fn) ".pp")
    (* `tester.ml` also should be excluded *)
    && (not @@ String.equal fn "tester.ml")
  in
     Sys.readdir tests_dir
  |> Array.to_list
  |> List.filter check_fn
  |> List.map Filename.remove_extension
  |> List.sort String.compare

(*** discovering ***)

let discover_tests _ tests =
  Cfg.Flags.write_lines "tests.txt" tests

let discover_camlp5_dir cfg =
  String.trim @@
    Cfg.Process.run_capture_exn cfg
      "ocamlfind" ["query"; "camlp5"]

let discover_stubs_dir cfg =
  let s = String.trim @@ Cfg.Process.run_capture_exn cfg "ocamlfind" ["query"; "camlp5"] in
(*  let s = String.concat " " s in*)
  Cfg.Flags.write_lines "stublibs-dir.cfg" @@
  [Printf.sprintf "%s/../stublibs" s]

let discover_camlp5_flags cfg =
  let camlp5_dir = discover_camlp5_dir cfg in
  let camlp5_archives =
    List.map
      (fun arch -> String.concat Filename.dir_sep [camlp5_dir; arch])
      ["pa_o.cmo"; "pa_op.cmo"; "pr_o.cmo"; "pr_dump.cmo" ]
  in
  Cfg.Flags.write_lines "camlp5-flags.cfg" camlp5_archives

let discover_gt_flags cfg =
  let gt_archives =
    Cfg.Process.run_capture_exn cfg
      "ocamlfind" ["query"; "-pp"; "camlp5"; "-a-format"; "-predicates"; "byte"; "GT,GT.syntax"]
  in
  Cfg.Flags.write_lines "gt-flags.cfg" @@ extract_words gt_archives;
  let gt_archives_native =
    Cfg.Process.run_capture_exn cfg
      "ocamlfind" ["query"; "-pp"; "camlp5"; "-a-format"; "-predicates"; "native"; "GT,GT.syntax"]
  in
  Cfg.Flags.write_lines "gt-flags-native.cfg" @@ extract_words gt_archives_native

let discover_logger_flags cfg =
  (* logger has two kinds of CMOs: two from camlp5 (pr_o and pr_dump) and one for logger.
      `pr_o` is required because logger uses pretty-printing inside itself.
      `pr_dump` is required for printing result in binary format (to save line numbers).
      `pa_log` for logger itself

    in META file they are listed as `pr_o.cmo pr_dump.cmo pa_log.cmo`
    With ocamlfind they are passed as is to compilation command prefixed by
    linking directory options. Because of that we can't write, for example,
    '../camlp5/pr_o.cmo` in META file.

    With dune these three cmos are prefixed using full path, so using naive
    approach they are all located in the same directory $LIB/logger. This is
    wrong but we can hack it in dune script because we know exact names of cmos.
  *)

  let camlp5_dir = discover_camlp5_dir cfg in
  let logger_archives =
    Cfg.Process.run_capture_exn cfg
      "ocamlfind" ["query"; "-pp"; "camlp5"; "-a-format"; "-predicates"; "byte"; "logger,logger.syntax"]
  in
  let pr_o_cmo = "pr_o.cmo" in
  let pr_dump_cmo = "pr_dump.cmo" in
  let cmos =
    extract_words logger_archives |>
    List.map (fun file ->
      if Filename.basename file = pr_o_cmo then
        Filename.concat camlp5_dir pr_o_cmo
      else if Filename.basename file = pr_dump_cmo then
        Filename.concat camlp5_dir pr_dump_cmo
      else file
    )
  in
  Cfg.Flags.write_lines "logger-flags.cfg" cmos

(*** generating dune files ***)

(* generates build rules for `test*.exe` *)
let gen_tests_dune _ tests =
  let tpl_fn = "tests.dune.tpl" in
  let dune_fn = "tests.dune" in
  let tpl = read_file tpl_fn in
  let re = Str.regexp "%{tests}" in
  let tests = String.concat "\n    " tests in
  let dune = Str.global_replace re tests tpl in
  let outchn = open_out dune_fn in
  output_string outchn dune

(*** command line arguments ***)

let tests         = ref false
let tests_dune    = ref false
let tests_dir     = ref None
let camlp5_flags  = ref false
let gt_flags      = ref false
let logger_flags  = ref false
let all_flags     = ref false
let all           = ref false

let args =
  let set_tests_dir s = tests_dir := Some s in
  Arg.align @@
    [ ("-tests-dir"   , Arg.String set_tests_dir, "DIR discover tests in this directory"      )
    ; ("-tests"       , Arg.Set tests           , " discover tests (tests.txt)"               )
    ; ("-tests-dune"  , Arg.Set tests_dune      , " generate dune build file for tests"       )
    ; ("-camlp5-flags", Arg.Set camlp5_flags    , " discover camlp5 flags (camlp5-flags.cfg)" )
    ; ("-gt-flags"    , Arg.Set gt_flags        , " discover GT flags (gt-flags.cfg)"         )
    ; ("-gt-flags"    , Arg.Set logger_flags    , " discover logger flags (logger-flags.cfg)" )
    ; ("-all-flags"   , Arg.Set all_flags       , " discover all flags"                       )
    ; ("-all"         , Arg.Set all             , " discover all"                             )
    ]

(*** main ***)

let () =

  Cfg.main ~name:"ocanren" ~args (fun cfg ->
    let testnames =
      if !tests || !tests_dune || !all then
        match !tests_dir with
        | Some dir -> get_tests dir
        | None     -> failwith "-tests-dir argument is not set"
      else []
    in

    if !tests || !all then
      discover_tests cfg testnames ;
    if !tests_dune || !all then
      gen_tests_dune cfg testnames ;
    if !camlp5_flags || !all_flags || !all then
      discover_camlp5_flags cfg ;
    if !gt_flags || !all_flags || !all then
      (discover_stubs_dir cfg; discover_gt_flags cfg);
    if !logger_flags || !all_flags || !all then
      discover_logger_flags cfg ;
    ()
  )
