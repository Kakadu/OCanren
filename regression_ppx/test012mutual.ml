let () = print_endline "test012"

(* [%%distrib
type 'a targ = T of 'a jtyp * 'a

and 'a jtyp =
  | Array of 'a jtyp
  | V of 'a targ
[@@deriving gt ~options:{ gmap }]] *)

type nonrec ('a, 'a0) targ_fuly = T of 'a0 * 'a [@@deriving gt ~options:{ gmap }]

type nonrec ('a, 'a1, 'a0) jtyp_fuly =
  | Array of 'a1
  | V of 'a0
[@@deriving gt ~options:{ gmap }]

type 'a targ_logic = ('a, 'a jtyp_logic) targ_fuly OCanren.logic

and 'a jtyp_logic = ('a, 'a jtyp_logic, 'a targ_logic) jtyp_fuly OCanren.logic
[@@deriving gt ~options:{ gmap }]

let __ (type a b) : (a -> b) -> a jtyp_logic -> b jtyp_logic = fun eta -> GT.gmap jtyp_logic eta
(* 
type nonrec ('a, 'a0) targ_fuly = T of 'a0 * 'a [@@deriving gt ~options:{ gmap }]

type nonrec ('a, 'a1, 'a0) jtyp_fuly =
  | Array of 'a1
  | V of 'a0
[@@deriving gt ~options:{ gmap }]

type 'a targ = ('a, 'a jtyp) targ_fuly
and 'a jtyp = ('a, 'a jtyp, 'a targ) jtyp_fuly [@@deriving gt ~options:{ gmap }]

let (_ : int) = GT.gmap jtyp *)

(* let rec pp_arg fa ppf : 'a targ -> unit = function
  | TNoarg -> Format.fprintf ppf "noarg"
  | T (l, r) -> Format.fprintf ppf "(%a,%a)" (pp_typ fa) l fa r

and pp_typ fa ppf : 'a jtyp -> unit = function
  | Array typ -> Format.fprintf ppf "(Array %a)" (pp_typ fa) typ
  | V arg -> Format.fprintf ppf "%a" (pp_arg fa) arg
  | Other a -> Format.fprintf ppf "(Other %a)" fa a
;;

open OCanren

let () =
  OCanren.(run q) (fun q -> q === !!TNoarg) (fun rr -> rr#reify (targ_prj_exn OCanren.prj_exn))
  |> OCanren.Stream.take
  |> Stdlib.List.iter (Format.printf "%a\n%!" (pp_arg Format.pp_print_int))
;;

let () =
  OCanren.(run q)
    (fun q -> q === !!(Array !!(V !!(T (!!(Other !!1), !!2)))))
    (fun rr -> rr#reify (jtyp_prj_exn OCanren.prj_exn))
  |> OCanren.Stream.take
  |> Stdlib.List.iter (Format.printf "%a\n%!" (pp_typ Format.pp_print_int))
;; *)
