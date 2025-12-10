open GT
open OCanren
open OCanren.Std

[%%ocanren_inject type logic =
    Str of GT.string[@@deriving gt ~options:{show}]
;;]

