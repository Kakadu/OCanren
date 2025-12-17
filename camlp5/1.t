$ ls
$ ls ../ppx
$ ocamlfind c -c test006.ml -pp ../ppx/pp_distrib.exe -verbose
  $ cat test006.ml
  $ ../ppx/pp_distrib.exe -new-typenames test006.ml
$ ocamlfind c -pp '../ppx/pp_distrib.exe -new-typenames' -package OCanren -rectypes test006.ml