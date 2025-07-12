#use "../../local-install/lib/ocaml/topfind.camlp5";;
#require "fmt";;
#camlp5o ;;
#directory "../../ppxprint";;
#load "ppxprint.cma";;
Pp_MLast.Gen.Ploc.pp_loc_verbose := true ;;
# 10 "fixtures/r.ml"
#use "use1.ml" ;;
