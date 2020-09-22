(* camlp5o *)
(* eg_sexp.ml,v *)
(* Copyright (c) INRIA 2007-2017 *)

open Fmt ;;

let x = 1 ;;
let nil = Sexp.Nil ;;
let nil' = SEXP () ;;
(*Probably gonna ask a question HERE*)
let l = SEXP (a b (c . ()) . d) ;;
