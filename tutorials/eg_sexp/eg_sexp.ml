(* camlp5o *)
(* eg_sexp.ml,v *)
(* Copyright (c) INRIA 2007-2017 *)

open Fmt ;;

let x = 1 ;;
let nil = Sexp.Nil ;;
let nil' = SEXP () ;;
(*Probably gonna ask a question HERE*)
let l = SEXP (a b (c . ()) . d) ;;

#qmod "" ;;
let nil = <:expr< SEXP () >> ;;

let rec pp pps = function
    <:expr< SEXP () >> -> Fmt.(pf pps "()")
  | <:expr< SEXP ( $exp:a$ . $exp:b$ ) >> -> Fmt.(pf pps "(%a . %a)" pp a pp b)
  | <:expr< SEXP $atom:a$ >> -> Fmt.(pf pps "%a" string a)
;;

let subst rho e =
  let rec srec = function
    <:expr< SEXP () >> -> <:expr< SEXP () >>
  | <:expr< SEXP ( $exp:a$ . $exp:b$ ) >> -> 
    <:expr< SEXP ( $exp:srec a$ . $exp:srec b$ ) >>
  | <:expr< SEXP $atom:a$ >> as z ->
    if List.mem_assoc a rho then List.assoc a rho
    else z
in srec e
;;
