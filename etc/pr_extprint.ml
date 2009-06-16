(* camlp5r q_MLast.cmo -I . pa_extfun.cmo pa_extprint.cmo pa_pprintf.cmo *)
(* $Id: pr_extprint.ml,v 1.1 2008/01/05 02:45:13 deraugla Exp $ *)
(* Copyright (c) INRIA 2007-2008 *)

(* heuristic to rebuild the EXTEND_PRINTER statement from the AST *)

open Pcaml;

(**)
value test = ref False;
Pcaml.add_option "-test" (Arg.Set test) " test";
(**)

(* Extracting *)

value unextend_body pr pos body =
  let pos =
    match pos with
    [ <:expr< Some $p$ >> ->
        let p =
          match p with
          [ <:expr< Eprinter.First >> -> Eprinter.First
          | <:expr< Eprinter.Last >> -> Eprinter.Last
          | <:expr< Eprinter.Before $str:n$ >> -> Eprinter.Before n
          | <:expr< Eprinter.After $str:n$ >> -> Eprinter.After n
          | <:expr< Eprinter.Level $str:n$ >> -> Eprinter.Level n
          | _ -> raise Not_found ]
        in
        Some p
    | <:expr< None >> -> None
    | _ -> raise Not_found ]
  in
  let body =
    loop body where rec loop =
      fun
      [ <:expr< [($lab$, $rules$) :: $levs$] >> ->
          let label =
            match lab with
            [ <:expr< Some $str:s$ >> -> Some s
            | <:expr< None >> -> None
            | _ -> raise Not_found ]
          in
          [(label, rules) :: loop levs]
      | <:expr< [] >> -> []
      | _ -> raise Not_found ]
  in
  (pr, pos, body)
;

(* Printing *)

value expr = Eprinter.apply pr_expr;

value extend_body pc _ = pprintf pc "ouais";

value extend pc =
  fun
  [ <:expr< Eprinter.extend $pr$ $pos$ $body$ >> ->
      if test.val then
      try
        let ex = unextend_body pr pos body in
        pprintf pc "EXTEND_PRINTER@;%p@ END" extend_body ex
      with
      [ Not_found ->
          let expr = Eprinter.apply_level pr_expr "dot" in
          pprintf pc "Eprinter.extend@;%p@ %p@ %p@" expr pr expr pos
            expr body ]
      else
      pprintf pc "fuck"
  | e -> expr pc e ]
;

EXTEND_PRINTER
  pr_expr: LEVEL "apply"
    [ [ <:expr< Eprinter.extend $_$ $_$ $_$ >> as e -> next pc e ] ]
  ;
  pr_expr: LEVEL "simple"
    [ [ <:expr< Eprinter.extend $_$ $_$ $_$ >> as e -> extend pc e ] ]
  ;
END;
