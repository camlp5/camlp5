(* camlp5r *)
(* pa_extfold.ml,v *)

#load "pa_extend.cmo";
#load "q_MLast.cmo";

open Pcaml;
open Pa_extend;

value folder loc lml f e s sep_opt =
let sep_opt = match sep_opt with [ None -> None | Some sep -> Some(sep, False) ] in
let n = abs(Hashtbl.hash (f,e)) in
let p = Printf.sprintf "l_%x" n in
let s = ASlist loc lml s sep_opt in
let ps = {ap_loc = loc; ap_patt = Some <:patt< $lid:p$ >>; ap_symb = s} in
let e_action = <:expr< List.fold_left $f$ $e$ $lid:p$ >> in
let r = {ar_loc = loc; ar_psymbols = [ps]; ar_action = Some e_action} in
ASrules loc {au_loc = loc; au_rules = [r] }
;

EXTEND
  GLOBAL: symbol;
  symbol: LEVEL "top"
    [ [ UIDENT "FOLD0"; f = simple_expr; e = simple_expr; s = SELF ->
          folder loc LML_0 f e s None
      | UIDENT "FOLD1"; f = simple_expr; e = simple_expr; s = SELF ->
          folder loc LML_1 f e s None
      | UIDENT "FOLD0"; f = simple_expr; e = simple_expr; s = SELF;
        UIDENT "SEP"; sep = SELF ->
          folder loc LML_0 f e s (Some sep)
      | UIDENT "FOLD1"; f = simple_expr; e = simple_expr; s = SELF;
        UIDENT "SEP"; sep = SELF ->
          folder loc LML_1 f e s (Some sep)
      ] ]
  ;
  simple_expr:
    [ [ e = expr LEVEL "simple" -> e ] ]
  ;
END;
