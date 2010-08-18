(* camlp5r *)
(* $Id: pa_extfold.ml,v 1.6 2010/08/18 16:26:25 deraugla Exp $ *)

#load "pa_extend.cmo";
#load "q_MLast.cmo";

open Pcaml;
open Pa_extend;

EXTEND
  GLOBAL: symbol;
  symbol: LEVEL "top"
    [ [ UIDENT "FOLD0"; f = simple_expr; e = simple_expr; s = SELF ->
          ASfold loc "FOLD0" "sfold0" f e s None
      | UIDENT "FOLD1"; f = simple_expr; e = simple_expr; s = SELF ->
          ASfold loc "FOLD1" "sfold1" f e s None
      | UIDENT "FOLD0"; f = simple_expr; e = simple_expr; s = SELF;
        UIDENT "SEP"; sep = SELF ->
          ASfold loc "FOLD0 SEP" "sfold0sep" f e s (Some sep)
      | UIDENT "FOLD1"; f = simple_expr; e = simple_expr; s = SELF;
        UIDENT "SEP"; sep = SELF ->
          ASfold loc "FOLD1 SEP" "sfold1sep" f e s (Some sep) ] ]
  ;
  simple_expr:
    [ [ e = expr LEVEL "simple" -> e ] ]
  ;
END;
