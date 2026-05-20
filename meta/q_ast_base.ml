(* camlp5r *)
(* q_ast_base.ml,v *)
(* Copyright (c) INRIA 2007-2017 *)

#load "pa_macro.cmo";
#load "pa_extend.cmo";
#load "parse_q_MLast.cmo";
#load "q_MLast.cmo";

include Parse_q_ast_base ;
include (PA(Pcaml.ParseBase)(Pcaml.QH)) ;
