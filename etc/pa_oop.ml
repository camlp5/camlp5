(* camlp5r *)
(* pa_oop.ml,v *)
(* Copyright (c) INRIA 2007-2017 *)

#load "pa_extend.cmo";
#load "q_MLast.cmo";

include Parse_oop ;
include (PA(Mlsyntax.Lexer)(Pcaml.ParseBase)) ;
