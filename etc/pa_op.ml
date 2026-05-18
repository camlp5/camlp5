(* camlp5r *)
(* pa_op.ml,v *)
(* Copyright (c) INRIA 2007-2017 *)

#load "pa_extend.cmo";
#load "parse_q_MLast.cmo";
#load "q_MLast.cmo";

include Parse_op ;
include (PA(Pcaml.ParseBase)) ;
