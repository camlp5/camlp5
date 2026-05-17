(* camlp5r *)
(* pa_r.ml,v *)
(* Copyright (c) INRIA 2007-2017 *)

#load "pa_extend.cmo";
#load "q_MLast.cmo";
#load "pa_macro.cmo";
#load "pa_macro_gram.cmo";

open Asttools;
open Pcaml;
open Mlsyntax.Revised;

Pcaml.syntax_name.val := "Revised";
Pcaml.no_constructors_arity.val := False;

include Parse_r ;
include (PA(Mlsyntax.Lexer)(Pcaml.ParseBase)) ;
