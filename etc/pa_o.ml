(* camlp5r *)
(* pa_o.ml,v *)
(* Copyright (c) INRIA 2007-2017 *)

#load "pa_extend.cmo"; (* REMOVE FOR COMPILE *)
#load "q_MLast.cmo"; (* REMOVE FOR COMPILE *)
#load "pa_macro.cmo"; (* REMOVE FOR COMPILE *)
#load "pa_macro_gram.cmo"; (* REMOVE FOR COMPILE *)

open Asttools;
open Pcaml;
open Mlsyntax.Original;

Pcaml.syntax_name.val := "OCaml";
Pcaml.no_constructors_arity.val := True;

include Parse_o ;
include (PA(Mlsyntax.Lexer)(Pcaml.ParseBase)) ;
