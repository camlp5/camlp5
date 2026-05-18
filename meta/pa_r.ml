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
include (PA(Pcaml.ParseBase)) ;

Pcaml.(set_ast_parse transduce_interf (Grammar.Entry.parse interf));
Pcaml.(set_ast_parse transduce_implem (Grammar.Entry.parse implem));
Pcaml.(set_ast_parse transduce_top_phrase (Grammar.Entry.parse top_phrase));
Pcaml.(set_ast_parse transduce_use_file (Grammar.Entry.parse use_file));
Pcaml.add_options (Pcaml.ParseBase.get_options()) ;
Pcaml.add_directives (Pcaml.ParseBase.get_directives()) ;
