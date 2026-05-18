(* camlp5r *)
(* pa_o.ml,v *)
(* Copyright (c) INRIA 2007-2017 *)

#load "pa_extend.cmo"; (* REMOVE FOR COMPILE *)
#load "parse_q_MLast.cmo";  (* REMOVE FOR COMPILE *)
#load "q_MLast.cmo"; (* REMOVE FOR COMPILE *)
#load "pa_macro.cmo"; (* REMOVE FOR COMPILE *)
#load "pa_macro_gram.cmo"; (* REMOVE FOR COMPILE *)

open Asttools;
open Pcaml;
open Mlsyntax.Original;

Pcaml.syntax_name.val := "OCaml";
Pcaml.no_constructors_arity.val := True;

include Parse_o ;
include (PA(Pcaml.ParseBase)) ;

Pcaml.(set_ast_parse transduce_interf (Grammar.Entry.parse interf));
Pcaml.(set_ast_parse transduce_implem (Grammar.Entry.parse implem)); (* REMOVE FOR COMPILE *)
Pcaml.(set_ast_parse transduce_top_phrase (Grammar.Entry.parse top_phrase));
Pcaml.(set_ast_parse transduce_use_file (Grammar.Entry.parse use_file));
Pcaml.add_options (Pcaml.ParseBase.get_options()) ;
Pcaml.add_directives (Pcaml.ParseBase.get_directives()) ;
