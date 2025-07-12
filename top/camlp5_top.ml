(* camlp5r *)
(* camlp5_top.ml,v *)
(* Copyright (c) INRIA 2007-2017 *)

#load "pa_macro.cmo";
#load "q_MLast.cmo";

open Parsetree;
open Lexing;
open Versdep;
open Camlp5_top_funs;

Toploop.parse_toplevel_phrase.val := wrapped_toplevel_phrase ;

Toploop.parse_use_file.val := wrapped_use_file ;

Pcaml.warning.val := wrapped_print_warning ;
