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

Toploop.parse_use_file.val :=
  wrap use_file (fun lb -> lb.lex_curr_pos - lb.lex_start_pos)
;

Pcaml.warning.val :=
  fun loc txt ->
      Toploop.print_warning (Ast2pt.mkloc loc) Format.err_formatter
        (Warnings.Preprocessor txt)
;
