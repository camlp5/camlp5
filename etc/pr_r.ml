(* camlp5r *)
(* pr_r.ml,v *)
(* Copyright (c) INRIA 2007-2017 *)

#directory ".";
#load "q_MLast.cmo";
#load "pa_extfun.cmo";
#load "pa_extprint.cmo";
#load "pa_macro.cmo";
#load "pa_macro_print.cmo";
#load "pa_pprintf.cmo";

open Asttools;
open Pretty;
open Pcaml;
open Prtools;
open Versdep;
open Mlsyntax.Revised;
open Pp_debug ;

value flag_add_locations = ref False;
value flag_comments_in_phrases = Pcaml.flag_comments_in_phrases;
value flag_extensions_are_irrefutable = ref True;
value flag_expand_declare = ref False;
value flag_horiz_let_in = ref False;
value flag_sequ_begin_at_eol = ref True;
value flag_equilibrate_cases = Pcaml.flag_equilibrate_cases;
value flag_expand_letop_syntax = Pcaml.flag_expand_letop_syntax;

value flag_where_after_in = ref True;
value flag_where_after_let_eq = ref True;
value flag_where_after_match = ref True;
value flag_where_after_lparen = ref True;
value flag_where_after_field_eq = ref False;
value flag_where_in_sequences = ref True;
value flag_where_after_then = ref True;
value flag_where_after_value_eq = ref True;
value flag_where_after_arrow = ref True;

value sep = Pcaml.inter_phrases;


include Print_r ;
include (PP(Pcaml.Base)) ;
