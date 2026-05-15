(* camlp5r *)
(* pr_o.ml,v *)
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
open Prtools;
open Versdep;
open Mlsyntax.Original;
open Pp_debug ;

include Print_o ;
include (PP(Pcaml.Base)) ;
Pcaml.add_options (Pcaml.Base.get_options()) ;
Pcaml.print_interf.val := print_interf;
Pcaml.print_implem.val := print_implem;
