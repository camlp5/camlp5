(* camlp5r *)
(* pr_r.ml,v *)
(* Copyright (c) INRIA 2007-2017 *)

#directory ".";
#load "parse_q_MLast.cmo";
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

module R = Print_patr.PP(Pcaml.PrintBase) ;
include (R) ;
Pcaml.add_options (Pcaml.PrintBase.get_options()) ;
Pcaml.print_interf.val := R.print_interf;
Pcaml.print_implem.val := R.print_implem;
