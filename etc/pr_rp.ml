(* camlp5r *)
(* pr_rp.ml,v *)
(* Copyright (c) INRIA 2007-2017 *)

#directory ".";
#load "q_MLast.cmo";
#load "pa_extfun.cmo";
#load "pa_extprint.cmo";
#load "pa_pprintf.cmo";
#load "pa_macro.cmo";

open Exparser;
open Parserify;
open Pcaml;
open Pretty;
open Prtools;

include Print_rp ;
include (PP(Pcaml.Base)(Pr_r.R)) ;
