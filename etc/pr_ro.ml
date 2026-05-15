(* camlp5r *)
(* pr_ro.ml,v *)
(* Copyright (c) INRIA 2007-2017 *)

#directory ".";
#load "pa_macro.cmo";
#load "q_MLast.cmo";
#load "pa_extfun.cmo";
#load "pa_extprint.cmo";
#load "pa_pprintf.cmo";

(* Pretty printing extension for objects and labels *)

open Pcaml;
open Prtools;
open Printf;
open Pretty;
open Mlsyntax.Revised;

include Print_ro ;
include (PP(Pcaml.Base)(Pr_r.R)) ;
