(* camlp5r *)
(* q_MLast.ml,v *)
(* Copyright (c) INRIA 2007-2017 *)

(* #load "pa_extend.cmo" *)
(* #load "pa_extend_m.cmo" *)
(* #load "parse_q_MLast.cmo" *)
(* #load "q_MLast.cmo" *)
(* #load "pa_macro.cmo" *)

open Asttools;;
open Mlsyntax.Revised;;

include Parse_q_MLast;;
include PA (Pcaml.ParseBase);;
