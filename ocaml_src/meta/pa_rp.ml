(* camlp5r *)
(* pa_rp.ml,v *)
(* Copyright (c) INRIA 2007-2017 *)

(* #load "pa_extend.cmo" *)
(* #load "parse_q_MLast.cmo" *)
(* #load "q_MLast.cmo" *)

open Asttools;;
open Exparser;;
open Pcaml;;

include Parse_rp;;
include PA (Pcaml.ParseBase);;
