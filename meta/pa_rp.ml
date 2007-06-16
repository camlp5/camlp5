(* camlp4r pa_extend.cmo q_MLast.cmo *)
(***********************************************************************)
(*                                                                     *)
(*                             Camlp4                                  *)
(*                                                                     *)
(*                Daniel de Rauglaudre, INRIA Rocquencourt             *)
(*                                                                     *)
(*  Copyright 2007 Institut National de Recherche en Informatique et   *)
(*  Automatique.  Distributed only by permission.                      *)
(*                                                                     *)
(***********************************************************************)

(* $Id: pa_rp.ml,v 1.8 2007/06/16 14:17:43 deraugla Exp $ *)

open Exparser;
open Pcaml;

(* Syntax extensions in Revised Syntax grammar *)

EXTEND
  GLOBAL: expr;
  expr: LEVEL "top"
    [ [ "parser"; po = OPT ipatt; "["; pcl = LIST0 parser_case SEP "|"; "]" ->
          <:expr< $cparser loc po pcl$ >>
      | "parser"; po = OPT ipatt; pc = parser_case ->
          <:expr< $cparser loc po [pc]$ >>
      | "match"; e = SELF; "with"; "parser"; po = OPT ipatt; "[";
        pcl = LIST0 parser_case SEP "|"; "]" ->
          <:expr< $cparser_match loc e po pcl$ >>
      | "match"; e = SELF; "with"; "parser"; po = OPT ipatt;
        pc = parser_case ->
          <:expr< $cparser_match loc e po [pc]$ >> ] ]
  ;
  parser_case:
    [ [ "[:"; sp = stream_patt; ":]"; po = OPT ipatt; "->"; e = expr ->
          (sp, po, e) ] ]
  ;
  stream_patt:
    [ [ spc = stream_patt_comp -> [(spc, SpoNoth)]
      | spc = stream_patt_comp; ";";
        sp = LIST1 stream_patt_comp_err SEP ";" ->
          [(spc, SpoNoth) :: sp]
      | -> [] ] ]
  ;
  stream_patt_comp_err:
    [ [ spc = stream_patt_comp; "?"; e = expr -> (spc, SpoQues e)
      | spc = stream_patt_comp; "!" -> (spc, SpoBang)
      | spc = stream_patt_comp -> (spc, SpoNoth) ] ]
  ;
  stream_patt_comp:
    [ [ "`"; p = patt; eo = OPT [ "when"; e = expr -> e ] -> SpTrm loc p eo
      | "?="; pll = LIST1 lookahead SEP "|" -> SpLhd loc pll
      | p = patt; "="; e = expr -> SpNtr loc p e
      | p = patt -> SpStr loc p ] ]
  ;
  lookahead:
    [ [ "["; pl = LIST1 patt SEP ";"; "]" -> pl ] ]
  ;
  ipatt:
    [ [ i = LIDENT -> <:patt< $lid:i$ >> ] ]
  ;
  expr: LEVEL "simple"
    [ [ "[:"; se = LIST0 stream_expr_comp SEP ";"; ":]" ->
          <:expr< $cstream loc se$ >> ] ]
  ;
  stream_expr_comp:
    [ [ "`"; e = expr -> SeTrm loc e | e = expr -> SeNtr loc e ] ]
  ;
END;
