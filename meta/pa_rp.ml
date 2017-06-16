(* camlp5r *)
(* pa_rp.ml,v *)
(* Copyright (c) INRIA 2007-2017 *)

#load "pa_extend.cmo";
#load "q_MLast.cmo";

open Exparser;
open Pcaml;

(* Syntax extensions in Revised Syntax grammar *)

EXTEND
  GLOBAL: expr ipatt;
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
      | spc = stream_patt_comp; ";"; sp = stream_patt_kont ->
          [(spc, SpoNoth) :: sp]
      | spc = stream_patt_let; sp = stream_patt -> [spc :: sp]
      | -> [] ] ]
  ;
  stream_patt_kont:
    [ [ spc = stream_patt_comp_err -> [spc]
      | spc = stream_patt_comp_err; ";"; sp = stream_patt_kont -> [spc :: sp]
      | spc = stream_patt_let; sp = stream_patt_kont -> [spc :: sp] ] ]
  ;
  stream_patt_comp_err:
    [ [ spc = stream_patt_comp; "?"; e = expr -> (spc, SpoQues e)
      | spc = stream_patt_comp; "!" -> (spc, SpoBang)
      | spc = stream_patt_comp -> (spc, SpoNoth) ] ]
  ;
  stream_patt_comp:
    [ [ "`"; p = patt; eo = V (OPT [ "when"; e = expr -> e ]) ->
          SpTrm loc p eo
      | "?="; pll = LIST1 lookahead SEP "|" -> SpLhd loc pll
      | p = patt; "="; e = expr -> SpNtr loc p e
      | p = patt -> SpStr loc p ] ]
  ;
  stream_patt_let:
    [ [ "let"; p = ipatt; "="; e = expr; "in" -> (SpLet loc p e, SpoNoth) ] ]
  ;
  lookahead:
    [ [ "["; pl = LIST1 patt SEP ";"; "]" -> pl ] ]
  ;
  expr: LEVEL "simple"
    [ [ "[:"; se = LIST0 stream_expr_comp SEP ";"; ":]" ->
          <:expr< $cstream loc se$ >> ] ]
  ;
  stream_expr_comp:
    [ [ "`"; e = expr -> SeTrm loc e | e = expr -> SeNtr loc e ] ]
  ;
END;
