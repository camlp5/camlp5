(* camlp5r *)
(* pa_op.ml,v *)
(* Copyright (c) INRIA 2007-2017 *)

#load "pa_extend.cmo";
#load "q_MLast.cmo";

open Asttools;
open Exparser;
open Pcaml;

(* Syntax extensions in Ocaml grammar *)

EXTEND
  GLOBAL: expr ipatt ext_attributes stream_expr stream_parser stream_match;

  stream_parser:
    [ [ "parser"; po = OPT ipatt; OPT "|"; pcl = LIST1 parser_case SEP "|" ->
          (loc, (po, pcl))
      ] ]
  ;

  stream_match:
    [ [ "match"; (ext,attrs) = ext_attributes; e = expr LEVEL "expr1" ; "with"; "parser"; po = OPT ipatt; OPT "|";
        pcl = LIST1 parser_case SEP "|" ->
          (loc, e, (po, pcl))
      ] ]
  ;

  stream_expr:
    [ [ "[<"; ">]" -> (loc, [])
      | "[<"; sel = stream_expr_comp_list; ">]" ->
          (loc, sel) ] ]
  ;

  expr: LEVEL "expr1"
    [ [ "parser"; po = OPT ipatt; OPT "|"; pcl = LIST1 parser_case SEP "|" ->
          <:expr< $cparser loc (po, pcl)$ >>
      | "match"; (ext,attrs) = ext_attributes; e = SELF; "with"; "parser"; po = OPT ipatt; OPT "|";
        pcl = LIST1 parser_case SEP "|" ->
          expr_to_inline <:expr< $cparser_match loc e (po, pcl)$ >> ext attrs
      ] ]
  ;
  parser_case:
    [ [ "[<"; sp = stream_patt; ">]"; po = OPT ipatt; "->"; e = expr ->
          (sp, po, e) ] ]
  ;
  stream_patt:
    [ [ spc = stream_patt_comp -> [(spc, SpoNoth)]
      | spc = stream_patt_comp; ";" -> [(spc, SpoNoth)]
      | spc = stream_patt_comp; ";"; sp = stream_patt_kont ->
          [(spc, SpoNoth) :: sp]
      | spc = stream_patt_let; sp = stream_patt -> [spc :: sp]
      | -> [] ] ]
  ;
  stream_patt_kont:
    [ RIGHTA
      [ spc = stream_patt_comp_err -> [spc]
      | spc = stream_patt_comp_err; ";" -> [spc]
      | spc = stream_patt_comp_err; ";"; sp = stream_patt_kont -> [spc :: sp]
      | spc = stream_patt_let; sp = stream_patt_kont -> [spc :: sp] ] ]
  ;
  stream_patt_comp_err:
    [ [ spc = stream_patt_comp; "??"; e = expr LEVEL "expr1" ->
          (spc, SpoQues e)
      | spc = stream_patt_comp; "?!" -> (spc, SpoBang)
      | spc = stream_patt_comp -> (spc, SpoNoth) ] ]
  ;
  stream_patt_comp:
    [ [ "'"; p = patt; eo = V (OPT [ "when"; e = expr LEVEL "expr1" -> e ]) ->
          SpTrm loc p eo
      | "?="; pll = LIST1 lookahead SEP "|"; eo = V (OPT [ "when"; e = expr LEVEL "expr1" -> e ]) -> SpLhd loc pll eo
      | p = patt; "="; e = expr LEVEL "expr1" -> SpNtr loc p e
      | p = patt -> SpStr loc p ] ]
  ;
  stream_patt_let:
    [ [ "let"; p = ipatt; "="; e = expr; "in" -> (SpLet loc p e, SpoNoth) ] ]
  ;
  lookahead:
    [ [ "["; pl = LIST1 patt SEP ";"; "]" -> pl ] ]
  ;
  ipatt:
    [ [ i = LIDENT -> <:patt< $lid:i$ >>
      | "_" -> <:patt< _ >> ] ]
  ;

  expr: LEVEL "simple"
    [ [ "[<"; ">]" -> <:expr< $cstream loc []$ >>
      | "[<"; sel = stream_expr_comp_list; ">]" ->
          <:expr< $cstream loc sel$ >> ] ]
  ;
  stream_expr_comp_list:
    [ RIGHTA
      [ se = stream_expr_comp; ";"; sel = SELF -> [se :: sel]
      | se = stream_expr_comp; ";" -> [se]
      | se = stream_expr_comp -> [se] ] ]
  ;
  stream_expr_comp:
    [ [ "'"; e = expr LEVEL "expr1" -> SeTrm loc e
      | e = expr LEVEL "expr1" -> SeNtr loc e ] ]
  ;
END;
