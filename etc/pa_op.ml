(* camlp5r *)
(* pa_op.ml,v *)
(* Copyright (c) INRIA 2007-2017 *)

#load "pa_extend.cmo";
#load "q_MLast.cmo";

open Exparser;
open Pcaml;

(* Syntax extensions in Ocaml grammar *)

EXTEND
  GLOBAL: expr ipatt;
  expr: LEVEL "expr1"
    [ [ "parser"; po = OPT ipatt; OPT "|"; pcl = LIST1 parser_case SEP "|" ->
          <:expr< $cparser loc po pcl$ >>
      | "match"; e = SELF; "with"; "parser"; po = OPT ipatt; OPT "|";
        pcl = LIST1 parser_case SEP "|" ->
          <:expr< $cparser_match loc e po pcl$ >> ] ]
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
      | "?="; pll = LIST1 lookahead SEP "|" -> SpLhd loc pll
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
