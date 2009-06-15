(* camlp5r pa_extend.cmo q_MLast.cmo *)
(* $Id: pa_extend_m.ml,v 1.31 2007/09/30 21:41:52 deraugla Exp $ *)
(* Copyright (c) INRIA 2007 *)

open Pa_extend;

EXTEND
  GLOBAL: symbol;
  symbol: LEVEL "top"
    [ NONA
      [ UIDENT "SLIST0"; s = SELF;
        sep = OPT [ UIDENT "SEP"; t = symbol -> t ] ->
          ASquot loc (ASlist loc False s sep)
      | UIDENT "SLIST1"; s = SELF;
        sep = OPT [ UIDENT "SEP"; t = symbol -> t ] ->
          ASquot loc (ASlist loc True s sep)
      | UIDENT "SOPT"; s = SELF ->
          ASquot loc (ASopt loc s)
      | UIDENT "SFLAG"; s = SELF ->
          ASquot loc (ASflag loc s) ] ]
  ;
  symbol: LEVEL "vala"
    [ [ UIDENT "SV"; UIDENT "SELF"; al = LIST0 STRING; oe = OPT name ->
          let s = ASself loc in
          ASvala2 loc s al oe
      | UIDENT "SV"; UIDENT "NEXT"; al = LIST0 STRING; oe = OPT name ->
          let s = ASnext loc in
          ASvala2 loc s al oe
      | UIDENT "SV"; x = UIDENT; al = LIST0 STRING; oe = OPT name ->
          let s = AStok loc x None in
          ASvala2 loc s al oe
      | UIDENT "SV"; s = NEXT; al = LIST0 STRING; oe = OPT name ->
          ASvala2 loc s al oe ] ]
  ;
  name:
    [ [ i = LIDENT  -> (i, <:expr< $lid:i$ >>) ] ]
  ;
END;
