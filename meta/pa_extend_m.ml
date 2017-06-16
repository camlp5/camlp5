(* camlp5r *)
(* pa_extend_m.ml,v *)
(* Copyright (c) INRIA 2007-2017 *)

#load "pa_extend.cmo";
#load "q_MLast.cmo";

open Pa_extend;

EXTEND
  GLOBAL: symbol;
  symbol: LEVEL "top"
    [ NONA
      [ UIDENT "SLIST0"; s = SELF;
        sep = OPT [ UIDENT "SEP"; t = symbol -> (t, False) ] ->
          ASquot loc (ASlist loc LML_0 s sep)
      | UIDENT "SLIST1"; s = SELF;
        sep = OPT [ UIDENT "SEP"; t = symbol -> (t, False) ] ->
          ASquot loc (ASlist loc LML_1 s sep)
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
    [ [ i = LIDENT -> (i, <:expr< $lid:i$ >>) ] ]
  ;
END;
