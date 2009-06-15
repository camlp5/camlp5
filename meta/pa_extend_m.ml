(* camlp5r pa_extend.cmo *)
(* $Id: pa_extend_m.ml,v 1.25 2007/09/20 19:31:19 deraugla Exp $ *)
(* Copyright (c) INRIA 2007 *)

open Pa_extend;

EXTEND
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
          ASquot loc (ASflag loc s)

      | UIDENT "SV"; UIDENT "LIST0"; s = SELF;
        sep = OPT [ UIDENT "SEP"; t = symbol -> t ] ->
          ASvala2 loc (ASquot loc (ASlist loc False s sep)) []
      | UIDENT "SV"; UIDENT "LIST1"; s = SELF;
        sep = OPT [ UIDENT "SEP"; t = symbol -> t ] ->
          ASvala2 loc (ASquot loc (ASlist loc True s sep)) []
      | UIDENT "SV"; UIDENT "OPT"; s = SELF ->
          ASvala2 loc (ASquot loc (ASopt loc s)) []
      | UIDENT "SV"; UIDENT "FLAG"; s = SELF ->
          ASvala2 loc (ASquot loc (ASflag loc s)) []
      | UIDENT "SV"; s = UIDENT ->
          ASvala2 loc (ASquot loc (AStok loc s None)) [] ] ]
  ;
END;
