(* camlp5r pa_extend.cmo *)
(* $Id: pa_extend_m.ml,v 1.29 2007/09/21 17:41:21 deraugla Exp $ *)
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
          ASquot loc (ASflag loc s) ] ]
  ;
  symbol: LEVEL "vala"
    [ [ UIDENT "SV"; s = NEXT; al = LIST0 STRING -> ASvala2 loc s al ] ]
  ;
END;
