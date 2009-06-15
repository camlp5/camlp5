(* camlp5r pa_extend.cmo *)
(* $Id: pa_extend_m.ml,v 1.24 2007/09/20 03:26:28 deraugla Exp $ *)
(* Copyright (c) INRIA 2007 *)

open Pa_extend;

EXTEND
  symbol: LEVEL "top"
    [ NONA
      [ UIDENT "SLIST0"; s = SELF;
        sep = OPT [ UIDENT "SEP"; t = symbol -> t ] ->
          sslist loc False sep s
      | UIDENT "SLIST1"; s = SELF;
        sep = OPT [ UIDENT "SEP"; t = symbol -> t ] ->
          sslist loc True sep s
      | UIDENT "SOPT"; s = SELF -> ssopt loc s
      | UIDENT "SFLAG"; s = SELF -> ssflag loc s

      | UIDENT "SV"; UIDENT "LIST0"; s = SELF;
        sep = OPT [ UIDENT "SEP"; t = symbol -> t ] ->
          ss2_of_ss loc [] (sslist loc False sep s)
      | UIDENT "SV"; UIDENT "LIST1"; s = SELF;
        sep = OPT [ UIDENT "SEP"; t = symbol -> t ] ->
          ss2_of_ss loc [] (sslist loc True sep s)
      | UIDENT "SV"; UIDENT "OPT"; s = SELF ->
          ss2_of_ss loc [] (ssopt loc s)
      | UIDENT "SV"; UIDENT "FLAG"; s = SELF ->
          ss2_of_ss loc [] (ssflag loc s)
      | UIDENT "SV"; s = UIDENT -> ss2_of_ss loc [] (sstoken loc s) ] ]
  ;
END;
