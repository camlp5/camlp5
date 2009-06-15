(* camlp5r pa_extend.cmo *)
(***********************************************************************)
(*                                                                     *)
(*                             Camlp5                                  *)
(*                                                                     *)
(*                Daniel de Rauglaudre, INRIA Rocquencourt             *)
(*                                                                     *)
(*  Copyright 2007 Institut National de Recherche en Informatique et   *)
(*  Automatique.  Distributed only by permission.                      *)
(*                                                                     *)
(***********************************************************************)

(* $Id: pa_extend_m.ml,v 1.20 2007/09/08 15:36:54 deraugla Exp $ *)

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
          sslist2 loc False sep s
      | UIDENT "SV"; UIDENT "LIST1"; s = SELF;
        sep = OPT [ UIDENT "SEP"; t = symbol -> t ] ->
          sslist2 loc True sep s
      | UIDENT "SV"; UIDENT "FLAG"; s = SELF ->
          ssflag2 loc s
      | UIDENT "SV"; s = UIDENT ->
          sstoken2 loc s ] ]
  ;
END;
