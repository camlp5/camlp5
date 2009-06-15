(* camlp5r pa_macro.cmo pa_extend.cmo *)
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

(* $Id: pa_extend_m.ml,v 1.16 2007/09/06 04:44:02 deraugla Exp $ *)

open Pa_extend;

EXTEND
  symbol: LEVEL "top"
    [ NONA
      [ min = [ UIDENT "SLIST0" -> False | UIDENT "SLIST1" -> True ];
        s = SELF; sep = OPT [ UIDENT "SEP"; t = symbol -> t ] ->
          sslist loc min sep s
      | UIDENT "SOPT"; s = SELF -> ssopt loc s
      | UIDENT "SFLAG"; s = SELF -> ssflag loc s
      | UIDENT "SFLAG2"; s = SELF ->
          IFNDEF STRICT THEN ssflag loc s ELSE ssflag2 loc s END ] ]
  ;
END;
