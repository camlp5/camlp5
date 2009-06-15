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

(* $Id: pa_extend_m.ml,v 1.18 2007/09/07 13:24:52 deraugla Exp $ *)

open Pa_extend;

EXTEND
  symbol: LEVEL "top"
    [ NONA
      [ min = [ UIDENT "SLIST0" -> False | UIDENT "SLIST1" -> True ];
        s = SELF; sep = OPT [ UIDENT "SEP"; t = symbol -> t ] ->
          sslist loc min sep s
      | UIDENT "SOPT"; s = SELF -> ssopt loc s
      | UIDENT "SFLAG"; s = SELF -> ssflag loc s
      | UIDENT "V"; UIDENT "SFLAG"; s = SELF ->
          if Pcaml.strict_mode.val then ssflag2 loc s else ssflag loc s ] ]
  ;
END;
