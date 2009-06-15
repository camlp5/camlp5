(* camlp5r pa_extend.cmo q_MLast.cmo *)
(* $Id: pa_extfold.ml,v 1.4 2007/07/27 22:32:27 deraugla Exp $ *)

open Pcaml;
open Pa_extend;

value sfold loc n foldfun f e s =
  let styp = STquo loc (new_type_var ()) in
  let e = <:expr< Extfold.$lid:foldfun$ $f$ $e$ >> in
  let t = STapp loc (STapp loc (STtyp <:ctyp< Extfold.t _ >>) s.styp) styp in
  {used = s.used; text = TXmeta loc n [s.text] e t; styp = styp}
;

value sfoldsep loc n foldfun f e s sep =
  let styp = STquo loc (new_type_var ()) in
  let e = <:expr< Extfold.$lid:foldfun$ $f$ $e$ >> in
  let t =
    STapp loc (STapp loc (STtyp <:ctyp< Extfold.tsep _ >>) s.styp) styp
  in
  {used = s.used @ sep.used; text = TXmeta loc n [s.text; sep.text] e t;
   styp = styp}
;

EXTEND
  GLOBAL: symbol;
  symbol: LEVEL "top"
    [ [ UIDENT "FOLD0"; f = simple_expr; e = simple_expr; s = SELF ->
          sfold loc "FOLD0" "sfold0" f e s
      | UIDENT "FOLD1"; f = simple_expr; e = simple_expr; s = SELF ->
          sfold loc "FOLD1" "sfold1" f e s
      | UIDENT "FOLD0"; f = simple_expr; e = simple_expr; s = SELF;
        UIDENT "SEP"; sep = SELF ->
          sfoldsep loc "FOLD0 SEP" "sfold0sep" f e s sep
      | UIDENT "FOLD1"; f = simple_expr; e = simple_expr; s = SELF;
        UIDENT "SEP"; sep = SELF ->
          sfoldsep loc "FOLD1 SEP" "sfold1sep" f e s sep ] ]
  ;
  simple_expr:
    [ [ e = expr LEVEL "simple" -> e ] ]
  ;
END;
