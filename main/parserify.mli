(* camlp5r *)
(* parserify.mli,v *)
(* Copyright (c) INRIA 2007-2017 *)

type spat_comp = Exparser.spat_comp ;

type spat_comp_opt = Exparser.spat_comp_opt ;

value unparser_body :
  MLast.expr ->
    (option MLast.patt *
     list (list (spat_comp * spat_comp_opt) * option MLast.patt * MLast.expr))
;
