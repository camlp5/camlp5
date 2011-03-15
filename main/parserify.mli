(* camlp5r *)
(* $Id: parserify.mli,v 6.2 2011/03/15 13:49:11 deraugla Exp $ *)
(* Copyright (c) INRIA 2007-2011 *)

type spat_comp =
  [ SpTrm of MLast.loc and MLast.patt and MLast.v (option MLast.expr)
  | SpNtr of MLast.loc and MLast.patt and MLast.expr
  | SpLet of MLast.loc and MLast.patt and MLast.expr
  | SpLhd of MLast.loc and list (list MLast.patt)
  | SpStr of MLast.loc and MLast.patt ]
;

type spat_comp_opt =
  [ SpoNoth
  | SpoBang
  | SpoQues of MLast.expr ]
;

value unparser_body :
  MLast.expr ->
    (option string *
     list (list (spat_comp * spat_comp_opt) * option string * MLast.expr))
;
