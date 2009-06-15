(* camlp5r *)
(* $Id: parserify.mli,v 1.2 2007/12/27 10:30:24 deraugla Exp $ *)
(* Copyright (c) INRIA 2007-2008 *)

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
