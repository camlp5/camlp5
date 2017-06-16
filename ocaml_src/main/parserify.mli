(* camlp5r *)
(* parserify.mli,v *)
(* Copyright (c) INRIA 2007-2017 *)

type spat_comp =
    SpTrm of MLast.loc * MLast.patt * MLast.expr option MLast.v
  | SpNtr of MLast.loc * MLast.patt * MLast.expr
  | SpLet of MLast.loc * MLast.patt * MLast.expr
  | SpLhd of MLast.loc * MLast.patt list list
  | SpStr of MLast.loc * MLast.patt
;;

type spat_comp_opt =
    SpoNoth
  | SpoBang
  | SpoQues of MLast.expr
;;

val unparser_body :
  MLast.expr ->
    string option *
      ((spat_comp * spat_comp_opt) list * string option * MLast.expr) list;;
