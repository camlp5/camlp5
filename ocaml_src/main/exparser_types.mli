(* camlp5r *)
(* exparser.ml,v *)
(* Copyright (c) INRIA 2007-2017 *)

type spat_comp =
    SpTrm of MLast.loc * MLast.patt * MLast.expr option MLast.v
  | SpNtr of MLast.loc * MLast.patt * MLast.expr
  | SpLet of MLast.loc * MLast.patt * MLast.expr
  | SpLhd of MLast.loc * MLast.patt list list * MLast.expr option MLast.v
  | SpStr of MLast.loc * MLast.patt
;;
type sexp_comp =
    SeTrm of MLast.loc * MLast.expr
  | SeNtr of MLast.loc * MLast.expr
;;

type spat_comp_opt =
    SpoNoth
  | SpoBang
  | SpoQues of MLast.expr
;;

type spat_parser_ast =
  MLast.patt option *
    ((spat_comp * spat_comp_opt) list * MLast.patt option * MLast.expr) list
;;
