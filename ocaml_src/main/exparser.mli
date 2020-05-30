(* camlp5r *)
(* exparser.mli,v *)
(* Copyright (c) INRIA 2007-2017 *)

(* expand parser ast into normal one *)

type spat_comp =
    SpTrm of MLast.loc * MLast.patt * MLast.expr option MLast.v
  | SpNtr of MLast.loc * MLast.patt * MLast.expr
  | SpLet of MLast.loc * MLast.patt * MLast.expr
  | SpLhd of MLast.loc * MLast.patt list list
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

val optim : bool ref;;

val strm_n : string;;

val cparser : MLast.loc -> spat_parser_ast -> MLast.expr;;

val cparser_match : MLast.loc -> MLast.expr -> spat_parser_ast -> MLast.expr;;

val cstream : MLast.loc -> sexp_comp list -> MLast.expr;;
