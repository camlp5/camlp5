(* camlp5r *)
(* exparser.mli,v *)
(* Copyright (c) INRIA 2007-2017 *)

(* expand parser ast into normal one *)

type spat_comp =
  [ SpTrm of MLast.loc and MLast.patt and MLast.v (option MLast.expr)
  | SpNtr of MLast.loc and MLast.patt and MLast.expr
  | SpLet of MLast.loc and MLast.patt and MLast.expr
  | SpLhd of MLast.loc and list (list MLast.patt)
  | SpStr of MLast.loc and MLast.patt ]
;

type sexp_comp =
  [ SeTrm of MLast.loc and MLast.expr
  | SeNtr of MLast.loc and MLast.expr ]
;

type spat_comp_opt =
  [ SpoNoth
  | SpoBang
  | SpoQues of MLast.expr ]
;

value strm_n : string;

value cparser :
  MLast.loc -> option MLast.patt ->
    list
      (list (spat_comp * spat_comp_opt) * option MLast.patt * MLast.expr) ->
    MLast.expr;

value cparser_match :
  MLast.loc -> MLast.expr -> option MLast.patt ->
    list
      (list (spat_comp * spat_comp_opt) * option MLast.patt * MLast.expr) ->
    MLast.expr;

value cstream : MLast.loc -> list sexp_comp -> MLast.expr;
