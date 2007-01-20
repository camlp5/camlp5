(* camlp4r *)
(***********************************************************************)
(*                                                                     *)
(*                             Camlp4                                  *)
(*                                                                     *)
(*                Daniel de Rauglaudre, INRIA Rocquencourt             *)
(*                                                                     *)
(*  Copyright 2007 Institut National de Recherche en Informatique et   *)
(*  Automatique.  Distributed only by permission.                      *)
(*                                                                     *)
(***********************************************************************)

(* $Id$ *)

(* expand parser ast into normal one *)

type spat_comp =
  [ SpTrm of MLast.loc and MLast.patt and option MLast.expr
  | SpNtr of MLast.loc and MLast.patt and MLast.expr
  | SpStr of MLast.loc and MLast.patt ]
;

type sexp_comp =
  [ SeTrm of MLast.loc and MLast.expr
  | SeNtr of MLast.loc and MLast.expr ]
;

value cparser :
  MLast.loc -> option MLast.patt ->
    list
      (list (spat_comp * option (option MLast.expr)) * option MLast.patt *
       MLast.expr) ->
    MLast.expr;

value cparser_match :
  MLast.loc -> MLast.expr -> option MLast.patt ->
    list
      (list (spat_comp * option (option MLast.expr)) * option MLast.patt *
       MLast.expr) ->
    MLast.expr;

value cstream : MLast.loc -> list sexp_comp -> MLast.expr;
