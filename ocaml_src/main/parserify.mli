(* camlp5r *)
(* parserify.mli,v *)
(* Copyright (c) INRIA 2007-2017 *)

type spat_comp = Exparser.spat_comp;;

type spat_comp_opt = Exparser.spat_comp_opt;;

val unparser_body :
  MLast.expr ->
    MLast.patt option *
      ((spat_comp * spat_comp_opt) list * MLast.patt option * MLast.expr)
        list;;
