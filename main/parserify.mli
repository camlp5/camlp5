(* camlp5r *)
(* parserify.mli,v *)
(* Copyright (c) INRIA 2007-2017 *)

type spat_comp = Exparser.spat_comp ;

type spat_comp_opt = Exparser.spat_comp_opt ;

type spat_parser_ast = Exparser.spat_parser_ast ;

value unparser_body : MLast.expr -> spat_parser_ast
;
