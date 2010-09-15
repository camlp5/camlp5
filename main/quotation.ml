(* camlp5r *)
(* $Id: quotation.ml,v 6.1 2010/09/15 16:00:24 deraugla Exp $ *)
(* Copyright (c) INRIA 2007-2010 *)

type expander =
  [ ExStr of bool -> string -> string
  | ExAst of (string -> MLast.expr * string -> MLast.patt) ]
;

value expanders_table = ref [];

value default = ref "";
value translate = ref (fun x -> x);

value expander_name name =
  match translate.val name with
  [ "" -> default.val
  | name -> name ]
;

value find name = List.assoc (expander_name name) expanders_table.val;

value add name f = expanders_table.val := [(name, f) :: expanders_table.val];
