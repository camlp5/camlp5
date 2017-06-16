(* camlp5r *)
(* quotation.ml,v *)
(* Copyright (c) INRIA 2007-2017 *)

type expander =
    ExStr of (bool -> string -> string)
  | ExAst of ((string -> MLast.expr) * (string -> MLast.patt))
;;

let expanders_table = ref [];;

let default = ref "";;
let translate = ref (fun x -> x);;

let expander_name name =
  match !translate name with
    "" -> !default
  | name -> name
;;

let find name = List.assoc (expander_name name) !expanders_table;;

let add name f = expanders_table := (name, f) :: !expanders_table;;
