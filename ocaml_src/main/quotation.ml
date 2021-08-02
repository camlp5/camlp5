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

let add name f =
  if List.mem_assoc name !expanders_table then
    begin
      Printf.fprintf stderr
        "Failure: Quotation.add: cannot add the quotation \"%s\" twice\n%!"
        name;
      Ploc.raise Ploc.dummy
        (Failure
           Printf.
           (sprintf "Quotation.add: cannot add the quotation \"%s\" twice"
             name))
    end
  else expanders_table := (name, f) :: !expanders_table
;;

let upsert name f =
  if List.mem_assoc name !expanders_table then
    Printf.fprintf stderr
      "Warning: Quotation.upsert: overwriting the quotation \"%s\"\n%!" name;
  expanders_table := (name, f) :: !expanders_table
;;
