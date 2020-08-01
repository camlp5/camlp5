(* camlp5r *)
(* pp_outcometree.mli,v *)

IFDEF BOOTSTRAP THEN

module Type_immediacy : sig
[%%import: Type_immediacy.t] [@@deriving show]
end

open Pp_parsetree

[%%import: Outcometree.out_name] [@@deriving show]
[%%import: Outcometree.out_ident] [@@deriving show]
[%%import: Outcometree.out_string] [@@deriving show]
[%%import: Outcometree.out_attribute] [@@deriving show]
[%%import: Outcometree.out_value] [@@deriving show]
[%%import: Outcometree.out_type] [@@deriving show]
[%%import: Outcometree.out_class_type] [@@deriving show]
[%%import: Outcometree.out_module_type] [@@deriving show]
[%%import: Outcometree.out_phrase [@with exn := Exceptions.t]] [@@deriving show]

ELSE
END


