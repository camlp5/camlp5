(* camlp5r *)
(* pp_MLast.mli,v *)

IFDEF BOOTSTRAP THEN

module Ploc : sig
include (module type of Ploc with type t = Ploc.t)

val pp : Format.formatter -> t -> unit
type 'a vala = [%import: 'a Ploc.vala] [@@deriving show]
end

type loc = [%import: MLast.loc] [@@deriving show]
type type_var = [%import: MLast.type_var] [@@deriving show]

[%%import: MLast.expr] [@@deriving show]

ELSE
val show_longid : MLast.longid -> string
val show_longid_lident : MLast.longid_lident -> string
val show_ctyp : MLast.ctyp -> string
END


