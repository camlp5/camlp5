(* camlp5r *)
(* pp_MLast.mli,v *)

IFDEF BOOTSTRAP THEN
module Gen : sig
module Ploc : sig
include (module type of Ploc with type t = Ploc.t)

val pp : Format.formatter -> t -> unit
type 'a vala = [%import: 'a Ploc.vala] [@@deriving show]
val pp_loc_verbose : bool ref

end

type loc = [%import: MLast.loc] [@@deriving show]
type type_var = [%import: MLast.type_var] [@@deriving show]

[%%import: MLast.expr] [@@deriving show]
end
END
