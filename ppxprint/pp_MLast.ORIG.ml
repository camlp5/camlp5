(* camlp5r *)
(* pp_MLast.ml,v *)

IFDEF BOOTSTRAP THEN

module Ploc = struct
include Ploc

let pp ppf x = Fmt.(const string "<loc>" ppf ())
type 'a vala = [%import: 'a Ploc.vala] [@@deriving show]
end

type loc = [%import: MLast.loc] [@@deriving show]
type type_var = [%import: MLast.type_var] [@@deriving show]

[%%import: MLast.expr] [@@deriving show]

ELSE
let show_longid _ = "<longid>"
let show_longid_lident _ = "<longid_lident>"
let show_ctyp _ = "<ctyp>"

END
