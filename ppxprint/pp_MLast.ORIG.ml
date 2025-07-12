(* camlp5r *)
(* pp_MLast.ml,v *)

IFDEF BOOTSTRAP THEN

module Gen = struct
module Ploc = struct
include Ploc


let pp0_loc ppf loc =
  let fname = Ploc.file_name loc in
  let line = Ploc.line_nb loc in
  let bp = Ploc.first_pos loc in
  let ep = Ploc.last_pos loc in
  let bol = Ploc.bol_pos loc in

  let bp = bp - bol in
  let ep = ep - bol in
  Fmt.(pf ppf "<%a:%d:%d-%d>" (quote string) fname line bp ep)

let pp1_loc ppf x = Fmt.(const string "<loc>" ppf ())

let pp_loc_verbose = ref false

let pp ppf x =
  if !pp_loc_verbose then
    pp0_loc ppf x
  else
    pp1_loc ppf x

type 'a vala = [%import: 'a Ploc.vala] [@@deriving show]
end

type loc = [%import: MLast.loc] [@@deriving show]
type type_var = [%import: MLast.type_var] [@@deriving show]

[%%import: MLast.expr] [@@deriving show]

end

Pp_debug.Pp_MLast.ref_pp_longid := Gen.pp_longid;
Pp_debug.Pp_MLast.ref_pp_longid_lident := Gen.pp_longid_lident;
Pp_debug.Pp_MLast.ref_pp_ctyp := Gen.pp_ctyp;
Pp_debug.Pp_MLast.ref_pp_expr := Gen.pp_expr;
Pp_debug.Pp_MLast.ref_pp_patt := Gen.pp_patt;

END
