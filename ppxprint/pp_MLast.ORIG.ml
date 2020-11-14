(* camlp5r *)
(* pp_MLast.ml,v *)

IFDEF BOOTSTRAP THEN

module Gen = struct
module Ploc = struct
include Ploc

let pp ppf x = Format.fprintf ppf "<loc>"
type 'a vala = [%import: 'a Ploc.vala] [@@deriving show]
end

type loc = [%import: MLast.loc] [@@deriving show]
type type_var = [%import: MLast.type_var] [@@deriving show]

[%%import: MLast.expr] [@@deriving show]

end

open Ppx_debug
ref_show_longid := Gen.show_longid ;;
ref_show_longid_lident := Gen.show_longid_lident ;;
ref_show_ctyp := Gen.show_ctyp ;;
ref_show_expr := Gen.show_expr ;;
ref_show_patt := Gen.show_patt ;;

END
