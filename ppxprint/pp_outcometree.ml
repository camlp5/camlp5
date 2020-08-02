(* camlp5r *)
(* camlp5r *)
(* pp_outcometree.ml,v *)

declare
  value pp_out_sig_item pps x =
    Format.fprintf pps "<unrecognized out_sig_item>"
  ;
  value pp_out_sig_item_list pps x =
    Format.fprintf pps "<unrecognized out_sig_item list>"
  ;
end;

