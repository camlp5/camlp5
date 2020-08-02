(* camlp5r *)
(* camlp5r *)
(* pp_outcometree.mli,v *)

declare
  value pp_out_sig_item : Format.formatter → Outcometree.out_sig_item → unit;
  value pp_out_sig_item_list :
    Format.formatter → list Outcometree.out_sig_item → unit;
end;


