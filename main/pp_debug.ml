(* camlp5r *)
(* pp_debug.ml,v *)

module Pp_MLast = struct

value ref_show_longid = ref (fun (_ : MLast.longid) -> "<longid>");
value ref_show_longid_lident =
  ref (fun (_ : MLast.longid_lident) -> "<longid_lident>")
;
value ref_show_ctyp = ref (fun (_ : MLast.ctyp) -> "<ctyp>");
value ref_show_expr = ref (fun (_ : MLast.expr) -> "<expr>");
value ref_show_patt = ref (fun (_ : MLast.patt) -> "<patt>");

value show_longid x = ref_show_longid.val x;
value show_longid_lident x = ref_show_longid_lident.val x;
value show_ctyp x = ref_show_ctyp.val x;
value show_expr x = ref_show_expr.val x;
value show_patt x = ref_show_patt.val x;

end;

module Pp_outcometree = struct
value ref_pp_out_sig_item = ref (fun pps (x : Outcometree.out_sig_item) ->
    Format.fprintf pps "<unrecognized out_sig_item>")
  ;
value ref_pp_out_sig_item_list = ref (fun pps (x : list Outcometree.out_sig_item) ->
    Format.fprintf pps "<unrecognized out_sig_item list>")
  ;

value pp_out_sig_item pps x = ref_pp_out_sig_item.val pps x ;
value pp_out_sig_item_list pps x = ref_pp_out_sig_item_list.val pps x ;

end ;
