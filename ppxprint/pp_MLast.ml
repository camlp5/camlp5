(* camlp5r *)
(* camlp5r *)
(* pp_MLast.ml,v *)

value ref_show_longid = ref (fun (_ : MLast.longid) → "<longid>");
value ref_show_longid_lident =
  ref (fun (_ : MLast.longid_lident) → "<longid_lident>")
;
value ref_show_ctyp = ref (fun (_ : MLast.ctyp) → "<ctyp>");
value ref_show_expr = ref (fun (_ : MLast.expr) → "<expr>");
value ref_show_patt = ref (fun (_ : MLast.patt) → "<patt>");

declare end;

value show_longid x = ref_show_longid.val x;
value show_longid_lident x = ref_show_longid_lident.val x;
value show_ctyp x = ref_show_ctyp.val x;
value show_expr x = ref_show_expr.val x;
value show_patt x = ref_show_patt.val x;
