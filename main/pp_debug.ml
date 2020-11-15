(* camlp5r *)
(* pp_debug.ml,v *)

module Pp_MLast = struct

value ref_show_loc = ref (fun (_ : MLast.loc) -> "<>") ;
value ref_show_type_var = ref (fun (_ : MLast.type_var) -> "<type_var>") ;
value ref_show_longid = ref (fun (_ : MLast.longid) -> "<longid>") ;
value ref_show_ctyp = ref (fun (_ : MLast.ctyp) -> "<ctyp>") ;
value ref_show_poly_variant = ref (fun (_ : MLast.poly_variant) -> "<poly_variant>") ;
value ref_show_patt = ref (fun (_ : MLast.patt) -> "<patt>") ;
value ref_show_expr = ref (fun (_ : MLast.expr) -> "<expr>") ;
value ref_show_case_branch = ref (fun (_ : MLast.case_branch) -> "<case_branch>") ;
value ref_show_module_type = ref (fun (_ : MLast.module_type) -> "<module_type>") ;
value ref_show_functor_parameter = ref (fun (_ : MLast.functor_parameter) -> "<functor_parameter>") ;
value ref_show_sig_item = ref (fun (_ : MLast.sig_item) -> "<sig_item>") ;
value ref_show_with_constr = ref (fun (_ : MLast.with_constr) -> "<with_constr>") ;
value ref_show_module_expr = ref (fun (_ : MLast.module_expr) -> "<module_expr>") ;
value ref_show_str_item = ref (fun (_ : MLast.str_item) -> "<str_item>") ;
value ref_show_type_decl = ref (fun (_ : MLast.type_decl) -> "<type_decl>") ;
value ref_show_generic_constructor = ref (fun (_ : MLast.generic_constructor) -> "<generic_constructor>") ;
value ref_show_extension_constructor = ref (fun (_ : MLast.extension_constructor) -> "<extension_constructor>") ;
value ref_show_type_extension = ref (fun (_ : MLast.type_extension) -> "<type_extension>") ;
value ref_show_class_type = ref (fun (_ : MLast.class_type) -> "<class_type>") ;
value ref_show_class_sig_item = ref (fun (_ : MLast.class_sig_item) -> "<class_sig_item>") ;
value ref_show_class_expr = ref (fun (_ : MLast.class_expr) -> "<class_expr>") ;
value ref_show_class_str_item = ref (fun (_ : MLast.class_str_item) -> "<class_str_item>") ;
value ref_show_longid_lident = ref (fun (_ : MLast.longid_lident) -> "<longid_lident>") ;
value ref_show_payload = ref (fun (_ : MLast.payload) -> "<payload>") ;
value ref_show_attribute_body = ref (fun (_ : MLast.attribute_body) -> "<attribute_body>") ;
value ref_show_attribute = ref (fun (_ : MLast.attribute) -> "<attribute>") ;
value ref_show_attributes_no_anti = ref (fun (_ : MLast.attributes_no_anti) -> "<attributes_no_anti>") ;
value ref_show_attributes = ref (fun (_ : MLast.attributes) -> "<attributes>") ;

value show_longid x = ref_show_longid.val x;
value show_longid_lident x = ref_show_longid_lident.val x;
value show_ctyp x = ref_show_ctyp.val x;
value show_expr x = ref_show_expr.val x;
value show_patt x = ref_show_patt.val x;
value show_loc x = ref_show_loc.val x ;
value show_type_var x = ref_show_type_var.val x ;
value show_longid x = ref_show_longid.val x ;
value show_ctyp x = ref_show_ctyp.val x ;
value show_poly_variant x = ref_show_poly_variant.val x ;
value show_patt x = ref_show_patt.val x ;
value show_expr x = ref_show_expr.val x ;
value show_case_branch x = ref_show_case_branch.val x ;
value show_module_type x = ref_show_module_type.val x ;
value show_functor_parameter x = ref_show_functor_parameter.val x ;
value show_sig_item x = ref_show_sig_item.val x ;
value show_with_constr x = ref_show_with_constr.val x ;
value show_module_expr x = ref_show_module_expr.val x ;
value show_str_item x = ref_show_str_item.val x ;
value show_type_decl x = ref_show_type_decl.val x ;
value show_generic_constructor x = ref_show_generic_constructor.val x ;
value show_extension_constructor x = ref_show_extension_constructor.val x ;
value show_type_extension x = ref_show_type_extension.val x ;
value show_class_type x = ref_show_class_type.val x ;
value show_class_sig_item x = ref_show_class_sig_item.val x ;
value show_class_expr x = ref_show_class_expr.val x ;
value show_class_str_item x = ref_show_class_str_item.val x ;
value show_longid_lident x = ref_show_longid_lident.val x ;
value show_payload x = ref_show_payload.val x ;
value show_attribute_body x = ref_show_attribute_body.val x ;
value show_attribute x = ref_show_attribute.val x ;
value show_attributes_no_anti x = ref_show_attributes_no_anti.val x ;
value show_attributes x = ref_show_attributes.val x ;

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
