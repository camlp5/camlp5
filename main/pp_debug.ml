(* camlp5r *)
(* pp_debug.ml,v *)

module Pp_MLast = struct

value ref_pp_str_item = ref (fun pps (x : MLast.str_item) ->
    Format.fprintf pps "<unrecognized str_item>") ;

value ref_pp_loc = ref (fun pps (x : MLast.loc) ->
    Format.fprintf pps "<unrecognized loc>") ;

value ref_pp_type_var = ref (fun pps (x : MLast.type_var) ->
    Format.fprintf pps "<unrecognized type_var>") ;

value ref_pp_longid = ref (fun pps (x : MLast.longid) ->
    Format.fprintf pps "<unrecognized longid>") ;

value ref_pp_ctyp = ref (fun pps (x : MLast.ctyp) ->
    Format.fprintf pps "<unrecognized ctyp>") ;

value ref_pp_poly_variant = ref (fun pps (x : MLast.poly_variant) ->
    Format.fprintf pps "<unrecognized poly_variant>") ;

value ref_pp_patt = ref (fun pps (x : MLast.patt) ->
    Format.fprintf pps "<unrecognized patt>") ;

value ref_pp_expr = ref (fun pps (x : MLast.expr) ->
    Format.fprintf pps "<unrecognized expr>") ;

value ref_pp_case_branch = ref (fun pps (x : MLast.case_branch) ->
    Format.fprintf pps "<unrecognized case_branch>") ;

value ref_pp_module_type = ref (fun pps (x : MLast.module_type) ->
    Format.fprintf pps "<unrecognized module_type>") ;

value ref_pp_functor_parameter = ref (fun pps (x : MLast.functor_parameter) ->
    Format.fprintf pps "<unrecognized functor_parameter>") ;

value ref_pp_sig_item = ref (fun pps (x : MLast.sig_item) ->
    Format.fprintf pps "<unrecognized sig_item>") ;

value ref_pp_with_constr = ref (fun pps (x : MLast.with_constr) ->
    Format.fprintf pps "<unrecognized with_constr>") ;

value ref_pp_module_expr = ref (fun pps (x : MLast.module_expr) ->
    Format.fprintf pps "<unrecognized module_expr>") ;

value ref_pp_str_item = ref (fun pps (x : MLast.str_item) ->
    Format.fprintf pps "<unrecognized str_item>") ;

value ref_pp_type_decl = ref (fun pps (x : MLast.type_decl) ->
    Format.fprintf pps "<unrecognized type_decl>") ;

value ref_pp_generic_constructor = ref (fun pps (x : MLast.generic_constructor) ->
    Format.fprintf pps "<unrecognized generic_constructor>") ;

value ref_pp_extension_constructor = ref (fun pps (x : MLast.extension_constructor) ->
    Format.fprintf pps "<unrecognized extension_constructor>") ;

value ref_pp_type_extension = ref (fun pps (x : MLast.type_extension) ->
    Format.fprintf pps "<unrecognized type_extension>") ;

value ref_pp_class_type = ref (fun pps (x : MLast.class_type) ->
    Format.fprintf pps "<unrecognized class_type>") ;

value ref_pp_class_sig_item = ref (fun pps (x : MLast.class_sig_item) ->
    Format.fprintf pps "<unrecognized class_sig_item>") ;

value ref_pp_class_expr = ref (fun pps (x : MLast.class_expr) ->
    Format.fprintf pps "<unrecognized class_expr>") ;

value ref_pp_class_str_item = ref (fun pps (x : MLast.class_str_item) ->
    Format.fprintf pps "<unrecognized class_str_item>") ;

value ref_pp_longid_lident = ref (fun pps (x : MLast.longid_lident) ->
    Format.fprintf pps "<unrecognized longid_lident>") ;

value ref_pp_payload = ref (fun pps (x : MLast.payload) ->
    Format.fprintf pps "<unrecognized payload>") ;

value ref_pp_attribute_body = ref (fun pps (x : MLast.attribute_body) ->
    Format.fprintf pps "<unrecognized attribute_body>") ;

value ref_pp_attribute = ref (fun pps (x : MLast.attribute) ->
    Format.fprintf pps "<unrecognized attribute>") ;

value ref_pp_attributes_no_anti = ref (fun pps (x : MLast.attributes_no_anti) ->
    Format.fprintf pps "<unrecognized attributes_no_anti>") ;

value ref_pp_attributes = ref (fun pps (x : MLast.attributes) ->
    Format.fprintf pps "<unrecognized attributes>") ;

value pp_loc x = ref_pp_loc.val x ;
value pp_type_var x = ref_pp_type_var.val x ;
value pp_longid x = ref_pp_longid.val x ;
value pp_ctyp x = ref_pp_ctyp.val x ;
value pp_poly_variant x = ref_pp_poly_variant.val x ;
value pp_patt x = ref_pp_patt.val x ;
value pp_expr x = ref_pp_expr.val x ;
value pp_case_branch x = ref_pp_case_branch.val x ;
value pp_module_type x = ref_pp_module_type.val x ;
value pp_functor_parameter x = ref_pp_functor_parameter.val x ;
value pp_sig_item x = ref_pp_sig_item.val x ;
value pp_with_constr x = ref_pp_with_constr.val x ;
value pp_module_expr x = ref_pp_module_expr.val x ;
value pp_str_item x = ref_pp_str_item.val x ;
value pp_type_decl x = ref_pp_type_decl.val x ;
value pp_generic_constructor x = ref_pp_generic_constructor.val x ;
value pp_extension_constructor x = ref_pp_extension_constructor.val x ;
value pp_type_extension x = ref_pp_type_extension.val x ;
value pp_class_type x = ref_pp_class_type.val x ;
value pp_class_sig_item x = ref_pp_class_sig_item.val x ;
value pp_class_expr x = ref_pp_class_expr.val x ;
value pp_class_str_item x = ref_pp_class_str_item.val x ;
value pp_longid_lident x = ref_pp_longid_lident.val x ;
value pp_payload x = ref_pp_payload.val x ;
value pp_attribute_body x = ref_pp_attribute_body.val x ;
value pp_attribute x = ref_pp_attribute.val x ;
value pp_attributes_no_anti x = ref_pp_attributes_no_anti.val x ;
value pp_attributes x = ref_pp_attributes.val x ;

end;

module Pp_outcometree = struct

value ref_pp_out_sig_item = ref (fun pps (x : Outcometree.out_sig_item) ->
    Format.fprintf pps "<unrecognized out_sig_item>") ;

value pp_out_sig_item x = ref_pp_out_sig_item.val x ;

end ;
