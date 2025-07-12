(* camlp5r *)
(* pp_debug.ml,v *)

module Pp_MLast = struct

Pp_debug.Pp_MLast.ref_pp_loc.val := Pp_MLast.Gen.Ploc.pp ;
Pp_debug.Pp_MLast.ref_pp_type_var.val := Pp_MLast.Gen.pp_type_var ;

Pp_debug.Pp_MLast.ref_pp_longid.val := Pp_MLast.Gen.pp_longid ;
Pp_debug.Pp_MLast.ref_pp_ctyp.val := Pp_MLast.Gen.pp_ctyp ;
Pp_debug.Pp_MLast.ref_pp_poly_variant.val := Pp_MLast.Gen.pp_poly_variant ;
Pp_debug.Pp_MLast.ref_pp_patt.val := Pp_MLast.Gen.pp_patt ;
Pp_debug.Pp_MLast.ref_pp_expr.val := Pp_MLast.Gen.pp_expr ;
Pp_debug.Pp_MLast.ref_pp_case_branch.val := Pp_MLast.Gen.pp_case_branch ;
Pp_debug.Pp_MLast.ref_pp_module_type.val := Pp_MLast.Gen.pp_module_type ;
Pp_debug.Pp_MLast.ref_pp_functor_parameter.val := Pp_MLast.Gen.pp_functor_parameter ;
Pp_debug.Pp_MLast.ref_pp_sig_item.val := Pp_MLast.Gen.pp_sig_item ;
Pp_debug.Pp_MLast.ref_pp_with_constr.val := Pp_MLast.Gen.pp_with_constr ;
Pp_debug.Pp_MLast.ref_pp_module_expr.val := Pp_MLast.Gen.pp_module_expr ;
Pp_debug.Pp_MLast.ref_pp_str_item.val := Pp_MLast.Gen.pp_str_item ;
Pp_debug.Pp_MLast.ref_pp_type_decl.val := Pp_MLast.Gen.pp_type_decl ;
Pp_debug.Pp_MLast.ref_pp_generic_constructor.val := Pp_MLast.Gen.pp_generic_constructor ;
Pp_debug.Pp_MLast.ref_pp_extension_constructor.val := Pp_MLast.Gen.pp_extension_constructor ;
Pp_debug.Pp_MLast.ref_pp_type_extension.val := Pp_MLast.Gen.pp_type_extension ;
Pp_debug.Pp_MLast.ref_pp_class_type.val := Pp_MLast.Gen.pp_class_type ;
Pp_debug.Pp_MLast.ref_pp_class_sig_item.val := Pp_MLast.Gen.pp_class_sig_item ;
Pp_debug.Pp_MLast.ref_pp_class_expr.val := Pp_MLast.Gen.pp_class_expr ;
Pp_debug.Pp_MLast.ref_pp_class_str_item.val := Pp_MLast.Gen.pp_class_str_item ;
Pp_debug.Pp_MLast.ref_pp_longid_lident.val := Pp_MLast.Gen.pp_longid_lident ;
Pp_debug.Pp_MLast.ref_pp_payload.val := Pp_MLast.Gen.pp_payload ;
Pp_debug.Pp_MLast.ref_pp_attribute_body.val := Pp_MLast.Gen.pp_attribute_body ;
Pp_debug.Pp_MLast.ref_pp_attribute.val := Pp_MLast.Gen.pp_attribute ;
Pp_debug.Pp_MLast.ref_pp_attributes_no_anti.val := Pp_MLast.Gen.pp_attributes_no_anti ;
Pp_debug.Pp_MLast.ref_pp_attributes.val := Pp_MLast.Gen.pp_attributes ;

end;

module Pp_outcometree = struct

Pp_debug.Pp_outcometree.ref_pp_out_sig_item.val := Pp_outcometree.pp_out_sig_item ;

end ;
