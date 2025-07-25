(* camlp5r *)
(* pp_debug.ml,v *)

module Pp_MLast =
  struct
    let ref_pp_str_item =
      ref
        (fun pps (x : MLast.str_item) ->
           Format.fprintf pps "<unrecognized str_item>")
    ;;
    let ref_pp_loc =
      ref (fun pps (x : MLast.loc) -> Format.fprintf pps "<unrecognized loc>")
    ;;
    let ref_pp_type_var =
      ref
        (fun pps (x : MLast.type_var) ->
           Format.fprintf pps "<unrecognized type_var>")
    ;;
    let ref_pp_longid =
      ref
        (fun pps (x : MLast.longid) ->
           Format.fprintf pps "<unrecognized longid>")
    ;;
    let ref_pp_ctyp =
      ref
        (fun pps (x : MLast.ctyp) -> Format.fprintf pps "<unrecognized ctyp>")
    ;;
    let ref_pp_poly_variant =
      ref
        (fun pps (x : MLast.poly_variant) ->
           Format.fprintf pps "<unrecognized poly_variant>")
    ;;
    let ref_pp_patt =
      ref
        (fun pps (x : MLast.patt) -> Format.fprintf pps "<unrecognized patt>")
    ;;
    let ref_pp_expr =
      ref
        (fun pps (x : MLast.expr) -> Format.fprintf pps "<unrecognized expr>")
    ;;
    let ref_pp_case_branch =
      ref
        (fun pps (x : MLast.case_branch) ->
           Format.fprintf pps "<unrecognized case_branch>")
    ;;
    let ref_pp_module_type =
      ref
        (fun pps (x : MLast.module_type) ->
           Format.fprintf pps "<unrecognized module_type>")
    ;;
    let ref_pp_functor_parameter =
      ref
        (fun pps (x : MLast.functor_parameter) ->
           Format.fprintf pps "<unrecognized functor_parameter>")
    ;;
    let ref_pp_sig_item =
      ref
        (fun pps (x : MLast.sig_item) ->
           Format.fprintf pps "<unrecognized sig_item>")
    ;;
    let ref_pp_with_constr =
      ref
        (fun pps (x : MLast.with_constr) ->
           Format.fprintf pps "<unrecognized with_constr>")
    ;;
    let ref_pp_module_expr =
      ref
        (fun pps (x : MLast.module_expr) ->
           Format.fprintf pps "<unrecognized module_expr>")
    ;;
    let ref_pp_str_item =
      ref
        (fun pps (x : MLast.str_item) ->
           Format.fprintf pps "<unrecognized str_item>")
    ;;
    let ref_pp_type_decl =
      ref
        (fun pps (x : MLast.type_decl) ->
           Format.fprintf pps "<unrecognized type_decl>")
    ;;
    let ref_pp_generic_constructor =
      ref
        (fun pps (x : MLast.generic_constructor) ->
           Format.fprintf pps "<unrecognized generic_constructor>")
    ;;
    let ref_pp_extension_constructor =
      ref
        (fun pps (x : MLast.extension_constructor) ->
           Format.fprintf pps "<unrecognized extension_constructor>")
    ;;
    let ref_pp_type_extension =
      ref
        (fun pps (x : MLast.type_extension) ->
           Format.fprintf pps "<unrecognized type_extension>")
    ;;
    let ref_pp_class_type =
      ref
        (fun pps (x : MLast.class_type) ->
           Format.fprintf pps "<unrecognized class_type>")
    ;;
    let ref_pp_class_sig_item =
      ref
        (fun pps (x : MLast.class_sig_item) ->
           Format.fprintf pps "<unrecognized class_sig_item>")
    ;;
    let ref_pp_class_expr =
      ref
        (fun pps (x : MLast.class_expr) ->
           Format.fprintf pps "<unrecognized class_expr>")
    ;;
    let ref_pp_class_str_item =
      ref
        (fun pps (x : MLast.class_str_item) ->
           Format.fprintf pps "<unrecognized class_str_item>")
    ;;
    let ref_pp_longid_lident =
      ref
        (fun pps (x : MLast.longid_lident) ->
           Format.fprintf pps "<unrecognized longid_lident>")
    ;;
    let ref_pp_payload =
      ref
        (fun pps (x : MLast.payload) ->
           Format.fprintf pps "<unrecognized payload>")
    ;;
    let ref_pp_attribute_body =
      ref
        (fun pps (x : MLast.attribute_body) ->
           Format.fprintf pps "<unrecognized attribute_body>")
    ;;
    let ref_pp_attribute =
      ref
        (fun pps (x : MLast.attribute) ->
           Format.fprintf pps "<unrecognized attribute>")
    ;;
    let ref_pp_attributes_no_anti =
      ref
        (fun pps (x : MLast.attributes_no_anti) ->
           Format.fprintf pps "<unrecognized attributes_no_anti>")
    ;;
    let ref_pp_attributes =
      ref
        (fun pps (x : MLast.attributes) ->
           Format.fprintf pps "<unrecognized attributes>")
    ;;
    let pp_loc x = !ref_pp_loc x;;
    let pp_type_var x = !ref_pp_type_var x;;
    let pp_longid x = !ref_pp_longid x;;
    let pp_ctyp x = !ref_pp_ctyp x;;
    let pp_poly_variant x = !ref_pp_poly_variant x;;
    let pp_patt x = !ref_pp_patt x;;
    let pp_expr x = !ref_pp_expr x;;
    let pp_case_branch x = !ref_pp_case_branch x;;
    let pp_module_type x = !ref_pp_module_type x;;
    let pp_functor_parameter x = !ref_pp_functor_parameter x;;
    let pp_sig_item x = !ref_pp_sig_item x;;
    let pp_with_constr x = !ref_pp_with_constr x;;
    let pp_module_expr x = !ref_pp_module_expr x;;
    let pp_str_item x = !ref_pp_str_item x;;
    let pp_type_decl x = !ref_pp_type_decl x;;
    let pp_generic_constructor x = !ref_pp_generic_constructor x;;
    let pp_extension_constructor x = !ref_pp_extension_constructor x;;
    let pp_type_extension x = !ref_pp_type_extension x;;
    let pp_class_type x = !ref_pp_class_type x;;
    let pp_class_sig_item x = !ref_pp_class_sig_item x;;
    let pp_class_expr x = !ref_pp_class_expr x;;
    let pp_class_str_item x = !ref_pp_class_str_item x;;
    let pp_longid_lident x = !ref_pp_longid_lident x;;
    let pp_payload x = !ref_pp_payload x;;
    let pp_attribute_body x = !ref_pp_attribute_body x;;
    let pp_attribute x = !ref_pp_attribute x;;
    let pp_attributes_no_anti x = !ref_pp_attributes_no_anti x;;
    let pp_attributes x = !ref_pp_attributes x;;
    let show_fun ppf x = Format.asprintf "%a" ppf x;;
    let show_loc x = show_fun pp_loc x;;
    let show_type_var x = show_fun pp_type_var x;;
    let show_longid x = show_fun pp_longid x;;
    let show_ctyp x = show_fun pp_ctyp x;;
    let show_poly_variant x = show_fun pp_poly_variant x;;
    let show_patt x = show_fun pp_patt x;;
    let show_expr x = show_fun pp_expr x;;
    let show_case_branch x = show_fun pp_case_branch x;;
    let show_module_type x = show_fun pp_module_type x;;
    let show_functor_parameter x = show_fun pp_functor_parameter x;;
    let show_sig_item x = show_fun pp_sig_item x;;
    let show_with_constr x = show_fun pp_with_constr x;;
    let show_module_expr x = show_fun pp_module_expr x;;
    let show_str_item x = show_fun pp_str_item x;;
    let show_type_decl x = show_fun pp_type_decl x;;
    let show_generic_constructor x = show_fun pp_generic_constructor x;;
    let show_extension_constructor x = show_fun pp_extension_constructor x;;
    let show_type_extension x = show_fun pp_type_extension x;;
    let show_class_type x = show_fun pp_class_type x;;
    let show_class_sig_item x = show_fun pp_class_sig_item x;;
    let show_class_expr x = show_fun pp_class_expr x;;
    let show_class_str_item x = show_fun pp_class_str_item x;;
    let show_longid_lident x = show_fun pp_longid_lident x;;
    let show_payload x = show_fun pp_payload x;;
    let show_attribute_body x = show_fun pp_attribute_body x;;
    let show_attribute x = show_fun pp_attribute x;;
    let show_attributes_no_anti x = show_fun pp_attributes_no_anti x;;
    let show_attributes x = show_fun pp_attributes x;;
  end
;;

module Pp_outcometree =
  struct
    let ref_pp_out_sig_item =
      ref
        (fun pps (x : Outcometree.out_sig_item) ->
           Format.fprintf pps "<unrecognized out_sig_item>")
    ;;
    let pp_out_sig_item x = !ref_pp_out_sig_item x;;
    let show_out_sig_item x = Pp_MLast.show_fun pp_out_sig_item x;;
  end
;;
