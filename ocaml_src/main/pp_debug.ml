(* camlp5r *)
(* pp_debug.ml,v *)

module Pp_MLast =
  struct
    let ref_show_loc = ref (fun (_ : MLast.loc) -> "<>");;
    let ref_show_type_var = ref (fun (_ : MLast.type_var) -> "<type_var>");;
    let ref_show_longid = ref (fun (_ : MLast.longid) -> "<longid>");;
    let ref_show_ctyp = ref (fun (_ : MLast.ctyp) -> "<ctyp>");;
    let ref_show_poly_variant =
      ref (fun (_ : MLast.poly_variant) -> "<poly_variant>")
    ;;
    let ref_show_patt = ref (fun (_ : MLast.patt) -> "<patt>");;
    let ref_show_expr = ref (fun (_ : MLast.expr) -> "<expr>");;
    let ref_show_case_branch =
      ref (fun (_ : MLast.case_branch) -> "<case_branch>")
    ;;
    let ref_show_module_type =
      ref (fun (_ : MLast.module_type) -> "<module_type>")
    ;;
    let ref_show_functor_parameter =
      ref (fun (_ : MLast.functor_parameter) -> "<functor_parameter>")
    ;;
    let ref_show_sig_item = ref (fun (_ : MLast.sig_item) -> "<sig_item>");;
    let ref_show_with_constr =
      ref (fun (_ : MLast.with_constr) -> "<with_constr>")
    ;;
    let ref_show_module_expr =
      ref (fun (_ : MLast.module_expr) -> "<module_expr>")
    ;;
    let ref_show_str_item = ref (fun (_ : MLast.str_item) -> "<str_item>");;
    let ref_show_type_decl =
      ref (fun (_ : MLast.type_decl) -> "<type_decl>")
    ;;
    let ref_show_generic_constructor =
      ref (fun (_ : MLast.generic_constructor) -> "<generic_constructor>")
    ;;
    let ref_show_extension_constructor =
      ref (fun (_ : MLast.extension_constructor) -> "<extension_constructor>")
    ;;
    let ref_show_type_extension =
      ref (fun (_ : MLast.type_extension) -> "<type_extension>")
    ;;
    let ref_show_class_type =
      ref (fun (_ : MLast.class_type) -> "<class_type>")
    ;;
    let ref_show_class_sig_item =
      ref (fun (_ : MLast.class_sig_item) -> "<class_sig_item>")
    ;;
    let ref_show_class_expr =
      ref (fun (_ : MLast.class_expr) -> "<class_expr>")
    ;;
    let ref_show_class_str_item =
      ref (fun (_ : MLast.class_str_item) -> "<class_str_item>")
    ;;
    let ref_show_longid_lident =
      ref (fun (_ : MLast.longid_lident) -> "<longid_lident>")
    ;;
    let ref_show_payload = ref (fun (_ : MLast.payload) -> "<payload>");;
    let ref_show_attribute_body =
      ref (fun (_ : MLast.attribute_body) -> "<attribute_body>")
    ;;
    let ref_show_attribute =
      ref (fun (_ : MLast.attribute) -> "<attribute>")
    ;;
    let ref_show_attributes_no_anti =
      ref (fun (_ : MLast.attributes_no_anti) -> "<attributes_no_anti>")
    ;;
    let ref_show_attributes =
      ref (fun (_ : MLast.attributes) -> "<attributes>")
    ;;
    let show_longid x = !ref_show_longid x;;
    let show_longid_lident x = !ref_show_longid_lident x;;
    let show_ctyp x = !ref_show_ctyp x;;
    let show_expr x = !ref_show_expr x;;
    let show_patt x = !ref_show_patt x;;
    let show_loc x = !ref_show_loc x;;
    let show_type_var x = !ref_show_type_var x;;
    let show_longid x = !ref_show_longid x;;
    let show_ctyp x = !ref_show_ctyp x;;
    let show_poly_variant x = !ref_show_poly_variant x;;
    let show_patt x = !ref_show_patt x;;
    let show_expr x = !ref_show_expr x;;
    let show_case_branch x = !ref_show_case_branch x;;
    let show_module_type x = !ref_show_module_type x;;
    let show_functor_parameter x = !ref_show_functor_parameter x;;
    let show_sig_item x = !ref_show_sig_item x;;
    let show_with_constr x = !ref_show_with_constr x;;
    let show_module_expr x = !ref_show_module_expr x;;
    let show_str_item x = !ref_show_str_item x;;
    let show_type_decl x = !ref_show_type_decl x;;
    let show_generic_constructor x = !ref_show_generic_constructor x;;
    let show_extension_constructor x = !ref_show_extension_constructor x;;
    let show_type_extension x = !ref_show_type_extension x;;
    let show_class_type x = !ref_show_class_type x;;
    let show_class_sig_item x = !ref_show_class_sig_item x;;
    let show_class_expr x = !ref_show_class_expr x;;
    let show_class_str_item x = !ref_show_class_str_item x;;
    let show_longid_lident x = !ref_show_longid_lident x;;
    let show_payload x = !ref_show_payload x;;
    let show_attribute_body x = !ref_show_attribute_body x;;
    let show_attribute x = !ref_show_attribute x;;
    let show_attributes_no_anti x = !ref_show_attributes_no_anti x;;
    let show_attributes x = !ref_show_attributes x;;
  end
;;

module Pp_outcometree =
  struct
    let ref_pp_out_sig_item =
      ref
        (fun pps (x : Outcometree.out_sig_item) ->
           Format.fprintf pps "<unrecognized out_sig_item>")
    ;;
    let ref_pp_out_sig_item_list =
      ref
        (fun pps (x : Outcometree.out_sig_item list) ->
           Format.fprintf pps "<unrecognized out_sig_item list>")
    ;;
    let pp_out_sig_item pps x = !ref_pp_out_sig_item pps x;;
    let pp_out_sig_item_list pps x = !ref_pp_out_sig_item_list pps x;;
  end
;;
