(* camlp5r *)
module Lexing :
  sig
    type position =
      Lexing.position ==
        { pos_fname : string; pos_lnum : int; pos_bol : int; pos_cnum : int }[@@"deriving_inline" show;]
    ;
    value pp_position : Fmt.t position;
    value show_position : position → Stdlib.String.t;
    [@@@"end"];
  end
;
module Location :
  sig
    type t =
      Warnings.loc ==
        { loc_start : Lexing.position;
          loc_end : Lexing.position;
          loc_ghost : bool }[@@"deriving_inline" show;]
    ;
    value pp : Fmt.t t;
    value show : t → Stdlib.String.t;
    [@@@"end"];
    type loc α =
      Location.loc α == { txt : α; loc : t }[@@"deriving_inline" show;]
    ;
    value pp_loc : Fmt.t α → Fmt.t (loc α);
    value show_loc : Fmt.t α → loc α → Stdlib.String.t;
    [@@@"end"];
  end
;
module Longident :
  sig
    type t =
      Longident.t ==
        [ Lident of string
        | Ldot of t and string
        | Lapply of t and t ][@@"deriving_inline" show;]
    ;
    value pp : Fmt.t t;
    value show : t → Stdlib.String.t;
    [@@@"end"];
  end
;
module Asttypes :
  sig
    type loc α =
      Location.loc α == { txt : α; loc : Location.t }[@@"deriving_inline" show;]
    ;
    value pp_loc : Fmt.t α → Fmt.t (loc α);
    value show_loc : Fmt.t α → loc α → Stdlib.String.t;
    [@@@"end"];
    type arg_label =
      Asttypes.arg_label ==
        [ Nolabel
        | Labelled of string
        | Optional of string ][@@"deriving_inline" show;]
    ;
    value pp_arg_label : Fmt.t arg_label;
    value show_arg_label : arg_label → Stdlib.String.t;
    [@@@"end"];
    type label = string[@@"deriving_inline" show;];
    value pp_label : Fmt.t label;
    value show_label : label → Stdlib.String.t;
    [@@@"end"];
    type closed_flag =
      Asttypes.closed_flag == [ Closed | Open ][@@"deriving_inline" show;]
    ;
    value pp_closed_flag : Fmt.t closed_flag;
    value show_closed_flag : closed_flag → Stdlib.String.t;
    [@@@"end"];
    type rec_flag =
      Asttypes.rec_flag == [ Nonrecursive | Recursive ][@@"deriving_inline" show;]
    ;
    value pp_rec_flag : Fmt.t rec_flag;
    value show_rec_flag : rec_flag → Stdlib.String.t;
    [@@@"end"];
    type direction_flag =
      Asttypes.direction_flag == [ Upto | Downto ][@@"deriving_inline" show;]
    ;
    value pp_direction_flag : Fmt.t direction_flag;
    value show_direction_flag : direction_flag → Stdlib.String.t;
    [@@@"end"];
    type private_flag =
      Asttypes.private_flag == [ Private | Public ][@@"deriving_inline" show;]
    ;
    value pp_private_flag : Fmt.t private_flag;
    value show_private_flag : private_flag → Stdlib.String.t;
    [@@@"end"];
    type mutable_flag =
      Asttypes.mutable_flag == [ Immutable | Mutable ][@@"deriving_inline" show;]
    ;
    value pp_mutable_flag : Fmt.t mutable_flag;
    value show_mutable_flag : mutable_flag → Stdlib.String.t;
    [@@@"end"];
    type virtual_flag =
      Asttypes.virtual_flag == [ Virtual | Concrete ][@@"deriving_inline" show;]
    ;
    value pp_virtual_flag : Fmt.t virtual_flag;
    value show_virtual_flag : virtual_flag → Stdlib.String.t;
    [@@@"end"];
    type override_flag =
      Asttypes.override_flag == [ Override | Fresh ][@@"deriving_inline" show;]
    ;
    value pp_override_flag : Fmt.t override_flag;
    value show_override_flag : override_flag → Stdlib.String.t;
    [@@@"end"];
    type variance =
      Asttypes.variance == [ Covariant | Contravariant | NoVariance ][@@"deriving_inline" show;]
    ;
    value pp_variance : Fmt.t variance;
    value show_variance : variance → Stdlib.String.t;
    [@@@"end"];
    type injectivity =
      Asttypes.injectivity == [ Injective | NoInjectivity ][@@"deriving_inline" show;]
    ;
    value pp_injectivity : Fmt.t injectivity;
    value show_injectivity : injectivity → Stdlib.String.t;
    [@@@"end"];
  end
;
type constant =
  Parsetree.constant ==
    { pconst_desc : constant_desc; pconst_loc : Location.t }
and constant_desc =
  Parsetree.constant_desc ==
    [ Pconst_integer of string and option char
    | Pconst_char of char
    | Pconst_string of string and Location.t and option string
    | Pconst_float of string and option char ][@@"deriving_inline" show;]
;
value pp_constant : Fmt.t constant;
value show_constant : constant → Stdlib.String.t;
value pp_constant_desc : Fmt.t constant_desc;
value show_constant_desc : constant_desc → Stdlib.String.t;
[@@@"end"];
type location_stack = list Location.t[@@"deriving_inline" show;];
value pp_location_stack : Fmt.t location_stack;
value show_location_stack : location_stack → Stdlib.String.t;
[@@@"end"];
type attribute =
  Parsetree.attribute ==
    { attr_name : Asttypes.loc string;
      attr_payload : payload;
      attr_loc : Location.t }
and extension = (Asttypes.loc string * payload)
and attributes = list attribute
and payload =
  Parsetree.payload ==
    [ PStr of structure
    | PSig of signature
    | PTyp of core_type
    | PPat of pattern and option expression ]
and core_type =
  Parsetree.core_type ==
    { ptyp_desc : core_type_desc;
      ptyp_loc : Location.t;
      ptyp_loc_stack : location_stack;
      ptyp_attributes : attributes }
and core_type_desc =
  Parsetree.core_type_desc ==
    [ Ptyp_any
    | Ptyp_var of string
    | Ptyp_arrow of Asttypes.arg_label and core_type and core_type
    | Ptyp_tuple of list core_type
    | Ptyp_constr of Asttypes.loc Longident.t and list core_type
    | Ptyp_object of list object_field and Asttypes.closed_flag
    | Ptyp_class of Asttypes.loc Longident.t and list core_type
    | Ptyp_alias of core_type and Asttypes.loc string
    | Ptyp_variant of
        list row_field and Asttypes.closed_flag and
          option (list Asttypes.label)
    | Ptyp_poly of list (Asttypes.loc string) and core_type
    | Ptyp_package of package_type
    | Ptyp_open of Asttypes.loc Longident.t and core_type
    | Ptyp_extension of extension ]
and package_type =
  (Asttypes.loc Longident.t * list (Asttypes.loc Longident.t * core_type))
and row_field =
  Parsetree.row_field ==
    { prf_desc : row_field_desc;
      prf_loc : Location.t;
      prf_attributes : attributes }
and row_field_desc =
  Parsetree.row_field_desc ==
    [ Rtag of Asttypes.loc Asttypes.label and bool and list core_type
    | Rinherit of core_type ]
and object_field =
  Parsetree.object_field ==
    { pof_desc : object_field_desc;
      pof_loc : Location.t;
      pof_attributes : attributes }
and object_field_desc =
  Parsetree.object_field_desc ==
    [ Otag of Asttypes.loc Asttypes.label and core_type
    | Oinherit of core_type ]
and pattern =
  Parsetree.pattern ==
    { ppat_desc : pattern_desc;
      ppat_loc : Location.t;
      ppat_loc_stack : location_stack;
      ppat_attributes : attributes }
and pattern_desc =
  Parsetree.pattern_desc ==
    [ Ppat_any
    | Ppat_var of Asttypes.loc string
    | Ppat_alias of pattern and Asttypes.loc string
    | Ppat_constant of constant
    | Ppat_interval of constant and constant
    | Ppat_tuple of list pattern
    | Ppat_construct of
        Asttypes.loc Longident.t and
          option (list (Asttypes.loc string) * pattern)
    | Ppat_variant of Asttypes.label and option pattern
    | Ppat_record of
        list (Asttypes.loc Longident.t * pattern) and Asttypes.closed_flag
    | Ppat_array of list pattern
    | Ppat_or of pattern and pattern
    | Ppat_constraint of pattern and core_type
    | Ppat_type of Asttypes.loc Longident.t
    | Ppat_lazy of pattern
    | Ppat_unpack of Asttypes.loc (option string)
    | Ppat_exception of pattern
    | Ppat_effect of pattern and pattern
    | Ppat_extension of extension
    | Ppat_open of Asttypes.loc Longident.t and pattern ]
and expression =
  Parsetree.expression ==
    { pexp_desc : expression_desc;
      pexp_loc : Location.t;
      pexp_loc_stack : location_stack;
      pexp_attributes : attributes }
and expression_desc =
  Parsetree.expression_desc ==
    [ Pexp_ident of Asttypes.loc Longident.t
    | Pexp_constant of constant
    | Pexp_let of Asttypes.rec_flag and list value_binding and expression
    | Pexp_function of
        list function_param and option type_constraint and function_body
    | Pexp_apply of expression and list (Asttypes.arg_label * expression)
    | Pexp_match of expression and list case
    | Pexp_try of expression and list case
    | Pexp_tuple of list expression
    | Pexp_construct of Asttypes.loc Longident.t and option expression
    | Pexp_variant of Asttypes.label and option expression
    | Pexp_record of
        list (Asttypes.loc Longident.t * expression) and option expression
    | Pexp_field of expression and Asttypes.loc Longident.t
    | Pexp_setfield of expression and Asttypes.loc Longident.t and expression
    | Pexp_array of list expression
    | Pexp_ifthenelse of expression and expression and option expression
    | Pexp_sequence of expression and expression
    | Pexp_while of expression and expression
    | Pexp_for of
        pattern and expression and expression and Asttypes.direction_flag and
          expression
    | Pexp_constraint of expression and core_type
    | Pexp_coerce of expression and option core_type and core_type
    | Pexp_send of expression and Asttypes.loc Asttypes.label
    | Pexp_new of Asttypes.loc Longident.t
    | Pexp_setinstvar of Asttypes.loc Asttypes.label and expression
    | Pexp_override of list (Asttypes.loc Asttypes.label * expression)
    | Pexp_letmodule of
        Asttypes.loc (option string) and module_expr and expression
    | Pexp_letexception of extension_constructor and expression
    | Pexp_assert of expression
    | Pexp_lazy of expression
    | Pexp_poly of expression and option core_type
    | Pexp_object of class_structure
    | Pexp_newtype of Asttypes.loc string and expression
    | Pexp_pack of module_expr
    | Pexp_open of open_declaration and expression
    | Pexp_letop of letop
    | Pexp_extension of extension
    | Pexp_unreachable ]
and case =
  Parsetree.case ==
    { pc_lhs : pattern; pc_guard : option expression; pc_rhs : expression }
and letop =
  Parsetree.letop ==
    { let_ : binding_op; ands : list binding_op; body : expression }
and binding_op =
  Parsetree.binding_op ==
    { pbop_op : Asttypes.loc string;
      pbop_pat : pattern;
      pbop_exp : expression;
      pbop_loc : Location.t }
and function_param_desc =
  Parsetree.function_param_desc ==
    [ Pparam_val of Asttypes.arg_label and option expression and pattern
    | Pparam_newtype of Asttypes.loc string ]
and function_param =
  Parsetree.function_param ==
    { pparam_loc : Location.t; pparam_desc : function_param_desc }
and function_body =
  Parsetree.function_body ==
    [ Pfunction_body of expression
    | Pfunction_cases of list case and Location.t and attributes ]
and type_constraint =
  Parsetree.type_constraint ==
    [ Pconstraint of core_type
    | Pcoerce of option core_type and core_type ]
and value_description =
  Parsetree.value_description ==
    { pval_name : Asttypes.loc string;
      pval_type : core_type;
      pval_prim : list string;
      pval_attributes : attributes;
      pval_loc : Location.t }
and type_declaration =
  Parsetree.type_declaration ==
    { ptype_name : Asttypes.loc string;
      ptype_params :
        list (core_type * (Asttypes.variance * Asttypes.injectivity));
      ptype_cstrs : list (core_type * core_type * Location.t);
      ptype_kind : type_kind;
      ptype_private : Asttypes.private_flag;
      ptype_manifest : option core_type;
      ptype_attributes : attributes;
      ptype_loc : Location.t }
and type_kind =
  Parsetree.type_kind ==
    [ Ptype_abstract
    | Ptype_variant of list constructor_declaration
    | Ptype_record of list label_declaration
    | Ptype_open ]
and label_declaration =
  Parsetree.label_declaration ==
    { pld_name : Asttypes.loc string;
      pld_mutable : Asttypes.mutable_flag;
      pld_type : core_type;
      pld_loc : Location.t;
      pld_attributes : attributes }
and constructor_declaration =
  Parsetree.constructor_declaration ==
    { pcd_name : Asttypes.loc string;
      pcd_vars : list (Asttypes.loc string);
      pcd_args : constructor_arguments;
      pcd_res : option core_type;
      pcd_loc : Location.t;
      pcd_attributes : attributes }
and constructor_arguments =
  Parsetree.constructor_arguments ==
    [ Pcstr_tuple of list core_type
    | Pcstr_record of list label_declaration ]
and type_extension =
  Parsetree.type_extension ==
    { ptyext_path : Asttypes.loc Longident.t;
      ptyext_params :
        list (core_type * (Asttypes.variance * Asttypes.injectivity));
      ptyext_constructors : list extension_constructor;
      ptyext_private : Asttypes.private_flag;
      ptyext_loc : Location.t;
      ptyext_attributes : attributes }
and extension_constructor =
  Parsetree.extension_constructor ==
    { pext_name : Asttypes.loc string;
      pext_kind : extension_constructor_kind;
      pext_loc : Location.t;
      pext_attributes : attributes }
and type_exception =
  Parsetree.type_exception ==
    { ptyexn_constructor : extension_constructor;
      ptyexn_loc : Location.t;
      ptyexn_attributes : attributes }
and extension_constructor_kind =
  Parsetree.extension_constructor_kind ==
    [ Pext_decl of
        list (Asttypes.loc string) and constructor_arguments and
          option core_type
    | Pext_rebind of Asttypes.loc Longident.t ]
and class_type =
  Parsetree.class_type ==
    { pcty_desc : class_type_desc;
      pcty_loc : Location.t;
      pcty_attributes : attributes }
and class_type_desc =
  Parsetree.class_type_desc ==
    [ Pcty_constr of Asttypes.loc Longident.t and list core_type
    | Pcty_signature of class_signature
    | Pcty_arrow of Asttypes.arg_label and core_type and class_type
    | Pcty_extension of extension
    | Pcty_open of open_description and class_type ]
and class_signature =
  Parsetree.class_signature ==
    { pcsig_self : core_type; pcsig_fields : list class_type_field }
and class_type_field =
  Parsetree.class_type_field ==
    { pctf_desc : class_type_field_desc;
      pctf_loc : Location.t;
      pctf_attributes : attributes }
and class_type_field_desc =
  Parsetree.class_type_field_desc ==
    [ Pctf_inherit of class_type
    | Pctf_val of
        (Asttypes.loc Asttypes.label * Asttypes.mutable_flag *
         Asttypes.virtual_flag * core_type)
    | Pctf_method of
        (Asttypes.loc Asttypes.label * Asttypes.private_flag *
         Asttypes.virtual_flag * core_type)
    | Pctf_constraint of (core_type * core_type)
    | Pctf_attribute of attribute
    | Pctf_extension of extension ]
and class_infos α =
  Parsetree.class_infos α ==
    { pci_virt : Asttypes.virtual_flag;
      pci_params :
        list (core_type * (Asttypes.variance * Asttypes.injectivity));
      pci_name : Asttypes.loc string;
      pci_expr : α;
      pci_loc : Location.t;
      pci_attributes : attributes }
and class_description = class_infos class_type
and class_type_declaration = class_infos class_type
and class_expr =
  Parsetree.class_expr ==
    { pcl_desc : class_expr_desc;
      pcl_loc : Location.t;
      pcl_attributes : attributes }
and class_expr_desc =
  Parsetree.class_expr_desc ==
    [ Pcl_constr of Asttypes.loc Longident.t and list core_type
    | Pcl_structure of class_structure
    | Pcl_fun of
        Asttypes.arg_label and option expression and pattern and class_expr
    | Pcl_apply of class_expr and list (Asttypes.arg_label * expression)
    | Pcl_let of Asttypes.rec_flag and list value_binding and class_expr
    | Pcl_constraint of class_expr and class_type
    | Pcl_extension of extension
    | Pcl_open of open_description and class_expr ]
and class_structure =
  Parsetree.class_structure ==
    { pcstr_self : pattern; pcstr_fields : list class_field }
and class_field =
  Parsetree.class_field ==
    { pcf_desc : class_field_desc;
      pcf_loc : Location.t;
      pcf_attributes : attributes }
and class_field_desc =
  Parsetree.class_field_desc ==
    [ Pcf_inherit of
        Asttypes.override_flag and class_expr and option (Asttypes.loc string)
    | Pcf_val of
        (Asttypes.loc Asttypes.label * Asttypes.mutable_flag *
         class_field_kind)
    | Pcf_method of
        (Asttypes.loc Asttypes.label * Asttypes.private_flag *
         class_field_kind)
    | Pcf_constraint of (core_type * core_type)
    | Pcf_initializer of expression
    | Pcf_attribute of attribute
    | Pcf_extension of extension ]
and class_field_kind =
  Parsetree.class_field_kind ==
    [ Cfk_virtual of core_type
    | Cfk_concrete of Asttypes.override_flag and expression ]
and class_declaration = class_infos class_expr
and module_type =
  Parsetree.module_type ==
    { pmty_desc : module_type_desc;
      pmty_loc : Location.t;
      pmty_attributes : attributes }
and module_type_desc =
  Parsetree.module_type_desc ==
    [ Pmty_ident of Asttypes.loc Longident.t
    | Pmty_signature of signature
    | Pmty_functor of functor_parameter and module_type
    | Pmty_with of module_type and list with_constraint
    | Pmty_typeof of module_expr
    | Pmty_extension of extension
    | Pmty_alias of Asttypes.loc Longident.t ]
and functor_parameter =
  Parsetree.functor_parameter ==
    [ Unit
    | Named of Asttypes.loc (option string) and module_type ]
and signature = list signature_item
and signature_item =
  Parsetree.signature_item ==
    { psig_desc : signature_item_desc; psig_loc : Location.t }
and signature_item_desc =
  Parsetree.signature_item_desc ==
    [ Psig_value of value_description
    | Psig_type of Asttypes.rec_flag and list type_declaration
    | Psig_typesubst of list type_declaration
    | Psig_typext of type_extension
    | Psig_exception of type_exception
    | Psig_module of module_declaration
    | Psig_modsubst of module_substitution
    | Psig_recmodule of list module_declaration
    | Psig_modtype of module_type_declaration
    | Psig_modtypesubst of module_type_declaration
    | Psig_open of open_description
    | Psig_include of include_description
    | Psig_class of list class_description
    | Psig_class_type of list class_type_declaration
    | Psig_attribute of attribute
    | Psig_extension of extension and attributes ]
and module_declaration =
  Parsetree.module_declaration ==
    { pmd_name : Asttypes.loc (option string);
      pmd_type : module_type;
      pmd_attributes : attributes;
      pmd_loc : Location.t }
and module_substitution =
  Parsetree.module_substitution ==
    { pms_name : Asttypes.loc string;
      pms_manifest : Asttypes.loc Longident.t;
      pms_attributes : attributes;
      pms_loc : Location.t }
and module_type_declaration =
  Parsetree.module_type_declaration ==
    { pmtd_name : Asttypes.loc string;
      pmtd_type : option module_type;
      pmtd_attributes : attributes;
      pmtd_loc : Location.t }
and open_infos α =
  Parsetree.open_infos α ==
    { popen_expr : α;
      popen_override : Asttypes.override_flag;
      popen_loc : Location.t;
      popen_attributes : attributes }
and open_description = open_infos (Asttypes.loc Longident.t)
and open_declaration = open_infos module_expr
and include_infos α =
  Parsetree.include_infos α ==
    { pincl_mod : α; pincl_loc : Location.t; pincl_attributes : attributes }
and include_description = include_infos module_type
and include_declaration = include_infos module_expr
and with_constraint =
  Parsetree.with_constraint ==
    [ Pwith_type of Asttypes.loc Longident.t and type_declaration
    | Pwith_module of Asttypes.loc Longident.t and Asttypes.loc Longident.t
    | Pwith_modtype of Asttypes.loc Longident.t and module_type
    | Pwith_modtypesubst of Asttypes.loc Longident.t and module_type
    | Pwith_typesubst of Asttypes.loc Longident.t and type_declaration
    | Pwith_modsubst of
        Asttypes.loc Longident.t and Asttypes.loc Longident.t ]
and module_expr =
  Parsetree.module_expr ==
    { pmod_desc : module_expr_desc;
      pmod_loc : Location.t;
      pmod_attributes : attributes }
and module_expr_desc =
  Parsetree.module_expr_desc ==
    [ Pmod_ident of Asttypes.loc Longident.t
    | Pmod_structure of structure
    | Pmod_functor of functor_parameter and module_expr
    | Pmod_apply of module_expr and module_expr
    | Pmod_apply_unit of module_expr
    | Pmod_constraint of module_expr and module_type
    | Pmod_unpack of expression
    | Pmod_extension of extension ]
and structure = list structure_item
and structure_item =
  Parsetree.structure_item ==
    { pstr_desc : structure_item_desc; pstr_loc : Location.t }
and structure_item_desc =
  Parsetree.structure_item_desc ==
    [ Pstr_eval of expression and attributes
    | Pstr_value of Asttypes.rec_flag and list value_binding
    | Pstr_primitive of value_description
    | Pstr_type of Asttypes.rec_flag and list type_declaration
    | Pstr_typext of type_extension
    | Pstr_exception of type_exception
    | Pstr_module of module_binding
    | Pstr_recmodule of list module_binding
    | Pstr_modtype of module_type_declaration
    | Pstr_open of open_declaration
    | Pstr_class of list class_declaration
    | Pstr_class_type of list class_type_declaration
    | Pstr_include of include_declaration
    | Pstr_attribute of attribute
    | Pstr_extension of extension and attributes ]
and value_constraint =
  Parsetree.value_constraint ==
    [ Pvc_constraint of
        { locally_abstract_univars : list (Asttypes.loc string);
          typ : core_type }
    | Pvc_coercion of { ground : option core_type; coercion : core_type } ]
and value_binding =
  Parsetree.value_binding ==
    { pvb_pat : pattern;
      pvb_expr : expression;
      pvb_constraint : option value_constraint;
      pvb_attributes : attributes;
      pvb_loc : Location.t }
and module_binding =
  Parsetree.module_binding ==
    { pmb_name : Asttypes.loc (option string);
      pmb_expr : module_expr;
      pmb_attributes : attributes;
      pmb_loc : Location.t }[@@"deriving_inline" show;]
;
value pp_attribute : Fmt.t attribute;
value show_attribute : attribute → Stdlib.String.t;
value pp_extension : Fmt.t extension;
value show_extension : extension → Stdlib.String.t;
value pp_attributes : Fmt.t attributes;
value show_attributes : attributes → Stdlib.String.t;
value pp_payload : Fmt.t payload;
value show_payload : payload → Stdlib.String.t;
value pp_core_type : Fmt.t core_type;
value show_core_type : core_type → Stdlib.String.t;
value pp_core_type_desc : Fmt.t core_type_desc;
value show_core_type_desc : core_type_desc → Stdlib.String.t;
value pp_package_type : Fmt.t package_type;
value show_package_type : package_type → Stdlib.String.t;
value pp_row_field : Fmt.t row_field;
value show_row_field : row_field → Stdlib.String.t;
value pp_row_field_desc : Fmt.t row_field_desc;
value show_row_field_desc : row_field_desc → Stdlib.String.t;
value pp_object_field : Fmt.t object_field;
value show_object_field : object_field → Stdlib.String.t;
value pp_object_field_desc : Fmt.t object_field_desc;
value show_object_field_desc : object_field_desc → Stdlib.String.t;
value pp_pattern : Fmt.t pattern;
value show_pattern : pattern → Stdlib.String.t;
value pp_pattern_desc : Fmt.t pattern_desc;
value show_pattern_desc : pattern_desc → Stdlib.String.t;
value pp_expression : Fmt.t expression;
value show_expression : expression → Stdlib.String.t;
value pp_expression_desc : Fmt.t expression_desc;
value show_expression_desc : expression_desc → Stdlib.String.t;
value pp_case : Fmt.t case;
value show_case : case → Stdlib.String.t;
value pp_letop : Fmt.t letop;
value show_letop : letop → Stdlib.String.t;
value pp_binding_op : Fmt.t binding_op;
value show_binding_op : binding_op → Stdlib.String.t;
value pp_function_param_desc : Fmt.t function_param_desc;
value show_function_param_desc : function_param_desc → Stdlib.String.t;
value pp_function_param : Fmt.t function_param;
value show_function_param : function_param → Stdlib.String.t;
value pp_function_body : Fmt.t function_body;
value show_function_body : function_body → Stdlib.String.t;
value pp_type_constraint : Fmt.t type_constraint;
value show_type_constraint : type_constraint → Stdlib.String.t;
value pp_value_description : Fmt.t value_description;
value show_value_description : value_description → Stdlib.String.t;
value pp_type_declaration : Fmt.t type_declaration;
value show_type_declaration : type_declaration → Stdlib.String.t;
value pp_type_kind : Fmt.t type_kind;
value show_type_kind : type_kind → Stdlib.String.t;
value pp_label_declaration : Fmt.t label_declaration;
value show_label_declaration : label_declaration → Stdlib.String.t;
value pp_constructor_declaration : Fmt.t constructor_declaration;
value show_constructor_declaration :
  constructor_declaration → Stdlib.String.t;
value pp_constructor_arguments : Fmt.t constructor_arguments;
value show_constructor_arguments : constructor_arguments → Stdlib.String.t;
value pp_type_extension : Fmt.t type_extension;
value show_type_extension : type_extension → Stdlib.String.t;
value pp_extension_constructor : Fmt.t extension_constructor;
value show_extension_constructor : extension_constructor → Stdlib.String.t;
value pp_type_exception : Fmt.t type_exception;
value show_type_exception : type_exception → Stdlib.String.t;
value pp_extension_constructor_kind : Fmt.t extension_constructor_kind;
value show_extension_constructor_kind :
  extension_constructor_kind → Stdlib.String.t;
value pp_class_type : Fmt.t class_type;
value show_class_type : class_type → Stdlib.String.t;
value pp_class_type_desc : Fmt.t class_type_desc;
value show_class_type_desc : class_type_desc → Stdlib.String.t;
value pp_class_signature : Fmt.t class_signature;
value show_class_signature : class_signature → Stdlib.String.t;
value pp_class_type_field : Fmt.t class_type_field;
value show_class_type_field : class_type_field → Stdlib.String.t;
value pp_class_type_field_desc : Fmt.t class_type_field_desc;
value show_class_type_field_desc : class_type_field_desc → Stdlib.String.t;
value pp_class_infos : Fmt.t α → Fmt.t (class_infos α);
value show_class_infos : Fmt.t α → class_infos α → Stdlib.String.t;
value pp_class_description : Fmt.t class_description;
value show_class_description : class_description → Stdlib.String.t;
value pp_class_type_declaration : Fmt.t class_type_declaration;
value show_class_type_declaration : class_type_declaration → Stdlib.String.t;
value pp_class_expr : Fmt.t class_expr;
value show_class_expr : class_expr → Stdlib.String.t;
value pp_class_expr_desc : Fmt.t class_expr_desc;
value show_class_expr_desc : class_expr_desc → Stdlib.String.t;
value pp_class_structure : Fmt.t class_structure;
value show_class_structure : class_structure → Stdlib.String.t;
value pp_class_field : Fmt.t class_field;
value show_class_field : class_field → Stdlib.String.t;
value pp_class_field_desc : Fmt.t class_field_desc;
value show_class_field_desc : class_field_desc → Stdlib.String.t;
value pp_class_field_kind : Fmt.t class_field_kind;
value show_class_field_kind : class_field_kind → Stdlib.String.t;
value pp_class_declaration : Fmt.t class_declaration;
value show_class_declaration : class_declaration → Stdlib.String.t;
value pp_module_type : Fmt.t module_type;
value show_module_type : module_type → Stdlib.String.t;
value pp_module_type_desc : Fmt.t module_type_desc;
value show_module_type_desc : module_type_desc → Stdlib.String.t;
value pp_functor_parameter : Fmt.t functor_parameter;
value show_functor_parameter : functor_parameter → Stdlib.String.t;
value pp_signature : Fmt.t signature;
value show_signature : signature → Stdlib.String.t;
value pp_signature_item : Fmt.t signature_item;
value show_signature_item : signature_item → Stdlib.String.t;
value pp_signature_item_desc : Fmt.t signature_item_desc;
value show_signature_item_desc : signature_item_desc → Stdlib.String.t;
value pp_module_declaration : Fmt.t module_declaration;
value show_module_declaration : module_declaration → Stdlib.String.t;
value pp_module_substitution : Fmt.t module_substitution;
value show_module_substitution : module_substitution → Stdlib.String.t;
value pp_module_type_declaration : Fmt.t module_type_declaration;
value show_module_type_declaration :
  module_type_declaration → Stdlib.String.t;
value pp_open_infos : Fmt.t α → Fmt.t (open_infos α);
value show_open_infos : Fmt.t α → open_infos α → Stdlib.String.t;
value pp_open_description : Fmt.t open_description;
value show_open_description : open_description → Stdlib.String.t;
value pp_open_declaration : Fmt.t open_declaration;
value show_open_declaration : open_declaration → Stdlib.String.t;
value pp_include_infos : Fmt.t α → Fmt.t (include_infos α);
value show_include_infos : Fmt.t α → include_infos α → Stdlib.String.t;
value pp_include_description : Fmt.t include_description;
value show_include_description : include_description → Stdlib.String.t;
value pp_include_declaration : Fmt.t include_declaration;
value show_include_declaration : include_declaration → Stdlib.String.t;
value pp_with_constraint : Fmt.t with_constraint;
value show_with_constraint : with_constraint → Stdlib.String.t;
value pp_module_expr : Fmt.t module_expr;
value show_module_expr : module_expr → Stdlib.String.t;
value pp_module_expr_desc : Fmt.t module_expr_desc;
value show_module_expr_desc : module_expr_desc → Stdlib.String.t;
value pp_structure : Fmt.t structure;
value show_structure : structure → Stdlib.String.t;
value pp_structure_item : Fmt.t structure_item;
value show_structure_item : structure_item → Stdlib.String.t;
value pp_structure_item_desc : Fmt.t structure_item_desc;
value show_structure_item_desc : structure_item_desc → Stdlib.String.t;
value pp_value_constraint : Fmt.t value_constraint;
value show_value_constraint : value_constraint → Stdlib.String.t;
value pp_value_binding : Fmt.t value_binding;
value show_value_binding : value_binding → Stdlib.String.t;
value pp_module_binding : Fmt.t module_binding;
value show_module_binding : module_binding → Stdlib.String.t;
[@@@"end"];


