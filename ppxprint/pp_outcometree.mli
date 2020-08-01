(* camlp5r *)
module Type_immediacy :
  sig
    type t =
      Type_immediacy.t == [ Unknown | Always | Always_on_64bits ][@@"deriving_inline" show;]
    ;
    value pp : Fmt.t t;
    value show : t → Stdlib.String.t;
    [@@@"end"];
  end
;
open Pp_parsetree;
type out_name =
  Outcometree.out_name == { printed_name : mutable string }[@@"deriving_inline" show;]
;
value pp_out_name : Fmt.t out_name;
value show_out_name : out_name → Stdlib.String.t;
[@@@"end"];
type out_ident =
  Outcometree.out_ident ==
    [ Oide_apply of out_ident and out_ident
    | Oide_dot of out_ident and string
    | Oide_ident of out_name ][@@"deriving_inline" show;]
;
value pp_out_ident : Fmt.t out_ident;
value show_out_ident : out_ident → Stdlib.String.t;
[@@@"end"];
type out_string =
  Outcometree.out_string == [ Ostr_string | Ostr_bytes ][@@"deriving_inline" show;]
;
value pp_out_string : Fmt.t out_string;
value show_out_string : out_string → Stdlib.String.t;
[@@@"end"];
type out_attribute =
  Outcometree.out_attribute == { oattr_name : string }[@@"deriving_inline" show;]
;
value pp_out_attribute : Fmt.t out_attribute;
value show_out_attribute : out_attribute → Stdlib.String.t;
[@@@"end"];
type out_value =
  Outcometree.out_value ==
    [ Oval_array of list out_value
    | Oval_char of char
    | Oval_constr of out_ident and list out_value
    | Oval_ellipsis
    | Oval_float of float
    | Oval_int of int
    | Oval_int32 of int32
    | Oval_int64 of int64
    | Oval_nativeint of nativeint
    | Oval_list of list out_value
    | Oval_printer of Format.formatter → unit
    | Oval_record of list (out_ident * out_value)
    | Oval_string of string and int and out_string
    | Oval_stuff of string
    | Oval_tuple of list out_value
    | Oval_variant of string and option out_value ][@@"deriving_inline" show;]
;
value pp_out_value : Fmt.t out_value;
value show_out_value : out_value → Stdlib.String.t;
[@@@"end"];
type out_type =
  Outcometree.out_type ==
    [ Otyp_abstract
    | Otyp_open
    | Otyp_alias of out_type and string
    | Otyp_arrow of string and out_type and out_type
    | Otyp_class of bool and out_ident and list out_type
    | Otyp_constr of out_ident and list out_type
    | Otyp_manifest of out_type and out_type
    | Otyp_object of list (string * out_type) and option bool
    | Otyp_record of list (string * bool * out_type)
    | Otyp_stuff of string
    | Otyp_sum of list (string * list out_type * option out_type)
    | Otyp_tuple of list out_type
    | Otyp_var of bool and string
    | Otyp_variant of bool and out_variant and bool and option (list string)
    | Otyp_poly of list string and out_type
    | Otyp_module of out_ident and list string and list out_type
    | Otyp_attribute of out_type and out_attribute ]
and out_variant =
  Outcometree.out_variant ==
    [ Ovar_fields of list (string * bool * list out_type)
    | Ovar_typ of out_type ][@@"deriving_inline" show;]
;
value pp_out_type : Fmt.t out_type;
value show_out_type : out_type → Stdlib.String.t;
value pp_out_variant : Fmt.t out_variant;
value show_out_variant : out_variant → Stdlib.String.t;
[@@@"end"];
type out_class_type =
  Outcometree.out_class_type ==
    [ Octy_constr of out_ident and list out_type
    | Octy_arrow of string and out_type and out_class_type
    | Octy_signature of option out_type and list out_class_sig_item ]
and out_class_sig_item =
  Outcometree.out_class_sig_item ==
    [ Ocsg_constraint of out_type and out_type
    | Ocsg_method of string and bool and bool and out_type
    | Ocsg_value of string and bool and bool and out_type ][@@"deriving_inline" show;]
;
value pp_out_class_type : Fmt.t out_class_type;
value show_out_class_type : out_class_type → Stdlib.String.t;
value pp_out_class_sig_item : Fmt.t out_class_sig_item;
value show_out_class_sig_item : out_class_sig_item → Stdlib.String.t;
[@@@"end"];
type out_module_type =
  Outcometree.out_module_type ==
    [ Omty_abstract
    | Omty_functor of
        option (option string * out_module_type) and out_module_type
    | Omty_ident of out_ident
    | Omty_signature of list out_sig_item
    | Omty_alias of out_ident ]
and out_sig_item =
  Outcometree.out_sig_item ==
    [ Osig_class of
        bool and string and list (string * (bool * bool)) and
          out_class_type and out_rec_status
    | Osig_class_type of
        bool and string and list (string * (bool * bool)) and
          out_class_type and out_rec_status
    | Osig_typext of out_extension_constructor and out_ext_status
    | Osig_modtype of string and out_module_type
    | Osig_module of string and out_module_type and out_rec_status
    | Osig_type of out_type_decl and out_rec_status
    | Osig_value of out_val_decl
    | Osig_ellipsis ]
and out_type_decl =
  Outcometree.out_type_decl ==
    { otype_name : string;
      otype_params : list (string * (bool * bool));
      otype_type : out_type;
      otype_private : Asttypes.private_flag;
      otype_immediate : Type_immediacy.t;
      otype_unboxed : bool;
      otype_cstrs : list (out_type * out_type) }
and out_extension_constructor =
  Outcometree.out_extension_constructor ==
    { oext_name : string;
      oext_type_name : string;
      oext_type_params : list string;
      oext_args : list out_type;
      oext_ret_type : option out_type;
      oext_private : Asttypes.private_flag }
and out_type_extension =
  Outcometree.out_type_extension ==
    { otyext_name : string;
      otyext_params : list string;
      otyext_constructors : list (string * list out_type * option out_type);
      otyext_private : Asttypes.private_flag }
and out_val_decl =
  Outcometree.out_val_decl ==
    { oval_name : string;
      oval_type : out_type;
      oval_prims : list string;
      oval_attributes : list out_attribute }
and out_rec_status =
  Outcometree.out_rec_status == [ Orec_not | Orec_first | Orec_next ]
and out_ext_status =
  Outcometree.out_ext_status == [ Oext_first | Oext_next | Oext_exception ][@@"deriving_inline" show;]
;
value pp_out_module_type : Fmt.t out_module_type;
value show_out_module_type : out_module_type → Stdlib.String.t;
value pp_out_sig_item : Fmt.t out_sig_item;
value show_out_sig_item : out_sig_item → Stdlib.String.t;
value pp_out_type_decl : Fmt.t out_type_decl;
value show_out_type_decl : out_type_decl → Stdlib.String.t;
value pp_out_extension_constructor : Fmt.t out_extension_constructor;
value show_out_extension_constructor :
  out_extension_constructor → Stdlib.String.t;
value pp_out_type_extension : Fmt.t out_type_extension;
value show_out_type_extension : out_type_extension → Stdlib.String.t;
value pp_out_val_decl : Fmt.t out_val_decl;
value show_out_val_decl : out_val_decl → Stdlib.String.t;
value pp_out_rec_status : Fmt.t out_rec_status;
value show_out_rec_status : out_rec_status → Stdlib.String.t;
value pp_out_ext_status : Fmt.t out_ext_status;
value show_out_ext_status : out_ext_status → Stdlib.String.t;
[@@@"end"];
type out_phrase =
  Outcometree.out_phrase ==
    [ Ophr_eval of out_value and out_type
    | Ophr_signature of list (out_sig_item * option out_value)
    | Ophr_exception of (Exceptions.t * out_value) ][@@"deriving_inline" show;]
;
value pp_out_phrase : Fmt.t out_phrase;
value show_out_phrase : out_phrase → Stdlib.String.t;
[@@@"end"];


