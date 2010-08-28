(* camlp5r *)
(* $Id: versdep.mli,v 1.5 2010/08/28 17:22:20 deraugla Exp $ *)
(* Copyright (c) INRIA 2007-2010 *)

open Parsetree;
open Asttypes;

value sys_ocaml_version : string;

value ocaml_location : (string * int * int * int * int) -> Location.t;

value ocaml_ptyp_poly : option (list string -> core_type -> core_type_desc);
value ocaml_type_declaration :
  list string -> list (core_type * core_type * Location.t) ->
    type_kind -> private_flag -> option core_type -> Location.t ->
    list (bool * bool) -> type_declaration;
value ocaml_ptype_record :
  list (string * mutable_flag * core_type * Location.t) -> 'a -> type_kind;
value ocaml_ptype_variant :
  list (string * list core_type * Location.t) -> 'a -> type_kind;
value ocaml_ptype_private : type_kind;
value ocaml_pwith_type :
  list string -> type_kind -> bool -> option core_type ->
    list (bool * bool) -> Location.t -> with_constraint;

value module_prefix_can_be_in_first_record_label_only : bool;

value ocaml_pexp_lazy : option (expression -> expression_desc);
value ocaml_const_int32 : option (string -> constant);
value ocaml_const_int64 : option (string -> constant);
value ocaml_const_nativeint : option (string -> constant);
value ocaml_pexp_object : option (class_structure -> expression_desc);

value ocaml_ppat_lazy : option (pattern -> pattern_desc);
value ocaml_ppat_record : list (Longident.t * pattern) -> pattern_desc;

value ocaml_psig_recmodule :
  option (list (string * module_type) -> signature_item_desc);
value ocaml_pstr_recmodule :
  option (list (string * module_type * module_expr) -> structure_item_desc);

value ocaml_pctf_val :
  (string * mutable_flag * core_type * Location.t) -> class_type_field;
value ocaml_pcf_inher : class_expr -> option string -> class_field;
value ocaml_pcf_meth :
  (string * private_flag * expression * Location.t) -> class_field;
value ocaml_pcf_val :
  (string * mutable_flag * expression * Location.t) -> class_field;
value ocaml_pexp_poly :
  option (expression -> option core_type -> expression_desc);

value action_arg : string -> list string -> Arg.spec -> option (list string);
value arg_symbol : Arg.spec -> option (list string);
