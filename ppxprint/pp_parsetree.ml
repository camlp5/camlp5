(* camlp5r *)
module Lexing =
  struct
    type position =
      Lexing.position ==
        { pos_fname : string; pos_lnum : int; pos_bol : int; pos_cnum : int }[@@"deriving_inline" show;]
    ;
    value rec pp_position : Fmt.t position =
      fun (ofmt : Format.formatter) arg →
        (fun ofmt
             ({pos_fname = v_pos_fname; pos_lnum = v_pos_lnum;
               pos_bol = v_pos_bol; pos_cnum = v_pos_cnum} :
              position) →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt
             "@[<2>{ @[Lexing.pos_fname =@ %a@];@ @[pos_lnum =@ %a@];@ @[pos_bol =@ %a@];@ @[pos_cnum =@ %a@] }@]"
             (fun ofmt arg →
                let open Ppxprint_runtime.Runtime.Fmt in pf ofmt "%S" arg)
             v_pos_fname
             (fun ofmt arg →
                let open Ppxprint_runtime.Runtime.Fmt in pf ofmt "%d" arg)
             v_pos_lnum
             (fun ofmt arg →
                let open Ppxprint_runtime.Runtime.Fmt in pf ofmt "%d" arg)
             v_pos_bol
             (fun ofmt arg →
                let open Ppxprint_runtime.Runtime.Fmt in pf ofmt "%d" arg)
             v_pos_cnum)
          ofmt arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
    and show_position : position → Stdlib.String.t =
      fun arg → Format.asprintf "%a" pp_position arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
    ;
    [@@@"end"];
  end
;
module Location =
  struct
    type t =
      Warnings.loc ==
        { loc_start : Lexing.position;
          loc_end : Lexing.position;
          loc_ghost : bool }[@@"deriving_inline" show;]
    ;
    value rec pp : Fmt.t t =
      fun (ofmt : Format.formatter) arg →
        (fun ofmt
             ({loc_start = v_loc_start; loc_end = v_loc_end;
               loc_ghost = v_loc_ghost} :
              t) →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt
             "@[<2>{ @[Warnings.loc_start =@ %a@];@ @[loc_end =@ %a@];@ @[loc_ghost =@ %a@] }@]"
             Lexing.pp_position v_loc_start Lexing.pp_position v_loc_end
             Fmt.bool v_loc_ghost)
          ofmt arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
    and show : t → Stdlib.String.t =
      fun arg → Format.asprintf "%a" pp arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
    ;
    [@@@"end"];
    type loc α =
      Location.loc α == { txt : α; loc : t }[@@"deriving_inline" show;]
    ;
    value rec pp_loc : ! α . Fmt.t α → Fmt.t (loc α) =
      fun (type a) (tp_0 : Fmt.t a) (ofmt : Format.formatter) arg →
        (fun ofmt ({txt = v_txt; loc = v_loc} : loc a) →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt
             "@[<2>{ @[Pp_parsetree.Location.txt =@ %a@];@ @[loc =@ %a@] }@]"
             tp_0 v_txt pp v_loc)
          ofmt arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
    and show_loc : ! α . Fmt.t α → loc α → Stdlib.String.t =
      fun (type a) (tp_0 : Fmt.t a) arg →
        Format.asprintf "%a" (pp_loc tp_0) arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
    ;
    [@@@"end"];
  end
;
module Longident =
  struct
    type t =
      Longident.t ==
        [ Lident of string
        | Ldot of t and string
        | Lapply of t and t ][@@"deriving_inline" show;]
    ;
    value rec pp : Fmt.t t =
      fun (ofmt : Format.formatter) arg →
        (fun ofmt →
           fun
           [ Lident v0 →
               let open Ppxprint_runtime.Runtime.Fmt in
               pf ofmt "(@[<2>Longident.Lident@ %a)@]"
                 (fun ofmt arg →
                    let open Ppxprint_runtime.Runtime.Fmt in pf ofmt "%S" arg)
                 v0
           | Ldot v0 v1 →
               let open Ppxprint_runtime.Runtime.Fmt in
               pf ofmt "(@[<2>Longident.Ldot@ (@,%a,@ %a@,))@]" pp v0
                 (fun ofmt arg →
                    let open Ppxprint_runtime.Runtime.Fmt in pf ofmt "%S" arg)
                 v1
           | Lapply v0 v1 →
               let open Ppxprint_runtime.Runtime.Fmt in
               pf ofmt "(@[<2>Longident.Lapply@ (@,%a,@ %a@,))@]" pp v0 pp
                 v1 ])
          ofmt arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
    and show : t → Stdlib.String.t =
      fun arg → Format.asprintf "%a" pp arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
    ;
    [@@@"end"];
  end
;
module Asttypes =
  struct
    type loc α =
      Location.loc α == { txt : α; loc : Location.t }[@@"deriving_inline" show;]
    ;
    value rec pp_loc : ! α . Fmt.t α → Fmt.t (loc α) =
      fun (type a) (tp_0 : Fmt.t a) (ofmt : Format.formatter) arg →
        (fun ofmt ({txt = v_txt; loc = v_loc} : loc a) →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt
             "@[<2>{ @[Pp_parsetree.Asttypes.txt =@ %a@];@ @[loc =@ %a@] }@]"
             tp_0 v_txt Location.pp v_loc)
          ofmt arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
    and show_loc : ! α . Fmt.t α → loc α → Stdlib.String.t =
      fun (type a) (tp_0 : Fmt.t a) arg →
        Format.asprintf "%a" (pp_loc tp_0) arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
    ;
    [@@@"end"];
    type arg_label =
      Asttypes.arg_label ==
        [ Nolabel
        | Labelled of string
        | Optional of string ][@@"deriving_inline" show;]
    ;
    value rec pp_arg_label : Fmt.t arg_label =
      fun (ofmt : Format.formatter) arg →
        (fun ofmt →
           fun
           [ Nolabel →
               let open Ppxprint_runtime.Runtime.Fmt in
               pf ofmt "@[<2>Asttypes.Nolabel@]"
           | Labelled v0 →
               let open Ppxprint_runtime.Runtime.Fmt in
               pf ofmt "(@[<2>Asttypes.Labelled@ %a)@]"
                 (fun ofmt arg →
                    let open Ppxprint_runtime.Runtime.Fmt in pf ofmt "%S" arg)
                 v0
           | Optional v0 →
               let open Ppxprint_runtime.Runtime.Fmt in
               pf ofmt "(@[<2>Asttypes.Optional@ %a)@]"
                 (fun ofmt arg →
                    let open Ppxprint_runtime.Runtime.Fmt in pf ofmt "%S" arg)
                 v0 ])
          ofmt arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
    and show_arg_label : arg_label → Stdlib.String.t =
      fun arg → Format.asprintf "%a" pp_arg_label arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
    ;
    [@@@"end"];
    type label = string[@@"deriving_inline" show;];
    value rec pp_label : Fmt.t label =
      fun (ofmt : Format.formatter) arg →
        (fun ofmt arg →
           let open Ppxprint_runtime.Runtime.Fmt in pf ofmt "%S" arg)
          ofmt arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
    and show_label : label → Stdlib.String.t =
      fun arg → Format.asprintf "%a" pp_label arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
    ;
    [@@@"end"];
    type closed_flag =
      Asttypes.closed_flag == [ Closed | Open ][@@"deriving_inline" show;]
    ;
    value rec pp_closed_flag : Fmt.t closed_flag =
      fun (ofmt : Format.formatter) arg →
        (fun ofmt →
           fun
           [ Closed →
               let open Ppxprint_runtime.Runtime.Fmt in
               pf ofmt "@[<2>Asttypes.Closed@]"
           | Open →
               let open Ppxprint_runtime.Runtime.Fmt in
               pf ofmt "@[<2>Asttypes.Open@]" ])
          ofmt arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
    and show_closed_flag : closed_flag → Stdlib.String.t =
      fun arg → Format.asprintf "%a" pp_closed_flag arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
    ;
    [@@@"end"];
    type rec_flag =
      Asttypes.rec_flag == [ Nonrecursive | Recursive ][@@"deriving_inline" show;]
    ;
    value rec pp_rec_flag : Fmt.t rec_flag =
      fun (ofmt : Format.formatter) arg →
        (fun ofmt →
           fun
           [ Nonrecursive →
               let open Ppxprint_runtime.Runtime.Fmt in
               pf ofmt "@[<2>Asttypes.Nonrecursive@]"
           | Recursive →
               let open Ppxprint_runtime.Runtime.Fmt in
               pf ofmt "@[<2>Asttypes.Recursive@]" ])
          ofmt arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
    and show_rec_flag : rec_flag → Stdlib.String.t =
      fun arg → Format.asprintf "%a" pp_rec_flag arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
    ;
    [@@@"end"];
    type direction_flag =
      Asttypes.direction_flag == [ Upto | Downto ][@@"deriving_inline" show;]
    ;
    value rec pp_direction_flag : Fmt.t direction_flag =
      fun (ofmt : Format.formatter) arg →
        (fun ofmt →
           fun
           [ Upto →
               let open Ppxprint_runtime.Runtime.Fmt in
               pf ofmt "@[<2>Asttypes.Upto@]"
           | Downto →
               let open Ppxprint_runtime.Runtime.Fmt in
               pf ofmt "@[<2>Asttypes.Downto@]" ])
          ofmt arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
    and show_direction_flag : direction_flag → Stdlib.String.t =
      fun arg → Format.asprintf "%a" pp_direction_flag arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
    ;
    [@@@"end"];
    type private_flag =
      Asttypes.private_flag == [ Private | Public ][@@"deriving_inline" show;]
    ;
    value rec pp_private_flag : Fmt.t private_flag =
      fun (ofmt : Format.formatter) arg →
        (fun ofmt →
           fun
           [ Private →
               let open Ppxprint_runtime.Runtime.Fmt in
               pf ofmt "@[<2>Asttypes.Private@]"
           | Public →
               let open Ppxprint_runtime.Runtime.Fmt in
               pf ofmt "@[<2>Asttypes.Public@]" ])
          ofmt arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
    and show_private_flag : private_flag → Stdlib.String.t =
      fun arg → Format.asprintf "%a" pp_private_flag arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
    ;
    [@@@"end"];
    type mutable_flag =
      Asttypes.mutable_flag == [ Immutable | Mutable ][@@"deriving_inline" show;]
    ;
    value rec pp_mutable_flag : Fmt.t mutable_flag =
      fun (ofmt : Format.formatter) arg →
        (fun ofmt →
           fun
           [ Immutable →
               let open Ppxprint_runtime.Runtime.Fmt in
               pf ofmt "@[<2>Asttypes.Immutable@]"
           | Mutable →
               let open Ppxprint_runtime.Runtime.Fmt in
               pf ofmt "@[<2>Asttypes.Mutable@]" ])
          ofmt arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
    and show_mutable_flag : mutable_flag → Stdlib.String.t =
      fun arg → Format.asprintf "%a" pp_mutable_flag arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
    ;
    [@@@"end"];
    type virtual_flag =
      Asttypes.virtual_flag == [ Virtual | Concrete ][@@"deriving_inline" show;]
    ;
    value rec pp_virtual_flag : Fmt.t virtual_flag =
      fun (ofmt : Format.formatter) arg →
        (fun ofmt →
           fun
           [ Virtual →
               let open Ppxprint_runtime.Runtime.Fmt in
               pf ofmt "@[<2>Asttypes.Virtual@]"
           | Concrete →
               let open Ppxprint_runtime.Runtime.Fmt in
               pf ofmt "@[<2>Asttypes.Concrete@]" ])
          ofmt arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
    and show_virtual_flag : virtual_flag → Stdlib.String.t =
      fun arg → Format.asprintf "%a" pp_virtual_flag arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
    ;
    [@@@"end"];
    type override_flag =
      Asttypes.override_flag == [ Override | Fresh ][@@"deriving_inline" show;]
    ;
    value rec pp_override_flag : Fmt.t override_flag =
      fun (ofmt : Format.formatter) arg →
        (fun ofmt →
           fun
           [ Override →
               let open Ppxprint_runtime.Runtime.Fmt in
               pf ofmt "@[<2>Asttypes.Override@]"
           | Fresh →
               let open Ppxprint_runtime.Runtime.Fmt in
               pf ofmt "@[<2>Asttypes.Fresh@]" ])
          ofmt arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
    and show_override_flag : override_flag → Stdlib.String.t =
      fun arg → Format.asprintf "%a" pp_override_flag arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
    ;
    [@@@"end"];
    type variance =
      Asttypes.variance == [ Covariant | Contravariant | NoVariance ][@@"deriving_inline" show;]
    ;
    value rec pp_variance : Fmt.t variance =
      fun (ofmt : Format.formatter) arg →
        (fun ofmt →
           fun
           [ Covariant →
               let open Ppxprint_runtime.Runtime.Fmt in
               pf ofmt "@[<2>Asttypes.Covariant@]"
           | Contravariant →
               let open Ppxprint_runtime.Runtime.Fmt in
               pf ofmt "@[<2>Asttypes.Contravariant@]"
           | NoVariance →
               let open Ppxprint_runtime.Runtime.Fmt in
               pf ofmt "@[<2>Asttypes.NoVariance@]" ])
          ofmt arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
    and show_variance : variance → Stdlib.String.t =
      fun arg → Format.asprintf "%a" pp_variance arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
    ;
    [@@@"end"];
    type injectivity =
      Asttypes.injectivity == [ Injective | NoInjectivity ][@@"deriving_inline" show;]
    ;
    value rec pp_injectivity : Fmt.t injectivity =
      fun (ofmt : Format.formatter) arg →
        (fun ofmt →
           fun
           [ Injective →
               let open Ppxprint_runtime.Runtime.Fmt in
               pf ofmt "@[<2>Asttypes.Injective@]"
           | NoInjectivity →
               let open Ppxprint_runtime.Runtime.Fmt in
               pf ofmt "@[<2>Asttypes.NoInjectivity@]" ])
          ofmt arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
    and show_injectivity : injectivity → Stdlib.String.t =
      fun arg → Format.asprintf "%a" pp_injectivity arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
    ;
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
value rec pp_constant : Fmt.t constant =
  fun (ofmt : Format.formatter) arg →
    (fun ofmt
         ({pconst_desc = v_pconst_desc; pconst_loc = v_pconst_loc} :
          constant) →
       let open Ppxprint_runtime.Runtime.Fmt in
       pf ofmt
         "@[<2>{ @[Parsetree.pconst_desc =@ %a@];@ @[pconst_loc =@ %a@] }@]"
         pp_constant_desc v_pconst_desc Location.pp v_pconst_loc)
      ofmt arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and show_constant : constant → Stdlib.String.t =
  fun arg → Format.asprintf "%a" pp_constant arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and pp_constant_desc : Fmt.t constant_desc =
  fun (ofmt : Format.formatter) arg →
    (fun ofmt →
       fun
       [ Pconst_integer v0 v1 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Parsetree.Pconst_integer@ (@,%a,@ %a@,))@]"
             (fun ofmt arg →
                let open Ppxprint_runtime.Runtime.Fmt in pf ofmt "%S" arg)
             v0
             (fun ofmt →
                fun
                [ None →
                    let open Ppxprint_runtime.Runtime.Fmt in
                    const string "None" ofmt ()
                | Some arg →
                    let open Ppxprint_runtime.Runtime.Fmt in
                    pf ofmt "(Some %a)"
                      (fun ofmt arg →
                         let open Ppxprint_runtime.Runtime.Fmt in
                         pf ofmt "%C" arg)
                      arg ])
             v1
       | Pconst_char v0 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Parsetree.Pconst_char@ %a)@]"
             (fun ofmt arg →
                let open Ppxprint_runtime.Runtime.Fmt in pf ofmt "%C" arg)
             v0
       | Pconst_string v0 v1 v2 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Parsetree.Pconst_string@ (@,%a,@ %a,@ %a@,))@]"
             (fun ofmt arg →
                let open Ppxprint_runtime.Runtime.Fmt in pf ofmt "%S" arg)
             v0 Location.pp v1
             (fun ofmt →
                fun
                [ None →
                    let open Ppxprint_runtime.Runtime.Fmt in
                    const string "None" ofmt ()
                | Some arg →
                    let open Ppxprint_runtime.Runtime.Fmt in
                    pf ofmt "(Some %a)"
                      (fun ofmt arg →
                         let open Ppxprint_runtime.Runtime.Fmt in
                         pf ofmt "%S" arg)
                      arg ])
             v2
       | Pconst_float v0 v1 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Parsetree.Pconst_float@ (@,%a,@ %a@,))@]"
             (fun ofmt arg →
                let open Ppxprint_runtime.Runtime.Fmt in pf ofmt "%S" arg)
             v0
             (fun ofmt →
                fun
                [ None →
                    let open Ppxprint_runtime.Runtime.Fmt in
                    const string "None" ofmt ()
                | Some arg →
                    let open Ppxprint_runtime.Runtime.Fmt in
                    pf ofmt "(Some %a)"
                      (fun ofmt arg →
                         let open Ppxprint_runtime.Runtime.Fmt in
                         pf ofmt "%C" arg)
                      arg ])
             v1 ])
      ofmt arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and show_constant_desc : constant_desc → Stdlib.String.t =
  fun arg → Format.asprintf "%a" pp_constant_desc arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
;
[@@@"end"];
type location_stack = list Location.t[@@"deriving_inline" show;];
value rec pp_location_stack : Fmt.t location_stack =
  fun (ofmt : Format.formatter) arg →
    (fun (ofmt : Format.formatter) arg →
       let open Ppxprint_runtime.Runtime.Fmt in
       pf ofmt "@[<2>[%a@,]@]" (list ~{sep = semi} Location.pp) arg)
      ofmt arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and show_location_stack : location_stack → Stdlib.String.t =
  fun arg → Format.asprintf "%a" pp_location_stack arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
;
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
value rec pp_attribute : Fmt.t attribute =
  fun (ofmt : Format.formatter) arg →
    (fun ofmt
         ({attr_name = v_attr_name; attr_payload = v_attr_payload;
           attr_loc = v_attr_loc} :
          attribute) →
       let open Ppxprint_runtime.Runtime.Fmt in
       pf ofmt
         "@[<2>{ @[Parsetree.attr_name =@ %a@];@ @[attr_payload =@ %a@];@ @[attr_loc =@ %a@] }@]"
         (Asttypes.pp_loc
            (fun ofmt arg →
               let open Ppxprint_runtime.Runtime.Fmt in pf ofmt "%S" arg))
         v_attr_name pp_payload v_attr_payload Location.pp v_attr_loc)
      ofmt arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and show_attribute : attribute → Stdlib.String.t =
  fun arg → Format.asprintf "%a" pp_attribute arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and pp_extension : Fmt.t extension =
  fun (ofmt : Format.formatter) arg →
    (fun (ofmt : Format.formatter) (v0, v1) →
       let open Ppxprint_runtime.Runtime.Fmt in
       pf ofmt "(@[%a,@ %a@])"
         (Asttypes.pp_loc
            (fun ofmt arg →
               let open Ppxprint_runtime.Runtime.Fmt in pf ofmt "%S" arg))
         v0 pp_payload v1)
      ofmt arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and show_extension : extension → Stdlib.String.t =
  fun arg → Format.asprintf "%a" pp_extension arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and pp_attributes : Fmt.t attributes =
  fun (ofmt : Format.formatter) arg →
    (fun (ofmt : Format.formatter) arg →
       let open Ppxprint_runtime.Runtime.Fmt in
       pf ofmt "@[<2>[%a@,]@]" (list ~{sep = semi} pp_attribute) arg)
      ofmt arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and show_attributes : attributes → Stdlib.String.t =
  fun arg → Format.asprintf "%a" pp_attributes arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and pp_payload : Fmt.t payload =
  fun (ofmt : Format.formatter) arg →
    (fun ofmt →
       fun
       [ PStr v0 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Parsetree.PStr@ %a)@]" pp_structure v0
       | PSig v0 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Parsetree.PSig@ %a)@]" pp_signature v0
       | PTyp v0 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Parsetree.PTyp@ %a)@]" pp_core_type v0
       | PPat v0 v1 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Parsetree.PPat@ (@,%a,@ %a@,))@]" pp_pattern v0
             (fun ofmt →
                fun
                [ None →
                    let open Ppxprint_runtime.Runtime.Fmt in
                    const string "None" ofmt ()
                | Some arg →
                    let open Ppxprint_runtime.Runtime.Fmt in
                    pf ofmt "(Some %a)" pp_expression arg ])
             v1 ])
      ofmt arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and show_payload : payload → Stdlib.String.t =
  fun arg → Format.asprintf "%a" pp_payload arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and pp_core_type : Fmt.t core_type =
  fun (ofmt : Format.formatter) arg →
    (fun ofmt
         ({ptyp_desc = v_ptyp_desc; ptyp_loc = v_ptyp_loc;
           ptyp_loc_stack = v_ptyp_loc_stack;
           ptyp_attributes = v_ptyp_attributes} :
          core_type) →
       let open Ppxprint_runtime.Runtime.Fmt in
       pf ofmt
         "@[<2>{ @[Parsetree.ptyp_desc =@ %a@];@ @[ptyp_loc =@ %a@];@ @[ptyp_loc_stack =@ %a@];@ @[ptyp_attributes =@ %a@] }@]"
         pp_core_type_desc v_ptyp_desc Location.pp v_ptyp_loc
         pp_location_stack v_ptyp_loc_stack pp_attributes v_ptyp_attributes)
      ofmt arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and show_core_type : core_type → Stdlib.String.t =
  fun arg → Format.asprintf "%a" pp_core_type arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and pp_core_type_desc : Fmt.t core_type_desc =
  fun (ofmt : Format.formatter) arg →
    (fun ofmt →
       fun
       [ Ptyp_any →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "@[<2>Parsetree.Ptyp_any@]"
       | Ptyp_var v0 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Parsetree.Ptyp_var@ %a)@]"
             (fun ofmt arg →
                let open Ppxprint_runtime.Runtime.Fmt in pf ofmt "%S" arg)
             v0
       | Ptyp_arrow v0 v1 v2 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Parsetree.Ptyp_arrow@ (@,%a,@ %a,@ %a@,))@]"
             Asttypes.pp_arg_label v0 pp_core_type v1 pp_core_type v2
       | Ptyp_tuple v0 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Parsetree.Ptyp_tuple@ %a)@]"
             (fun (ofmt : Format.formatter) arg →
                let open Ppxprint_runtime.Runtime.Fmt in
                pf ofmt "@[<2>[%a@,]@]" (list ~{sep = semi} pp_core_type) arg)
             v0
       | Ptyp_constr v0 v1 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Parsetree.Ptyp_constr@ (@,%a,@ %a@,))@]"
             (Asttypes.pp_loc Longident.pp) v0
             (fun (ofmt : Format.formatter) arg →
                let open Ppxprint_runtime.Runtime.Fmt in
                pf ofmt "@[<2>[%a@,]@]" (list ~{sep = semi} pp_core_type) arg)
             v1
       | Ptyp_object v0 v1 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Parsetree.Ptyp_object@ (@,%a,@ %a@,))@]"
             (fun (ofmt : Format.formatter) arg →
                let open Ppxprint_runtime.Runtime.Fmt in
                pf ofmt "@[<2>[%a@,]@]" (list ~{sep = semi} pp_object_field)
                  arg)
             v0 Asttypes.pp_closed_flag v1
       | Ptyp_class v0 v1 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Parsetree.Ptyp_class@ (@,%a,@ %a@,))@]"
             (Asttypes.pp_loc Longident.pp) v0
             (fun (ofmt : Format.formatter) arg →
                let open Ppxprint_runtime.Runtime.Fmt in
                pf ofmt "@[<2>[%a@,]@]" (list ~{sep = semi} pp_core_type) arg)
             v1
       | Ptyp_alias v0 v1 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Parsetree.Ptyp_alias@ (@,%a,@ %a@,))@]" pp_core_type
             v0
             (Asttypes.pp_loc
                (fun ofmt arg →
                   let open Ppxprint_runtime.Runtime.Fmt in pf ofmt "%S" arg))
             v1
       | Ptyp_variant v0 v1 v2 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Parsetree.Ptyp_variant@ (@,%a,@ %a,@ %a@,))@]"
             (fun (ofmt : Format.formatter) arg →
                let open Ppxprint_runtime.Runtime.Fmt in
                pf ofmt "@[<2>[%a@,]@]" (list ~{sep = semi} pp_row_field) arg)
             v0 Asttypes.pp_closed_flag v1
             (fun ofmt →
                fun
                [ None →
                    let open Ppxprint_runtime.Runtime.Fmt in
                    const string "None" ofmt ()
                | Some arg →
                    let open Ppxprint_runtime.Runtime.Fmt in
                    pf ofmt "(Some %a)"
                      (fun (ofmt : Format.formatter) arg →
                         let open Ppxprint_runtime.Runtime.Fmt in
                         pf ofmt "@[<2>[%a@,]@]"
                           (list ~{sep = semi} Asttypes.pp_label) arg)
                      arg ])
             v2
       | Ptyp_poly v0 v1 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Parsetree.Ptyp_poly@ (@,%a,@ %a@,))@]"
             (fun (ofmt : Format.formatter) arg →
                let open Ppxprint_runtime.Runtime.Fmt in
                pf ofmt "@[<2>[%a@,]@]"
                  (list ~{sep = semi}
                     (Asttypes.pp_loc
                        (fun ofmt arg →
                           let open Ppxprint_runtime.Runtime.Fmt in
                           pf ofmt "%S" arg)))
                  arg)
             v0 pp_core_type v1
       | Ptyp_package v0 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Parsetree.Ptyp_package@ %a)@]" pp_package_type v0
       | Ptyp_open v0 v1 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Parsetree.Ptyp_open@ (@,%a,@ %a@,))@]"
             (Asttypes.pp_loc Longident.pp) v0 pp_core_type v1
       | Ptyp_extension v0 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Parsetree.Ptyp_extension@ %a)@]" pp_extension v0 ])
      ofmt arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and show_core_type_desc : core_type_desc → Stdlib.String.t =
  fun arg → Format.asprintf "%a" pp_core_type_desc arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and pp_package_type : Fmt.t package_type =
  fun (ofmt : Format.formatter) arg →
    (fun (ofmt : Format.formatter) (v0, v1) →
       let open Ppxprint_runtime.Runtime.Fmt in
       pf ofmt "(@[%a,@ %a@])" (Asttypes.pp_loc Longident.pp) v0
         (fun (ofmt : Format.formatter) arg →
            let open Ppxprint_runtime.Runtime.Fmt in
            pf ofmt "@[<2>[%a@,]@]"
              (list ~{sep = semi}
                 (fun (ofmt : Format.formatter) (v0, v1) →
                    let open Ppxprint_runtime.Runtime.Fmt in
                    pf ofmt "(@[%a,@ %a@])" (Asttypes.pp_loc Longident.pp) v0
                      pp_core_type v1))
              arg)
         v1)
      ofmt arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and show_package_type : package_type → Stdlib.String.t =
  fun arg → Format.asprintf "%a" pp_package_type arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and pp_row_field : Fmt.t row_field =
  fun (ofmt : Format.formatter) arg →
    (fun ofmt
         ({prf_desc = v_prf_desc; prf_loc = v_prf_loc;
           prf_attributes = v_prf_attributes} :
          row_field) →
       let open Ppxprint_runtime.Runtime.Fmt in
       pf ofmt
         "@[<2>{ @[Parsetree.prf_desc =@ %a@];@ @[prf_loc =@ %a@];@ @[prf_attributes =@ %a@] }@]"
         pp_row_field_desc v_prf_desc Location.pp v_prf_loc pp_attributes
         v_prf_attributes)
      ofmt arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and show_row_field : row_field → Stdlib.String.t =
  fun arg → Format.asprintf "%a" pp_row_field arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and pp_row_field_desc : Fmt.t row_field_desc =
  fun (ofmt : Format.formatter) arg →
    (fun ofmt →
       fun
       [ Rtag v0 v1 v2 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Parsetree.Rtag@ (@,%a,@ %a,@ %a@,))@]"
             (Asttypes.pp_loc Asttypes.pp_label) v0 Fmt.bool v1
             (fun (ofmt : Format.formatter) arg →
                let open Ppxprint_runtime.Runtime.Fmt in
                pf ofmt "@[<2>[%a@,]@]" (list ~{sep = semi} pp_core_type) arg)
             v2
       | Rinherit v0 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Parsetree.Rinherit@ %a)@]" pp_core_type v0 ])
      ofmt arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and show_row_field_desc : row_field_desc → Stdlib.String.t =
  fun arg → Format.asprintf "%a" pp_row_field_desc arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and pp_object_field : Fmt.t object_field =
  fun (ofmt : Format.formatter) arg →
    (fun ofmt
         ({pof_desc = v_pof_desc; pof_loc = v_pof_loc;
           pof_attributes = v_pof_attributes} :
          object_field) →
       let open Ppxprint_runtime.Runtime.Fmt in
       pf ofmt
         "@[<2>{ @[Parsetree.pof_desc =@ %a@];@ @[pof_loc =@ %a@];@ @[pof_attributes =@ %a@] }@]"
         pp_object_field_desc v_pof_desc Location.pp v_pof_loc pp_attributes
         v_pof_attributes)
      ofmt arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and show_object_field : object_field → Stdlib.String.t =
  fun arg → Format.asprintf "%a" pp_object_field arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and pp_object_field_desc : Fmt.t object_field_desc =
  fun (ofmt : Format.formatter) arg →
    (fun ofmt →
       fun
       [ Otag v0 v1 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Parsetree.Otag@ (@,%a,@ %a@,))@]"
             (Asttypes.pp_loc Asttypes.pp_label) v0 pp_core_type v1
       | Oinherit v0 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Parsetree.Oinherit@ %a)@]" pp_core_type v0 ])
      ofmt arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and show_object_field_desc : object_field_desc → Stdlib.String.t =
  fun arg → Format.asprintf "%a" pp_object_field_desc arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and pp_pattern : Fmt.t pattern =
  fun (ofmt : Format.formatter) arg →
    (fun ofmt
         ({ppat_desc = v_ppat_desc; ppat_loc = v_ppat_loc;
           ppat_loc_stack = v_ppat_loc_stack;
           ppat_attributes = v_ppat_attributes} :
          pattern) →
       let open Ppxprint_runtime.Runtime.Fmt in
       pf ofmt
         "@[<2>{ @[Parsetree.ppat_desc =@ %a@];@ @[ppat_loc =@ %a@];@ @[ppat_loc_stack =@ %a@];@ @[ppat_attributes =@ %a@] }@]"
         pp_pattern_desc v_ppat_desc Location.pp v_ppat_loc pp_location_stack
         v_ppat_loc_stack pp_attributes v_ppat_attributes)
      ofmt arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and show_pattern : pattern → Stdlib.String.t =
  fun arg → Format.asprintf "%a" pp_pattern arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and pp_pattern_desc : Fmt.t pattern_desc =
  fun (ofmt : Format.formatter) arg →
    (fun ofmt →
       fun
       [ Ppat_any →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "@[<2>Parsetree.Ppat_any@]"
       | Ppat_var v0 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Parsetree.Ppat_var@ %a)@]"
             (Asttypes.pp_loc
                (fun ofmt arg →
                   let open Ppxprint_runtime.Runtime.Fmt in pf ofmt "%S" arg))
             v0
       | Ppat_alias v0 v1 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Parsetree.Ppat_alias@ (@,%a,@ %a@,))@]" pp_pattern
             v0
             (Asttypes.pp_loc
                (fun ofmt arg →
                   let open Ppxprint_runtime.Runtime.Fmt in pf ofmt "%S" arg))
             v1
       | Ppat_constant v0 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Parsetree.Ppat_constant@ %a)@]" pp_constant v0
       | Ppat_interval v0 v1 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Parsetree.Ppat_interval@ (@,%a,@ %a@,))@]"
             pp_constant v0 pp_constant v1
       | Ppat_tuple v0 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Parsetree.Ppat_tuple@ %a)@]"
             (fun (ofmt : Format.formatter) arg →
                let open Ppxprint_runtime.Runtime.Fmt in
                pf ofmt "@[<2>[%a@,]@]" (list ~{sep = semi} pp_pattern) arg)
             v0
       | Ppat_construct v0 v1 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Parsetree.Ppat_construct@ (@,%a,@ %a@,))@]"
             (Asttypes.pp_loc Longident.pp) v0
             (fun ofmt →
                fun
                [ None →
                    let open Ppxprint_runtime.Runtime.Fmt in
                    const string "None" ofmt ()
                | Some arg →
                    let open Ppxprint_runtime.Runtime.Fmt in
                    pf ofmt "(Some %a)"
                      (fun (ofmt : Format.formatter) (v0, v1) →
                         let open Ppxprint_runtime.Runtime.Fmt in
                         pf ofmt "(@[%a,@ %a@])"
                           (fun (ofmt : Format.formatter) arg →
                              let open Ppxprint_runtime.Runtime.Fmt in
                              pf ofmt "@[<2>[%a@,]@]"
                                (list ~{sep = semi}
                                   (Asttypes.pp_loc
                                      (fun ofmt arg →
                                         let open Ppxprint_runtime.Runtime.Fmt
                                         in
                                         pf ofmt "%S" arg)))
                                arg)
                           v0 pp_pattern v1)
                      arg ])
             v1
       | Ppat_variant v0 v1 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Parsetree.Ppat_variant@ (@,%a,@ %a@,))@]"
             Asttypes.pp_label v0
             (fun ofmt →
                fun
                [ None →
                    let open Ppxprint_runtime.Runtime.Fmt in
                    const string "None" ofmt ()
                | Some arg →
                    let open Ppxprint_runtime.Runtime.Fmt in
                    pf ofmt "(Some %a)" pp_pattern arg ])
             v1
       | Ppat_record v0 v1 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Parsetree.Ppat_record@ (@,%a,@ %a@,))@]"
             (fun (ofmt : Format.formatter) arg →
                let open Ppxprint_runtime.Runtime.Fmt in
                pf ofmt "@[<2>[%a@,]@]"
                  (list ~{sep = semi}
                     (fun (ofmt : Format.formatter) (v0, v1) →
                        let open Ppxprint_runtime.Runtime.Fmt in
                        pf ofmt "(@[%a,@ %a@])" (Asttypes.pp_loc Longident.pp)
                          v0 pp_pattern v1))
                  arg)
             v0 Asttypes.pp_closed_flag v1
       | Ppat_array v0 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Parsetree.Ppat_array@ %a)@]"
             (fun (ofmt : Format.formatter) arg →
                let open Ppxprint_runtime.Runtime.Fmt in
                pf ofmt "@[<2>[%a@,]@]" (list ~{sep = semi} pp_pattern) arg)
             v0
       | Ppat_or v0 v1 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Parsetree.Ppat_or@ (@,%a,@ %a@,))@]" pp_pattern v0
             pp_pattern v1
       | Ppat_constraint v0 v1 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Parsetree.Ppat_constraint@ (@,%a,@ %a@,))@]"
             pp_pattern v0 pp_core_type v1
       | Ppat_type v0 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Parsetree.Ppat_type@ %a)@]"
             (Asttypes.pp_loc Longident.pp) v0
       | Ppat_lazy v0 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Parsetree.Ppat_lazy@ %a)@]" pp_pattern v0
       | Ppat_unpack v0 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Parsetree.Ppat_unpack@ %a)@]"
             (Asttypes.pp_loc
                (fun ofmt →
                   fun
                   [ None →
                       let open Ppxprint_runtime.Runtime.Fmt in
                       const string "None" ofmt ()
                   | Some arg →
                       let open Ppxprint_runtime.Runtime.Fmt in
                       pf ofmt "(Some %a)"
                         (fun ofmt arg →
                            let open Ppxprint_runtime.Runtime.Fmt in
                            pf ofmt "%S" arg)
                         arg ]))
             v0
       | Ppat_exception v0 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Parsetree.Ppat_exception@ %a)@]" pp_pattern v0
       | Ppat_effect v0 v1 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Parsetree.Ppat_effect@ (@,%a,@ %a@,))@]" pp_pattern
             v0 pp_pattern v1
       | Ppat_extension v0 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Parsetree.Ppat_extension@ %a)@]" pp_extension v0
       | Ppat_open v0 v1 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Parsetree.Ppat_open@ (@,%a,@ %a@,))@]"
             (Asttypes.pp_loc Longident.pp) v0 pp_pattern v1 ])
      ofmt arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and show_pattern_desc : pattern_desc → Stdlib.String.t =
  fun arg → Format.asprintf "%a" pp_pattern_desc arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and pp_expression : Fmt.t expression =
  fun (ofmt : Format.formatter) arg →
    (fun ofmt
         ({pexp_desc = v_pexp_desc; pexp_loc = v_pexp_loc;
           pexp_loc_stack = v_pexp_loc_stack;
           pexp_attributes = v_pexp_attributes} :
          expression) →
       let open Ppxprint_runtime.Runtime.Fmt in
       pf ofmt
         "@[<2>{ @[Parsetree.pexp_desc =@ %a@];@ @[pexp_loc =@ %a@];@ @[pexp_loc_stack =@ %a@];@ @[pexp_attributes =@ %a@] }@]"
         pp_expression_desc v_pexp_desc Location.pp v_pexp_loc
         pp_location_stack v_pexp_loc_stack pp_attributes v_pexp_attributes)
      ofmt arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and show_expression : expression → Stdlib.String.t =
  fun arg → Format.asprintf "%a" pp_expression arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and pp_expression_desc : Fmt.t expression_desc =
  fun (ofmt : Format.formatter) arg →
    (fun ofmt →
       fun
       [ Pexp_ident v0 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Parsetree.Pexp_ident@ %a)@]"
             (Asttypes.pp_loc Longident.pp) v0
       | Pexp_constant v0 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Parsetree.Pexp_constant@ %a)@]" pp_constant v0
       | Pexp_let v0 v1 v2 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Parsetree.Pexp_let@ (@,%a,@ %a,@ %a@,))@]"
             Asttypes.pp_rec_flag v0
             (fun (ofmt : Format.formatter) arg →
                let open Ppxprint_runtime.Runtime.Fmt in
                pf ofmt "@[<2>[%a@,]@]" (list ~{sep = semi} pp_value_binding)
                  arg)
             v1 pp_expression v2
       | Pexp_function v0 v1 v2 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Parsetree.Pexp_function@ (@,%a,@ %a,@ %a@,))@]"
             (fun (ofmt : Format.formatter) arg →
                let open Ppxprint_runtime.Runtime.Fmt in
                pf ofmt "@[<2>[%a@,]@]" (list ~{sep = semi} pp_function_param)
                  arg)
             v0
             (fun ofmt →
                fun
                [ None →
                    let open Ppxprint_runtime.Runtime.Fmt in
                    const string "None" ofmt ()
                | Some arg →
                    let open Ppxprint_runtime.Runtime.Fmt in
                    pf ofmt "(Some %a)" pp_type_constraint arg ])
             v1 pp_function_body v2
       | Pexp_apply v0 v1 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Parsetree.Pexp_apply@ (@,%a,@ %a@,))@]"
             pp_expression v0
             (fun (ofmt : Format.formatter) arg →
                let open Ppxprint_runtime.Runtime.Fmt in
                pf ofmt "@[<2>[%a@,]@]"
                  (list ~{sep = semi}
                     (fun (ofmt : Format.formatter) (v0, v1) →
                        let open Ppxprint_runtime.Runtime.Fmt in
                        pf ofmt "(@[%a,@ %a@])" Asttypes.pp_arg_label v0
                          pp_expression v1))
                  arg)
             v1
       | Pexp_match v0 v1 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Parsetree.Pexp_match@ (@,%a,@ %a@,))@]"
             pp_expression v0
             (fun (ofmt : Format.formatter) arg →
                let open Ppxprint_runtime.Runtime.Fmt in
                pf ofmt "@[<2>[%a@,]@]" (list ~{sep = semi} pp_case) arg)
             v1
       | Pexp_try v0 v1 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Parsetree.Pexp_try@ (@,%a,@ %a@,))@]" pp_expression
             v0
             (fun (ofmt : Format.formatter) arg →
                let open Ppxprint_runtime.Runtime.Fmt in
                pf ofmt "@[<2>[%a@,]@]" (list ~{sep = semi} pp_case) arg)
             v1
       | Pexp_tuple v0 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Parsetree.Pexp_tuple@ %a)@]"
             (fun (ofmt : Format.formatter) arg →
                let open Ppxprint_runtime.Runtime.Fmt in
                pf ofmt "@[<2>[%a@,]@]" (list ~{sep = semi} pp_expression)
                  arg)
             v0
       | Pexp_construct v0 v1 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Parsetree.Pexp_construct@ (@,%a,@ %a@,))@]"
             (Asttypes.pp_loc Longident.pp) v0
             (fun ofmt →
                fun
                [ None →
                    let open Ppxprint_runtime.Runtime.Fmt in
                    const string "None" ofmt ()
                | Some arg →
                    let open Ppxprint_runtime.Runtime.Fmt in
                    pf ofmt "(Some %a)" pp_expression arg ])
             v1
       | Pexp_variant v0 v1 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Parsetree.Pexp_variant@ (@,%a,@ %a@,))@]"
             Asttypes.pp_label v0
             (fun ofmt →
                fun
                [ None →
                    let open Ppxprint_runtime.Runtime.Fmt in
                    const string "None" ofmt ()
                | Some arg →
                    let open Ppxprint_runtime.Runtime.Fmt in
                    pf ofmt "(Some %a)" pp_expression arg ])
             v1
       | Pexp_record v0 v1 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Parsetree.Pexp_record@ (@,%a,@ %a@,))@]"
             (fun (ofmt : Format.formatter) arg →
                let open Ppxprint_runtime.Runtime.Fmt in
                pf ofmt "@[<2>[%a@,]@]"
                  (list ~{sep = semi}
                     (fun (ofmt : Format.formatter) (v0, v1) →
                        let open Ppxprint_runtime.Runtime.Fmt in
                        pf ofmt "(@[%a,@ %a@])" (Asttypes.pp_loc Longident.pp)
                          v0 pp_expression v1))
                  arg)
             v0
             (fun ofmt →
                fun
                [ None →
                    let open Ppxprint_runtime.Runtime.Fmt in
                    const string "None" ofmt ()
                | Some arg →
                    let open Ppxprint_runtime.Runtime.Fmt in
                    pf ofmt "(Some %a)" pp_expression arg ])
             v1
       | Pexp_field v0 v1 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Parsetree.Pexp_field@ (@,%a,@ %a@,))@]"
             pp_expression v0 (Asttypes.pp_loc Longident.pp) v1
       | Pexp_setfield v0 v1 v2 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Parsetree.Pexp_setfield@ (@,%a,@ %a,@ %a@,))@]"
             pp_expression v0 (Asttypes.pp_loc Longident.pp) v1 pp_expression
             v2
       | Pexp_array v0 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Parsetree.Pexp_array@ %a)@]"
             (fun (ofmt : Format.formatter) arg →
                let open Ppxprint_runtime.Runtime.Fmt in
                pf ofmt "@[<2>[%a@,]@]" (list ~{sep = semi} pp_expression)
                  arg)
             v0
       | Pexp_ifthenelse v0 v1 v2 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Parsetree.Pexp_ifthenelse@ (@,%a,@ %a,@ %a@,))@]"
             pp_expression v0 pp_expression v1
             (fun ofmt →
                fun
                [ None →
                    let open Ppxprint_runtime.Runtime.Fmt in
                    const string "None" ofmt ()
                | Some arg →
                    let open Ppxprint_runtime.Runtime.Fmt in
                    pf ofmt "(Some %a)" pp_expression arg ])
             v2
       | Pexp_sequence v0 v1 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Parsetree.Pexp_sequence@ (@,%a,@ %a@,))@]"
             pp_expression v0 pp_expression v1
       | Pexp_while v0 v1 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Parsetree.Pexp_while@ (@,%a,@ %a@,))@]"
             pp_expression v0 pp_expression v1
       | Pexp_for v0 v1 v2 v3 v4 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Parsetree.Pexp_for@ (@,%a,@ %a,@ %a,@ %a,@ %a@,))@]"
             pp_pattern v0 pp_expression v1 pp_expression v2
             Asttypes.pp_direction_flag v3 pp_expression v4
       | Pexp_constraint v0 v1 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Parsetree.Pexp_constraint@ (@,%a,@ %a@,))@]"
             pp_expression v0 pp_core_type v1
       | Pexp_coerce v0 v1 v2 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Parsetree.Pexp_coerce@ (@,%a,@ %a,@ %a@,))@]"
             pp_expression v0
             (fun ofmt →
                fun
                [ None →
                    let open Ppxprint_runtime.Runtime.Fmt in
                    const string "None" ofmt ()
                | Some arg →
                    let open Ppxprint_runtime.Runtime.Fmt in
                    pf ofmt "(Some %a)" pp_core_type arg ])
             v1 pp_core_type v2
       | Pexp_send v0 v1 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Parsetree.Pexp_send@ (@,%a,@ %a@,))@]" pp_expression
             v0 (Asttypes.pp_loc Asttypes.pp_label) v1
       | Pexp_new v0 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Parsetree.Pexp_new@ %a)@]"
             (Asttypes.pp_loc Longident.pp) v0
       | Pexp_setinstvar v0 v1 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Parsetree.Pexp_setinstvar@ (@,%a,@ %a@,))@]"
             (Asttypes.pp_loc Asttypes.pp_label) v0 pp_expression v1
       | Pexp_override v0 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Parsetree.Pexp_override@ %a)@]"
             (fun (ofmt : Format.formatter) arg →
                let open Ppxprint_runtime.Runtime.Fmt in
                pf ofmt "@[<2>[%a@,]@]"
                  (list ~{sep = semi}
                     (fun (ofmt : Format.formatter) (v0, v1) →
                        let open Ppxprint_runtime.Runtime.Fmt in
                        pf ofmt "(@[%a,@ %a@])"
                          (Asttypes.pp_loc Asttypes.pp_label) v0 pp_expression
                          v1))
                  arg)
             v0
       | Pexp_letmodule v0 v1 v2 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Parsetree.Pexp_letmodule@ (@,%a,@ %a,@ %a@,))@]"
             (Asttypes.pp_loc
                (fun ofmt →
                   fun
                   [ None →
                       let open Ppxprint_runtime.Runtime.Fmt in
                       const string "None" ofmt ()
                   | Some arg →
                       let open Ppxprint_runtime.Runtime.Fmt in
                       pf ofmt "(Some %a)"
                         (fun ofmt arg →
                            let open Ppxprint_runtime.Runtime.Fmt in
                            pf ofmt "%S" arg)
                         arg ]))
             v0 pp_module_expr v1 pp_expression v2
       | Pexp_letexception v0 v1 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Parsetree.Pexp_letexception@ (@,%a,@ %a@,))@]"
             pp_extension_constructor v0 pp_expression v1
       | Pexp_assert v0 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Parsetree.Pexp_assert@ %a)@]" pp_expression v0
       | Pexp_lazy v0 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Parsetree.Pexp_lazy@ %a)@]" pp_expression v0
       | Pexp_poly v0 v1 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Parsetree.Pexp_poly@ (@,%a,@ %a@,))@]" pp_expression
             v0
             (fun ofmt →
                fun
                [ None →
                    let open Ppxprint_runtime.Runtime.Fmt in
                    const string "None" ofmt ()
                | Some arg →
                    let open Ppxprint_runtime.Runtime.Fmt in
                    pf ofmt "(Some %a)" pp_core_type arg ])
             v1
       | Pexp_object v0 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Parsetree.Pexp_object@ %a)@]" pp_class_structure v0
       | Pexp_newtype v0 v1 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Parsetree.Pexp_newtype@ (@,%a,@ %a@,))@]"
             (Asttypes.pp_loc
                (fun ofmt arg →
                   let open Ppxprint_runtime.Runtime.Fmt in pf ofmt "%S" arg))
             v0 pp_expression v1
       | Pexp_pack v0 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Parsetree.Pexp_pack@ %a)@]" pp_module_expr v0
       | Pexp_open v0 v1 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Parsetree.Pexp_open@ (@,%a,@ %a@,))@]"
             pp_open_declaration v0 pp_expression v1
       | Pexp_letop v0 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Parsetree.Pexp_letop@ %a)@]" pp_letop v0
       | Pexp_extension v0 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Parsetree.Pexp_extension@ %a)@]" pp_extension v0
       | Pexp_unreachable →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "@[<2>Parsetree.Pexp_unreachable@]" ])
      ofmt arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and show_expression_desc : expression_desc → Stdlib.String.t =
  fun arg → Format.asprintf "%a" pp_expression_desc arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and pp_case : Fmt.t case =
  fun (ofmt : Format.formatter) arg →
    (fun ofmt
         ({pc_lhs = v_pc_lhs; pc_guard = v_pc_guard; pc_rhs = v_pc_rhs} :
          case) →
       let open Ppxprint_runtime.Runtime.Fmt in
       pf ofmt
         "@[<2>{ @[Parsetree.pc_lhs =@ %a@];@ @[pc_guard =@ %a@];@ @[pc_rhs =@ %a@] }@]"
         pp_pattern v_pc_lhs
         (fun ofmt →
            fun
            [ None →
                let open Ppxprint_runtime.Runtime.Fmt in
                const string "None" ofmt ()
            | Some arg →
                let open Ppxprint_runtime.Runtime.Fmt in
                pf ofmt "(Some %a)" pp_expression arg ])
         v_pc_guard pp_expression v_pc_rhs)
      ofmt arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and show_case : case → Stdlib.String.t =
  fun arg → Format.asprintf "%a" pp_case arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and pp_letop : Fmt.t letop =
  fun (ofmt : Format.formatter) arg →
    (fun ofmt ({let_ = v_let_; ands = v_ands; body = v_body} : letop) →
       let open Ppxprint_runtime.Runtime.Fmt in
       pf ofmt
         "@[<2>{ @[Parsetree.let_ =@ %a@];@ @[ands =@ %a@];@ @[body =@ %a@] }@]"
         pp_binding_op v_let_
         (fun (ofmt : Format.formatter) arg →
            let open Ppxprint_runtime.Runtime.Fmt in
            pf ofmt "@[<2>[%a@,]@]" (list ~{sep = semi} pp_binding_op) arg)
         v_ands pp_expression v_body)
      ofmt arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and show_letop : letop → Stdlib.String.t =
  fun arg → Format.asprintf "%a" pp_letop arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and pp_binding_op : Fmt.t binding_op =
  fun (ofmt : Format.formatter) arg →
    (fun ofmt
         ({pbop_op = v_pbop_op; pbop_pat = v_pbop_pat; pbop_exp = v_pbop_exp;
           pbop_loc = v_pbop_loc} :
          binding_op) →
       let open Ppxprint_runtime.Runtime.Fmt in
       pf ofmt
         "@[<2>{ @[Parsetree.pbop_op =@ %a@];@ @[pbop_pat =@ %a@];@ @[pbop_exp =@ %a@];@ @[pbop_loc =@ %a@] }@]"
         (Asttypes.pp_loc
            (fun ofmt arg →
               let open Ppxprint_runtime.Runtime.Fmt in pf ofmt "%S" arg))
         v_pbop_op pp_pattern v_pbop_pat pp_expression v_pbop_exp Location.pp
         v_pbop_loc)
      ofmt arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and show_binding_op : binding_op → Stdlib.String.t =
  fun arg → Format.asprintf "%a" pp_binding_op arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and pp_function_param_desc : Fmt.t function_param_desc =
  fun (ofmt : Format.formatter) arg →
    (fun ofmt →
       fun
       [ Pparam_val v0 v1 v2 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Parsetree.Pparam_val@ (@,%a,@ %a,@ %a@,))@]"
             Asttypes.pp_arg_label v0
             (fun ofmt →
                fun
                [ None →
                    let open Ppxprint_runtime.Runtime.Fmt in
                    const string "None" ofmt ()
                | Some arg →
                    let open Ppxprint_runtime.Runtime.Fmt in
                    pf ofmt "(Some %a)" pp_expression arg ])
             v1 pp_pattern v2
       | Pparam_newtype v0 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Parsetree.Pparam_newtype@ %a)@]"
             (Asttypes.pp_loc
                (fun ofmt arg →
                   let open Ppxprint_runtime.Runtime.Fmt in pf ofmt "%S" arg))
             v0 ])
      ofmt arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and show_function_param_desc : function_param_desc → Stdlib.String.t =
  fun arg → Format.asprintf "%a" pp_function_param_desc arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and pp_function_param : Fmt.t function_param =
  fun (ofmt : Format.formatter) arg →
    (fun ofmt
         ({pparam_loc = v_pparam_loc; pparam_desc = v_pparam_desc} :
          function_param) →
       let open Ppxprint_runtime.Runtime.Fmt in
       pf ofmt
         "@[<2>{ @[Parsetree.pparam_loc =@ %a@];@ @[pparam_desc =@ %a@] }@]"
         Location.pp v_pparam_loc pp_function_param_desc v_pparam_desc)
      ofmt arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and show_function_param : function_param → Stdlib.String.t =
  fun arg → Format.asprintf "%a" pp_function_param arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and pp_function_body : Fmt.t function_body =
  fun (ofmt : Format.formatter) arg →
    (fun ofmt →
       fun
       [ Pfunction_body v0 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Parsetree.Pfunction_body@ %a)@]" pp_expression v0
       | Pfunction_cases v0 v1 v2 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Parsetree.Pfunction_cases@ (@,%a,@ %a,@ %a@,))@]"
             (fun (ofmt : Format.formatter) arg →
                let open Ppxprint_runtime.Runtime.Fmt in
                pf ofmt "@[<2>[%a@,]@]" (list ~{sep = semi} pp_case) arg)
             v0 Location.pp v1 pp_attributes v2 ])
      ofmt arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and show_function_body : function_body → Stdlib.String.t =
  fun arg → Format.asprintf "%a" pp_function_body arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and pp_type_constraint : Fmt.t type_constraint =
  fun (ofmt : Format.formatter) arg →
    (fun ofmt →
       fun
       [ Pconstraint v0 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Parsetree.Pconstraint@ %a)@]" pp_core_type v0
       | Pcoerce v0 v1 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Parsetree.Pcoerce@ (@,%a,@ %a@,))@]"
             (fun ofmt →
                fun
                [ None →
                    let open Ppxprint_runtime.Runtime.Fmt in
                    const string "None" ofmt ()
                | Some arg →
                    let open Ppxprint_runtime.Runtime.Fmt in
                    pf ofmt "(Some %a)" pp_core_type arg ])
             v0 pp_core_type v1 ])
      ofmt arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and show_type_constraint : type_constraint → Stdlib.String.t =
  fun arg → Format.asprintf "%a" pp_type_constraint arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and pp_value_description : Fmt.t value_description =
  fun (ofmt : Format.formatter) arg →
    (fun ofmt
         ({pval_name = v_pval_name; pval_type = v_pval_type;
           pval_prim = v_pval_prim; pval_attributes = v_pval_attributes;
           pval_loc = v_pval_loc} :
          value_description) →
       let open Ppxprint_runtime.Runtime.Fmt in
       pf ofmt
         "@[<2>{ @[Parsetree.pval_name =@ %a@];@ @[pval_type =@ %a@];@ @[pval_prim =@ %a@];@ @[pval_attributes =@ %a@];@ @[pval_loc =@ %a@] }@]"
         (Asttypes.pp_loc
            (fun ofmt arg →
               let open Ppxprint_runtime.Runtime.Fmt in pf ofmt "%S" arg))
         v_pval_name pp_core_type v_pval_type
         (fun (ofmt : Format.formatter) arg →
            let open Ppxprint_runtime.Runtime.Fmt in
            pf ofmt "@[<2>[%a@,]@]"
              (list ~{sep = semi}
                 (fun ofmt arg →
                    let open Ppxprint_runtime.Runtime.Fmt in
                    pf ofmt "%S" arg))
              arg)
         v_pval_prim pp_attributes v_pval_attributes Location.pp v_pval_loc)
      ofmt arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and show_value_description : value_description → Stdlib.String.t =
  fun arg → Format.asprintf "%a" pp_value_description arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and pp_type_declaration : Fmt.t type_declaration =
  fun (ofmt : Format.formatter) arg →
    (fun ofmt
         ({ptype_name = v_ptype_name; ptype_params = v_ptype_params;
           ptype_cstrs = v_ptype_cstrs; ptype_kind = v_ptype_kind;
           ptype_private = v_ptype_private; ptype_manifest = v_ptype_manifest;
           ptype_attributes = v_ptype_attributes; ptype_loc = v_ptype_loc} :
          type_declaration) →
       let open Ppxprint_runtime.Runtime.Fmt in
       pf ofmt
         "@[<2>{ @[Parsetree.ptype_name =@ %a@];@ @[ptype_params =@ %a@];@ @[ptype_cstrs =@ %a@];@ @[ptype_kind =@ %a@];@ @[ptype_private =@ %a@];@ @[ptype_manifest =@ %a@];@ @[ptype_attributes =@ %a@];@ @[ptype_loc =@ %a@] }@]"
         (Asttypes.pp_loc
            (fun ofmt arg →
               let open Ppxprint_runtime.Runtime.Fmt in pf ofmt "%S" arg))
         v_ptype_name
         (fun (ofmt : Format.formatter) arg →
            let open Ppxprint_runtime.Runtime.Fmt in
            pf ofmt "@[<2>[%a@,]@]"
              (list ~{sep = semi}
                 (fun (ofmt : Format.formatter) (v0, v1) →
                    let open Ppxprint_runtime.Runtime.Fmt in
                    pf ofmt "(@[%a,@ %a@])" pp_core_type v0
                      (fun (ofmt : Format.formatter) (v0, v1) →
                         let open Ppxprint_runtime.Runtime.Fmt in
                         pf ofmt "(@[%a,@ %a@])" Asttypes.pp_variance v0
                           Asttypes.pp_injectivity v1)
                      v1))
              arg)
         v_ptype_params
         (fun (ofmt : Format.formatter) arg →
            let open Ppxprint_runtime.Runtime.Fmt in
            pf ofmt "@[<2>[%a@,]@]"
              (list ~{sep = semi}
                 (fun (ofmt : Format.formatter) (v0, v1, v2) →
                    let open Ppxprint_runtime.Runtime.Fmt in
                    pf ofmt "(@[%a,@ %a,@ %a@])" pp_core_type v0 pp_core_type
                      v1 Location.pp v2))
              arg)
         v_ptype_cstrs pp_type_kind v_ptype_kind Asttypes.pp_private_flag
         v_ptype_private
         (fun ofmt →
            fun
            [ None →
                let open Ppxprint_runtime.Runtime.Fmt in
                const string "None" ofmt ()
            | Some arg →
                let open Ppxprint_runtime.Runtime.Fmt in
                pf ofmt "(Some %a)" pp_core_type arg ])
         v_ptype_manifest pp_attributes v_ptype_attributes Location.pp
         v_ptype_loc)
      ofmt arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and show_type_declaration : type_declaration → Stdlib.String.t =
  fun arg → Format.asprintf "%a" pp_type_declaration arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and pp_type_kind : Fmt.t type_kind =
  fun (ofmt : Format.formatter) arg →
    (fun ofmt →
       fun
       [ Ptype_abstract →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "@[<2>Parsetree.Ptype_abstract@]"
       | Ptype_variant v0 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Parsetree.Ptype_variant@ %a)@]"
             (fun (ofmt : Format.formatter) arg →
                let open Ppxprint_runtime.Runtime.Fmt in
                pf ofmt "@[<2>[%a@,]@]"
                  (list ~{sep = semi} pp_constructor_declaration) arg)
             v0
       | Ptype_record v0 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Parsetree.Ptype_record@ %a)@]"
             (fun (ofmt : Format.formatter) arg →
                let open Ppxprint_runtime.Runtime.Fmt in
                pf ofmt "@[<2>[%a@,]@]"
                  (list ~{sep = semi} pp_label_declaration) arg)
             v0
       | Ptype_open →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "@[<2>Parsetree.Ptype_open@]" ])
      ofmt arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and show_type_kind : type_kind → Stdlib.String.t =
  fun arg → Format.asprintf "%a" pp_type_kind arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and pp_label_declaration : Fmt.t label_declaration =
  fun (ofmt : Format.formatter) arg →
    (fun ofmt
         ({pld_name = v_pld_name; pld_mutable = v_pld_mutable;
           pld_type = v_pld_type; pld_loc = v_pld_loc;
           pld_attributes = v_pld_attributes} :
          label_declaration) →
       let open Ppxprint_runtime.Runtime.Fmt in
       pf ofmt
         "@[<2>{ @[Parsetree.pld_name =@ %a@];@ @[pld_mutable =@ %a@];@ @[pld_type =@ %a@];@ @[pld_loc =@ %a@];@ @[pld_attributes =@ %a@] }@]"
         (Asttypes.pp_loc
            (fun ofmt arg →
               let open Ppxprint_runtime.Runtime.Fmt in pf ofmt "%S" arg))
         v_pld_name Asttypes.pp_mutable_flag v_pld_mutable pp_core_type
         v_pld_type Location.pp v_pld_loc pp_attributes v_pld_attributes)
      ofmt arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and show_label_declaration : label_declaration → Stdlib.String.t =
  fun arg → Format.asprintf "%a" pp_label_declaration arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and pp_constructor_declaration : Fmt.t constructor_declaration =
  fun (ofmt : Format.formatter) arg →
    (fun ofmt
         ({pcd_name = v_pcd_name; pcd_vars = v_pcd_vars;
           pcd_args = v_pcd_args; pcd_res = v_pcd_res; pcd_loc = v_pcd_loc;
           pcd_attributes = v_pcd_attributes} :
          constructor_declaration) →
       let open Ppxprint_runtime.Runtime.Fmt in
       pf ofmt
         "@[<2>{ @[Parsetree.pcd_name =@ %a@];@ @[pcd_vars =@ %a@];@ @[pcd_args =@ %a@];@ @[pcd_res =@ %a@];@ @[pcd_loc =@ %a@];@ @[pcd_attributes =@ %a@] }@]"
         (Asttypes.pp_loc
            (fun ofmt arg →
               let open Ppxprint_runtime.Runtime.Fmt in pf ofmt "%S" arg))
         v_pcd_name
         (fun (ofmt : Format.formatter) arg →
            let open Ppxprint_runtime.Runtime.Fmt in
            pf ofmt "@[<2>[%a@,]@]"
              (list ~{sep = semi}
                 (Asttypes.pp_loc
                    (fun ofmt arg →
                       let open Ppxprint_runtime.Runtime.Fmt in
                       pf ofmt "%S" arg)))
              arg)
         v_pcd_vars pp_constructor_arguments v_pcd_args
         (fun ofmt →
            fun
            [ None →
                let open Ppxprint_runtime.Runtime.Fmt in
                const string "None" ofmt ()
            | Some arg →
                let open Ppxprint_runtime.Runtime.Fmt in
                pf ofmt "(Some %a)" pp_core_type arg ])
         v_pcd_res Location.pp v_pcd_loc pp_attributes v_pcd_attributes)
      ofmt arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and show_constructor_declaration : constructor_declaration → Stdlib.String.t =
  fun arg → Format.asprintf "%a" pp_constructor_declaration arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and pp_constructor_arguments : Fmt.t constructor_arguments =
  fun (ofmt : Format.formatter) arg →
    (fun ofmt →
       fun
       [ Pcstr_tuple v0 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Parsetree.Pcstr_tuple@ %a)@]"
             (fun (ofmt : Format.formatter) arg →
                let open Ppxprint_runtime.Runtime.Fmt in
                pf ofmt "@[<2>[%a@,]@]" (list ~{sep = semi} pp_core_type) arg)
             v0
       | Pcstr_record v0 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Parsetree.Pcstr_record@ %a)@]"
             (fun (ofmt : Format.formatter) arg →
                let open Ppxprint_runtime.Runtime.Fmt in
                pf ofmt "@[<2>[%a@,]@]"
                  (list ~{sep = semi} pp_label_declaration) arg)
             v0 ])
      ofmt arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and show_constructor_arguments : constructor_arguments → Stdlib.String.t =
  fun arg → Format.asprintf "%a" pp_constructor_arguments arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and pp_type_extension : Fmt.t type_extension =
  fun (ofmt : Format.formatter) arg →
    (fun ofmt
         ({ptyext_path = v_ptyext_path; ptyext_params = v_ptyext_params;
           ptyext_constructors = v_ptyext_constructors;
           ptyext_private = v_ptyext_private; ptyext_loc = v_ptyext_loc;
           ptyext_attributes = v_ptyext_attributes} :
          type_extension) →
       let open Ppxprint_runtime.Runtime.Fmt in
       pf ofmt
         "@[<2>{ @[Parsetree.ptyext_path =@ %a@];@ @[ptyext_params =@ %a@];@ @[ptyext_constructors =@ %a@];@ @[ptyext_private =@ %a@];@ @[ptyext_loc =@ %a@];@ @[ptyext_attributes =@ %a@] }@]"
         (Asttypes.pp_loc Longident.pp) v_ptyext_path
         (fun (ofmt : Format.formatter) arg →
            let open Ppxprint_runtime.Runtime.Fmt in
            pf ofmt "@[<2>[%a@,]@]"
              (list ~{sep = semi}
                 (fun (ofmt : Format.formatter) (v0, v1) →
                    let open Ppxprint_runtime.Runtime.Fmt in
                    pf ofmt "(@[%a,@ %a@])" pp_core_type v0
                      (fun (ofmt : Format.formatter) (v0, v1) →
                         let open Ppxprint_runtime.Runtime.Fmt in
                         pf ofmt "(@[%a,@ %a@])" Asttypes.pp_variance v0
                           Asttypes.pp_injectivity v1)
                      v1))
              arg)
         v_ptyext_params
         (fun (ofmt : Format.formatter) arg →
            let open Ppxprint_runtime.Runtime.Fmt in
            pf ofmt "@[<2>[%a@,]@]"
              (list ~{sep = semi} pp_extension_constructor) arg)
         v_ptyext_constructors Asttypes.pp_private_flag v_ptyext_private
         Location.pp v_ptyext_loc pp_attributes v_ptyext_attributes)
      ofmt arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and show_type_extension : type_extension → Stdlib.String.t =
  fun arg → Format.asprintf "%a" pp_type_extension arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and pp_extension_constructor : Fmt.t extension_constructor =
  fun (ofmt : Format.formatter) arg →
    (fun ofmt
         ({pext_name = v_pext_name; pext_kind = v_pext_kind;
           pext_loc = v_pext_loc; pext_attributes = v_pext_attributes} :
          extension_constructor) →
       let open Ppxprint_runtime.Runtime.Fmt in
       pf ofmt
         "@[<2>{ @[Parsetree.pext_name =@ %a@];@ @[pext_kind =@ %a@];@ @[pext_loc =@ %a@];@ @[pext_attributes =@ %a@] }@]"
         (Asttypes.pp_loc
            (fun ofmt arg →
               let open Ppxprint_runtime.Runtime.Fmt in pf ofmt "%S" arg))
         v_pext_name pp_extension_constructor_kind v_pext_kind Location.pp
         v_pext_loc pp_attributes v_pext_attributes)
      ofmt arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and show_extension_constructor : extension_constructor → Stdlib.String.t =
  fun arg → Format.asprintf "%a" pp_extension_constructor arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and pp_type_exception : Fmt.t type_exception =
  fun (ofmt : Format.formatter) arg →
    (fun ofmt
         ({ptyexn_constructor = v_ptyexn_constructor;
           ptyexn_loc = v_ptyexn_loc;
           ptyexn_attributes = v_ptyexn_attributes} :
          type_exception) →
       let open Ppxprint_runtime.Runtime.Fmt in
       pf ofmt
         "@[<2>{ @[Parsetree.ptyexn_constructor =@ %a@];@ @[ptyexn_loc =@ %a@];@ @[ptyexn_attributes =@ %a@] }@]"
         pp_extension_constructor v_ptyexn_constructor Location.pp
         v_ptyexn_loc pp_attributes v_ptyexn_attributes)
      ofmt arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and show_type_exception : type_exception → Stdlib.String.t =
  fun arg → Format.asprintf "%a" pp_type_exception arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and pp_extension_constructor_kind : Fmt.t extension_constructor_kind =
  fun (ofmt : Format.formatter) arg →
    (fun ofmt →
       fun
       [ Pext_decl v0 v1 v2 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Parsetree.Pext_decl@ (@,%a,@ %a,@ %a@,))@]"
             (fun (ofmt : Format.formatter) arg →
                let open Ppxprint_runtime.Runtime.Fmt in
                pf ofmt "@[<2>[%a@,]@]"
                  (list ~{sep = semi}
                     (Asttypes.pp_loc
                        (fun ofmt arg →
                           let open Ppxprint_runtime.Runtime.Fmt in
                           pf ofmt "%S" arg)))
                  arg)
             v0 pp_constructor_arguments v1
             (fun ofmt →
                fun
                [ None →
                    let open Ppxprint_runtime.Runtime.Fmt in
                    const string "None" ofmt ()
                | Some arg →
                    let open Ppxprint_runtime.Runtime.Fmt in
                    pf ofmt "(Some %a)" pp_core_type arg ])
             v2
       | Pext_rebind v0 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Parsetree.Pext_rebind@ %a)@]"
             (Asttypes.pp_loc Longident.pp) v0 ])
      ofmt arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and show_extension_constructor_kind : extension_constructor_kind → Stdlib.String.t =
  fun arg → Format.asprintf "%a" pp_extension_constructor_kind arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and pp_class_type : Fmt.t class_type =
  fun (ofmt : Format.formatter) arg →
    (fun ofmt
         ({pcty_desc = v_pcty_desc; pcty_loc = v_pcty_loc;
           pcty_attributes = v_pcty_attributes} :
          class_type) →
       let open Ppxprint_runtime.Runtime.Fmt in
       pf ofmt
         "@[<2>{ @[Parsetree.pcty_desc =@ %a@];@ @[pcty_loc =@ %a@];@ @[pcty_attributes =@ %a@] }@]"
         pp_class_type_desc v_pcty_desc Location.pp v_pcty_loc pp_attributes
         v_pcty_attributes)
      ofmt arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and show_class_type : class_type → Stdlib.String.t =
  fun arg → Format.asprintf "%a" pp_class_type arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and pp_class_type_desc : Fmt.t class_type_desc =
  fun (ofmt : Format.formatter) arg →
    (fun ofmt →
       fun
       [ Pcty_constr v0 v1 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Parsetree.Pcty_constr@ (@,%a,@ %a@,))@]"
             (Asttypes.pp_loc Longident.pp) v0
             (fun (ofmt : Format.formatter) arg →
                let open Ppxprint_runtime.Runtime.Fmt in
                pf ofmt "@[<2>[%a@,]@]" (list ~{sep = semi} pp_core_type) arg)
             v1
       | Pcty_signature v0 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Parsetree.Pcty_signature@ %a)@]" pp_class_signature
             v0
       | Pcty_arrow v0 v1 v2 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Parsetree.Pcty_arrow@ (@,%a,@ %a,@ %a@,))@]"
             Asttypes.pp_arg_label v0 pp_core_type v1 pp_class_type v2
       | Pcty_extension v0 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Parsetree.Pcty_extension@ %a)@]" pp_extension v0
       | Pcty_open v0 v1 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Parsetree.Pcty_open@ (@,%a,@ %a@,))@]"
             pp_open_description v0 pp_class_type v1 ])
      ofmt arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and show_class_type_desc : class_type_desc → Stdlib.String.t =
  fun arg → Format.asprintf "%a" pp_class_type_desc arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and pp_class_signature : Fmt.t class_signature =
  fun (ofmt : Format.formatter) arg →
    (fun ofmt
         ({pcsig_self = v_pcsig_self; pcsig_fields = v_pcsig_fields} :
          class_signature) →
       let open Ppxprint_runtime.Runtime.Fmt in
       pf ofmt
         "@[<2>{ @[Parsetree.pcsig_self =@ %a@];@ @[pcsig_fields =@ %a@] }@]"
         pp_core_type v_pcsig_self
         (fun (ofmt : Format.formatter) arg →
            let open Ppxprint_runtime.Runtime.Fmt in
            pf ofmt "@[<2>[%a@,]@]" (list ~{sep = semi} pp_class_type_field)
              arg)
         v_pcsig_fields)
      ofmt arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and show_class_signature : class_signature → Stdlib.String.t =
  fun arg → Format.asprintf "%a" pp_class_signature arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and pp_class_type_field : Fmt.t class_type_field =
  fun (ofmt : Format.formatter) arg →
    (fun ofmt
         ({pctf_desc = v_pctf_desc; pctf_loc = v_pctf_loc;
           pctf_attributes = v_pctf_attributes} :
          class_type_field) →
       let open Ppxprint_runtime.Runtime.Fmt in
       pf ofmt
         "@[<2>{ @[Parsetree.pctf_desc =@ %a@];@ @[pctf_loc =@ %a@];@ @[pctf_attributes =@ %a@] }@]"
         pp_class_type_field_desc v_pctf_desc Location.pp v_pctf_loc
         pp_attributes v_pctf_attributes)
      ofmt arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and show_class_type_field : class_type_field → Stdlib.String.t =
  fun arg → Format.asprintf "%a" pp_class_type_field arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and pp_class_type_field_desc : Fmt.t class_type_field_desc =
  fun (ofmt : Format.formatter) arg →
    (fun ofmt →
       fun
       [ Pctf_inherit v0 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Parsetree.Pctf_inherit@ %a)@]" pp_class_type v0
       | Pctf_val v0 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Parsetree.Pctf_val@ %a)@]"
             (fun (ofmt : Format.formatter) (v0, v1, v2, v3) →
                let open Ppxprint_runtime.Runtime.Fmt in
                pf ofmt "(@[%a,@ %a,@ %a,@ %a@])"
                  (Asttypes.pp_loc Asttypes.pp_label) v0
                  Asttypes.pp_mutable_flag v1 Asttypes.pp_virtual_flag v2
                  pp_core_type v3)
             v0
       | Pctf_method v0 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Parsetree.Pctf_method@ %a)@]"
             (fun (ofmt : Format.formatter) (v0, v1, v2, v3) →
                let open Ppxprint_runtime.Runtime.Fmt in
                pf ofmt "(@[%a,@ %a,@ %a,@ %a@])"
                  (Asttypes.pp_loc Asttypes.pp_label) v0
                  Asttypes.pp_private_flag v1 Asttypes.pp_virtual_flag v2
                  pp_core_type v3)
             v0
       | Pctf_constraint v0 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Parsetree.Pctf_constraint@ %a)@]"
             (fun (ofmt : Format.formatter) (v0, v1) →
                let open Ppxprint_runtime.Runtime.Fmt in
                pf ofmt "(@[%a,@ %a@])" pp_core_type v0 pp_core_type v1)
             v0
       | Pctf_attribute v0 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Parsetree.Pctf_attribute@ %a)@]" pp_attribute v0
       | Pctf_extension v0 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Parsetree.Pctf_extension@ %a)@]" pp_extension v0 ])
      ofmt arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and show_class_type_field_desc : class_type_field_desc → Stdlib.String.t =
  fun arg → Format.asprintf "%a" pp_class_type_field_desc arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and pp_class_infos : ! α . Fmt.t α → Fmt.t (class_infos α) =
  fun (type a) (tp_0 : Fmt.t a) (ofmt : Format.formatter) arg →
    (fun ofmt
         ({pci_virt = v_pci_virt; pci_params = v_pci_params;
           pci_name = v_pci_name; pci_expr = v_pci_expr; pci_loc = v_pci_loc;
           pci_attributes = v_pci_attributes} :
          class_infos a) →
       let open Ppxprint_runtime.Runtime.Fmt in
       pf ofmt
         "@[<2>{ @[Pp_parsetree.pci_virt =@ %a@];@ @[pci_params =@ %a@];@ @[pci_name =@ %a@];@ @[pci_expr =@ %a@];@ @[pci_loc =@ %a@];@ @[pci_attributes =@ %a@] }@]"
         Asttypes.pp_virtual_flag v_pci_virt
         (fun (ofmt : Format.formatter) arg →
            let open Ppxprint_runtime.Runtime.Fmt in
            pf ofmt "@[<2>[%a@,]@]"
              (list ~{sep = semi}
                 (fun (ofmt : Format.formatter) (v0, v1) →
                    let open Ppxprint_runtime.Runtime.Fmt in
                    pf ofmt "(@[%a,@ %a@])" pp_core_type v0
                      (fun (ofmt : Format.formatter) (v0, v1) →
                         let open Ppxprint_runtime.Runtime.Fmt in
                         pf ofmt "(@[%a,@ %a@])" Asttypes.pp_variance v0
                           Asttypes.pp_injectivity v1)
                      v1))
              arg)
         v_pci_params
         (Asttypes.pp_loc
            (fun ofmt arg →
               let open Ppxprint_runtime.Runtime.Fmt in pf ofmt "%S" arg))
         v_pci_name tp_0 v_pci_expr Location.pp v_pci_loc pp_attributes
         v_pci_attributes)
      ofmt arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and show_class_infos : ! α . Fmt.t α → class_infos α → Stdlib.String.t =
  fun (type a) (tp_0 : Fmt.t a) arg →
    Format.asprintf "%a" (pp_class_infos tp_0) arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and pp_class_description : Fmt.t class_description =
  fun (ofmt : Format.formatter) arg → pp_class_infos pp_class_type ofmt arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and show_class_description : class_description → Stdlib.String.t =
  fun arg → Format.asprintf "%a" pp_class_description arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and pp_class_type_declaration : Fmt.t class_type_declaration =
  fun (ofmt : Format.formatter) arg → pp_class_infos pp_class_type ofmt arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and show_class_type_declaration : class_type_declaration → Stdlib.String.t =
  fun arg → Format.asprintf "%a" pp_class_type_declaration arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and pp_class_expr : Fmt.t class_expr =
  fun (ofmt : Format.formatter) arg →
    (fun ofmt
         ({pcl_desc = v_pcl_desc; pcl_loc = v_pcl_loc;
           pcl_attributes = v_pcl_attributes} :
          class_expr) →
       let open Ppxprint_runtime.Runtime.Fmt in
       pf ofmt
         "@[<2>{ @[Parsetree.pcl_desc =@ %a@];@ @[pcl_loc =@ %a@];@ @[pcl_attributes =@ %a@] }@]"
         pp_class_expr_desc v_pcl_desc Location.pp v_pcl_loc pp_attributes
         v_pcl_attributes)
      ofmt arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and show_class_expr : class_expr → Stdlib.String.t =
  fun arg → Format.asprintf "%a" pp_class_expr arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and pp_class_expr_desc : Fmt.t class_expr_desc =
  fun (ofmt : Format.formatter) arg →
    (fun ofmt →
       fun
       [ Pcl_constr v0 v1 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Parsetree.Pcl_constr@ (@,%a,@ %a@,))@]"
             (Asttypes.pp_loc Longident.pp) v0
             (fun (ofmt : Format.formatter) arg →
                let open Ppxprint_runtime.Runtime.Fmt in
                pf ofmt "@[<2>[%a@,]@]" (list ~{sep = semi} pp_core_type) arg)
             v1
       | Pcl_structure v0 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Parsetree.Pcl_structure@ %a)@]" pp_class_structure
             v0
       | Pcl_fun v0 v1 v2 v3 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Parsetree.Pcl_fun@ (@,%a,@ %a,@ %a,@ %a@,))@]"
             Asttypes.pp_arg_label v0
             (fun ofmt →
                fun
                [ None →
                    let open Ppxprint_runtime.Runtime.Fmt in
                    const string "None" ofmt ()
                | Some arg →
                    let open Ppxprint_runtime.Runtime.Fmt in
                    pf ofmt "(Some %a)" pp_expression arg ])
             v1 pp_pattern v2 pp_class_expr v3
       | Pcl_apply v0 v1 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Parsetree.Pcl_apply@ (@,%a,@ %a@,))@]" pp_class_expr
             v0
             (fun (ofmt : Format.formatter) arg →
                let open Ppxprint_runtime.Runtime.Fmt in
                pf ofmt "@[<2>[%a@,]@]"
                  (list ~{sep = semi}
                     (fun (ofmt : Format.formatter) (v0, v1) →
                        let open Ppxprint_runtime.Runtime.Fmt in
                        pf ofmt "(@[%a,@ %a@])" Asttypes.pp_arg_label v0
                          pp_expression v1))
                  arg)
             v1
       | Pcl_let v0 v1 v2 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Parsetree.Pcl_let@ (@,%a,@ %a,@ %a@,))@]"
             Asttypes.pp_rec_flag v0
             (fun (ofmt : Format.formatter) arg →
                let open Ppxprint_runtime.Runtime.Fmt in
                pf ofmt "@[<2>[%a@,]@]" (list ~{sep = semi} pp_value_binding)
                  arg)
             v1 pp_class_expr v2
       | Pcl_constraint v0 v1 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Parsetree.Pcl_constraint@ (@,%a,@ %a@,))@]"
             pp_class_expr v0 pp_class_type v1
       | Pcl_extension v0 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Parsetree.Pcl_extension@ %a)@]" pp_extension v0
       | Pcl_open v0 v1 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Parsetree.Pcl_open@ (@,%a,@ %a@,))@]"
             pp_open_description v0 pp_class_expr v1 ])
      ofmt arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and show_class_expr_desc : class_expr_desc → Stdlib.String.t =
  fun arg → Format.asprintf "%a" pp_class_expr_desc arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and pp_class_structure : Fmt.t class_structure =
  fun (ofmt : Format.formatter) arg →
    (fun ofmt
         ({pcstr_self = v_pcstr_self; pcstr_fields = v_pcstr_fields} :
          class_structure) →
       let open Ppxprint_runtime.Runtime.Fmt in
       pf ofmt
         "@[<2>{ @[Parsetree.pcstr_self =@ %a@];@ @[pcstr_fields =@ %a@] }@]"
         pp_pattern v_pcstr_self
         (fun (ofmt : Format.formatter) arg →
            let open Ppxprint_runtime.Runtime.Fmt in
            pf ofmt "@[<2>[%a@,]@]" (list ~{sep = semi} pp_class_field) arg)
         v_pcstr_fields)
      ofmt arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and show_class_structure : class_structure → Stdlib.String.t =
  fun arg → Format.asprintf "%a" pp_class_structure arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and pp_class_field : Fmt.t class_field =
  fun (ofmt : Format.formatter) arg →
    (fun ofmt
         ({pcf_desc = v_pcf_desc; pcf_loc = v_pcf_loc;
           pcf_attributes = v_pcf_attributes} :
          class_field) →
       let open Ppxprint_runtime.Runtime.Fmt in
       pf ofmt
         "@[<2>{ @[Parsetree.pcf_desc =@ %a@];@ @[pcf_loc =@ %a@];@ @[pcf_attributes =@ %a@] }@]"
         pp_class_field_desc v_pcf_desc Location.pp v_pcf_loc pp_attributes
         v_pcf_attributes)
      ofmt arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and show_class_field : class_field → Stdlib.String.t =
  fun arg → Format.asprintf "%a" pp_class_field arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and pp_class_field_desc : Fmt.t class_field_desc =
  fun (ofmt : Format.formatter) arg →
    (fun ofmt →
       fun
       [ Pcf_inherit v0 v1 v2 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Parsetree.Pcf_inherit@ (@,%a,@ %a,@ %a@,))@]"
             Asttypes.pp_override_flag v0 pp_class_expr v1
             (fun ofmt →
                fun
                [ None →
                    let open Ppxprint_runtime.Runtime.Fmt in
                    const string "None" ofmt ()
                | Some arg →
                    let open Ppxprint_runtime.Runtime.Fmt in
                    pf ofmt "(Some %a)"
                      (Asttypes.pp_loc
                         (fun ofmt arg →
                            let open Ppxprint_runtime.Runtime.Fmt in
                            pf ofmt "%S" arg))
                      arg ])
             v2
       | Pcf_val v0 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Parsetree.Pcf_val@ %a)@]"
             (fun (ofmt : Format.formatter) (v0, v1, v2) →
                let open Ppxprint_runtime.Runtime.Fmt in
                pf ofmt "(@[%a,@ %a,@ %a@])"
                  (Asttypes.pp_loc Asttypes.pp_label) v0
                  Asttypes.pp_mutable_flag v1 pp_class_field_kind v2)
             v0
       | Pcf_method v0 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Parsetree.Pcf_method@ %a)@]"
             (fun (ofmt : Format.formatter) (v0, v1, v2) →
                let open Ppxprint_runtime.Runtime.Fmt in
                pf ofmt "(@[%a,@ %a,@ %a@])"
                  (Asttypes.pp_loc Asttypes.pp_label) v0
                  Asttypes.pp_private_flag v1 pp_class_field_kind v2)
             v0
       | Pcf_constraint v0 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Parsetree.Pcf_constraint@ %a)@]"
             (fun (ofmt : Format.formatter) (v0, v1) →
                let open Ppxprint_runtime.Runtime.Fmt in
                pf ofmt "(@[%a,@ %a@])" pp_core_type v0 pp_core_type v1)
             v0
       | Pcf_initializer v0 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Parsetree.Pcf_initializer@ %a)@]" pp_expression v0
       | Pcf_attribute v0 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Parsetree.Pcf_attribute@ %a)@]" pp_attribute v0
       | Pcf_extension v0 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Parsetree.Pcf_extension@ %a)@]" pp_extension v0 ])
      ofmt arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and show_class_field_desc : class_field_desc → Stdlib.String.t =
  fun arg → Format.asprintf "%a" pp_class_field_desc arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and pp_class_field_kind : Fmt.t class_field_kind =
  fun (ofmt : Format.formatter) arg →
    (fun ofmt →
       fun
       [ Cfk_virtual v0 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Parsetree.Cfk_virtual@ %a)@]" pp_core_type v0
       | Cfk_concrete v0 v1 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Parsetree.Cfk_concrete@ (@,%a,@ %a@,))@]"
             Asttypes.pp_override_flag v0 pp_expression v1 ])
      ofmt arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and show_class_field_kind : class_field_kind → Stdlib.String.t =
  fun arg → Format.asprintf "%a" pp_class_field_kind arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and pp_class_declaration : Fmt.t class_declaration =
  fun (ofmt : Format.formatter) arg → pp_class_infos pp_class_expr ofmt arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and show_class_declaration : class_declaration → Stdlib.String.t =
  fun arg → Format.asprintf "%a" pp_class_declaration arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and pp_module_type : Fmt.t module_type =
  fun (ofmt : Format.formatter) arg →
    (fun ofmt
         ({pmty_desc = v_pmty_desc; pmty_loc = v_pmty_loc;
           pmty_attributes = v_pmty_attributes} :
          module_type) →
       let open Ppxprint_runtime.Runtime.Fmt in
       pf ofmt
         "@[<2>{ @[Parsetree.pmty_desc =@ %a@];@ @[pmty_loc =@ %a@];@ @[pmty_attributes =@ %a@] }@]"
         pp_module_type_desc v_pmty_desc Location.pp v_pmty_loc pp_attributes
         v_pmty_attributes)
      ofmt arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and show_module_type : module_type → Stdlib.String.t =
  fun arg → Format.asprintf "%a" pp_module_type arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and pp_module_type_desc : Fmt.t module_type_desc =
  fun (ofmt : Format.formatter) arg →
    (fun ofmt →
       fun
       [ Pmty_ident v0 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Parsetree.Pmty_ident@ %a)@]"
             (Asttypes.pp_loc Longident.pp) v0
       | Pmty_signature v0 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Parsetree.Pmty_signature@ %a)@]" pp_signature v0
       | Pmty_functor v0 v1 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Parsetree.Pmty_functor@ (@,%a,@ %a@,))@]"
             pp_functor_parameter v0 pp_module_type v1
       | Pmty_with v0 v1 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Parsetree.Pmty_with@ (@,%a,@ %a@,))@]"
             pp_module_type v0
             (fun (ofmt : Format.formatter) arg →
                let open Ppxprint_runtime.Runtime.Fmt in
                pf ofmt "@[<2>[%a@,]@]"
                  (list ~{sep = semi} pp_with_constraint) arg)
             v1
       | Pmty_typeof v0 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Parsetree.Pmty_typeof@ %a)@]" pp_module_expr v0
       | Pmty_extension v0 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Parsetree.Pmty_extension@ %a)@]" pp_extension v0
       | Pmty_alias v0 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Parsetree.Pmty_alias@ %a)@]"
             (Asttypes.pp_loc Longident.pp) v0 ])
      ofmt arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and show_module_type_desc : module_type_desc → Stdlib.String.t =
  fun arg → Format.asprintf "%a" pp_module_type_desc arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and pp_functor_parameter : Fmt.t functor_parameter =
  fun (ofmt : Format.formatter) arg →
    (fun ofmt →
       fun
       [ Unit →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "@[<2>Parsetree.Unit@]"
       | Named v0 v1 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Parsetree.Named@ (@,%a,@ %a@,))@]"
             (Asttypes.pp_loc
                (fun ofmt →
                   fun
                   [ None →
                       let open Ppxprint_runtime.Runtime.Fmt in
                       const string "None" ofmt ()
                   | Some arg →
                       let open Ppxprint_runtime.Runtime.Fmt in
                       pf ofmt "(Some %a)"
                         (fun ofmt arg →
                            let open Ppxprint_runtime.Runtime.Fmt in
                            pf ofmt "%S" arg)
                         arg ]))
             v0 pp_module_type v1 ])
      ofmt arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and show_functor_parameter : functor_parameter → Stdlib.String.t =
  fun arg → Format.asprintf "%a" pp_functor_parameter arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and pp_signature : Fmt.t signature =
  fun (ofmt : Format.formatter) arg →
    (fun (ofmt : Format.formatter) arg →
       let open Ppxprint_runtime.Runtime.Fmt in
       pf ofmt "@[<2>[%a@,]@]" (list ~{sep = semi} pp_signature_item) arg)
      ofmt arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and show_signature : signature → Stdlib.String.t =
  fun arg → Format.asprintf "%a" pp_signature arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and pp_signature_item : Fmt.t signature_item =
  fun (ofmt : Format.formatter) arg →
    (fun ofmt
         ({psig_desc = v_psig_desc; psig_loc = v_psig_loc} : signature_item) →
       let open Ppxprint_runtime.Runtime.Fmt in
       pf ofmt "@[<2>{ @[Parsetree.psig_desc =@ %a@];@ @[psig_loc =@ %a@] }@]"
         pp_signature_item_desc v_psig_desc Location.pp v_psig_loc)
      ofmt arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and show_signature_item : signature_item → Stdlib.String.t =
  fun arg → Format.asprintf "%a" pp_signature_item arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and pp_signature_item_desc : Fmt.t signature_item_desc =
  fun (ofmt : Format.formatter) arg →
    (fun ofmt →
       fun
       [ Psig_value v0 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Parsetree.Psig_value@ %a)@]" pp_value_description v0
       | Psig_type v0 v1 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Parsetree.Psig_type@ (@,%a,@ %a@,))@]"
             Asttypes.pp_rec_flag v0
             (fun (ofmt : Format.formatter) arg →
                let open Ppxprint_runtime.Runtime.Fmt in
                pf ofmt "@[<2>[%a@,]@]"
                  (list ~{sep = semi} pp_type_declaration) arg)
             v1
       | Psig_typesubst v0 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Parsetree.Psig_typesubst@ %a)@]"
             (fun (ofmt : Format.formatter) arg →
                let open Ppxprint_runtime.Runtime.Fmt in
                pf ofmt "@[<2>[%a@,]@]"
                  (list ~{sep = semi} pp_type_declaration) arg)
             v0
       | Psig_typext v0 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Parsetree.Psig_typext@ %a)@]" pp_type_extension v0
       | Psig_exception v0 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Parsetree.Psig_exception@ %a)@]" pp_type_exception
             v0
       | Psig_module v0 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Parsetree.Psig_module@ %a)@]" pp_module_declaration
             v0
       | Psig_modsubst v0 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Parsetree.Psig_modsubst@ %a)@]"
             pp_module_substitution v0
       | Psig_recmodule v0 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Parsetree.Psig_recmodule@ %a)@]"
             (fun (ofmt : Format.formatter) arg →
                let open Ppxprint_runtime.Runtime.Fmt in
                pf ofmt "@[<2>[%a@,]@]"
                  (list ~{sep = semi} pp_module_declaration) arg)
             v0
       | Psig_modtype v0 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Parsetree.Psig_modtype@ %a)@]"
             pp_module_type_declaration v0
       | Psig_modtypesubst v0 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Parsetree.Psig_modtypesubst@ %a)@]"
             pp_module_type_declaration v0
       | Psig_open v0 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Parsetree.Psig_open@ %a)@]" pp_open_description v0
       | Psig_include v0 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Parsetree.Psig_include@ %a)@]"
             pp_include_description v0
       | Psig_class v0 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Parsetree.Psig_class@ %a)@]"
             (fun (ofmt : Format.formatter) arg →
                let open Ppxprint_runtime.Runtime.Fmt in
                pf ofmt "@[<2>[%a@,]@]"
                  (list ~{sep = semi} pp_class_description) arg)
             v0
       | Psig_class_type v0 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Parsetree.Psig_class_type@ %a)@]"
             (fun (ofmt : Format.formatter) arg →
                let open Ppxprint_runtime.Runtime.Fmt in
                pf ofmt "@[<2>[%a@,]@]"
                  (list ~{sep = semi} pp_class_type_declaration) arg)
             v0
       | Psig_attribute v0 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Parsetree.Psig_attribute@ %a)@]" pp_attribute v0
       | Psig_extension v0 v1 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Parsetree.Psig_extension@ (@,%a,@ %a@,))@]"
             pp_extension v0 pp_attributes v1 ])
      ofmt arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and show_signature_item_desc : signature_item_desc → Stdlib.String.t =
  fun arg → Format.asprintf "%a" pp_signature_item_desc arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and pp_module_declaration : Fmt.t module_declaration =
  fun (ofmt : Format.formatter) arg →
    (fun ofmt
         ({pmd_name = v_pmd_name; pmd_type = v_pmd_type;
           pmd_attributes = v_pmd_attributes; pmd_loc = v_pmd_loc} :
          module_declaration) →
       let open Ppxprint_runtime.Runtime.Fmt in
       pf ofmt
         "@[<2>{ @[Parsetree.pmd_name =@ %a@];@ @[pmd_type =@ %a@];@ @[pmd_attributes =@ %a@];@ @[pmd_loc =@ %a@] }@]"
         (Asttypes.pp_loc
            (fun ofmt →
               fun
               [ None →
                   let open Ppxprint_runtime.Runtime.Fmt in
                   const string "None" ofmt ()
               | Some arg →
                   let open Ppxprint_runtime.Runtime.Fmt in
                   pf ofmt "(Some %a)"
                     (fun ofmt arg →
                        let open Ppxprint_runtime.Runtime.Fmt in
                        pf ofmt "%S" arg)
                     arg ]))
         v_pmd_name pp_module_type v_pmd_type pp_attributes v_pmd_attributes
         Location.pp v_pmd_loc)
      ofmt arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and show_module_declaration : module_declaration → Stdlib.String.t =
  fun arg → Format.asprintf "%a" pp_module_declaration arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and pp_module_substitution : Fmt.t module_substitution =
  fun (ofmt : Format.formatter) arg →
    (fun ofmt
         ({pms_name = v_pms_name; pms_manifest = v_pms_manifest;
           pms_attributes = v_pms_attributes; pms_loc = v_pms_loc} :
          module_substitution) →
       let open Ppxprint_runtime.Runtime.Fmt in
       pf ofmt
         "@[<2>{ @[Parsetree.pms_name =@ %a@];@ @[pms_manifest =@ %a@];@ @[pms_attributes =@ %a@];@ @[pms_loc =@ %a@] }@]"
         (Asttypes.pp_loc
            (fun ofmt arg →
               let open Ppxprint_runtime.Runtime.Fmt in pf ofmt "%S" arg))
         v_pms_name (Asttypes.pp_loc Longident.pp) v_pms_manifest
         pp_attributes v_pms_attributes Location.pp v_pms_loc)
      ofmt arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and show_module_substitution : module_substitution → Stdlib.String.t =
  fun arg → Format.asprintf "%a" pp_module_substitution arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and pp_module_type_declaration : Fmt.t module_type_declaration =
  fun (ofmt : Format.formatter) arg →
    (fun ofmt
         ({pmtd_name = v_pmtd_name; pmtd_type = v_pmtd_type;
           pmtd_attributes = v_pmtd_attributes; pmtd_loc = v_pmtd_loc} :
          module_type_declaration) →
       let open Ppxprint_runtime.Runtime.Fmt in
       pf ofmt
         "@[<2>{ @[Parsetree.pmtd_name =@ %a@];@ @[pmtd_type =@ %a@];@ @[pmtd_attributes =@ %a@];@ @[pmtd_loc =@ %a@] }@]"
         (Asttypes.pp_loc
            (fun ofmt arg →
               let open Ppxprint_runtime.Runtime.Fmt in pf ofmt "%S" arg))
         v_pmtd_name
         (fun ofmt →
            fun
            [ None →
                let open Ppxprint_runtime.Runtime.Fmt in
                const string "None" ofmt ()
            | Some arg →
                let open Ppxprint_runtime.Runtime.Fmt in
                pf ofmt "(Some %a)" pp_module_type arg ])
         v_pmtd_type pp_attributes v_pmtd_attributes Location.pp v_pmtd_loc)
      ofmt arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and show_module_type_declaration : module_type_declaration → Stdlib.String.t =
  fun arg → Format.asprintf "%a" pp_module_type_declaration arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and pp_open_infos : ! α . Fmt.t α → Fmt.t (open_infos α) =
  fun (type a) (tp_0 : Fmt.t a) (ofmt : Format.formatter) arg →
    (fun ofmt
         ({popen_expr = v_popen_expr; popen_override = v_popen_override;
           popen_loc = v_popen_loc; popen_attributes = v_popen_attributes} :
          open_infos a) →
       let open Ppxprint_runtime.Runtime.Fmt in
       pf ofmt
         "@[<2>{ @[Pp_parsetree.popen_expr =@ %a@];@ @[popen_override =@ %a@];@ @[popen_loc =@ %a@];@ @[popen_attributes =@ %a@] }@]"
         tp_0 v_popen_expr Asttypes.pp_override_flag v_popen_override
         Location.pp v_popen_loc pp_attributes v_popen_attributes)
      ofmt arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and show_open_infos : ! α . Fmt.t α → open_infos α → Stdlib.String.t =
  fun (type a) (tp_0 : Fmt.t a) arg →
    Format.asprintf "%a" (pp_open_infos tp_0) arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and pp_open_description : Fmt.t open_description =
  fun (ofmt : Format.formatter) arg →
    pp_open_infos (Asttypes.pp_loc Longident.pp) ofmt arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and show_open_description : open_description → Stdlib.String.t =
  fun arg → Format.asprintf "%a" pp_open_description arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and pp_open_declaration : Fmt.t open_declaration =
  fun (ofmt : Format.formatter) arg → pp_open_infos pp_module_expr ofmt arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and show_open_declaration : open_declaration → Stdlib.String.t =
  fun arg → Format.asprintf "%a" pp_open_declaration arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and pp_include_infos : ! α . Fmt.t α → Fmt.t (include_infos α) =
  fun (type a) (tp_0 : Fmt.t a) (ofmt : Format.formatter) arg →
    (fun ofmt
         ({pincl_mod = v_pincl_mod; pincl_loc = v_pincl_loc;
           pincl_attributes = v_pincl_attributes} :
          include_infos a) →
       let open Ppxprint_runtime.Runtime.Fmt in
       pf ofmt
         "@[<2>{ @[Pp_parsetree.pincl_mod =@ %a@];@ @[pincl_loc =@ %a@];@ @[pincl_attributes =@ %a@] }@]"
         tp_0 v_pincl_mod Location.pp v_pincl_loc pp_attributes
         v_pincl_attributes)
      ofmt arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and show_include_infos : ! α . Fmt.t α → include_infos α → Stdlib.String.t =
  fun (type a) (tp_0 : Fmt.t a) arg →
    Format.asprintf "%a" (pp_include_infos tp_0) arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and pp_include_description : Fmt.t include_description =
  fun (ofmt : Format.formatter) arg → pp_include_infos pp_module_type ofmt arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and show_include_description : include_description → Stdlib.String.t =
  fun arg → Format.asprintf "%a" pp_include_description arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and pp_include_declaration : Fmt.t include_declaration =
  fun (ofmt : Format.formatter) arg → pp_include_infos pp_module_expr ofmt arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and show_include_declaration : include_declaration → Stdlib.String.t =
  fun arg → Format.asprintf "%a" pp_include_declaration arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and pp_with_constraint : Fmt.t with_constraint =
  fun (ofmt : Format.formatter) arg →
    (fun ofmt →
       fun
       [ Pwith_type v0 v1 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Parsetree.Pwith_type@ (@,%a,@ %a@,))@]"
             (Asttypes.pp_loc Longident.pp) v0 pp_type_declaration v1
       | Pwith_module v0 v1 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Parsetree.Pwith_module@ (@,%a,@ %a@,))@]"
             (Asttypes.pp_loc Longident.pp) v0 (Asttypes.pp_loc Longident.pp)
             v1
       | Pwith_modtype v0 v1 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Parsetree.Pwith_modtype@ (@,%a,@ %a@,))@]"
             (Asttypes.pp_loc Longident.pp) v0 pp_module_type v1
       | Pwith_modtypesubst v0 v1 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Parsetree.Pwith_modtypesubst@ (@,%a,@ %a@,))@]"
             (Asttypes.pp_loc Longident.pp) v0 pp_module_type v1
       | Pwith_typesubst v0 v1 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Parsetree.Pwith_typesubst@ (@,%a,@ %a@,))@]"
             (Asttypes.pp_loc Longident.pp) v0 pp_type_declaration v1
       | Pwith_modsubst v0 v1 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Parsetree.Pwith_modsubst@ (@,%a,@ %a@,))@]"
             (Asttypes.pp_loc Longident.pp) v0 (Asttypes.pp_loc Longident.pp)
             v1 ])
      ofmt arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and show_with_constraint : with_constraint → Stdlib.String.t =
  fun arg → Format.asprintf "%a" pp_with_constraint arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and pp_module_expr : Fmt.t module_expr =
  fun (ofmt : Format.formatter) arg →
    (fun ofmt
         ({pmod_desc = v_pmod_desc; pmod_loc = v_pmod_loc;
           pmod_attributes = v_pmod_attributes} :
          module_expr) →
       let open Ppxprint_runtime.Runtime.Fmt in
       pf ofmt
         "@[<2>{ @[Parsetree.pmod_desc =@ %a@];@ @[pmod_loc =@ %a@];@ @[pmod_attributes =@ %a@] }@]"
         pp_module_expr_desc v_pmod_desc Location.pp v_pmod_loc pp_attributes
         v_pmod_attributes)
      ofmt arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and show_module_expr : module_expr → Stdlib.String.t =
  fun arg → Format.asprintf "%a" pp_module_expr arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and pp_module_expr_desc : Fmt.t module_expr_desc =
  fun (ofmt : Format.formatter) arg →
    (fun ofmt →
       fun
       [ Pmod_ident v0 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Parsetree.Pmod_ident@ %a)@]"
             (Asttypes.pp_loc Longident.pp) v0
       | Pmod_structure v0 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Parsetree.Pmod_structure@ %a)@]" pp_structure v0
       | Pmod_functor v0 v1 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Parsetree.Pmod_functor@ (@,%a,@ %a@,))@]"
             pp_functor_parameter v0 pp_module_expr v1
       | Pmod_apply v0 v1 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Parsetree.Pmod_apply@ (@,%a,@ %a@,))@]"
             pp_module_expr v0 pp_module_expr v1
       | Pmod_apply_unit v0 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Parsetree.Pmod_apply_unit@ %a)@]" pp_module_expr v0
       | Pmod_constraint v0 v1 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Parsetree.Pmod_constraint@ (@,%a,@ %a@,))@]"
             pp_module_expr v0 pp_module_type v1
       | Pmod_unpack v0 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Parsetree.Pmod_unpack@ %a)@]" pp_expression v0
       | Pmod_extension v0 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Parsetree.Pmod_extension@ %a)@]" pp_extension v0 ])
      ofmt arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and show_module_expr_desc : module_expr_desc → Stdlib.String.t =
  fun arg → Format.asprintf "%a" pp_module_expr_desc arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and pp_structure : Fmt.t structure =
  fun (ofmt : Format.formatter) arg →
    (fun (ofmt : Format.formatter) arg →
       let open Ppxprint_runtime.Runtime.Fmt in
       pf ofmt "@[<2>[%a@,]@]" (list ~{sep = semi} pp_structure_item) arg)
      ofmt arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and show_structure : structure → Stdlib.String.t =
  fun arg → Format.asprintf "%a" pp_structure arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and pp_structure_item : Fmt.t structure_item =
  fun (ofmt : Format.formatter) arg →
    (fun ofmt
         ({pstr_desc = v_pstr_desc; pstr_loc = v_pstr_loc} : structure_item) →
       let open Ppxprint_runtime.Runtime.Fmt in
       pf ofmt "@[<2>{ @[Parsetree.pstr_desc =@ %a@];@ @[pstr_loc =@ %a@] }@]"
         pp_structure_item_desc v_pstr_desc Location.pp v_pstr_loc)
      ofmt arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and show_structure_item : structure_item → Stdlib.String.t =
  fun arg → Format.asprintf "%a" pp_structure_item arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and pp_structure_item_desc : Fmt.t structure_item_desc =
  fun (ofmt : Format.formatter) arg →
    (fun ofmt →
       fun
       [ Pstr_eval v0 v1 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Parsetree.Pstr_eval@ (@,%a,@ %a@,))@]" pp_expression
             v0 pp_attributes v1
       | Pstr_value v0 v1 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Parsetree.Pstr_value@ (@,%a,@ %a@,))@]"
             Asttypes.pp_rec_flag v0
             (fun (ofmt : Format.formatter) arg →
                let open Ppxprint_runtime.Runtime.Fmt in
                pf ofmt "@[<2>[%a@,]@]" (list ~{sep = semi} pp_value_binding)
                  arg)
             v1
       | Pstr_primitive v0 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Parsetree.Pstr_primitive@ %a)@]"
             pp_value_description v0
       | Pstr_type v0 v1 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Parsetree.Pstr_type@ (@,%a,@ %a@,))@]"
             Asttypes.pp_rec_flag v0
             (fun (ofmt : Format.formatter) arg →
                let open Ppxprint_runtime.Runtime.Fmt in
                pf ofmt "@[<2>[%a@,]@]"
                  (list ~{sep = semi} pp_type_declaration) arg)
             v1
       | Pstr_typext v0 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Parsetree.Pstr_typext@ %a)@]" pp_type_extension v0
       | Pstr_exception v0 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Parsetree.Pstr_exception@ %a)@]" pp_type_exception
             v0
       | Pstr_module v0 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Parsetree.Pstr_module@ %a)@]" pp_module_binding v0
       | Pstr_recmodule v0 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Parsetree.Pstr_recmodule@ %a)@]"
             (fun (ofmt : Format.formatter) arg →
                let open Ppxprint_runtime.Runtime.Fmt in
                pf ofmt "@[<2>[%a@,]@]" (list ~{sep = semi} pp_module_binding)
                  arg)
             v0
       | Pstr_modtype v0 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Parsetree.Pstr_modtype@ %a)@]"
             pp_module_type_declaration v0
       | Pstr_open v0 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Parsetree.Pstr_open@ %a)@]" pp_open_declaration v0
       | Pstr_class v0 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Parsetree.Pstr_class@ %a)@]"
             (fun (ofmt : Format.formatter) arg →
                let open Ppxprint_runtime.Runtime.Fmt in
                pf ofmt "@[<2>[%a@,]@]"
                  (list ~{sep = semi} pp_class_declaration) arg)
             v0
       | Pstr_class_type v0 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Parsetree.Pstr_class_type@ %a)@]"
             (fun (ofmt : Format.formatter) arg →
                let open Ppxprint_runtime.Runtime.Fmt in
                pf ofmt "@[<2>[%a@,]@]"
                  (list ~{sep = semi} pp_class_type_declaration) arg)
             v0
       | Pstr_include v0 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Parsetree.Pstr_include@ %a)@]"
             pp_include_declaration v0
       | Pstr_attribute v0 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Parsetree.Pstr_attribute@ %a)@]" pp_attribute v0
       | Pstr_extension v0 v1 →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt "(@[<2>Parsetree.Pstr_extension@ (@,%a,@ %a@,))@]"
             pp_extension v0 pp_attributes v1 ])
      ofmt arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and show_structure_item_desc : structure_item_desc → Stdlib.String.t =
  fun arg → Format.asprintf "%a" pp_structure_item_desc arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and pp_value_constraint : Fmt.t value_constraint =
  fun (ofmt : Format.formatter) arg →
    (fun ofmt →
       fun
       [ Pvc_constraint
           {locally_abstract_univars = v_locally_abstract_univars;
            typ = v_typ} →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt
             "@[<2>Parsetree.Pvc_constraint {@[locally_abstract_univars =@ %a@];@ @[typ =@ %a@]}@]"
             (fun (ofmt : Format.formatter) arg →
                let open Ppxprint_runtime.Runtime.Fmt in
                pf ofmt "@[<2>[%a@,]@]"
                  (list ~{sep = semi}
                     (Asttypes.pp_loc
                        (fun ofmt arg →
                           let open Ppxprint_runtime.Runtime.Fmt in
                           pf ofmt "%S" arg)))
                  arg)
             v_locally_abstract_univars pp_core_type v_typ
       | Pvc_coercion {ground = v_ground; coercion = v_coercion} →
           let open Ppxprint_runtime.Runtime.Fmt in
           pf ofmt
             "@[<2>Parsetree.Pvc_coercion {@[ground =@ %a@];@ @[coercion =@ %a@]}@]"
             (fun ofmt →
                fun
                [ None →
                    let open Ppxprint_runtime.Runtime.Fmt in
                    const string "None" ofmt ()
                | Some arg →
                    let open Ppxprint_runtime.Runtime.Fmt in
                    pf ofmt "(Some %a)" pp_core_type arg ])
             v_ground pp_core_type v_coercion ])
      ofmt arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and show_value_constraint : value_constraint → Stdlib.String.t =
  fun arg → Format.asprintf "%a" pp_value_constraint arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and pp_value_binding : Fmt.t value_binding =
  fun (ofmt : Format.formatter) arg →
    (fun ofmt
         ({pvb_pat = v_pvb_pat; pvb_expr = v_pvb_expr;
           pvb_constraint = v_pvb_constraint;
           pvb_attributes = v_pvb_attributes; pvb_loc = v_pvb_loc} :
          value_binding) →
       let open Ppxprint_runtime.Runtime.Fmt in
       pf ofmt
         "@[<2>{ @[Parsetree.pvb_pat =@ %a@];@ @[pvb_expr =@ %a@];@ @[pvb_constraint =@ %a@];@ @[pvb_attributes =@ %a@];@ @[pvb_loc =@ %a@] }@]"
         pp_pattern v_pvb_pat pp_expression v_pvb_expr
         (fun ofmt →
            fun
            [ None →
                let open Ppxprint_runtime.Runtime.Fmt in
                const string "None" ofmt ()
            | Some arg →
                let open Ppxprint_runtime.Runtime.Fmt in
                pf ofmt "(Some %a)" pp_value_constraint arg ])
         v_pvb_constraint pp_attributes v_pvb_attributes Location.pp
         v_pvb_loc)
      ofmt arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and show_value_binding : value_binding → Stdlib.String.t =
  fun arg → Format.asprintf "%a" pp_value_binding arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and pp_module_binding : Fmt.t module_binding =
  fun (ofmt : Format.formatter) arg →
    (fun ofmt
         ({pmb_name = v_pmb_name; pmb_expr = v_pmb_expr;
           pmb_attributes = v_pmb_attributes; pmb_loc = v_pmb_loc} :
          module_binding) →
       let open Ppxprint_runtime.Runtime.Fmt in
       pf ofmt
         "@[<2>{ @[Parsetree.pmb_name =@ %a@];@ @[pmb_expr =@ %a@];@ @[pmb_attributes =@ %a@];@ @[pmb_loc =@ %a@] }@]"
         (Asttypes.pp_loc
            (fun ofmt →
               fun
               [ None →
                   let open Ppxprint_runtime.Runtime.Fmt in
                   const string "None" ofmt ()
               | Some arg →
                   let open Ppxprint_runtime.Runtime.Fmt in
                   pf ofmt "(Some %a)"
                     (fun ofmt arg →
                        let open Ppxprint_runtime.Runtime.Fmt in
                        pf ofmt "%S" arg)
                     arg ]))
         v_pmb_name pp_module_expr v_pmb_expr pp_attributes v_pmb_attributes
         Location.pp v_pmb_loc)
      ofmt arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
and show_module_binding : module_binding → Stdlib.String.t =
  fun arg → Format.asprintf "%a" pp_module_binding arg[@@"ocaml.warning" "-39";] [@@"ocaml.warning" "-33";]
;
[@@@"end"];


