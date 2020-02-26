val fast : bool ref
val get_tag : 'a -> int
val error : Ploc.t -> string -> 'a
val char_of_char_token : Ploc.t -> string -> char
val string_of_string_token : Ploc.t -> string -> string
val glob_fname : string ref
val mkloc : Ploc.t -> Location.t
val mktyp :
  ?alg_attributes:Parsetree.attributes ->
  Ploc.t -> Parsetree.core_type_desc -> Parsetree.core_type
val mkpat : Ploc.t -> Parsetree.pattern_desc -> Parsetree.pattern
val mkexp : Ploc.t -> Parsetree.expression_desc -> Parsetree.expression
val mkmty : Ploc.t -> Parsetree.module_type_desc -> Parsetree.module_type
val mksig :
  Ploc.t -> Parsetree.signature_item_desc -> Parsetree.signature_item
val mkmod : Ploc.t -> Parsetree.module_expr_desc -> Parsetree.module_expr
val mkstr :
  Ploc.t -> Parsetree.structure_item_desc -> Parsetree.structure_item
val mkfield :
  Ploc.t ->
  Asttypes.label * Parsetree.core_type ->
  Parsetree.object_field list -> Parsetree.object_field list
val mkfield_var : Ploc.t -> 'a list
val mkcty : Ploc.t -> Parsetree.class_type_desc -> Parsetree.class_type
val mkpcl : Ploc.t -> Parsetree.class_expr_desc -> Parsetree.class_expr
val mklazy : Ploc.t -> Parsetree.expression -> Parsetree.expression
val strip_char : char -> bytes -> bytes
val mkintconst : Ploc.t -> string -> string -> Asttypes.constant
val conv_con : string -> string
val conv_lab : string -> string
val array_function : string -> string -> Longident.t
val uv : 'a Ploc.vala -> 'a
val mkrf : bool -> Asttypes.rec_flag
val mkli : string -> string list -> Longident.t
val long_id_of_string_list : Ploc.t -> string list -> Longident.t
val long_id_class_type : Ploc.t -> MLast.class_type -> Longident.t
val ctyp_fa : MLast.ctyp list -> MLast.ctyp -> MLast.ctyp * MLast.ctyp list
val ctyp_long_id : MLast.ctyp -> bool * Longident.t
val module_type_long_id : MLast.module_type -> Longident.t
val variance_of_var : bool option -> bool * bool
val mktype :
  item_attributes:Parsetree.attributes ->
  Ploc.t ->
  string ->
  (string option Ploc.vala * bool option) list ->
  (Parsetree.core_type * Parsetree.core_type * Location.t) list ->
  Parsetree.type_kind ->
  Asttypes.private_flag ->
  Parsetree.core_type option -> Parsetree.type_declaration
val mkoverride : bool -> Asttypes.override_flag
val mkmutable : bool -> Asttypes.mutable_flag
val mkvirtual : bool -> Asttypes.virtual_flag
val mkprivate : bool -> Asttypes.private_flag
val option_map : ('a -> 'b) -> 'a option -> 'b option
val same_type_expr : MLast.ctyp -> MLast.expr -> bool
val module_expr_long_id : MLast.module_expr -> Longident.t
val patt_fa : MLast.patt list -> MLast.patt -> MLast.patt * MLast.patt list
val exception_to_constructor_pattern : MLast.patt -> MLast.patt
val mkrangepat : Ploc.t -> char -> char -> Parsetree.pattern
val patt_long_id : string list -> MLast.patt -> MLast.patt * string list
val patt_label_long_id : MLast.patt -> Longident.t
val int_of_string_l : Ploc.t -> string -> int
val expr_fa : MLast.expr list -> MLast.expr -> MLast.expr * MLast.expr list
val class_expr_fa :
  MLast.expr list -> MLast.class_expr -> MLast.class_expr * MLast.expr list
val sep_expr_acc :
  (MLast.loc * string list * MLast.expr) list ->
  MLast.expr -> (MLast.loc * string list * MLast.expr) list
val list_map_check : ('a -> 'b option) -> 'a list -> 'b list option
val class_info :
  ((string Ploc.vala * MLast.payload) Ploc.vala list Ploc.vala ->
   Parsetree.attributes) ->
  ('a -> 'b) -> 'a MLast.class_infos -> 'b Parsetree.class_infos
val bigarray_get : MLast.loc -> MLast.expr -> MLast.expr list -> MLast.expr
val bigarray_set :
  MLast.loc -> MLast.expr -> MLast.expr list -> MLast.expr -> MLast.expr
val neg_string : string -> string
val varify_constructors : string list -> MLast.ctyp -> MLast.ctyp
val label_of_patt : MLast.patt -> string
val type_decl_of_with_type :
  MLast.loc ->
  string ->
  MLast.type_var list Ploc.vala ->
  bool -> MLast.ctyp -> (string, Parsetree.type_declaration) Versdep.choice
val mkwithc : MLast.with_constr -> Longident.t * Parsetree.with_constraint
val mkvalue_desc :
  item_attributes:Parsetree.attributes ->
  string -> MLast.ctyp -> string list -> Parsetree.value_description
val mktvariant :
  MLast.loc ->
  (MLast.loc * string Ploc.vala * MLast.ctyp list Ploc.vala *
   MLast.ctyp option *
   (string Ploc.vala * MLast.payload) Ploc.vala list Ploc.vala)
  list -> bool -> Parsetree.type_kind
val mktrecord :
  (MLast.loc * string * bool * MLast.ctyp *
   (string Ploc.vala * MLast.payload) Ploc.vala list Ploc.vala)
  list -> bool -> Parsetree.type_kind
val ctyp : MLast.ctyp -> Parsetree.core_type
val meth_list :
  MLast.loc ->
  (string * MLast.ctyp) list -> bool Ploc.vala -> Parsetree.object_field list
val add_polytype : MLast.ctyp -> Parsetree.core_type
val package_of_module_type :
  MLast.loc -> MLast.module_type -> Parsetree.package_type
val type_decl :
  ?item_attributes:Parsetree.attributes ->
  string ->
  MLast.type_var list ->
  Asttypes.private_flag ->
  (Parsetree.core_type * Parsetree.core_type * Location.t) list ->
  MLast.ctyp -> Parsetree.type_declaration
val patt : MLast.patt -> Parsetree.pattern
val mklabpat :
  MLast.patt * MLast.patt -> Longident.t * Location.t * Parsetree.pattern
val expr : MLast.expr -> Parsetree.expression
val label_expr :
  (string * Parsetree.expression) list ->
  MLast.expr -> (string * Parsetree.expression) list
val mkjoinclause :
  MLast.joinclause ->
  Location.t *
  (Location.t *
   ((Location.t * (Location.t * string) * Parsetree.pattern) list *
    Parsetree.expression))
  list
val mkpe :
  MLast.patt * MLast.expr *
  (string Ploc.vala * MLast.payload) Ploc.vala list Ploc.vala ->
  Parsetree.value_binding
val expand_gadt_type :
  MLast.loc ->
  MLast.patt ->
  MLast.loc ->
  string list Ploc.vala ->
  MLast.ctyp -> MLast.expr -> MLast.patt * MLast.expr
val mkpwe :
  MLast.patt * MLast.expr option Ploc.vala * MLast.expr -> Parsetree.case
val mklabexp :
  MLast.patt * MLast.expr -> Longident.t * Location.t * Parsetree.expression
val mkideexp :
  Asttypes.label * MLast.expr -> Asttypes.label * Parsetree.expression
val mktype_decl : MLast.type_decl -> string * Parsetree.type_declaration
val module_type : MLast.module_type -> Parsetree.module_type
val sig_item : MLast.sig_item -> Parsetree.signature -> Parsetree.signature
val module_expr : MLast.module_expr -> Parsetree.module_expr
val str_item : MLast.str_item -> Parsetree.structure -> Parsetree.structure
val class_type : MLast.class_type -> Parsetree.class_type
val class_sig_item :
  MLast.class_sig_item ->
  Parsetree.class_type_field list -> Parsetree.class_type_field list
val class_expr : MLast.class_expr -> Parsetree.class_expr
val class_str_item :
  MLast.class_str_item ->
  Parsetree.class_field list -> Parsetree.class_field list
val item_attributes :
  (string Ploc.vala * MLast.payload) Ploc.vala list Ploc.vala ->
  Parsetree.attributes
val alg_attributes :
  (string Ploc.vala * MLast.payload) Ploc.vala list Ploc.vala ->
  Parsetree.attributes
val attr : string Ploc.vala * MLast.payload -> Parsetree.attribute
val extension : string Ploc.vala * MLast.payload -> Parsetree.extension
val interf : string -> MLast.sig_item list -> Parsetree.signature
val implem : string -> MLast.str_item list -> Parsetree.structure
val directive : Ploc.t -> MLast.expr -> Parsetree.directive_argument_desc
val directive_args :
  Ploc.t -> MLast.expr option -> Parsetree.directive_argument_desc option
val phrase : MLast.str_item -> Parsetree.toplevel_phrase
