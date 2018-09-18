(* camlp5r *)
(* pcaml.mli,v *)
(* Copyright (c) INRIA 2007-2017 *)

(* #load "pa_macro.cmo" *)

(** Language grammar, entries and printers.

   Hold variables to be set by language syntax extensions. Some of them
   are provided for quotations management. *)

val syntax_name : string ref;;

(** {6 Parsers} *)

type status = Ploc.t option;;

val parse_interf :
  (char Stream.t -> (MLast.sig_item * MLast.loc) list * status) ref;;
val parse_implem :
  (char Stream.t -> (MLast.str_item * MLast.loc) list * status) ref;;
   (** Called when parsing an interface (mli file) or an implementation
       (ml file) to build the syntax tree; the returned list contains the
       phrases (signature items or structure items) and their locations;
       the boolean tells that the parser has encountered a directive; in
       this case, since the directive may change the syntax, the parsing
       stops, the directive is evaluated, and this function is called
       again.
       These functions are references, because they can be changed to
       use another technology than the Camlp5 extended grammars. By
       default, they use the grammars entries [implem] and [interf]
       defined below. *)

val gram : Grammar.g;;
   (** Grammar variable of the OCaml language *)

val interf : ((MLast.sig_item * MLast.loc) list * status) Grammar.Entry.e;;
val implem : ((MLast.str_item * MLast.loc) list * status) Grammar.Entry.e;;
val top_phrase : MLast.str_item option Grammar.Entry.e;;
val use_file : (MLast.str_item list * bool) Grammar.Entry.e;;
val module_type : MLast.module_type Grammar.Entry.e;;
val module_expr : MLast.module_expr Grammar.Entry.e;;
val signature : MLast.sig_item list MLast.v Grammar.Entry.e;;
val structure : MLast.str_item list MLast.v Grammar.Entry.e;;
val sig_item : MLast.sig_item Grammar.Entry.e;;
val str_item : MLast.str_item Grammar.Entry.e;;
val expr : MLast.expr Grammar.Entry.e;;
val patt : MLast.patt Grammar.Entry.e;;
val ipatt : MLast.patt Grammar.Entry.e;;
val ctyp : MLast.ctyp Grammar.Entry.e;;
val let_binding : (MLast.patt * MLast.expr) Grammar.Entry.e;;
val type_decl : MLast.type_decl Grammar.Entry.e;;
val match_case :
  (MLast.patt * MLast.expr option MLast.v * MLast.expr) Grammar.Entry.e;;
val constructor_declaration :
  (MLast.loc * string MLast.v * MLast.ctyp list MLast.v * MLast.ctyp option)
    Grammar.Entry.e;;
val label_declaration :
  (MLast.loc * string * bool * MLast.ctyp) Grammar.Entry.e;;
val with_constr : MLast.with_constr Grammar.Entry.e;;
val poly_variant : MLast.poly_variant Grammar.Entry.e;;
val class_sig_item : MLast.class_sig_item Grammar.Entry.e;;
val class_str_item : MLast.class_str_item Grammar.Entry.e;;
val class_expr : MLast.class_expr Grammar.Entry.e;;
val class_type : MLast.class_type Grammar.Entry.e;;
   (** Some entries of the language, set by [pa_o.cmo] and [pa_r.cmo]. *)

val input_file : string ref;;
   (** The file currently being parsed. *)
val output_file : string option ref;;
   (** The output file, stdout if None (default) *)
val quotation_dump_file : string option ref;;
   (** [quotation_dump_file] optionally tells the compiler to dump the
       result of an expander (of kind "generating a string") if this
       result is syntactically incorrect.
       If [None] (default), this result is not dumped. If [Some fname], the
       result is dumped in the file [fname]. *)
val quotation_location : unit -> Ploc.t;;
   (** while expanding a quotation, returns the location of the quotation
       text (between the quotation quotes) in the source; raises
       [Failure] if not in the context of a quotation expander. *)
val version : string;;
   (** The current version of Camlp5. *)
val ocaml_version : string;;
   (** The current version of OCaml, possibly truncated after space or '+':
       e.g. if OCaml version is "4.05.0+beta3", it is "4.05.0" *)
val add_option : string -> Arg.spec -> string -> unit;;
   (** Add an option to the command line options. *)
val no_constructors_arity : bool ref;;
   (** [True]: dont generate constructor arity. *)
val string_of_loc : string -> int -> int -> int -> string;;
   (** [string_of_loc fname line bp ep] returns the location string for
       file [fname] at [line] and between character [bp] and [ep]. *)

val handle_expr_quotation : MLast.loc -> string * string -> MLast.expr;;
val handle_patt_quotation : MLast.loc -> string * string -> MLast.patt;;

(** {6 Printers} *)

val print_interf :
  ((MLast.sig_item * MLast.loc) list * MLast.loc -> unit) ref;;
val print_implem :
  ((MLast.str_item * MLast.loc) list * MLast.loc -> unit) ref;;

val pr_expr : MLast.expr Eprinter.t;;
val pr_patt : MLast.patt Eprinter.t;;
val pr_ctyp : MLast.ctyp Eprinter.t;;
val pr_str_item : MLast.str_item Eprinter.t;;
val pr_sig_item : MLast.sig_item Eprinter.t;;
val pr_module_expr : MLast.module_expr Eprinter.t;;
val pr_module_type : MLast.module_type Eprinter.t;;
val pr_class_sig_item : MLast.class_sig_item Eprinter.t;;
val pr_class_str_item : MLast.class_str_item Eprinter.t;;
val pr_class_type : MLast.class_type Eprinter.t;;
val pr_class_expr : MLast.class_expr Eprinter.t;;
   (** Some printers, set by [pr_dump.cmo], [pr_o.cmo] and [pr_r.cmo]. *)

val pr_expr_fun_args :
  (MLast.expr, MLast.patt list * MLast.expr) Extfun.t ref;;

val inter_phrases : string option ref;;
   (** String displayed between two consecutive phrases. If [None], the
       string is taken in the sources between these phrases. Default = None *)

(** {6 Directives} *)

type directive_fun = MLast.expr option -> unit;;
val add_directive : string -> directive_fun -> unit;;
val find_directive : string -> directive_fun;;

(** {6 equality over abstact syntax trees (ignoring locations)} *)

val eq_expr : MLast.expr -> MLast.expr -> bool;;
val eq_patt : MLast.patt -> MLast.patt -> bool;;
val eq_ctyp : MLast.ctyp -> MLast.ctyp -> bool;;
val eq_str_item : MLast.str_item -> MLast.str_item -> bool;;
val eq_sig_item : MLast.sig_item -> MLast.sig_item -> bool;;
val eq_module_expr : MLast.module_expr -> MLast.module_expr -> bool;;
val eq_module_type : MLast.module_type -> MLast.module_type -> bool;;
val eq_class_sig_item : MLast.class_sig_item -> MLast.class_sig_item -> bool;;
val eq_class_str_item : MLast.class_str_item -> MLast.class_str_item -> bool;;
val eq_class_type : MLast.class_type -> MLast.class_type -> bool;;
val eq_class_expr : MLast.class_expr -> MLast.class_expr -> bool;;

(** {6 Other} *)

val greek_ascii_equiv : string -> string;;
   (* Gives an ascii equivalent to a greek letter representing a type
      parameter. E.g. 'a' for 'α', 'b' for 'β', and so on. *)

val strict_mode : bool ref;;
   (* [True] if the current mode is "strict", [False] if "transitional" *)

(* *)

val unvala : 'a -> 'a;;
val vala_map : ('a -> 'b) -> 'a -> 'b;;
val vala_mapa : ('a -> 'b) -> (string -> 'b) -> 'a -> 'b;;

(**/**)

(* for system use *)

val warning : (Ploc.t -> string -> unit) ref;;
val expr_eoi : MLast.expr Grammar.Entry.e;;
val patt_eoi : MLast.patt Grammar.Entry.e;;
val arg_spec_list : unit -> (string * Arg.spec * string) list;;
val report_error : exn -> unit;;
val sync : (char Stream.t -> unit) ref;;
val patt_reloc : (MLast.loc -> MLast.loc) -> int -> MLast.patt -> MLast.patt;;
val expr_reloc : (MLast.loc -> MLast.loc) -> int -> MLast.expr -> MLast.expr;;
val rename_id : (string -> string) ref;;
val flag_comments_in_phrases : bool ref;;
val flag_equilibrate_cases : bool ref;;
val flag_compatible_old_versions_of_ocaml : bool ref;;
