(* camlp5r *)
(* pcaml.mli,v *)
(* Copyright (c) INRIA 2007-2017 *)

#load "pa_macro.cmo";

(** Language grammar, entries and printers.

   Hold variables to be set by language syntax extensions. Some of them
   are provided for quotations management. *)

value syntax_name : ref string;

(** {6 Parsers} *)

type status = option Ploc.t;

value parse_interf :
  ref (Stream.t char -> (list (MLast.sig_item * MLast.loc) * status));
value parse_implem :
  ref (Stream.t char -> (list (MLast.str_item * MLast.loc) * status));
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

value gram : Grammar.g;
   (** Grammar variable of the OCaml language *)

value interf : Grammar.Entry.e (list (MLast.sig_item * MLast.loc) * status);
value implem : Grammar.Entry.e (list (MLast.str_item * MLast.loc) * status);
value top_phrase : Grammar.Entry.e (option MLast.str_item);
value use_file : Grammar.Entry.e (list MLast.str_item * bool);
value module_type : Grammar.Entry.e MLast.module_type;
value module_expr : Grammar.Entry.e MLast.module_expr;
value signature : Grammar.Entry.e (MLast.v (list MLast.sig_item));
value structure : Grammar.Entry.e (MLast.v (list MLast.str_item));
value sig_item : Grammar.Entry.e MLast.sig_item;
value str_item : Grammar.Entry.e MLast.str_item;
value expr : Grammar.Entry.e MLast.expr;
value patt : Grammar.Entry.e MLast.patt;
value ipatt : Grammar.Entry.e MLast.patt;
value ctyp : Grammar.Entry.e MLast.ctyp;
value let_binding : Grammar.Entry.e (MLast.patt * MLast.expr);
value type_decl : Grammar.Entry.e MLast.type_decl;
value match_case :
  Grammar.Entry.e (MLast.patt * MLast.v (option MLast.expr) * MLast.expr);
value constructor_declaration :
  Grammar.Entry.e
    (MLast.loc * MLast.v string * MLast.v (list MLast.ctyp) *
     option MLast.ctyp);
value label_declaration :
  Grammar.Entry.e (MLast.loc * string * bool * MLast.ctyp);
value with_constr : Grammar.Entry.e MLast.with_constr;
value poly_variant : Grammar.Entry.e MLast.poly_variant;
value class_sig_item : Grammar.Entry.e MLast.class_sig_item;
value class_str_item : Grammar.Entry.e MLast.class_str_item;
value class_expr : Grammar.Entry.e MLast.class_expr;
value class_type : Grammar.Entry.e MLast.class_type;
   (** Some entries of the language, set by [pa_o.cmo] and [pa_r.cmo]. *)

value input_file : ref string;
   (** The file currently being parsed. *)
value output_file : ref (option string);
   (** The output file, stdout if None (default) *)
value quotation_dump_file : ref (option string);
   (** [quotation_dump_file] optionally tells the compiler to dump the
       result of an expander (of kind "generating a string") if this
       result is syntactically incorrect.
       If [None] (default), this result is not dumped. If [Some fname], the
       result is dumped in the file [fname]. *)
value quotation_location : unit -> Ploc.t;
   (** while expanding a quotation, returns the location of the quotation
       text (between the quotation quotes) in the source; raises
       [Failure] if not in the context of a quotation expander. *)
value version : string;
   (** The current version of Camlp5. *)
value ocaml_version : string;
   (** The current version of OCaml, possibly truncated after space or '+':
       e.g. if OCaml version is "4.05.0+beta3", it is "4.05.0" *)
value add_option : string -> Arg.spec -> string -> unit;
   (** Add an option to the command line options. *)
value no_constructors_arity : ref bool;
   (** [True]: dont generate constructor arity. *)
value string_of_loc : string -> int -> int -> int -> string;
   (** [string_of_loc fname line bp ep] returns the location string for
       file [fname] at [line] and between character [bp] and [ep]. *)

value handle_expr_quotation : MLast.loc -> (string * string) -> MLast.expr;
value handle_patt_quotation : MLast.loc -> (string * string) -> MLast.patt;

(** {6 Printers} *)

value print_interf :
  ref ((list (MLast.sig_item * MLast.loc) * MLast.loc) -> unit);
value print_implem :
  ref ((list (MLast.str_item * MLast.loc) * MLast.loc) -> unit);

value pr_expr : Eprinter.t MLast.expr;
value pr_patt : Eprinter.t MLast.patt;
value pr_ctyp : Eprinter.t MLast.ctyp;
value pr_str_item : Eprinter.t MLast.str_item;
value pr_sig_item : Eprinter.t MLast.sig_item;
value pr_module_expr : Eprinter.t MLast.module_expr;
value pr_module_type : Eprinter.t MLast.module_type;
value pr_class_sig_item : Eprinter.t MLast.class_sig_item;
value pr_class_str_item : Eprinter.t MLast.class_str_item;
value pr_class_type : Eprinter.t MLast.class_type;
value pr_class_expr : Eprinter.t MLast.class_expr;
   (** Some printers, set by [pr_dump.cmo], [pr_o.cmo] and [pr_r.cmo]. *)

value pr_expr_fun_args :
  ref (Extfun.t MLast.expr (list MLast.patt * MLast.expr));

value inter_phrases : ref (option string);
   (** String displayed between two consecutive phrases. If [None], the
       string is taken in the sources between these phrases. Default = None *)

(** {6 Directives} *)

type directive_fun = option MLast.expr -> unit;
value add_directive : string -> directive_fun -> unit;
value find_directive : string -> directive_fun;

(** {6 equality over abstact syntax trees (ignoring locations)} *)

value eq_expr : MLast.expr -> MLast.expr -> bool;
value eq_patt : MLast.patt -> MLast.patt -> bool;
value eq_ctyp : MLast.ctyp -> MLast.ctyp -> bool;
value eq_str_item : MLast.str_item -> MLast.str_item -> bool;
value eq_sig_item : MLast.sig_item -> MLast.sig_item -> bool;
value eq_module_expr : MLast.module_expr -> MLast.module_expr -> bool;
value eq_module_type : MLast.module_type -> MLast.module_type -> bool;
value eq_class_sig_item :
  MLast.class_sig_item -> MLast.class_sig_item -> bool;
value eq_class_str_item :
  MLast.class_str_item -> MLast.class_str_item -> bool;
value eq_class_type : MLast.class_type -> MLast.class_type -> bool;
value eq_class_expr : MLast.class_expr -> MLast.class_expr -> bool;

(** {6 Other} *)

value greek_ascii_equiv : string → string;
   (* Gives an ascii equivalent to a greek letter representing a type
      parameter. E.g. 'a' for 'α', 'b' for 'β', and so on. *)

value strict_mode : ref bool;
   (* [True] if the current mode is "strict", [False] if "transitional" *)

IFNDEF STRICT THEN
  DEFINE V t = t
ELSE
  DEFINE V t = Ploc.vala t
END;

value unvala : V 'a -> 'a;
value vala_map : ('a -> 'b) -> V 'a -> V 'b;
value vala_mapa : ('a -> 'b) -> (string -> 'b) -> V 'a -> 'b;

(**/**)

(* for system use *)

value warning : ref (Ploc.t -> string -> unit);
value expr_eoi : Grammar.Entry.e MLast.expr;
value patt_eoi : Grammar.Entry.e MLast.patt;
value arg_spec_list : unit -> list (string * Arg.spec * string);
value report_error : exn -> unit;
value sync : ref (Stream.t char -> unit);
value patt_reloc :
  (MLast.loc -> MLast.loc) -> int -> MLast.patt -> MLast.patt;
value expr_reloc :
  (MLast.loc -> MLast.loc) -> int -> MLast.expr -> MLast.expr;
value rename_id : ref (string -> string);
value flag_comments_in_phrases : ref bool;
value flag_equilibrate_cases : ref bool;
value flag_compatible_old_versions_of_ocaml : ref bool;
