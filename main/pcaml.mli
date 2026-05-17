(* camlp5r *)
(* pcaml.mli,v *)
(* Copyright (c) INRIA 2007-2017 *)

#load "pa_macro.cmo";

(** Language grammar, entries and printers.

   Hold variables to be set by language syntax extensions. Some of them
   are provided for quotations management. *)

value syntax_name : ref string;

(** {6 Parsers} *)

module ParseBase : Mlsyntax.PARSEBASESIG ;
include Mlsyntax.PARSERS ;

type ast_transducer_t 'a = {
  name : string ;
  parse : ref (option (Stream.t char -> 'a)) ;
  transform : ref (option ('a -> 'a))
} ;
value set_ast_parse : ast_transducer_t 'a ->  (Stream.t char -> 'a) -> unit ;
value set_ast_transform : ast_transducer_t 'a -> ('a -> 'a) -> unit ;
value transduce : ast_transducer_t 'a -> Stream.t char -> 'a ;
value transduce_interf : ast_transducer_t (list (MLast.sig_item * MLast.loc) * status) ;
value transduce_implem : ast_transducer_t (list (MLast.str_item * MLast.loc) * status) ;
value transduce_top_phrase : ast_transducer_t (option MLast.str_item) ;
value transduce_use_file : ast_transducer_t (list MLast.str_item * bool) ;

value parse_interf :
  (Stream.t char -> (list (MLast.sig_item * MLast.loc) * status));
value parse_implem :
  (Stream.t char -> (list (MLast.str_item * MLast.loc) * status));
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

value parse_top_phrase :
  (Stream.t char -> (option MLast.str_item));
value parse_use_file :
  (Stream.t char -> (list MLast.str_item * bool));


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
value add_options : list (string * Arg.spec * string) -> unit;
   (** Add a list of options to the command line options. *)
value no_constructors_arity : ref bool;
   (** [True]: dont generate constructor arity. *)
value string_of_loc : string -> int -> int -> int -> string;
   (** [string_of_loc fname line bp ep] returns the location string for
       file [fname] at [line] and between character [bp] and [ep]. *)


type err_ctx =
  [ Finding
  | Expanding
  | ParsingResult of Ploc.t and string ]
;
exception Qerror of string and string and err_ctx and exn;

value expand_quotation : Ploc.t -> (string -> 'b) -> int -> string -> string -> 'b ;
value handle_expr_quotation : MLast.loc -> (string * string) -> MLast.expr;
value handle_patt_quotation : MLast.loc -> (string * string) -> MLast.patt;

(** {6 Printers} *)

value print_interf :
  ref ((list (MLast.sig_item * MLast.loc) * MLast.loc) -> unit);
value print_implem :
  ref ((list (MLast.str_item * MLast.loc) * MLast.loc) -> unit);

module PrintBase : Mlsyntax.PRINTBASESIG ;
include Mlsyntax.PRINTERS ;

value inter_phrases : ref (option string);
   (** String displayed between two consecutive phrases. If [None], the
       string is taken in the sources between these phrases. Default = None *)

(** {6 Directives} *)

type directive_fun = option MLast.expr -> unit;
value add_directive : string -> directive_fun -> unit;
value add_directives : list (string * directive_fun) -> unit;
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

value strict_mode : ref bool;
   (* [True] if the current mode is "strict", [False] if "transitional" *)

IFNDEF STRICT THEN
  DEFINE V t = t
ELSE
  DEFINE V t = Ploc.vala t
END;

value unvala : V 'a -> 'a;
value vala_map : ('a -> 'b) -> V 'a -> V 'b;
value vala_it : ('a -> unit) -> V 'a -> unit;
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
value flag_expand_letop_syntax : ref bool;
