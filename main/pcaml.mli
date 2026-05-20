(* camlp5r *)
(* pcaml.mli,v *)
(* Copyright (c) INRIA 2007-2017 *)

#load "pa_macro.cmo";

include (module type of Pcamlbase) ;

type status = option Ploc.t;

(** Language grammar, entries and printers.

   Hold variables to be set by language syntax extensions. Some of them
   are provided for quotations management. *)

value syntax_name : ref string;

(** {6 Parsers} *)

module Lexer : Plexer.LEXER ;
module ParseBase : (Mlsyntax.PARSEBASESIG with module Lexer = Lexer) ;
open Mlsyntax ;

include Mlsyntax.PARSERS ;

value input_file : ref string;
   (** The file currently being parsed. *)

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


value output_file : ref (option string);
   (** The output file, stdout if None (default) *)
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

module QuotationHelper : Quotation.QUOTATION_EXPANSION ;
module QH : Quotation.QUOTATION_EXPANSION ;
include (module type of QH) ;

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

value arg_spec_list : unit -> list (string * Arg.spec * string);
value report_error : exn -> unit;
value sync : ref (Stream.t char -> unit);
value rename_id : ref (string -> string);
value flag_comments_in_phrases : ref bool;
value flag_equilibrate_cases : ref bool;
value flag_expand_letop_syntax : ref bool;
