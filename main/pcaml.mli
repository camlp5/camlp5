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

include Mlsyntax.PARSERS ;

value input_file : ref string;
   (** The file currently being parsed. *)



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

module QuotationHelper : module type of Quotation.QuotationExpansion(ParseBase) ;
module QH : module type of QuotationHelper ;

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
