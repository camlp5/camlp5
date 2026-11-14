(* camlp5r *)
(* pcaml.mli,v *)
(* Copyright (c) INRIA 2007-2017 *)

(* #load "pa_macro.cmo" *)

include module type of Pcamlbase;;

type status = Ploc.t option;;

(** Language grammar, entries and printers.

   Hold variables to be set by language syntax extensions. Some of them
   are provided for quotations management. *)

val syntax_name : string ref;;

(** {6 Parsers} *)

module Lexer : Plexer.LEXER;;
module ParseBase : (Mlsyntax.PARSEBASESIG with module Lexer = Lexer);;

include Mlsyntax.PARSERS;;

val input_file : string ref;;
   (** The file currently being parsed. *)



val output_file : string option ref;;
   (** The output file, stdout if None (default) *)
val version : string;;
   (** The current version of Camlp5. *)
val ocaml_version : string;;
   (** The current version of OCaml, possibly truncated after space or '+':
       e.g. if OCaml version is "4.05.0+beta3", it is "4.05.0" *)
val add_option : string -> Arg.spec -> string -> unit;;
   (** Add an option to the command line options. *)
val add_options : (string * Arg.spec * string) list -> unit;;
   (** Add a list of options to the command line options. *)
val no_constructors_arity : bool ref;;
   (** [True]: dont generate constructor arity. *)

module QuotationHelper :
  (module type of Quotation.QuotationExpansion (ParseBase))
;;
module QH : (module type of QuotationHelper);;

include module type of QH;;

(** {6 Printers} *)

val print_interf :
  ((MLast.sig_item * MLast.loc) list * MLast.loc -> unit) ref;;
val print_implem :
  ((MLast.str_item * MLast.loc) list * MLast.loc -> unit) ref;;

module PrintBase : Mlsyntax.PRINTBASESIG;;
include Mlsyntax.PRINTERS;;

val inter_phrases : string option ref;;
   (** String displayed between two consecutive phrases. If [None], the
       string is taken in the sources between these phrases. Default = None *)

(** {6 Directives} *)

type directive_fun = MLast.expr option -> unit;;
val add_directive : string -> directive_fun -> unit;;
val add_directives : (string * directive_fun) list -> unit;;
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

val strict_mode : bool ref;;
   (* [True] if the current mode is "strict", [False] if "transitional" *)

(* *)

val unvala : 'a -> 'a;;
val vala_map : ('a -> 'b) -> 'a -> 'b;;
val vala_it : ('a -> unit) -> 'a -> unit;;
val vala_mapa : ('a -> 'b) -> (string -> 'b) -> 'a -> 'b;;

(**/**)

(* for system use *)

val arg_spec_list : unit -> (string * Arg.spec * string) list;;
val report_error : exn -> unit;;
val sync : (char Stream.t -> unit) ref;;
val rename_id : (string -> string) ref;;
val flag_comments_in_phrases : bool ref;;
val flag_equilibrate_cases : bool ref;;
val flag_expand_letop_syntax : bool ref;;
