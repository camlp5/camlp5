(* camlp5r *)
(***********************************************************************)
(*                                                                     *)
(*                             Camlp5                                  *)
(*                                                                     *)
(*                Daniel de Rauglaudre, INRIA Rocquencourt             *)
(*                                                                     *)
(*  Copyright 2007 Institut National de Recherche en Informatique et   *)
(*  Automatique.  Distributed only by permission.                      *)
(*                                                                     *)
(***********************************************************************)

(* $Id: pcaml.mli,v 1.8 2007/08/16 09:50:12 deraugla Exp $ *)

(** Language grammar, entries and printers.

   Hold variables to be set by language syntax extensions. Some of them
   are provided for quotations management. *)

value syntax_name : ref string;

(** {6 Parsers} *)

value parse_interf :
  ref (Stream.t char -> (list (MLast.sig_item * MLast.loc) * bool));
value parse_implem :
  ref (Stream.t char -> (list (MLast.str_item * MLast.loc) * bool));
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

value interf : Grammar.Entry.e (list (MLast.sig_item * MLast.loc) * bool);
value implem : Grammar.Entry.e (list (MLast.str_item * MLast.loc) * bool);
value top_phrase : Grammar.Entry.e (option MLast.str_item);
value use_file : Grammar.Entry.e (list MLast.str_item * bool);
value module_type : Grammar.Entry.e MLast.module_type;
value module_expr : Grammar.Entry.e MLast.module_expr;
value sig_item : Grammar.Entry.e MLast.sig_item;
value str_item : Grammar.Entry.e MLast.str_item;
value expr : Grammar.Entry.e MLast.expr;
value patt : Grammar.Entry.e MLast.patt;
value ctyp : Grammar.Entry.e MLast.ctyp;
value let_binding : Grammar.Entry.e (MLast.patt * MLast.expr);
value type_declaration : Grammar.Entry.e MLast.type_decl;
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
value version : string;
   (** The current version of Camlp5. *)
value add_option : string -> Arg.spec -> string -> unit;
   (** Add an option to the command line options. *)
value no_constructors_arity : ref bool;
   (** [True]: dont generate constructor arity. *)

value handle_expr_quotation : MLast.loc -> (string * string) -> MLast.expr;
value handle_patt_quotation : MLast.loc -> (string * string) -> MLast.patt;

(** {6 Printers} *)

value print_interf : ref (list (MLast.sig_item * MLast.loc) -> unit);
value print_implem : ref (list (MLast.str_item * MLast.loc) -> unit);
   (** Some printers, set by [pr_dump.cmo], [pr_o.cmo] and [pr_r.cmo]. *)

module Printers :
  sig
    type printer_t 'a = Eprinter.t 'a
    and pr_level 'a =
      Eprinter.pr_level 'a ==
        { pr_label : string; pr_rules : mutable pr_rule 'a }
    and pr_rule 'a =
      Extfun.t 'a
        (pr_fun 'a -> pr_fun 'a -> pr_context string string -> string)
    and pr_fun 'a = pr_context string string -> 'a -> string
    and pr_context 'bef 'aft =
      Eprinter.pr_context 'bef 'aft ==
        { ind : int; bef : 'bef; aft : 'aft; dang : string }
    ;
    value pr_expr : printer_t MLast.expr;
    value pr_patt : printer_t MLast.patt;
    value pr_ctyp : printer_t MLast.ctyp;
    value pr_str_item : printer_t MLast.str_item;
    value pr_sig_item : printer_t MLast.sig_item;
    value pr_module_expr : printer_t MLast.module_expr;
    value pr_module_type : printer_t MLast.module_type;
    value pr_class_sig_item : printer_t MLast.class_sig_item;
    value pr_class_str_item : printer_t MLast.class_str_item;
    value pr_class_type : printer_t MLast.class_type;
    value pr_class_expr : printer_t MLast.class_expr;
    value find_pr_level : string -> list (pr_level 'a) -> pr_level 'a;
    value pr_expr_fun_args :
      ref (Extfun.t MLast.expr (list MLast.patt * MLast.expr));
  end
;

module OldPrinters :
  sig
    open Spretty;
    type printer_t 'a =
      { pr_fun : mutable string -> 'a -> string -> kont -> pretty;
        pr_levels : mutable list (pr_level 'a) }
    and pr_level 'a =
      { pr_label : string;
        pr_box : 'a -> Stream.t pretty -> pretty;
        pr_rules : mutable pr_rule 'a }
    and pr_rule 'a =
      Extfun.t 'a (curr 'a -> next 'a -> string -> kont -> Stream.t pretty)
    and curr 'a = 'a -> string -> kont -> Stream.t pretty
    and next 'a = 'a -> string -> kont -> pretty
    and kont = Stream.t pretty;
    value pr_sig_item : printer_t MLast.sig_item;
    value pr_str_item : printer_t MLast.str_item;
    value pr_module_type : printer_t MLast.module_type;
    value pr_module_expr : printer_t MLast.module_expr;
    value pr_expr : printer_t MLast.expr;
    value pr_patt : printer_t MLast.patt;
    value pr_ctyp : printer_t MLast.ctyp;
    value pr_class_sig_item : printer_t MLast.class_sig_item;
    value pr_class_str_item : printer_t MLast.class_str_item;
    value pr_class_type : printer_t MLast.class_type;
    value pr_class_expr : printer_t MLast.class_expr;
    value pr_expr_fun_args :
      ref (Extfun.t MLast.expr (list MLast.patt * MLast.expr));
    value find_pr_level : string -> list (pr_level 'a) -> pr_level 'a;
    value top_printer : printer_t 'a -> 'a -> unit;
    value string_of : printer_t 'a -> 'a -> string;
    value inter_phrases : ref (option string);
  end
;

(** {6 Directives} *)

type directive_fun = option MLast.expr -> unit;
value add_directive : string -> directive_fun -> unit;
value find_directive : string -> directive_fun;

(**/**)

(* for system use *)

value warning : ref (Token.location -> string -> unit);
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
