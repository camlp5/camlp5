(* camlp5r *)
(* quotation.mli,v *)
(* Copyright (c) INRIA 2007-2017 *)

(** Quotation operations. *)

open Pcamlbase ;

value default : ref string;
   (** [default] holds the default quotation name. *)

module type QUOTATION_EXPANSION = sig
  module Base : Mlsyntax.PARSEBASESIG ;

type expander =
  [ ExStr of bool -> string -> string
  | ExAst of (string -> MLast.expr * string -> MLast.patt) ]
;
(** The type for quotation expanders kind:
-      [ExStr exp] for an expander [exp] returning a string which
         can be parsed to create a syntax tree. Its boolean parameter
         tells whether the quotation is in position of an expression
         (True) or in position of a pattern (False). Quotations expanders
         created this way may work for some particular language syntax,
         and not for another one (e.g. may work when used with revised
         syntax and not when used with normal syntax, and conversely).
-      [ExAst (expr_exp, patt_exp)] for expanders returning directly
         syntax trees, therefore not necessiting to be parsed afterwards.
         The function [expr_exp] is called when the quotation is in
         position of an expression, and [patt_exp] when the quotation is
         in position of a pattern. Quotation expanders created this way
         are independent from the language syntax. *)

value add : string -> expander -> unit;
   (** [add name exp] adds the quotation [name] associated with the
       expander [exp]. *)

value upsert : string -> expander -> unit;
(** [upsert name exp] adds or updates the quotation [name] associated
   with the expander [exp]. If it's an update (the quotation already
   exists) then a warning message is emitted to stderr.

    WARNING: this should not be commonly-used, as it can and will lead
   to interesting and hard-to-debug errors if quotations are overriden
   and users are not aware of it (perhaps because they don't carefully
   scan logfiles for warnings).

  *)

value find : string -> expander;
   (** [find name] returns the expander of the given quotation name. *)

value translate : ref (string -> string);
   (** function translating quotation names; default = identity *)

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
  value expand_quotation : Ploc.t -> (string -> 'b) -> int -> string -> string -> 'b ;
  value handle_expr_quotation : MLast.loc -> (string * string) -> MLast.expr;
  value handle_patt_quotation : MLast.loc -> (string * string) -> MLast.patt;
  value expr_eoi : Grammar.Entry.e MLast.expr;
  value patt_eoi : Grammar.Entry.e MLast.patt;
  value pp_report_quotation_error :
    Format.formatter -> string -> string -> err_ctx -> unit ;
end ;

open Mlsyntax ;
module QuotationExpansion(PB : PARSEBASESIG) : QUOTATION_EXPANSION ;
