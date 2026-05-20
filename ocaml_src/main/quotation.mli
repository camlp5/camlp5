(* camlp5r *)
(* quotation.mli,v *)
(* Copyright (c) INRIA 2007-2017 *)

(** Quotation operations. *)

open Pcamlbase;;

val default : string ref;;
   (** [default] holds the default quotation name. *)

module type QUOTATION_EXPANSION =
  sig
    module Base : Mlsyntax.PARSEBASESIG;;
    type expander =
        ExStr of (bool -> string -> string)
      | ExAst of ((string -> MLast.expr) * (string -> MLast.patt))
    ;;
    val add : string -> expander -> unit;;
    val upsert : string -> expander -> unit;;
    val find : string -> expander;;
    val translate : (string -> string) ref;;
    val quotation_dump_file : string option ref;;
    val quotation_location : unit -> Ploc.t;;
    val expand_quotation :
      Ploc.t -> (string -> 'b) -> int -> string -> string -> 'b;;
    val handle_expr_quotation : MLast.loc -> string * string -> MLast.expr;;
    val handle_patt_quotation : MLast.loc -> string * string -> MLast.patt;;
    val expr_eoi : MLast.expr Grammar.Entry.e;;
    val patt_eoi : MLast.patt Grammar.Entry.e;;
    val pp_report_quotation_error :
      Format.formatter -> string -> string -> err_ctx -> unit;;
  end
;;

open Mlsyntax;;
module QuotationExpansion (PB : PARSEBASESIG) : QUOTATION_EXPANSION;;
