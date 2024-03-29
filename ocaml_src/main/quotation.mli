(* camlp5r *)
(* quotation.mli,v *)
(* Copyright (c) INRIA 2007-2017 *)

(** Quotation operations. *)

type expander =
    ExStr of (bool -> string -> string)
  | ExAst of ((string -> MLast.expr) * (string -> MLast.patt))
;;
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

val add : string -> expander -> unit;;
   (** [add name exp] adds the quotation [name] associated with the
       expander [exp]. *)

val upsert : string -> expander -> unit;;
(** [upsert name exp] adds or updates the quotation [name] associated
   with the expander [exp]. If it's an update (the quotation already
   exists) then a warning message is emitted to stderr.

    WARNING: this should not be commonly-used, as it can and will lead
   to interesting and hard-to-debug errors if quotations are overriden
   and users are not aware of it (perhaps because they don't carefully
   scan logfiles for warnings).

  *)

val find : string -> expander;;
   (** [find name] returns the expander of the given quotation name. *)

val default : string ref;;
   (** [default] holds the default quotation name. *)

val translate : (string -> string) ref;;
   (** function translating quotation names; default = identity *)
