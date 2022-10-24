(* camlp5r *)
(* ast2pt.mli,v *)

val longid_long_id : MLast.longid -> Longident.t;;
val conv_con : string -> string;;

(** Conversion between Camlp5 AST into OCaml AST *)

val interf : string -> MLast.sig_item list -> Parsetree.signature;;
   (** [interf fname ast] return the OCaml equivalent AST of an
       interface (mli file), [fname] being the input file name. *)
val implem : string -> MLast.str_item list -> Parsetree.structure;;
   (** [implem fname ast] return the OCaml equivalent AST of an
       implementation (ml file), [fname] being the input file name. *)
val phrase : MLast.str_item -> Parsetree.toplevel_phrase;;
   (** [phrase sil] return the OCaml equivalent AST of a toplevel phrase. *)
val mkloc : Ploc.t -> Location.t;;
   (** Convert a Camlp5 location into an OCaml location. *)
val fast : bool ref;;
   (** Flag to generate fast (unsafe) access to arrays. Default: False. *)
val ctyp_mentions : string -> MLast.ctyp -> bool;;
val ctyp : MLast.ctyp -> Parsetree.core_type;;
val expr : MLast.expr -> Parsetree.expression;;
val patt : MLast.patt -> Parsetree.pattern;;
val module_expr : MLast.module_expr -> Parsetree.module_expr;;
val module_type : MLast.module_type -> Parsetree.module_type;;
