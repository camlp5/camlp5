(* camlp5r *)
(* ast2pt.mli,v *)

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
