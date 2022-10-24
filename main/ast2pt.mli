(* camlp5r *)
(* ast2pt.mli,v *)

value longid_long_id : MLast.longid -> Longident.t ;
value conv_con : string -> string ;

(** Conversion between Camlp5 AST into OCaml AST *)

value interf : string -> list MLast.sig_item -> Parsetree.signature;
   (** [interf fname ast] return the OCaml equivalent AST of an
       interface (mli file), [fname] being the input file name. *)
value implem : string -> list MLast.str_item -> Parsetree.structure;
   (** [implem fname ast] return the OCaml equivalent AST of an
       implementation (ml file), [fname] being the input file name. *)
value phrase : MLast.str_item -> Parsetree.toplevel_phrase;
   (** [phrase sil] return the OCaml equivalent AST of a toplevel phrase. *)
value mkloc : Ploc.t -> Location.t;
   (** Convert a Camlp5 location into an OCaml location. *)
value fast : ref bool;
   (** Flag to generate fast (unsafe) access to arrays. Default: False. *)
value ctyp_mentions : string -> MLast.ctyp -> bool ;
value ctyp : MLast.ctyp -> Parsetree.core_type ;
value expr : MLast.expr -> Parsetree.expression ;
value patt : MLast.patt -> Parsetree.pattern ;
value module_expr : MLast.module_expr -> Parsetree.module_expr ;
value module_type : MLast.module_type -> Parsetree.module_type ;
