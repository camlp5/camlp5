(* camlp5r *)
(* asttools.mli,v *)

value symbolchar_or : (char → bool) → int → ?lim:int → string → bool;
value symbolchar : int → ?lim:int → string → bool;
value dotsymbolchar : int → ?lim:int → string → bool;
value kwdopchar : string → int → bool;
module Original :
  sig
    value is_prefixop : string → bool;
    value is_infixop0_0 : string → bool;
    value is_infixop0_1 : string → bool;
    value is_infixop0_2 : string → bool;
    value is_infixop0 : string → bool;
    value is_infixop1 : string → bool;
    value is_infixop2 : string → bool;
    value is_infixop3 : string → bool;
    value is_infixop4 : string → bool;
    value is_hashop : string → bool;
    value is_operator0 : string → bool;
    value is_andop : string → bool;
    value is_letop : string → bool;
    value is_operator : string → bool;
    value is_infix_operator : string → bool;
    value is_dotop : string → bool;
    value is_special_op : string → bool;
  end
;
module Revised :
  sig
    value is_prefixop : string → bool;
    value is_infixop0_0 : string → bool;
    value is_infixop0_1 : string → bool;
    value is_infixop1 : string → bool;
    value is_infixop2 : string → bool;
    value is_infixop3 : string → bool;
    value is_infixop4 : string → bool;
    value is_hashop : string → bool;
    value is_andop : string → bool;
    value is_letop : string → bool;
    value is_infixop0_2 : string → bool;
    value is_infixop0 : string → bool;
    value is_operator0 : string → bool;
    value is_operator : string → bool;
    value is_infix_operator : string → bool;
    value is_dotop : string → bool;
    value is_special_op : string → bool;

    value greek_ascii_equiv : string → string;
  (* Gives an ascii equivalent to a greek letter representing a type
     parameter. E.g. 'a' for 'α', 'b' for 'β', and so on. *)
  end
;

module type PARSERS = sig

type status = option Ploc.t;

value gram : Grammar.g;
   (** Grammar variable of the OCaml language *)

value attribute_body : Grammar.Entry.e MLast.attribute_body;
value interf : Grammar.Entry.e (list (MLast.sig_item * MLast.loc) * status);
value implem : Grammar.Entry.e (list (MLast.str_item * MLast.loc) * status);
value top_phrase : Grammar.Entry.e (option MLast.str_item);
value use_file : Grammar.Entry.e (list MLast.str_item * bool);
value functor_parameter : Grammar.Entry.e MLast.functor_parameter;
value module_type : Grammar.Entry.e MLast.module_type;
value longident : Grammar.Entry.e MLast.longid;
value longident_lident : Grammar.Entry.e MLast.longid_lident;
value extended_longident : Grammar.Entry.e MLast.longid;
value module_expr : Grammar.Entry.e MLast.module_expr;
value signature : Grammar.Entry.e (MLast.v (list MLast.sig_item));
value structure : Grammar.Entry.e (MLast.v (list MLast.str_item));
value sig_item : Grammar.Entry.e MLast.sig_item;
value str_item : Grammar.Entry.e MLast.str_item;
value expr : Grammar.Entry.e MLast.expr;
value patt : Grammar.Entry.e MLast.patt;
value ipatt : Grammar.Entry.e MLast.patt;
value ctyp : Grammar.Entry.e MLast.ctyp;
value let_binding : Grammar.Entry.e (MLast.patt * MLast.expr * MLast.attributes);
value type_decl : Grammar.Entry.e MLast.type_decl;
value type_extension : Grammar.Entry.e MLast.type_extension;
value extension_constructor : Grammar.Entry.e MLast.extension_constructor;
value match_case :
  Grammar.Entry.e (MLast.patt * MLast.v (option MLast.expr) * MLast.expr);
value constructor_declaration : Grammar.Entry.e MLast.generic_constructor;
value label_declaration :
  Grammar.Entry.e (MLast.loc * string * bool * MLast.ctyp * MLast.attributes);
value with_constr : Grammar.Entry.e MLast.with_constr;
value poly_variant : Grammar.Entry.e MLast.poly_variant;
value class_sig_item : Grammar.Entry.e MLast.class_sig_item;
value class_str_item : Grammar.Entry.e MLast.class_str_item;
value class_expr : Grammar.Entry.e MLast.class_expr;
value class_expr_simple : Grammar.Entry.e MLast.class_expr;
value class_type : Grammar.Entry.e MLast.class_type;
value alg_attribute : Grammar.Entry.e MLast.attribute;
value alg_attributes : Grammar.Entry.e MLast.attributes;
value ext_attributes : Grammar.Entry.e (option (Ploc.t * string) * MLast.attributes_no_anti);
   (** Some entries of the language, set by [pa_o.cmo] and [pa_r.cmo]. *)

open Exparser_types ;

value stream_expr : Grammar.Entry.e (MLast.loc * list sexp_comp);
value stream_parser : Grammar.Entry.e (MLast.loc * spat_parser_ast) ;
value stream_match : Grammar.Entry.e (MLast.loc * MLast.expr * spat_parser_ast) ;
end ;

module Lexer : Plexer.LEXER ;

type directive_fun = option MLast.expr -> unit;

module type PARSEBASESIG = sig
module Parsers : PARSERS ;
value input_file : ref string;
   (** The file currently being parsed. *)

value options : ref (list (string * Arg.spec * string)) ;
value add_option : string -> Arg.spec -> string -> unit ;
value get_options : unit -> list (string * Arg.spec * string) ;

value directives : ref (list (string * directive_fun)) ;
value add_directive : string -> directive_fun -> unit ;
value get_directives : unit -> list (string * directive_fun) ;
end
;

module ParseBase : functor () -> PARSEBASESIG ;

module type PRINTERS = sig
value pr_attribute_body : Eprinter.t MLast.attribute_body;
value pr_expr : Eprinter.t MLast.expr;
value pr_patt : Eprinter.t MLast.patt;
value pr_ctyp : Eprinter.t MLast.ctyp;
value pr_str_item : Eprinter.t MLast.str_item;
value pr_sig_item : Eprinter.t MLast.sig_item;
value pr_longident : Eprinter.t MLast.longid;
value pr_module_expr : Eprinter.t MLast.module_expr;
value pr_module_type : Eprinter.t MLast.module_type;
value pr_class_sig_item : Eprinter.t MLast.class_sig_item;
value pr_class_str_item : Eprinter.t MLast.class_str_item;
value pr_class_type : Eprinter.t MLast.class_type;
value pr_class_expr : Eprinter.t MLast.class_expr;
   (** Some printers, set by [pr_dump.cmo], [pr_o.cmo] and [pr_r.cmo]. *)

value pr_expr_fun_args :
  ref (Extfun.t MLast.expr (list MLast.patt * MLast.expr));
end ;

module type PRINTBASESIG = sig
module Printers : PRINTERS ;
value options : ref (list (string * Arg.spec * string)) ;
value add_option : string -> Arg.spec -> string -> unit ;
value get_options : unit -> list (string * Arg.spec * string) ;
end
;

module PrintBase : functor () -> PRINTBASESIG ;
