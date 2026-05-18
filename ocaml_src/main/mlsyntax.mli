(* camlp5r *)
(* asttools.mli,v *)

val symbolchar_or : (char -> bool) -> int -> ?lim:int -> string -> bool;;
val symbolchar : int -> ?lim:int -> string -> bool;;
val dotsymbolchar : int -> ?lim:int -> string -> bool;;
val kwdopchar : string -> int -> bool;;
module Original :
  sig
    val is_prefixop : string -> bool;;
    val is_infixop0_0 : string -> bool;;
    val is_infixop0_1 : string -> bool;;
    val is_infixop0_2 : string -> bool;;
    val is_infixop0 : string -> bool;;
    val is_infixop1 : string -> bool;;
    val is_infixop2 : string -> bool;;
    val is_infixop3 : string -> bool;;
    val is_infixop4 : string -> bool;;
    val is_hashop : string -> bool;;
    val is_operator0 : string -> bool;;
    val is_andop : string -> bool;;
    val is_letop : string -> bool;;
    val is_operator : string -> bool;;
    val is_infix_operator : string -> bool;;
    val is_dotop : string -> bool;;
    val is_special_op : string -> bool;;
  end
;;
module Revised :
  sig
    val is_prefixop : string -> bool;;
    val is_infixop0_0 : string -> bool;;
    val is_infixop0_1 : string -> bool;;
    val is_infixop1 : string -> bool;;
    val is_infixop2 : string -> bool;;
    val is_infixop3 : string -> bool;;
    val is_infixop4 : string -> bool;;
    val is_hashop : string -> bool;;
    val is_andop : string -> bool;;
    val is_letop : string -> bool;;
    val is_infixop0_2 : string -> bool;;
    val is_infixop0 : string -> bool;;
    val is_operator0 : string -> bool;;
    val is_operator : string -> bool;;
    val is_infix_operator : string -> bool;;
    val is_dotop : string -> bool;;
    val is_special_op : string -> bool;;
    val greek_ascii_equiv : string -> string;;
  end
;;

type status = Ploc.t option;;

module type PARSERS =
  sig
    val gram : Grammar.g;;
    val attribute_body : MLast.attribute_body Grammar.Entry.e;;
    val interf :
      ((MLast.sig_item * MLast.loc) list * status) Grammar.Entry.e;;
    val implem :
      ((MLast.str_item * MLast.loc) list * status) Grammar.Entry.e;;
    val top_phrase : MLast.str_item option Grammar.Entry.e;;
    val use_file : (MLast.str_item list * bool) Grammar.Entry.e;;
    val functor_parameter : MLast.functor_parameter Grammar.Entry.e;;
    val module_type : MLast.module_type Grammar.Entry.e;;
    val longident : MLast.longid Grammar.Entry.e;;
    val longident_lident : MLast.longid_lident Grammar.Entry.e;;
    val extended_longident : MLast.longid Grammar.Entry.e;;
    val module_expr : MLast.module_expr Grammar.Entry.e;;
    val signature : MLast.sig_item list MLast.v Grammar.Entry.e;;
    val structure : MLast.str_item list MLast.v Grammar.Entry.e;;
    val sig_item : MLast.sig_item Grammar.Entry.e;;
    val str_item : MLast.str_item Grammar.Entry.e;;
    val expr : MLast.expr Grammar.Entry.e;;
    val patt : MLast.patt Grammar.Entry.e;;
    val ipatt : MLast.patt Grammar.Entry.e;;
    val ctyp : MLast.ctyp Grammar.Entry.e;;
    val let_binding :
      (MLast.patt * MLast.expr * MLast.attributes) Grammar.Entry.e;;
    val type_decl : MLast.type_decl Grammar.Entry.e;;
    val type_extension : MLast.type_extension Grammar.Entry.e;;
    val extension_constructor : MLast.extension_constructor Grammar.Entry.e;;
    val match_case :
      (MLast.patt * MLast.expr option MLast.v * MLast.expr) Grammar.Entry.e;;
    val constructor_declaration : MLast.generic_constructor Grammar.Entry.e;;
    val label_declaration :
      (MLast.loc * string * bool * MLast.ctyp * MLast.attributes)
        Grammar.Entry.e;;
    val with_constr : MLast.with_constr Grammar.Entry.e;;
    val poly_variant : MLast.poly_variant Grammar.Entry.e;;
    val class_sig_item : MLast.class_sig_item Grammar.Entry.e;;
    val class_str_item : MLast.class_str_item Grammar.Entry.e;;
    val class_expr : MLast.class_expr Grammar.Entry.e;;
    val class_expr_simple : MLast.class_expr Grammar.Entry.e;;
    val class_type : MLast.class_type Grammar.Entry.e;;
    val alg_attribute : MLast.attribute Grammar.Entry.e;;
    val alg_attributes : MLast.attributes Grammar.Entry.e;;
    val ext_attributes :
      ((Ploc.t * string) option * MLast.attributes_no_anti) Grammar.Entry.e;;
    open Exparser_types;;
    val stream_expr : (MLast.loc * sexp_comp list) Grammar.Entry.e;;
    val stream_parser : (MLast.loc * spat_parser_ast) Grammar.Entry.e;;
    val stream_match :
      (MLast.loc * MLast.expr * spat_parser_ast) Grammar.Entry.e;;
  end
;;

type directive_fun = MLast.expr option -> unit;;

module type PARSEBASESIG =
  sig
    module Lexer : Plexer.LEXER;;
    module Parsers : PARSERS;;
    val input_file : string ref;;
    val options : (string * Arg.spec * string) list ref;;
    val add_option : string -> Arg.spec -> string -> unit;;
    val get_options : unit -> (string * Arg.spec * string) list;;
    val directives : (string * directive_fun) list ref;;
    val add_directive : string -> directive_fun -> unit;;
    val get_directives : unit -> (string * directive_fun) list;;
  end
;;

module ParseBase (Lexer : Plexer.LEXER) :
  (PARSEBASESIG with module Lexer = Lexer)
;;

module type PRINTERS =
  sig
    val pr_attribute_body : MLast.attribute_body Eprinter.t;;
    val pr_expr : MLast.expr Eprinter.t;;
    val pr_patt : MLast.patt Eprinter.t;;
    val pr_ctyp : MLast.ctyp Eprinter.t;;
    val pr_str_item : MLast.str_item Eprinter.t;;
    val pr_sig_item : MLast.sig_item Eprinter.t;;
    val pr_longident : MLast.longid Eprinter.t;;
    val pr_module_expr : MLast.module_expr Eprinter.t;;
    val pr_module_type : MLast.module_type Eprinter.t;;
    val pr_class_sig_item : MLast.class_sig_item Eprinter.t;;
    val pr_class_str_item : MLast.class_str_item Eprinter.t;;
    val pr_class_type : MLast.class_type Eprinter.t;;
    val pr_class_expr : MLast.class_expr Eprinter.t;;
    val pr_expr_fun_args :
      (MLast.expr, MLast.patt list * MLast.expr) Extfun.t ref;;
  end
;;

module type PRINTBASESIG =
  sig
    module Printers : PRINTERS;;
    val options : (string * Arg.spec * string) list ref;;
    val add_option : string -> Arg.spec -> string -> unit;;
    val get_options : unit -> (string * Arg.spec * string) list;;
  end
;;

module PrintBase () : PRINTBASESIG;;
