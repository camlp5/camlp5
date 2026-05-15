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
  end
;

module type PRBASESIG = sig
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
end
;
module PrBase : functor () -> PRBASESIG ;
