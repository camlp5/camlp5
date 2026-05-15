(* camlp5r *)
(* pr_base.ml,v *)
(* Copyright (c) INRIA 2007-2019 *)


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


module PrBase() : PRBASESIG = struct
value show_expr e = Format.asprintf "%a" Pp_debug.Pp_MLast.pp_expr e ;
value pr_attribute_body = Eprinter.make "pr_attribute_body";
value pr_expr = Eprinter.make ~{fail=show_expr} "expr";
value pr_patt = Eprinter.make "patt";
value pr_ctyp = Eprinter.make "type";
value pr_str_item = Eprinter.make "str_item";
value pr_sig_item = Eprinter.make "sig_item";
value pr_longident = Eprinter.make "longident";
value pr_module_expr = Eprinter.make "module_expr";
value pr_module_type = Eprinter.make "module_type";
value pr_class_sig_item = Eprinter.make "class_sig_item";
value pr_class_str_item = Eprinter.make "class_str_item";
value pr_class_expr = Eprinter.make "class_expr";
value pr_class_type = Eprinter.make "class_type";
value pr_expr_fun_args = ref Extfun.empty;
end
;
