(* camlp5r *)
(* camlp5r *)
(* pp_MLast.mli,v *)

value ref_show_longid : ref (MLast.longid → string);
value ref_show_longid_lident : ref (MLast.longid_lident → string);
value ref_show_expr : ref (MLast.expr → string);
value ref_show_ctyp : ref (MLast.ctyp → string);
value ref_show_patt : ref (MLast.patt → string);

declare end;

value show_longid : MLast.longid → string;
value show_longid_lident : MLast.longid_lident → string;
value show_expr : MLast.expr → string;
value show_ctyp : MLast.ctyp → string;
value show_patt : MLast.patt → string;

