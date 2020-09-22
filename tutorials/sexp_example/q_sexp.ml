(* camlp5r *)
(* pa_sexp.ml,v *)
(* Copyright (c) INRIA 2007-2017 *)

#load "pa_extend.cmo";
#load "q_MLast.cmo";
#load "pa_macro.cmo";
#load "pa_macro_gram.cmo";
#load "pa_extfun.cmo";

open Asttools;
open MLast;
open Q_MLast;

value sexp_eoi = Grammar.Entry.create gram "sexp_eoi";
value expr_atom a = Qast.Node "Sexp.Atom" [a] ;
value expr_nil =
  Qast.Node "Sexp.Nil" []
;
  
value expr_cons e1 e2 =
  Qast.Node "Sexp.Cons" [e1; e2]
;

EXTEND
  GLOBAL: sexp_eoi;

  sexp: [
    [
      a = atom -> expr_atom a
    | "(" ; l1 = LIST1 sexp ; opt_e2 = OPT [ "." ; e2 = sexp -> e2 ] ; ")" ->
      match opt_e2 with [
        None -> List.fold_right expr_cons l1 expr_nil
      | Some e2 -> List.fold_right expr_cons l1 e2
      ]
    | "(" ; ")" ->
        expr_nil
    ]
  | [ a = ANTIQUOT "exp" -> Qast.VaAnt "exp" loc a
    | a = ANTIQUOT "atom" -> Qast.Node "Sexp.Atom" [Qast.VaAnt "exp" loc a]
    ]
  ]
  ;

  sexp_eoi: [ [ x = sexp; EOI -> x ] ];

  atom: [
    [ i = LIDENT -> Qast.Str i | i = UIDENT -> Qast.Str i | i = INT -> Qast.Int i
    ]
  ]
  ;

END;

Quotation.add "sexp" (Q_MLast.apply_entry sexp_eoi "sexp") ;
  
