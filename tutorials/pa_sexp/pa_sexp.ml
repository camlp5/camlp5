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
open Pcaml;

value sexp_eoi = Grammar.Entry.create gram "sexp_eoi";

value expr_nil =
  let loc = Ploc.dummy in
  <:expr< Sexp.Nil >>
;
  
value expr_cons e1 e2 =
  let loc = Ploc.dummy in
  <:expr< Sexp.Cons $e1$ $e2$ >>
;

EXTEND
  GLOBAL: sexp_eoi expr;

  expr: LEVEL "simple" [[
    "SEXP" ; se = sexp -> se
  ]]
  ;

  sexp: [
    [
      a = atom -> <:expr< Sexp.Atom $str:a$ >>
    | "(" ; l1 = LIST1 sexp ; opt_e2 = OPT [ "." ; e2 = sexp -> e2 ] ; ")" ->
      match opt_e2 with [
        None -> List.fold_right expr_cons l1 expr_nil
      | Some e2 -> List.fold_right expr_cons l1 e2
      ]
    | "(" ; ")" ->
        expr_nil
    ]
(*
  | [ s = ANTIQUOT_LOC "" -> MLast.ExXtr loc s None
    | s = ANTIQUOT_LOC "anti" -> MLast.ExXtr loc s None
    | s = ANTIQUOT_LOC "exp" -> MLast.ExXtr loc s None
    ]
*)
  ]
  ;

  sexp_eoi: [ [ x = sexp; EOI -> x ] ];

  atom: [[ i = LIDENT -> i | i = UIDENT -> i | i = INT -> i ]] ;
END;
