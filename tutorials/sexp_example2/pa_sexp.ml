(* camlp5r *)
(* pa_sexp.ml,v *)
(* Copyright (c) INRIA 2007-2017 *)

open Asttools;
open MLast;
open Pcaml;

value sexp_eoi = Grammar.Entry.create gram "sexp_eoi";

value sexp_atom a = Sexp.Atom a ;
value sexp_nil = Sexp.Nil ;
value sexp_cons e1 e2 = Sexp.Cons e1 e2 ;

EXTEND
  GLOBAL: sexp_eoi;

  sexp: [
    [
      a = V atom "atom" -> sexp_atom a
    | "(" ; l1 = LIST1 v_sexp ; opt_e2 = OPT [ "." ; e2 = v_sexp -> e2 ] ; ")" ->
      match opt_e2 with [
        None -> List.fold_right (fun vse1 se2 -> Sexp.Cons vse1 <:vala< se2 >>) l1 sexp_nil
      | Some ve2 ->
         let (last, l1) = sep_last l1 in
         List.fold_right (fun vse1 se2 -> Sexp.Cons vse1 <:vala< se2 >>) l1
           (Sexp.Cons last ve2)
      ]
    | "(" ; ")" ->
        sexp_nil
    ]
  ]
  ;

  v_sexp: [[ v = V sexp "exp" -> v ]];

  sexp_eoi: [ [ x = sexp; EOI -> x ] ];

  atom: [[ i = LIDENT -> i | i = UIDENT -> i | i = INT -> i ]] ;
END;
