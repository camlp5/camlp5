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
      a = atom -> sexp_atom a
    | "(" ; l1 = LIST1 sexp ; opt_e2 = OPT [ "." ; e2 = sexp -> e2 ] ; ")" ->
      match opt_e2 with [
        None -> List.fold_right sexp_cons l1 sexp_nil
      | Some e2 -> List.fold_right sexp_cons l1 e2
      ]
    | "(" ; ")" ->
        sexp_nil
    ]
  | [ s = ANTIQUOT_LOC "" -> Sexp.SeXtr loc s
    | s = ANTIQUOT_LOC "anti" -> Sexp.SeXtr loc s
    | s = ANTIQUOT_LOC "exp" -> Sexp.SeXtr loc s
    | s = ANTIQUOT_LOC "atom" -> do {
      Sexp.SeXtr loc s
    }
    ]
  ]
  ;

  sexp_eoi: [ [ x = sexp; EOI -> x ] ];

  atom: [[ i = LIDENT -> i | i = UIDENT -> i | i = INT -> i ]] ;
END;
