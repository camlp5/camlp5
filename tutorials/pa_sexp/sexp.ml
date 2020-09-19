(* camlp5r *)
(* sexp.ml,v *)

type sexp = [
    Atom of string
  | Cons of sexp and sexp
  | Nil
]
;
