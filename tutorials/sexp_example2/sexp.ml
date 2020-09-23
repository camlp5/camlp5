(* camlp5r *)
(* sexp.ml,v *)

open Ploc;

type sexp = [
    Atom of (vala string)
  | Cons of (vala sexp) and (vala sexp)
  | Nil
]
;
