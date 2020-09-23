(* camlp5r *)
(* pa_sexp.ml,v *)
(* Copyright (c) INRIA 2007-2017 *)

open Asttools;
open MLast;
open Pcaml;

open Pa_sexp;
open Q_ast ;

value meta_e_sexp se =
  let open Meta_E in
  let prefix =
    let loc = Ploc.dummy in
    <:expr< Sexp >> in
  let node_no_loc = C.node_no_loc ~{prefix=prefix} in
  let rec sexp = fun [
    Sexp.Nil -> node_no_loc "Nil" []
  | Sexp.Cons a b -> node_no_loc "Cons" [C.vala sexp a ; C.vala sexp b]
  | Sexp.Atom a -> node_no_loc "Atom" [C.vala C.string a]
  ] in
  sexp se
;

value meta_p_sexp se =
  let open Meta_P in
  let prefix =
    let loc = Ploc.dummy in
    <:longident< Sexp >> in
  let node_no_loc = C.node_no_loc ~{prefix=prefix} in
  let rec sexp = fun [
    Sexp.Nil -> node_no_loc "Nil" []
  | Sexp.Cons a b -> node_no_loc "Cons" [C.vala sexp a ; C.vala sexp b]
  | Sexp.Atom a -> node_no_loc "Atom" [C.vala C.string a]
  ] in
  sexp se
;

Quotation.add "sexp"
  (apply_entry sexp_eoi meta_e_sexp meta_p_sexp)
;
