(* camlp5r *)
(* $Id: eprinter.mli,v 1.3 2007/08/16 18:40:41 deraugla Exp $ *)
(* Copyright (c) INRIA 2007 *)

type t 'a = 'abstract;
type pr_context = { ind : int; bef : string; aft : string; dang : string };

value make : string -> t 'a;

value apply : t 'a -> pr_context -> 'a -> string;
value apply_level : t 'a -> string -> pr_context -> 'a -> string;

value clear : t 'a -> unit;

value empty_pc : pr_context;

(**/**)

(* for system use *)

type position =
  [ First
  | Last
  | Before of string
  | After of string
  | Level of string ]
;

type pr_fun 'a = pr_context -> 'a -> string;

type pr_rule 'a =
  Extfun.t 'a (pr_fun 'a -> pr_fun 'a -> pr_context -> string)
;

value extend :
  t 'a -> option position ->
    list (option string * pr_rule 'a -> pr_rule 'a) -> unit;
