(* camlp5r *)
(* $Id: eprinter.mli,v 1.1 2007/08/16 11:14:04 deraugla Exp $ *)
(* Copyright (c) INRIA 2007 *)

type t 'a = 'abstract;

type gen_context 'bef 'aft =
  { ind : int; bef : 'bef; aft : 'aft; dang : string }
;
type pr_context = gen_context string string;

value make : string -> t 'a;

value apply : t 'a -> pr_context -> 'a -> string;
value apply_level : t 'a -> string -> pr_context -> 'a -> string;

value clear : t 'a -> unit;

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
