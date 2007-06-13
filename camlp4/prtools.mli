(* camlp4r *)
(* $Id$ *)
(* Copyright (c) INRIA 2007 *)

open Pcaml.NewPrinter;

value shi : pr_ctx -> int -> pr_ctx;
value tab : pr_ctx -> string;

value hlist : pr_fun 'a -> pr_fun (list 'a);
value hlist2 :
  ('a -> string -> 'b -> 'c -> string) ->
    ('a -> string -> 'b -> 'c -> string) -> 'a -> string -> list 'b -> 'c ->
    'c -> string;
value hlistl : pr_fun 'a -> pr_fun 'a -> pr_fun (list 'a);

value vlist : pr_fun 'a -> pr_fun (list 'a);
value vlist2 :
  (pr_ctx -> string -> 'a -> 'b -> string) ->
    (pr_ctx -> string -> 'a -> 'b -> string) -> pr_ctx -> string -> list 'a ->
    'b -> 'b -> string;
value vlistl : pr_fun 'a -> pr_fun 'a -> pr_fun (list 'a);

value plist :
  pr_fun 'a -> pr_ctx -> int -> string -> list ('a * string) -> string ->
    string;

value plistl :
  pr_fun 'a -> pr_fun 'a -> pr_ctx -> int -> string -> list ('a * string) ->
    string -> string;
