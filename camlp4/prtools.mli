(* camlp4r *)
(* $Id$ *)
(* Copyright (c) INRIA 2007 *)

open Pcaml.NewPrinter;

value shi : pr_ctx -> int -> pr_ctx;
value tab : pr_ctx -> string;

value hlist :
  ('a -> string -> 'b -> string -> string) -> 'a -> string -> list 'b ->
    string -> string;
value hlist2 :
  ('a -> string -> 'b -> 'c -> string) ->
    ('a -> string -> 'b -> 'c -> string) -> 'a -> string -> list 'b -> 'c ->
    'c -> string;
value hlistl :
  ('a -> string -> 'b -> string -> string) ->
    ('a -> string -> 'b -> string -> string) -> 'a -> string -> list 'b ->
    string -> string;

value vlist :
  (pr_ctx -> string -> 'a -> string -> string) -> pr_ctx -> string ->
    list 'a -> string -> string;
value vlist2 :
  (pr_ctx -> string -> 'a -> 'b -> string) ->
    (pr_ctx -> string -> 'a -> 'b -> string) -> pr_ctx -> string -> list 'a ->
    'b -> 'b -> string;
value vlistl :
  (pr_ctx -> string -> 'a -> string -> string) ->
    (pr_ctx -> string -> 'a -> string -> string) -> pr_ctx -> string ->
    list 'a -> string -> string;

value plistl :
  (pr_ctx -> string -> 'a -> 'b -> string) ->
    (pr_ctx -> string -> 'a -> 'c -> string) -> pr_ctx -> int -> string ->
    list ('a * 'b) -> 'c -> string;

value plist :
  (pr_ctx -> string -> 'a -> 'b -> string) -> pr_ctx -> int -> string ->
    list ('a * 'b) -> 'b -> string;
