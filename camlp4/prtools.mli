(* camlp4r *)
(* $Id$ *)
(* Copyright (c) INRIA 2007 *)

open Pcaml.NewPrinter;

type pr_gfun 'a 'b = pr_ctx -> string -> 'a -> 'b -> string;

value shi : pr_ctx -> int -> pr_ctx;
value tab : pr_ctx -> string;

value hlist : pr_fun 'a -> pr_fun (list 'a);
value hlist2 :
  pr_gfun 'a 'b -> pr_gfun 'a 'b ->
    pr_ctx -> string -> list 'a -> 'b -> 'b -> string;
value hlistl : pr_fun 'a -> pr_fun 'a -> pr_fun (list 'a);

value vlist : pr_fun 'a -> pr_fun (list 'a);
value vlist2 :
  pr_gfun 'a 'b -> pr_gfun 'a 'b ->
    pr_ctx -> string -> list 'a -> 'b -> 'b -> string;
value vlistl : pr_fun 'a -> pr_fun 'a -> pr_fun (list 'a);

value plist : pr_fun 'a -> int -> pr_fun (list ('a * string));
value plistl : pr_fun 'a -> pr_fun 'a -> int -> pr_fun (list ('a * string));
