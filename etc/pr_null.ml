(* camlp5r *)
(***********************************************************************)
(*                                                                     *)
(*                             Camlp5                                  *)
(*                                                                     *)
(*                Daniel de Rauglaudre, INRIA Rocquencourt             *)
(*                                                                     *)
(*  Copyright 2007 Institut National de Recherche en Informatique et   *)
(*  Automatique.  Distributed only by permission.                      *)
(*                                                                     *)
(***********************************************************************)

(* $Id: pr_null.ml,v 1.4 2007/07/11 12:01:39 deraugla Exp $ *)

Pcaml.print_interf.val := fun _ -> ();
Pcaml.print_implem.val := fun _ -> ();
