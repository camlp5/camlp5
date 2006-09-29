(* camlp4r *)
(***********************************************************************)
(*                                                                     *)
(*                             Camlp4                                  *)
(*                                                                     *)
(*        Daniel de Rauglaudre, projet Cristal, INRIA Rocquencourt     *)
(*                                                                     *)
(*  Copyright 1998 Institut National de Recherche en Informatique et   *)
(*  Automatique.  Distributed only by permission.                      *)
(*                                                                     *)
(***********************************************************************)

(* $Id: pr_null.ml,v 1.1 2006/09/29 04:45:49 deraugla Exp $ *)

Pcaml.print_interf.val := fun _ -> ();
Pcaml.print_implem.val := fun _ -> ();
