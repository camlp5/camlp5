(* camlp4r *)
(***********************************************************************)
(*                                                                     *)
(*                             Camlp4                                  *)
(*                                                                     *)
(*                Daniel de Rauglaudre, INRIA Rocquencourt             *)
(*                                                                     *)
(*  Copyright 2007 Institut National de Recherche en Informatique et   *)
(*  Automatique.  Distributed only by permission.                      *)
(*                                                                     *)
(***********************************************************************)

(* $Id: pr_null.ml,v 1.3 2006/12/26 08:54:09 deraugla Exp $ *)

Pcaml.print_interf.val := fun _ -> ();
Pcaml.print_implem.val := fun _ -> ();
