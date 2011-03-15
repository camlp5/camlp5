(* camlp5r *)
(* $Id: pr_null.ml,v 6.2 2011/03/15 13:49:10 deraugla Exp $ *)
(* Copyright (c) INRIA 2007-2011 *)

Pcaml.print_interf.val := fun _ -> ();
Pcaml.print_implem.val := fun _ -> ();
