(* camlp5r *)
(* $Id: pr_null.ml,v 6.3 2012/01/09 14:22:21 deraugla Exp $ *)
(* Copyright (c) INRIA 2007-2012 *)

Pcaml.print_interf.val := fun _ -> ();
Pcaml.print_implem.val := fun _ -> ();
