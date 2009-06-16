(* camlp5r *)
(* $Id: pr_null.ml,v 1.5 2007/12/29 03:40:22 deraugla Exp $ *)
(* Copyright (c) INRIA 2007-2008 *)

Pcaml.print_interf.val := fun _ -> ();
Pcaml.print_implem.val := fun _ -> ();
