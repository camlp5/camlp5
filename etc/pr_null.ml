(* camlp5r *)
(* $Id: pr_null.ml,v 6.1 2010/09/15 16:00:22 deraugla Exp $ *)
(* Copyright (c) INRIA 2007-2010 *)

Pcaml.print_interf.val := fun _ -> ();
Pcaml.print_implem.val := fun _ -> ();
