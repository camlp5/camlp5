(* camlp5r *)
(* $Id: pr_null.ml,v 1.6 2010/02/19 09:06:35 deraugla Exp $ *)
(* Copyright (c) INRIA 2007-2010 *)

Pcaml.print_interf.val := fun _ -> ();
Pcaml.print_implem.val := fun _ -> ();
