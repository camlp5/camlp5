(* camlp5r *)
(* $Id: stdpp.ml,v 6.2 2010/09/29 04:26:54 deraugla Exp $ *)
(* Copyright (c) INRIA 2007-2010 *)

type location = Ploc.t;

exception Exc_located of location and exn;
value raise_with_loc = Ploc.raise;

value make_lined_loc lin bol (bp, ep) = Ploc.make_loc lin bol (bp, ep) "";
value make_loc = Ploc.make_unlined;
value dummy_loc = Ploc.dummy;

value first_pos = Ploc.first_pos;
value last_pos = Ploc.last_pos;
value line_nb = Ploc.line_nb;
value bol_pos = Ploc.bol_pos;

value encl_loc = Ploc.encl;
value shift_loc = Ploc.shift;
value sub_loc = Ploc.sub;
value after_loc = Ploc.after;

value line_of_loc = Ploc.from_file;
value loc_name = Ploc.name;
