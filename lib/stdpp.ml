(* camlp5r *)
(* stdpp.ml,v *)
(* Copyright (c) INRIA 2007-2017 *)

type location = Ploc.t;

value raise_with_loc = Ploc.raise;

value make_lined_loc lin bol (bp, ep) = Ploc.make_loc "" lin bol (bp, ep) "";
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
