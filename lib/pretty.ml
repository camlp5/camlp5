(* camlp5r *)
(* $Id: pretty.ml,v 6.1 2010/09/15 16:00:23 deraugla Exp $ *)
(* Copyright (c) INRIA 2007-2010 *)

#load "pa_macro.cmo";

open Versdep;

exception GiveUp;

value line_length = ref 78;
value horiz_ctx = ref False;

value after_print s =
  if horiz_ctx.val then
    if string_contains s '\n' || String.length s > line_length.val then
      raise GiveUp
    else s
  else s
;

value sprintf fmt = Versdep.printf_ksprintf after_print fmt;

value horiz_vertic horiz vertic =
  try Ploc.call_with horiz_ctx True horiz () with
  [ GiveUp -> if horiz_ctx.val then raise GiveUp else vertic () ]
;

value horizontally () = horiz_ctx.val;
