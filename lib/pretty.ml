(* camlp5r *)
(* pretty.ml,v *)
(* Copyright (c) INRIA 2007-2017 *)

#load "pa_macro.cmo";

open Versdep;

exception GiveUp;

value line_length = ref 78;
value horiz_ctx = ref False;

value utf8_string_length s =
  loop 0 0 where rec loop i len =
    if i = String.length s then len
    else
      let c = Char.code s.[i] in
      if c < 0b1000_0000 || c >= 0b1100_0000 then loop (i + 1) (len + 1)
      else loop (i + 1) len
;

value after_print s =
  if horiz_ctx.val then
    if string_contains s '\n' || utf8_string_length s > line_length.val then
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
