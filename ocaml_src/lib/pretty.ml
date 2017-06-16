(* camlp5r *)
(* pretty.ml,v *)
(* Copyright (c) INRIA 2007-2017 *)

(* #load "pa_macro.cmo" *)

open Versdep;;

exception GiveUp;;

let line_length = ref 78;;
let horiz_ctx = ref false;;

let utf8_string_length s =
  let rec loop i len =
    if i = String.length s then len
    else
      let c = Char.code s.[i] in
      if c < 0b10000000 || c >= 0b11000000 then loop (i + 1) (len + 1)
      else loop (i + 1) len
  in
  loop 0 0
;;

let after_print s =
  if !horiz_ctx then
    if string_contains s '\n' || utf8_string_length s > !line_length then
      raise GiveUp
    else s
  else s
;;

let sprintf fmt = Versdep.printf_ksprintf after_print fmt;;

let horiz_vertic horiz vertic =
  try Ploc.call_with horiz_ctx true horiz () with
    GiveUp -> if !horiz_ctx then raise GiveUp else vertic ()
;;

let horizontally () = !horiz_ctx;;
