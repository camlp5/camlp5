(* camlp5r *)
(* $Id: pretty.ml,v 1.8 2010/08/27 20:18:49 deraugla Exp $ *)
(* Copyright (c) INRIA 2007-2010 *)

#load "pa_macro.cmo";

exception GiveUp;

value line_length = ref 78;
value horiz_ctx = ref False;

value after_print s =
  if horiz_ctx.val then
    if String.contains s '\n' || String.length s > line_length.val then
      raise GiveUp
    else s
  else s
;

IFNDEF OCAML_3_04 THEN
  value sprintf fmt = Printf.kprintf after_print fmt
ELSE
  declare
    value scan_format rev_sl fmt i doprn =
      match fmt.[i+1] with
      [ 'c' ->
          Obj.magic
            (fun (c : char)  -> doprn [String.make 1 c :: rev_sl] (i + 2))
      | 's' ->
          Obj.magic
            (fun (s : string)  -> doprn [s :: rev_sl] (i + 2))
      | c ->
          failwith
            (Printf.sprintf "Pretty.sprintf \"%s\" '%%%c' not impl" fmt c) ]
    ;
    value sprintf fmt =
      let fmt = (Obj.magic fmt : string) in
      let len = String.length fmt in
      doprn [] 0 where rec doprn rev_sl i =
        if i >= len then do {
          let s = String.concat "" (List.rev rev_sl) in
          Obj.magic (after_print s)
        }
        else do {
          match fmt.[i] with
          [ '%' -> scan_format rev_sl fmt i doprn
          | c -> doprn [String.make 1 c :: rev_sl] (i + 1)  ]
        }
    ;
  end
END;

value horiz_vertic horiz vertic =
  try Ploc.call_with horiz_ctx True horiz () with
  [ GiveUp -> if horiz_ctx.val then raise GiveUp else vertic () ]
;

value horizontally () = horiz_ctx.val;
