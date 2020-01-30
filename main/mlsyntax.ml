(* camlp5r *)
(* mlsyntax.ml *)
(* Copyright (c) INRIA 2007-2017 *)

value symbolchar =
  let list =
    ['!'; '$'; '%'; '&'; '*'; '+'; '-'; '.'; '/'; ':'; '<'; '='; '>'; '?';
     '@'; '^'; '|'; '~']
  in
  loop where rec loop s i =
    if i == String.length s then True
    else if List.mem s.[i] list then loop s (i + 1)
    else False
;

value is_prefixop =
  let list = ['!'; '?'; '~'] in
  let excl = ["!="; "??"; "?!"] in
  fun ?{doexcl=True} x ->
    not (doexcl && List.mem x excl) && String.length x >= 2 &&
    List.mem x.[0] list && symbolchar x 1
;

value is_infixop0 =
  let list = ['='; '<'; '>'; '|'; '&'; '$'] in
  let excl = ["<-"; "||"; "&&"] in
  fun x ->
    not (List.mem x excl) && (x = "$" || String.length x >= 2) &&
    List.mem x.[0] list && symbolchar x 1
;

value is_infixop1 =
  let list = ['@'; '^'] in
  fun x ->
    String.length x >= 2 && List.mem x.[0] list &&
    symbolchar x 1
;

value is_infixop2 =
  let list = ['+'; '-'] in
  fun x ->
    x <> "->" && String.length x >= 2 && List.mem x.[0] list &&
    symbolchar x 1
;

value is_infixop3 =
  let list = ['*'; '/'; '%'] in
  fun x ->
    String.length x >= 2 && List.mem x.[0] list &&
    symbolchar x 1
;

value is_infixop4 x =
  String.length x >= 3 && x.[0] == '*' && x.[1] == '*' &&
  symbolchar x 2
;
