(* camlp5r *)
(* mlsyntax.ml *)
(* Copyright (c) INRIA 2007-2017 *)

value symbolchar_or f st ?{lim} s =
  let list =
    ['!'; '$'; '%'; '&'; '*'; '+'; '-'; '.'; '/'; ':'; '<'; '='; '>'; '?';
     '@'; '^'; '|'; '~']
  in
  let lim = match lim with [ None -> String.length s | Some j -> j ] in
  loop st where rec loop i =
    if i == lim then True
    else if List.mem s.[i] list || f s.[i] then loop (i + 1)
    else False
;

value symbolchar = symbolchar_or (fun x -> False) ;

value dotsymbolchar st ?{lim} s = 
  let list = [ '!'; '$'; '%'; '&'; '*'; '+'; '-'; '/'; ':'; '='; '>'; '?';
               '@'; '^'; '|' ]
  in
  let lim = match lim with [ None -> String.length s | Some j -> j ] in
  loop st where rec loop i =
    if i == lim then True
    else if List.mem s.[i] list then loop (i + 1)
    else False
;

value kwdopchar =
  let list = [ '$'; '&'; '*'; '+'; '-'; '/'; '<'; '='; '>';
               '@'; '^'; '|' ]
  in
  fun s i -> 
    if i == String.length s then True
    else List.mem s.[i] list
;

module Original = struct
  
value is_prefixop =
  let list = ['!'; '?'; '~'] in
  let excl = ["!="; "??"; "?!"] in
  fun x ->
    not (List.mem x excl) && String.length x >= 2 &&
    List.mem x.[0] list && symbolchar_or (fun x -> '#' = x)  1 x
;

value is_infixop0_0 =
  let list = ['|'] in
  let excl = ["||"] in
  fun x ->
    not (List.mem x excl) && String.length x >= 2 &&
    List.mem x.[0] list && symbolchar 1 x
;

value is_infixop0_1 =
  let list = ['&'] in
  let excl = ["&&"] in
  fun x ->
    not (List.mem x excl) && String.length x >= 2 &&
    List.mem x.[0] list && symbolchar 1 x
;

value is_infixop0_2 =
  let list = ['='; '<'; '>'; '$'] in
  let excl = ["<-"] in
  fun x ->
    not (List.mem x excl) && (x = "$" || String.length x >= 2) &&
    List.mem x.[0] list && symbolchar 1 x
;

value is_infixop0 s =
   is_infixop0_0 s
|| is_infixop0_1 s
|| is_infixop0_2 s
;

value is_infixop1 =
  let list = ['@'; '^'] in
  fun x ->
    String.length x >= 2 && List.mem x.[0] list &&
    symbolchar 1 x
;

value is_infixop2 =
  let list = ['+'; '-'] in
  fun x ->
    x <> "->" && String.length x >= 2 && List.mem x.[0] list &&
    symbolchar 1 x
;

value is_infixop3 =
  let list = ['*'; '/'; '%'] in
  let excl = ["**"] in
  fun x ->
    not (List.mem x excl) && String.length x >= 2 && List.mem x.[0] list &&
    symbolchar 1 x
;

value is_infixop4 x =
  String.length x >= 3 && x.[0] == '*' && x.[1] == '*' &&
  symbolchar 2 x
;

value is_hashop =
  let list = ['#'] in
  let excl = ["#"] in
  fun x ->
    not (List.mem x excl) && String.length x >= 2 &&
    List.mem x.[0] list && symbolchar_or (fun x -> '#' = x)  1 x
;

value is_operator0 = do {
  let ht = Hashtbl.create 73 in
  let ct = Hashtbl.create 73 in
  List.iter (fun x -> Hashtbl.add ht x True)
    ["asr"; "land"; "lor"; "lsl"; "lsr"; "lxor"; "mod"; "or"];
  List.iter (fun x -> Hashtbl.add ct x True)
    ['!'; '&'; '*'; '+'; '-'; '/'; ':'; '<'; '='; '>'; '@'; '^'; '|'; '~';
     '?'; '%'; '.'; '$'];
  fun x ->
    try Hashtbl.find ht x with
    [ Not_found -> try Hashtbl.find ct x.[0] with _ -> False ]
};

value is_andop s =
  String.length s > 3 &&
  String.sub s 0 3 = "and" &&
  kwdopchar s 3 &&
  dotsymbolchar 4 s
;

value is_letop s =
  String.length s > 3 &&
  String.sub s 0 3 = "let" &&
  kwdopchar s 3 &&
  dotsymbolchar 4 s
;

value is_operator s =
  is_operator0 s || is_hashop s
;

value is_infix_operator op =
  is_operator op && (match op.[0] with [ '!'| '?'| '~' -> False | _ -> True ])
;

value is_dotop s =
  String.length s >= 2 &&
  String.get s 0 = '.' &&
  dotsymbolchar 1 ~{lim=2} s &&
  symbolchar 2 s
;

value is_special_op s = is_operator s || is_letop s || is_andop s || is_dotop s ;

end ;

module Revised = struct
include Original ;

value is_infixop0_2 =
  let list = ['='; '<'; '>'; '$'] in
  let excl = ["<-"] in
  fun x ->
    not (List.mem x excl) && String.length x >= 2 &&
    List.mem x.[0] list && symbolchar 1 x
;

value is_infixop0 s =
   is_infixop0_0 s
|| is_infixop0_1 s
|| is_infixop0_2 s
;

value is_operator0 s = s <> "$" && is_operator s ;

value is_operator s =
  is_operator0 s || is_hashop s
;

value is_infix_operator op =
  is_operator op && (match op.[0] with [ '!'| '?'| '~' -> False | _ -> True ])
;

value is_dotop s =
  String.length s >= 2 &&
  String.get s 0 = '.' &&
  dotsymbolchar 1 ~{lim=2} s &&
  symbolchar 2 s
;

value is_special_op s = is_operator s || is_letop s || is_andop s || is_dotop s ;

end ;
