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

value greek_lidents_list =
  [ ("α", "alpha")
  ; ("β", "beta")
  ; ("γ", "gamma")
  ; ("δ", "delta")
  ; ("ε", "epsilon")
  ; ("ζ", "zeta")
  ; ("η", "eta")
  ; ("θ", "theta")
  ; ("ι", "iota")
  ; ("κ", "kappa")
  ; ("λ", "lambda")
  ; ("μ", "mu")
  ; ("ν", "nu")
  ; ("ξ", "xi")
  ; ("ο", "omicron")
  ; ("π", "pi")
  ; ("ρ", "rho")
  ; ("σ", "sigma")
  ; ("τ", "tau")
  ; ("υ", "upsilon")
  ; ("φ", "phi")
  ; ("χ", "chi")
  ; ("ψ", "psi")
  ; ("ω", "omega")
  ]
;

value prefix = "__greek_" ;
value prefixlen = String.length prefix ;
value hexify_greek_lident s =
  let b = Buffer.create (prefixlen + (String.length s) * 2) in do {
    Buffer.add_string b prefix ;
    s |> String.iter (fun c -> Buffer.add_string b (Printf.sprintf "%02x" (Char.code c))) ;
    Buffer.contents b
  }
;
value unhexify_greek_lident s =
    let slen = String.length s in
    if slen <= prefixlen then None else
    if (slen - prefixlen) mod 2 <> 0 then None else
    if String.sub s 0 prefixlen <> prefix then None else
    let s = String.sub s prefixlen (slen - prefixlen) in
    let slen = String.length s in
    let b = Buffer.create (slen/2) in do {
      for i = 0 to (slen/2) - 1 do {
          let ofs = i * 2 in
          let cstr = String.sub s ofs 2 in
          let cstr = "0x"^cstr in
          let c = Char.chr (int_of_string cstr) in
          Buffer.add_char b c
        } ;
      Some (Buffer.contents b)
    }
;

value greek2english_lident_map = Hashtbl.create 23 ;
value english2greek_lident_map = Hashtbl.create 23 ;
greek_lidents_list
|> List.iter (fun (gid, engid) ->
       let engid = "__"^engid^"__" in do {
       Hashtbl.add greek2english_lident_map gid engid ;
       Hashtbl.add english2greek_lident_map engid gid
     }) ;

value english2greek_lident s =
  match Hashtbl.find_opt english2greek_lident_map s with [
      Some s -> s
    | None -> match unhexify_greek_lident s with [
                  Some s -> s
                | None -> s
                ]
    ]
;

value greek2english_lident loc s =
  match Hashtbl.find_opt greek2english_lident_map s with [
      Some s -> s
    | None -> hexify_greek_lident s
    ]
;

end ;

