(* camlp5r *)
(* mlsyntax.ml *)
(* Copyright (c) INRIA 2007-2017 *)

let symbolchar_or f st ?lim s =
  let list =
    ['!'; '$'; '%'; '&'; '*'; '+'; '-'; '.'; '/'; ':'; '<'; '='; '>'; '?';
     '@'; '^'; '|'; '~']
  in
  let lim =
    match lim with
      None -> String.length s
    | Some j -> j
  in
  let rec loop i =
    if i == lim then true
    else if List.mem s.[i] list || f s.[i] then loop (i + 1)
    else false
  in
  loop st
;;

let symbolchar = symbolchar_or (fun x -> false);;

let dotsymbolchar st ?lim s =
  let list =
    ['!'; '$'; '%'; '&'; '*'; '+'; '-'; '/'; ':'; '='; '>'; '?'; '@'; '^';
     '|']
  in
  let lim =
    match lim with
      None -> String.length s
    | Some j -> j
  in
  let rec loop i =
    if i == lim then true
    else if List.mem s.[i] list then loop (i + 1)
    else false
  in
  loop st
;;

let kwdopchar =
  let list = ['$'; '&'; '*'; '+'; '-'; '/'; '<'; '='; '>'; '@'; '^'; '|'] in
  fun s i -> if i == String.length s then true else List.mem s.[i] list
;;

module Original =
  struct
    let is_prefixop =
      let list = ['!'; '?'; '~'] in
      let excl = ["!="; "??"; "?!"] in
      fun x ->
        not (List.mem x excl) && String.length x >= 2 &&
        List.mem x.[0] list && symbolchar_or (fun x -> '#' = x) 1 x
    ;;
    let is_infixop0_0 =
      let list = ['|'] in
      let excl = ["||"] in
      fun x ->
        not (List.mem x excl) && String.length x >= 2 &&
        List.mem x.[0] list && symbolchar 1 x
    ;;
    let is_infixop0_1 =
      let list = ['&'] in
      let excl = ["&&"] in
      fun x ->
        not (List.mem x excl) && String.length x >= 2 &&
        List.mem x.[0] list && symbolchar 1 x
    ;;
    let is_infixop0_2 =
      let list = ['='; '<'; '>'; '$'] in
      let excl = ["<-"] in
      fun x ->
        not (List.mem x excl) && (x = "$" || String.length x >= 2) &&
        List.mem x.[0] list && symbolchar 1 x
    ;;
    let is_infixop0 s =
      is_infixop0_0 s || is_infixop0_1 s || is_infixop0_2 s
    ;;
    let is_infixop1 =
      let list = ['@'; '^'] in
      fun x -> String.length x >= 2 && List.mem x.[0] list && symbolchar 1 x
    ;;
    let is_infixop2 =
      let list = ['+'; '-'] in
      fun x ->
        x <> "->" && String.length x >= 2 && List.mem x.[0] list &&
        symbolchar 1 x
    ;;
    let is_infixop3 =
      let list = ['*'; '/'; '%'] in
      let excl = ["**"] in
      fun x ->
        not (List.mem x excl) && String.length x >= 2 &&
        List.mem x.[0] list && symbolchar 1 x
    ;;
    let is_infixop4 x =
      String.length x >= 3 && x.[0] == '*' && x.[1] == '*' && symbolchar 2 x
    ;;
    let is_hashop =
      let list = ['#'] in
      let excl = ["#"] in
      fun x ->
        not (List.mem x excl) && String.length x >= 2 &&
        List.mem x.[0] list && symbolchar_or (fun x -> '#' = x) 1 x
    ;;
    let is_operator0 =
      let ht = Hashtbl.create 73 in
      let ct = Hashtbl.create 73 in
      List.iter (fun x -> Hashtbl.add ht x true)
        ["asr"; "land"; "lor"; "lsl"; "lsr"; "lxor"; "mod"; "or"];
      List.iter (fun x -> Hashtbl.add ct x true)
        ['!'; '&'; '*'; '+'; '-'; '/'; ':'; '<'; '='; '>'; '@'; '^'; '|'; '~';
         '?'; '%'; '.'; '$'];
      fun x ->
        try Hashtbl.find ht x with
          Not_found -> try Hashtbl.find ct x.[0] with _ -> false
    ;;
    let is_andop s =
      String.length s > 3 && String.sub s 0 3 = "and" && kwdopchar s 3 &&
      dotsymbolchar 4 s
    ;;
    let is_letop s =
      String.length s > 3 && String.sub s 0 3 = "let" && kwdopchar s 3 &&
      dotsymbolchar 4 s
    ;;
    let is_operator s = is_operator0 s || is_hashop s;;
    let is_infix_operator op =
      is_operator op &&
      (match op.[0] with
         '!' | '?' | '~' -> false
       | _ -> true)
    ;;
    let is_dotop s =
      String.length s >= 2 && String.get s 0 = '.' &&
      dotsymbolchar 1 ~lim:2 s && symbolchar 2 s
    ;;
    let is_special_op s =
      is_operator s || is_letop s || is_andop s || is_dotop s
    ;;
  end
;;

module Revised =
  struct
    include Original;;
    let is_infixop0_2 =
      let list = ['='; '<'; '>'; '$'] in
      let excl = ["<-"] in
      fun x ->
        not (List.mem x excl) && String.length x >= 2 &&
        List.mem x.[0] list && symbolchar 1 x
    ;;
    let is_infixop0 s =
      is_infixop0_0 s || is_infixop0_1 s || is_infixop0_2 s
    ;;
    let is_operator0 s = s <> "$" && is_operator s;;
    let is_operator s = is_operator0 s || is_hashop s;;
    let is_infix_operator op =
      is_operator op &&
      (match op.[0] with
         '!' | '?' | '~' -> false
       | _ -> true)
    ;;
    let is_dotop s =
      String.length s >= 2 && String.get s 0 = '.' &&
      dotsymbolchar 1 ~lim:2 s && symbolchar 2 s
    ;;
    let is_special_op s =
      is_operator s || is_letop s || is_andop s || is_dotop s
    ;;
  end
;;
