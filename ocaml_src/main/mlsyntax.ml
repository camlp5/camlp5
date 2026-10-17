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
    let greek_lidents_list =
      ["α", "alpha"; "β", "beta"; "γ", "gamma"; "δ", "delta"; "ε", "epsilon";
       "ζ", "zeta"; "η", "eta"; "θ", "theta"; "ι", "iota"; "κ", "kappa";
       "λ", "lambda"; "μ", "mu"; "ν", "nu"; "ξ", "xi"; "ο", "omicron";
       "π", "pi"; "ρ", "rho"; "σ", "sigma"; "τ", "tau"; "υ", "upsilon";
       "φ", "phi"; "χ", "chi"; "ψ", "psi"; "ω", "omega"]
    ;;
    let prefix = "__greek_";;
    let prefixlen = String.length prefix;;
    let hexify_greek_lident s =
      let b = Buffer.create (prefixlen + String.length s * 2) in
      Buffer.add_string b prefix;
      s |>
        String.iter
          (fun c ->
             Buffer.add_string b (Printf.sprintf "%02x" (Char.code c)));
      Buffer.contents b
    ;;
    let unhexify_greek_lident s =
      let slen = String.length s in
      if slen <= prefixlen then None
      else if (slen - prefixlen) mod 2 <> 0 then None
      else if String.sub s 0 prefixlen <> prefix then None
      else
        let s = String.sub s prefixlen (slen - prefixlen) in
        let slen = String.length s in
        let b = Buffer.create (slen / 2) in
        for i = 0 to slen / 2 - 1 do
          let ofs = i * 2 in
          let cstr = String.sub s ofs 2 in
          let cstr = "0x" ^ cstr in
          let c = Char.chr (int_of_string cstr) in Buffer.add_char b c
        done;
        Some (Buffer.contents b)
    ;;
    let greek2english_lident_map = Hashtbl.create 23;;
    let english2greek_lident_map = Hashtbl.create 23;;
    greek_lidents_list |>
      List.iter
        (fun (gid, engid) ->
           let engid = "__" ^ engid ^ "__" in
           Hashtbl.add greek2english_lident_map gid engid;
           Hashtbl.add english2greek_lident_map engid gid);;
    let english2greek_lident s =
      match Hashtbl.find_opt english2greek_lident_map s with
        Some s -> s
      | None ->
          match unhexify_greek_lident s with
            Some s -> s
          | None -> s
    ;;
    let greek2english_lident loc s =
      match Hashtbl.find_opt greek2english_lident_map s with
        Some s -> s
      | None -> hexify_greek_lident s
    ;;
  end
;;

