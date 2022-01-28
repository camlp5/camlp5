(* camlp5r *)
(* plexer.ml,v *)
(* Copyright (c) INRIA 2007-2017 *)

(* #load "pa_lexer.cmo" *)

open Versdep;;

let simplest_raw_strings = ref false;;
let no_quotations = ref false;;
let error_on_unknown_keywords = ref false;;

let dollar_for_antiquotation = ref true;;
let specific_space_dot = ref false;;

let force_antiquot_loc = ref false;;

type context =
  { mutable after_space : bool;
    simplest_raw_strings : bool;
    dollar_for_antiquotation : bool;
    specific_space_dot : bool;
    find_kwd : string -> string;
    line_cnt : int -> char -> unit;
    set_line_nb : unit -> unit;
    make_lined_loc : int * int -> string -> Ploc.t }
;;

let err ctx loc msg =
  Ploc.raise (ctx.make_lined_loc loc "") (Plexing.Error msg)
;;

let keyword_or_error ctx loc s =
  try "", ctx.find_kwd s with
    Not_found ->
      if !error_on_unknown_keywords then err ctx loc ("illegal token: " ^ s)
      else "", s
;;

let rev_implode l =
  let s = string_create (List.length l) in
  let rec loop i =
    function
      c :: l -> string_unsafe_set s i c; loop (i - 1) l
    | [] -> s
  in
  bytes_to_string (loop (string_length s - 1) l)
;;

let implode l = rev_implode (List.rev l);;

let stream_peek_nth n strm =
  let rec loop n =
    function
      [] -> None
    | [x] -> if n == 1 then Some x else None
    | _ :: l -> loop (n - 1) l
  in
  loop n (Stream.npeek n strm)
;;

let utf8_lexing = ref false;;

let greek_tab =
  ["α"; "β"; "γ"; "δ"; "ε"; "ζ"; "η"; "θ"; "ι"; "κ"; "λ"; "μ"; "ν"; "ξ"; "ο";
   "π"; "ρ"; "σ"; "τ"; "υ"; "φ"; "χ"; "ψ"; "ω"]
;;

let greek_letter buf strm =
  if !utf8_lexing then
    match Stream.peek strm with
      Some c ->
        if Char.code c >= 128 then
          let x = implode (Stream.npeek 2 strm) in
          if List.mem x greek_tab then
            begin Stream.junk strm; Plexing.Lexbuf.add c buf end
          else raise Stream.Failure
        else raise Stream.Failure
    | None -> raise Stream.Failure
  else raise Stream.Failure
;;

let misc_letter buf strm =
  if !utf8_lexing then
    match Stream.peek strm with
      Some c ->
        if Char.code c >= 128 then
          match implode (Stream.npeek 3 strm) with
            "→" | "≤" | "≥" -> raise Stream.Failure
          | _ -> Stream.junk strm; Plexing.Lexbuf.add c buf
        else raise Stream.Failure
    | None -> raise Stream.Failure
  else
    let (strm__ : _ Stream.t) = strm in
    match Stream.peek strm__ with
      Some ('\128'..'\225' as c) ->
        Stream.junk strm__; Plexing.Lexbuf.add c buf
    | Some ('\227'..'\255' as c) ->
        Stream.junk strm__; Plexing.Lexbuf.add c buf
    | _ -> raise Stream.Failure
;;

let misc_punct buf strm =
  if !utf8_lexing then
    let (strm__ : _ Stream.t) = strm in
    match Stream.peek strm__ with
      Some '\226' ->
        Stream.junk strm__;
        begin match Stream.peek strm__ with
          Some c ->
            Stream.junk strm__;
            begin match Stream.peek strm__ with
              Some c1 ->
                Stream.junk strm__;
                Plexing.Lexbuf.add c1
                  (Plexing.Lexbuf.add c (Plexing.Lexbuf.add '\226' buf))
            | _ -> raise (Stream.Error "")
            end
        | _ -> raise (Stream.Error "")
        end
    | _ -> raise Stream.Failure
  else let (_ : _ Stream.t) = strm in raise Stream.Failure
;;

let utf8_equiv ctx bp buf strm =
  if !utf8_lexing then
    let (strm__ : _ Stream.t) = strm in
    match Stream.peek strm__ with
      Some '\226' ->
        Stream.junk strm__;
        begin try
          match Stream.peek strm__ with
            Some '\134' ->
              Stream.junk strm__;
              begin match Stream.peek strm__ with
                Some '\146' ->
                  Stream.junk strm__;
                  keyword_or_error ctx (bp, Stream.count strm__) "->"
              | _ -> raise (Stream.Error "")
              end
          | Some '\137' ->
              Stream.junk strm__;
              begin try
                match Stream.peek strm__ with
                  Some '\164' ->
                    Stream.junk strm__;
                    keyword_or_error ctx (bp, Stream.count strm__) "<="
                | Some '\165' ->
                    Stream.junk strm__;
                    keyword_or_error ctx (bp, Stream.count strm__) ">="
                | _ -> raise Stream.Failure
              with Stream.Failure -> raise (Stream.Error "")
              end
          | _ -> raise Stream.Failure
        with Stream.Failure -> raise (Stream.Error "")
        end
    | _ -> raise Stream.Failure
  else let (_ : _ Stream.t) = strm in raise Stream.Failure
;;

let rec ident buf (strm__ : _ Stream.t) =
  match
    try
      Some
        (match Stream.peek strm__ with
           Some ('A'..'Z' | 'a'..'z' | '0'..'9' | '_' | '\'' as c) ->
             Stream.junk strm__; Plexing.Lexbuf.add c buf
         | _ -> misc_letter buf strm__)
    with Stream.Failure -> None
  with
    Some buf -> ident buf strm__
  | _ -> buf
;;

let rec ident2_or other buf (strm__ : _ Stream.t) =
  match
    try
      Some
        (match Stream.peek strm__ with
           Some
             ('!' | '?' | '~' | '=' | '@' | '^' | '&' | '+' | '-' | '*' |
              '/' | '%' | '.' | ':' | '<' | '>' | '|' | '$' as c) ->
             Stream.junk strm__; Plexing.Lexbuf.add c buf
         | _ ->
             try other buf strm__ with
               Stream.Failure -> misc_punct buf strm__)
    with Stream.Failure -> None
  with
    Some buf -> ident2_or other buf strm__
  | _ -> buf
;;

let ident2 = ident2_or (fun buf strm -> raise Stream.Failure);;
let hash_follower_chars =
  ident2_or
    (fun buf (strm__ : _ Stream.t) ->
       match Stream.peek strm__ with
         Some '#' -> Stream.junk strm__; Plexing.Lexbuf.add '#' buf
       | _ -> raise Stream.Failure)
;;

let rec ident3 buf (strm__ : _ Stream.t) =
  match Stream.peek strm__ with
    Some
      ('0'..'9' | 'A'..'Z' | 'a'..'z' | '_' | '!' | '%' | '&' | '*' | '+' |
       '-' | '.' | '/' | ':' | '<' | '=' | '>' | '?' | '@' | '^' | '|' | '~' |
       '\'' | '$' | '\128'..'\255' as c) ->
      Stream.junk strm__; ident3 (Plexing.Lexbuf.add c buf) strm__
  | _ -> buf
;;

let binary buf (strm__ : _ Stream.t) =
  match Stream.peek strm__ with
    Some ('0' | '1' as c) -> Stream.junk strm__; Plexing.Lexbuf.add c buf
  | _ -> raise Stream.Failure
;;
let octal buf (strm__ : _ Stream.t) =
  match Stream.peek strm__ with
    Some ('0'..'7' as c) -> Stream.junk strm__; Plexing.Lexbuf.add c buf
  | _ -> raise Stream.Failure
;;
let decimal buf (strm__ : _ Stream.t) =
  match Stream.peek strm__ with
    Some ('0'..'9' as c) -> Stream.junk strm__; Plexing.Lexbuf.add c buf
  | _ -> raise Stream.Failure
;;
let hexa buf (strm__ : _ Stream.t) =
  match Stream.peek strm__ with
    Some ('0'..'9' | 'a'..'f' | 'A'..'F' as c) ->
      Stream.junk strm__; Plexing.Lexbuf.add c buf
  | _ -> raise Stream.Failure
;;

let end_integer buf (strm__ : _ Stream.t) =
  match Stream.peek strm__ with
    Some 'l' -> Stream.junk strm__; "INT_l", Plexing.Lexbuf.get buf
  | Some 'L' -> Stream.junk strm__; "INT_L", Plexing.Lexbuf.get buf
  | Some 'n' -> Stream.junk strm__; "INT_n", Plexing.Lexbuf.get buf
  | _ -> "INT", Plexing.Lexbuf.get buf
;;

let rec digits_under kind buf (strm__ : _ Stream.t) =
  match try Some (kind buf strm__) with Stream.Failure -> None with
    Some buf -> digits_under kind buf strm__
  | _ ->
      match Stream.peek strm__ with
        Some '_' ->
          Stream.junk strm__;
          digits_under kind (Plexing.Lexbuf.add '_' buf) strm__
      | _ -> end_integer buf strm__
;;

let digits kind buf (strm__ : _ Stream.t) =
  let buf =
    try kind buf strm__ with
      Stream.Failure -> raise (Stream.Error "ill-formed integer constant")
  in
  digits_under kind buf strm__
;;

let rec decimal_digits_under buf (strm__ : _ Stream.t) =
  match Stream.peek strm__ with
    Some ('0'..'9' | '_' as c) ->
      Stream.junk strm__;
      decimal_digits_under (Plexing.Lexbuf.add c buf) strm__
  | _ -> buf
;;

let exponent_part buf (strm__ : _ Stream.t) =
  match Stream.peek strm__ with
    Some ('e' | 'E' as c) ->
      Stream.junk strm__;
      let buf = Plexing.Lexbuf.add c buf in
      let buf =
        match Stream.peek strm__ with
          Some ('+' | '-' as c) ->
            Stream.junk strm__; Plexing.Lexbuf.add c buf
        | _ -> buf
      in
      begin match Stream.peek strm__ with
        Some ('0'..'9' as c) ->
          Stream.junk strm__;
          decimal_digits_under (Plexing.Lexbuf.add c buf) strm__
      | _ -> raise (Stream.Error "ill-formed floating-point constant")
      end
  | _ -> raise Stream.Failure
;;

let number buf (strm__ : _ Stream.t) =
  let buf = decimal_digits_under buf strm__ in
  match Stream.peek strm__ with
    Some '.' ->
      Stream.junk strm__;
      let buf = decimal_digits_under (Plexing.Lexbuf.add '.' buf) strm__ in
      begin match
        (try Some (exponent_part buf strm__) with Stream.Failure -> None)
      with
        Some buf -> "FLOAT", Plexing.Lexbuf.get buf
      | _ -> "FLOAT", Plexing.Lexbuf.get buf
      end
  | _ ->
      match
        try Some (exponent_part buf strm__) with Stream.Failure -> None
      with
        Some buf -> "FLOAT", Plexing.Lexbuf.get buf
      | _ -> end_integer buf strm__
;;

(*
let hex_float_literal =
  '0' ['x' 'X']
  ['0'-'9' 'A'-'F' 'a'-'f'] ['0'-'9' 'A'-'F' 'a'-'f' '_']*
  ('.' ['0'-'9' 'A'-'F' 'a'-'f' '_']* )?
  (['p' 'P'] ['+' '-']? ['0'-'9'] ['0'-'9' '_']* )?
let literal_modifier = ['G'-'Z' 'g'-'z']

let hex_float_literal =
  '0' ['x' 'X']
  ['0'-'9' 'A'-'F' 'a'-'f'] ['0'-'9' 'A'-'F' 'a'-'f' '_']*
  ('.' ['0'-'9' 'A'-'F' 'a'-'f' '_']* )?
  (['p' 'P'] ['+' '-']? ['0'-'9'] ['0'-'9' '_']* )?
let literal_modifier = ['G'-'Z' 'g'-'z']
*)

(* hex_digits* *)
let rec hex_digits_under_star buf (strm__ : _ Stream.t) =
  match Stream.peek strm__ with
    Some ('0'..'9' | 'a'..'f' | 'A'..'F' | '_' as c) ->
      Stream.junk strm__;
      hex_digits_under_star (Plexing.Lexbuf.add c buf) strm__
  | _ -> buf
;;
let rec hex_under_integer buf (strm__ : _ Stream.t) =
  match Stream.peek strm__ with
    Some ('0'..'9' | 'a'..'f' | 'A'..'F' as c) ->
      Stream.junk strm__;
      begin try hex_digits_under_star (Plexing.Lexbuf.add c buf) strm__ with
        Stream.Failure -> raise (Stream.Error "")
      end
  | _ -> raise Stream.Failure
;;
let rec decimal_under_integer buf (strm__ : _ Stream.t) =
  let buf =
    match Stream.peek strm__ with
      Some ('0'..'9' as c) -> Stream.junk strm__; Plexing.Lexbuf.add c buf
    | _ -> buf
  in
  decimal_digits_under buf strm__
;;

let hex_exponent_part buf (strm__ : _ Stream.t) =
  match Stream.peek strm__ with
    Some ('p' | 'P' as c) ->
      Stream.junk strm__;
      let buf = Plexing.Lexbuf.add c buf in
      let buf =
        match Stream.peek strm__ with
          Some ('+' | '-' as c) ->
            Stream.junk strm__; Plexing.Lexbuf.add c buf
        | _ -> buf
      in
      decimal_under_integer buf strm__
  | _ -> raise Stream.Failure
;;

let hex_number buf (strm__ : _ Stream.t) =
  let buf = hex_under_integer buf strm__ in
  match Stream.peek strm__ with
    Some '.' ->
      Stream.junk strm__;
      let buf = hex_digits_under_star (Plexing.Lexbuf.add '.' buf) strm__ in
      begin match
        (try Some (hex_exponent_part buf strm__) with Stream.Failure -> None)
      with
        Some buf -> "FLOAT", Plexing.Lexbuf.get buf
      | _ -> "FLOAT", Plexing.Lexbuf.get buf
      end
  | _ ->
      match
        try Some (hex_exponent_part buf strm__) with Stream.Failure -> None
      with
        Some buf -> "FLOAT", Plexing.Lexbuf.get buf
      | _ ->
          match
            try Some (exponent_part buf strm__) with Stream.Failure -> None
          with
            Some buf -> "FLOAT", Plexing.Lexbuf.get buf
          | _ -> end_integer buf strm__
;;

let char_after_bslash buf (strm__ : _ Stream.t) =
  match Stream.peek strm__ with
    Some '\'' -> Stream.junk strm__; buf
  | Some c ->
      Stream.junk strm__;
      let buf = Plexing.Lexbuf.add c buf in
      begin try
        match Stream.peek strm__ with
          Some '\'' -> Stream.junk strm__; buf
        | Some c ->
            Stream.junk strm__;
            let buf = Plexing.Lexbuf.add c buf in
            begin match Stream.peek strm__ with
              Some '\'' -> Stream.junk strm__; buf
            | _ -> buf
            end
        | _ -> raise Stream.Failure
      with Stream.Failure -> raise (Stream.Error "")
      end
  | _ -> raise Stream.Failure
;;

let char ctx bp buf (strm__ : _ Stream.t) =
  match Stream.peek strm__ with
    Some '\\' ->
      Stream.junk strm__;
      begin match Stream.peek strm__ with
        Some c ->
          Stream.junk strm__;
          char_after_bslash
            (Plexing.Lexbuf.add c (Plexing.Lexbuf.add '\\' buf)) strm__
      | _ -> err ctx (bp, Stream.count strm__) "char not terminated"
      end
  | _ ->
      match Stream.npeek 2 strm__ with
        [_; '\''] ->
          begin match Stream.peek strm__ with
            Some c ->
              Stream.junk strm__;
              begin match Stream.peek strm__ with
                Some '\'' -> Stream.junk strm__; Plexing.Lexbuf.add c buf
              | _ -> raise (Stream.Error "")
              end
          | _ -> raise Stream.Failure
          end
      | _ -> raise Stream.Failure
;;

let any ctx buf (strm__ : _ Stream.t) =
  let bp = Stream.count strm__ in
  match Stream.peek strm__ with
    Some c -> Stream.junk strm__; ctx.line_cnt bp c; Plexing.Lexbuf.add c buf
  | _ -> raise Stream.Failure
;;

let rec skiplws buf (strm__ : _ Stream.t) =
  match Stream.peek strm__ with
    Some ' ' -> Stream.junk strm__; skiplws buf strm__
  | Some '\t' -> Stream.junk strm__; skiplws buf strm__
  | _ -> buf
;;

let incrline ctx buf (strm__ : _ Stream.t) =
  let bp = Stream.count strm__ in ctx.line_cnt (bp - 1) '\n'; buf
;;

let rec string ctx bp buf (strm__ : _ Stream.t) =
  match Stream.peek strm__ with
    Some '"' -> Stream.junk strm__; buf
  | Some '\\' ->
      Stream.junk strm__;
      begin try
        match Stream.npeek 1 strm__ with
          ['\n'] ->
            begin match Stream.peek strm__ with
              Some '\n' ->
                Stream.junk strm__;
                let buf = incrline ctx buf strm__ in
                let buf = skiplws buf strm__ in string ctx bp buf strm__
            | _ -> raise (Stream.Error "")
            end
        | _ ->
            match Stream.npeek 1 strm__ with
              ['\n'] | [' '] ->
                let buf =
                  try any ctx buf strm__ with
                    Stream.Failure -> raise (Stream.Error "")
                in
                string ctx bp buf strm__
            | _ ->
                let buf = any ctx (Plexing.Lexbuf.add '\\' buf) strm__ in
                string ctx bp buf strm__
      with Stream.Failure -> raise (Stream.Error "")
      end
  | _ ->
      match try Some (any ctx buf strm__) with Stream.Failure -> None with
        Some buf -> string ctx bp buf strm__
      | _ -> err ctx (bp, Stream.count strm__) "string not terminated"
;;

let rec quotation ctx bp buf (strm__ : _ Stream.t) =
  match Stream.peek strm__ with
    Some '>' ->
      Stream.junk strm__;
      begin match Stream.peek strm__ with
        Some '>' -> Stream.junk strm__; buf
      | _ -> quotation ctx bp (Plexing.Lexbuf.add '>' buf) strm__
      end
  | Some '<' ->
      Stream.junk strm__;
      begin match Stream.peek strm__ with
        Some '<' ->
          Stream.junk strm__;
          let buf =
            quotation ctx bp
              (Plexing.Lexbuf.add '<' (Plexing.Lexbuf.add '<' buf)) strm__
          in
          let buf = Plexing.Lexbuf.add '>' (Plexing.Lexbuf.add '>' buf) in
          quotation ctx bp buf strm__
      | Some ':' ->
          Stream.junk strm__;
          let buf =
            ident (Plexing.Lexbuf.add ':' (Plexing.Lexbuf.add '<' buf)) strm__
          in
          begin match Stream.peek strm__ with
            Some '<' ->
              Stream.junk strm__;
              let buf =
                quotation ctx bp (Plexing.Lexbuf.add '<' buf) strm__
              in
              let buf = Plexing.Lexbuf.add '>' (Plexing.Lexbuf.add '>' buf) in
              quotation ctx bp buf strm__
          | _ -> quotation ctx bp buf strm__
          end
      | _ -> quotation ctx bp (Plexing.Lexbuf.add '<' buf) strm__
      end
  | Some '\\' ->
      Stream.junk strm__;
      begin match Stream.peek strm__ with
        Some ('>' | '<' | '\\' as c) ->
          Stream.junk strm__;
          quotation ctx bp (Plexing.Lexbuf.add c buf) strm__
      | _ -> quotation ctx bp (Plexing.Lexbuf.add '\\' buf) strm__
      end
  | _ ->
      match try Some (any ctx buf strm__) with Stream.Failure -> None with
        Some buf -> quotation ctx bp buf strm__
      | _ -> err ctx (bp, Stream.count strm__) "quotation not terminated"
;;

let less_expected = "character '<' expected";;

let less ctx bp buf strm =
  if !no_quotations then
    let (strm__ : _ Stream.t) = strm in
    let buf = Plexing.Lexbuf.add '<' buf in
    let buf = ident2 buf strm__ in
    keyword_or_error ctx (bp, Stream.count strm__) (Plexing.Lexbuf.get buf)
  else
    let (strm__ : _ Stream.t) = strm in
    match Stream.peek strm__ with
      Some '<' ->
        Stream.junk strm__;
        let buf =
          try quotation ctx bp buf strm__ with
            Stream.Failure -> raise (Stream.Error "")
        in
        "QUOTATION", ":" ^ Plexing.Lexbuf.get buf
    | Some ':' ->
        Stream.junk strm__;
        let buf = ident buf strm__ in
        begin try
          match Stream.peek strm__ with
            Some '<' ->
              Stream.junk strm__;
              let buf = Plexing.Lexbuf.add ':' buf in
              let buf =
                try quotation ctx bp buf strm__ with
                  Stream.Failure -> raise (Stream.Error "")
              in
              "QUOTATION", Plexing.Lexbuf.get buf
          | _ ->
              match Stream.peek strm__ with
                Some ':' ->
                  Stream.junk strm__;
                  begin match Stream.peek strm__ with
                    Some '<' ->
                      Stream.junk strm__;
                      let buf = Plexing.Lexbuf.add '@' buf in
                      let buf =
                        try quotation ctx bp buf strm__ with
                          Stream.Failure -> raise (Stream.Error "")
                      in
                      "QUOTATION", Plexing.Lexbuf.get buf
                  | _ -> raise (Stream.Error less_expected)
                  end
              | _ -> raise Stream.Failure
        with Stream.Failure -> raise (Stream.Error "")
        end
    | _ ->
        let buf = Plexing.Lexbuf.add '<' buf in
        let buf = ident2 buf strm__ in
        keyword_or_error ctx (bp, Stream.count strm__)
          (Plexing.Lexbuf.get buf)
;;

let rec antiquot_rest ctx bp buf (strm__ : _ Stream.t) =
  match Stream.peek strm__ with
    Some '$' -> Stream.junk strm__; buf
  | Some '\\' ->
      Stream.junk strm__;
      let buf =
        try any ctx buf strm__ with Stream.Failure -> raise (Stream.Error "")
      in
      antiquot_rest ctx bp buf strm__
  | _ ->
      match try Some (any ctx buf strm__) with Stream.Failure -> None with
        Some buf -> antiquot_rest ctx bp buf strm__
      | _ -> err ctx (bp, Stream.count strm__) "antiquotation not terminated"
;;

let rec antiquot ctx bp buf (strm__ : _ Stream.t) =
  match Stream.peek strm__ with
    Some '$' -> Stream.junk strm__; ":" ^ Plexing.Lexbuf.get buf
  | Some ('a'..'z' | 'A'..'Z' | '0'..'9' | '!' | '_' as c) ->
      Stream.junk strm__; antiquot ctx bp (Plexing.Lexbuf.add c buf) strm__
  | Some ':' ->
      Stream.junk strm__;
      let buf = antiquot_rest ctx bp (Plexing.Lexbuf.add ':' buf) strm__ in
      Plexing.Lexbuf.get buf
  | Some '\\' ->
      Stream.junk strm__;
      let buf =
        try any ctx buf strm__ with Stream.Failure -> raise (Stream.Error "")
      in
      let buf = antiquot_rest ctx bp buf strm__ in
      ":" ^ Plexing.Lexbuf.get buf
  | _ ->
      match try Some (any ctx buf strm__) with Stream.Failure -> None with
        Some buf ->
          let buf = antiquot_rest ctx bp buf strm__ in
          ":" ^ Plexing.Lexbuf.get buf
      | _ -> err ctx (bp, Stream.count strm__) "antiquotation not terminated"
;;

let antiloc bp ep s = Printf.sprintf "%d,%d:%s" bp ep s;;


let skip_to_next_colon s i =
  let rec loop j =
    if j = String.length s then i, 0
    else
      match s.[j] with
        ':' -> j, j - i - 1
      | 'a'..'z' | 'A'..'Z' | '0'..'9' | '!' | '_' -> loop (j + 1)
      | _ -> i, 0
  in
  loop (i + 1)
;;

let parse_antiquot s =
  try
    let i = String.index s ':' in
    let kind = String.sub s 0 i in
    let name = String.sub s (i + 1) (String.length s - (i + 1)) in
    Some (kind, name)
  with Not_found | Failure _ -> None
;;

let parse_antiloc s =
  try
    let i = String.index s ':' in
    let (j, len) = skip_to_next_colon s i in
    let kind = String.sub s (i + 1) len in
    let loc =
      let k = String.index s ',' in
      let bp = int_of_string (String.sub s 0 k) in
      let ep = int_of_string (String.sub s (k + 1) (i - k - 1)) in
      Ploc.make_unlined (bp, ep)
    in
    Some (loc, kind, String.sub s (j + 1) (String.length s - j - 1))
  with Not_found | Failure _ -> None
;;

let rec antiquot_loc ctx bp buf (strm__ : _ Stream.t) =
  match Stream.peek strm__ with
    Some '$' ->
      Stream.junk strm__;
      antiloc bp (Stream.count strm__) (":" ^ Plexing.Lexbuf.get buf)
  | Some ('a'..'z' | 'A'..'Z' | '0'..'9' | '!' | '_' as c) ->
      Stream.junk strm__;
      antiquot_loc ctx bp (Plexing.Lexbuf.add c buf) strm__
  | Some ':' ->
      Stream.junk strm__;
      let buf = antiquot_rest ctx bp (Plexing.Lexbuf.add ':' buf) strm__ in
      antiloc bp (Stream.count strm__) (Plexing.Lexbuf.get buf)
  | Some '\\' ->
      Stream.junk strm__;
      let buf =
        try any ctx buf strm__ with Stream.Failure -> raise (Stream.Error "")
      in
      let buf = antiquot_rest ctx bp buf strm__ in
      antiloc bp (Stream.count strm__) (":" ^ Plexing.Lexbuf.get buf)
  | _ ->
      match try Some (any ctx buf strm__) with Stream.Failure -> None with
        Some buf ->
          let buf = antiquot_rest ctx bp buf strm__ in
          antiloc bp (Stream.count strm__) (":" ^ Plexing.Lexbuf.get buf)
      | _ -> err ctx (bp, Stream.count strm__) "antiquotation not terminated"
;;

let dollar ctx bp buf strm =
  if not !no_quotations && ctx.dollar_for_antiquotation then
    "ANTIQUOT", antiquot ctx bp buf strm
  else if !force_antiquot_loc then
    "ANTIQUOT_LOC", antiquot_loc ctx bp buf strm
  else
    let (strm__ : _ Stream.t) = strm in
    let buf = Plexing.Lexbuf.add '$' buf in
    let buf = ident2 buf strm__ in "", Plexing.Lexbuf.get buf
;;

(* ANTIQUOT - specific case for QUESTIONIDENT and QUESTIONIDENTCOLON
    input         expr        patt
    -----         ----        ----
    ?$abc:d$      ?abc:d      ?abc
    ?$abc:d$:     ?abc:d:     ?abc:
    ?$d$          ?:d         ?
    ?$d$:         ?:d:        ?:
*)

(* ANTIQUOT_LOC - specific case for QUESTIONIDENT and QUESTIONIDENTCOLON
    input         expr             patt
    -----         ----             ----
    ?$abc:d$      ?8,13:abc:d      ?abc
    ?$abc:d$:     ?8,13:abc:d:     ?abc:
    ?$d$          ?8,9::d          ?
    ?$d$:         ?8,9::d:         ?:
*)

let question ctx bp buf strm =
  if ctx.dollar_for_antiquotation then
    let (strm__ : _ Stream.t) = strm in
    match Stream.peek strm__ with
      Some '$' ->
        Stream.junk strm__;
        let s =
          try antiquot ctx bp Plexing.Lexbuf.empty strm__ with
            Stream.Failure -> raise (Stream.Error "")
        in
        begin match Stream.peek strm__ with
          Some ':' -> Stream.junk strm__; "ANTIQUOT", "?" ^ s ^ ":"
        | _ -> "ANTIQUOT", "?" ^ s
        end
    | _ ->
        let (strm__ : _ Stream.t) = strm in
        let buf = hash_follower_chars buf strm__ in
        keyword_or_error ctx (bp, Stream.count strm__)
          (Plexing.Lexbuf.get buf)
  else if !force_antiquot_loc then
    let (strm__ : _ Stream.t) = strm in
    match Stream.peek strm__ with
      Some '$' ->
        Stream.junk strm__;
        let s =
          try antiquot_loc ctx bp Plexing.Lexbuf.empty strm__ with
            Stream.Failure -> raise (Stream.Error "")
        in
        begin match Stream.peek strm__ with
          Some ':' -> Stream.junk strm__; "ANTIQUOT_LOC", "?" ^ s ^ ":"
        | _ -> "ANTIQUOT_LOC", "?" ^ s
        end
    | _ ->
        let (strm__ : _ Stream.t) = strm in
        let buf = hash_follower_chars buf strm__ in
        keyword_or_error ctx (bp, Stream.count strm__)
          (Plexing.Lexbuf.get buf)
  else
    let (strm__ : _ Stream.t) = strm in
    let buf = hash_follower_chars buf strm__ in
    keyword_or_error ctx (bp, Stream.count strm__) (Plexing.Lexbuf.get buf)
;;

let tilde ctx bp buf strm =
  if ctx.dollar_for_antiquotation then
    let (strm__ : _ Stream.t) = strm in
    match Stream.peek strm__ with
      Some '$' ->
        Stream.junk strm__;
        let s =
          try antiquot ctx bp Plexing.Lexbuf.empty strm__ with
            Stream.Failure -> raise (Stream.Error "")
        in
        begin match Stream.peek strm__ with
          Some ':' -> Stream.junk strm__; "ANTIQUOT", "~" ^ s ^ ":"
        | _ -> "ANTIQUOT", "~" ^ s
        end
    | _ ->
        let (strm__ : _ Stream.t) = strm in
        let buf = hash_follower_chars buf strm__ in
        keyword_or_error ctx (bp, Stream.count strm__)
          (Plexing.Lexbuf.get buf)
  else if !force_antiquot_loc then
    let (strm__ : _ Stream.t) = strm in
    match Stream.peek strm__ with
      Some '$' ->
        Stream.junk strm__;
        let s =
          try antiquot_loc ctx bp Plexing.Lexbuf.empty strm__ with
            Stream.Failure -> raise (Stream.Error "")
        in
        begin match Stream.peek strm__ with
          Some ':' -> Stream.junk strm__; "ANTIQUOT_LOC", "~" ^ s ^ ":"
        | _ -> "ANTIQUOT_LOC", "~" ^ s
        end
    | _ ->
        let (strm__ : _ Stream.t) = strm in
        let buf = hash_follower_chars buf strm__ in
        keyword_or_error ctx (bp, Stream.count strm__)
          (Plexing.Lexbuf.get buf)
  else
    let (strm__ : _ Stream.t) = strm in
    let buf = hash_follower_chars buf strm__ in
    keyword_or_error ctx (bp, Stream.count strm__) (Plexing.Lexbuf.get buf)
;;

let tildeident buf (strm__ : _ Stream.t) =
  match Stream.peek strm__ with
    Some ':' -> Stream.junk strm__; "TILDEIDENTCOLON", Plexing.Lexbuf.get buf
  | _ -> "TILDEIDENT", Plexing.Lexbuf.get buf
;;

let questionident buf (strm__ : _ Stream.t) =
  match Stream.peek strm__ with
    Some ':' ->
      Stream.junk strm__; "QUESTIONIDENTCOLON", Plexing.Lexbuf.get buf
  | _ -> "QUESTIONIDENT", Plexing.Lexbuf.get buf
;;

let rec linedir n s =
  match stream_peek_nth n s with
    Some (' ' | '\t') -> linedir (n + 1) s
  | Some ('0'..'9') -> linedir_digits (n + 1) s
  | _ -> false
and linedir_digits n s =
  match stream_peek_nth n s with
    Some ('0'..'9') -> linedir_digits (n + 1) s
  | _ -> linedir_quote n s
and linedir_quote n s =
  match stream_peek_nth n s with
    Some (' ' | '\t') -> linedir_quote (n + 1) s
  | Some '"' -> true
  | _ -> false
;;

let rec any_to_nl buf (strm__ : _ Stream.t) =
  match Stream.peek strm__ with
    Some ('\r' | '\n' as c) -> Stream.junk strm__; Plexing.Lexbuf.add c buf
  | Some c -> Stream.junk strm__; any_to_nl (Plexing.Lexbuf.add c buf) strm__
  | _ -> buf
;;

let rec rawstring1 delimtok (ofs, delim) ctx buf (strm__ : _ Stream.t) =
  let bp = Stream.count strm__ in
  match Stream.peek strm__ with
    Some c ->
      Stream.junk strm__;
      let strm = strm__ in
      ctx.line_cnt bp c;
      let buf = Plexing.Lexbuf.add c buf in
      if String.get delim ofs <> c then
        if String.get delim 0 = c then
          rawstring1 delimtok (1, delim) ctx buf strm
        else rawstring1 delimtok (0, delim) ctx buf strm
      else if ofs + 1 < String.length delim then
        rawstring1 delimtok (ofs + 1, delim) ctx buf strm
      else
        let s = Plexing.Lexbuf.get buf in
        let slen = String.length s in
        delimtok, String.sub s 0 (slen - String.length delim)
  | _ -> raise Stream.Failure
;;

let rec rawstring0 ctx bp buf (strm__ : _ Stream.t) =
  let bp = Stream.count strm__ in
  match Stream.peek strm__ with
    Some '|' ->
      Stream.junk strm__;
      let strm = strm__ in
      rawstring1 (Plexing.Lexbuf.get buf)
        (0, "|" ^ Plexing.Lexbuf.get buf ^ "}") ctx Plexing.Lexbuf.empty strm
  | Some ('a'..'z' | '_' as c) ->
      Stream.junk strm__;
      let strm = strm__ in rawstring0 ctx bp (Plexing.Lexbuf.add c buf) strm
  | _ -> raise Stream.Failure
;;

let add_string buf s =
  let slen = String.length s in
  let rec addrec buf i =
    if i = slen then buf
    else addrec (Plexing.Lexbuf.add (String.get s i) buf) (i + 1)
  in
  addrec buf 0
;;

(*
 * This predicate checks that the stream contains a valid raw-string starter.  
 * The definition of "valid raw string starter" depends on the value of 
 * the variable [simplest_raw_strings]: if it is [False], then a valid
 * raw-string starter is "[:alpha:]+|"; if it is [True], a valid raw-string
 * starter is "[:alpha:]*|".  [simplest_raw_strings] is set to True in
 * original syntax.

 * This predicate gets called when the main lexer has already seen a "{".
*)
let raw_string_starter_p ctx strm =
  let rec predrec n =
    match stream_peek_nth n strm with
      None -> false
    | Some ('a'..'z' | '_') -> predrec (n + 1)
    | Some '|' when ctx.simplest_raw_strings || n > 1 -> true
    | Some _ -> false
  in
  predrec 1
;;

let comment_rawstring ctx bp (buf : Plexing.Lexbuf.t) strm =
  if not (raw_string_starter_p ctx strm) then buf
  else
    let (delim, s) = rawstring0 ctx bp Plexing.Lexbuf.empty strm in
    let rs = Printf.sprintf "{%s|%s|%s}" delim s delim in add_string buf rs
;;

let comment ctx bp =
  let rec comment buf (strm__ : _ Stream.t) =
    match Stream.peek strm__ with
      Some '*' ->
        Stream.junk strm__;
        begin match Stream.peek strm__ with
          Some ')' ->
            Stream.junk strm__;
            Plexing.Lexbuf.add ')' (Plexing.Lexbuf.add '*' buf)
        | _ -> comment (Plexing.Lexbuf.add '*' buf) strm__
        end
    | Some '{' ->
        Stream.junk strm__;
        let buf =
          comment_rawstring ctx bp (Plexing.Lexbuf.add '{' buf) strm__
        in
        comment buf strm__
    | Some '(' ->
        Stream.junk strm__;
        begin match Stream.peek strm__ with
          Some '*' ->
            Stream.junk strm__;
            let buf =
              comment (Plexing.Lexbuf.add '*' (Plexing.Lexbuf.add '(' buf))
                strm__
            in
            comment buf strm__
        | _ -> comment (Plexing.Lexbuf.add '(' buf) strm__
        end
    | Some '"' ->
        Stream.junk strm__;
        let buf = string ctx bp (Plexing.Lexbuf.add '"' buf) strm__ in
        let buf = Plexing.Lexbuf.add '"' buf in comment buf strm__
    | Some '\'' ->
        Stream.junk strm__;
        begin try
          match Stream.peek strm__ with
            Some '*' ->
              Stream.junk strm__;
              begin match Stream.peek strm__ with
                Some ')' ->
                  Stream.junk strm__;
                  Plexing.Lexbuf.add ')'
                    (Plexing.Lexbuf.add '*' (Plexing.Lexbuf.add '\'' buf))
              | _ ->
                  comment
                    (Plexing.Lexbuf.add '*' (Plexing.Lexbuf.add '\'' buf))
                    strm__
              end
          | _ ->
              let buf = any ctx (Plexing.Lexbuf.add '\'' buf) strm__ in
              comment buf strm__
        with Stream.Failure -> raise (Stream.Error "")
        end
    | _ ->
        match try Some (any ctx buf strm__) with Stream.Failure -> None with
          Some buf -> comment buf strm__
        | _ -> err ctx (bp, Stream.count strm__) "comment not terminated"
  in
  comment
;;

let keyword_or_error_or_rawstring ctx bp (loc, s) buf strm =
  if not (raw_string_starter_p ctx strm) then
    match stream_peek_nth 1 strm with
      Some '|' when not ctx.simplest_raw_strings ->
        Stream.junk strm; keyword_or_error ctx loc "{|"
    | _ -> keyword_or_error ctx loc "{"
  else
    let (delim, s) = rawstring0 ctx bp Plexing.Lexbuf.empty strm in
    "STRING", String.escaped s
;;

let zerobuf f buf strm = f Plexing.Lexbuf.empty strm;;

let rec ws buf (strm__ : _ Stream.t) =
  let buf =
    match Stream.peek strm__ with
      Some ' ' -> Stream.junk strm__; buf
    | Some '\t' -> Stream.junk strm__; buf
    | Some '\n' -> Stream.junk strm__; buf
    | _ -> raise Stream.Failure
  in
  try ws buf strm__ with Stream.Failure -> buf
;;

let rec extattrident buf (strm__ : _ Stream.t) =
  let buf = ident buf strm__ in
  match Stream.peek strm__ with
    Some '.' ->
      Stream.junk strm__;
      begin try extattrident (Plexing.Lexbuf.add '.' buf) strm__ with
        Stream.Failure -> raise (Stream.Error "")
      end
  | _ -> buf
;;

let quoted_extension1 ctx (bp, _) extid buf strm =
  let (delim, s) = rawstring0 ctx bp Plexing.Lexbuf.empty strm in
  "QUOTEDEXTENSION", extid ^ ":" ^ String.escaped s
;;

let quoted_extension0 ctx (bp, _) extid buf (strm__ : _ Stream.t) =
  match try Some (ws buf strm__) with Stream.Failure -> None with
    Some buf ->
      begin try
        zerobuf (quoted_extension1 ctx (bp, Stream.count strm__) extid) buf
          strm__
      with Stream.Failure -> raise (Stream.Error "")
      end
  | _ ->
      zerobuf (quoted_extension1 ctx (bp, Stream.count strm__) extid) buf
        strm__
;;

let quoted_extension ctx (bp, _) buf (strm__ : _ Stream.t) =
  let buf = extattrident buf strm__ in
  try
    zerobuf
      (quoted_extension0 ctx (bp, Stream.count strm__)
         (Plexing.Lexbuf.get buf))
      buf strm__
  with Stream.Failure -> raise (Stream.Error "")
;;
let dotsymbolchar buf (strm__ : _ Stream.t) =
  match Stream.peek strm__ with
    Some
      ('!' | '$' | '%' | '&' | '*' | '+' | '-' | '/' | ':' | '=' | '>' | '?' |
       '@' | '^' | '|' as c) ->
      Stream.junk strm__; Plexing.Lexbuf.add c buf
  | _ -> raise Stream.Failure
;;
let rec dotsymbolchar_star buf (strm__ : _ Stream.t) =
  match try Some (dotsymbolchar buf strm__) with Stream.Failure -> None with
    Some buf ->
      begin try dotsymbolchar_star buf strm__ with
        Stream.Failure -> raise (Stream.Error "")
      end
  | _ -> buf
;;
let kwdopchar buf (strm__ : _ Stream.t) =
  match Stream.peek strm__ with
    Some
      ('$' | '&' | '*' | '+' | '-' | '/' | '<' | '=' | '>' | '@' | '^' |
       '|' as c) ->
      Stream.junk strm__; Plexing.Lexbuf.add c buf
  | _ -> raise Stream.Failure
;;

let symbolchar buf (strm__ : _ Stream.t) =
  match Stream.peek strm__ with
    Some
      ('!' | '$' | '%' | '&' | '*' | '+' | '-' | '.' | '/' | ':' | '<' | '=' |
       '>' | '?' | '@' | '^' | '|' | '~' as c) ->
      Stream.junk strm__; Plexing.Lexbuf.add c buf
  | _ -> raise Stream.Failure
;;
let rec symbolchar_star buf (strm__ : _ Stream.t) =
  match try Some (symbolchar buf strm__) with Stream.Failure -> None with
    Some buf ->
      begin try symbolchar_star buf strm__ with
        Stream.Failure -> raise (Stream.Error "")
      end
  | _ -> buf
;;

let word_operators ctx id buf (strm__ : _ Stream.t) =
  match try Some (kwdopchar buf strm__) with Stream.Failure -> None with
    Some buf ->
      let buf =
        try dotsymbolchar_star buf strm__ with
          Stream.Failure -> raise (Stream.Error "")
      in
      "", id ^ Plexing.Lexbuf.get buf
  | _ -> try "", ctx.find_kwd id with Not_found -> "LIDENT", id
;;
let keyword ctx buf strm =
  let id = Plexing.Lexbuf.get buf in
  if id = "let" || id = "and" then
    word_operators ctx id Plexing.Lexbuf.empty strm
  else try "", ctx.find_kwd id with Not_found -> "LIDENT", id
;;

let dot ctx (bp, pos) buf strm =
  match Stream.peek strm with
    None ->
      let id =
        if ctx.specific_space_dot && ctx.after_space then " ." else "."
      in
      keyword_or_error ctx (bp, pos) id
  | _ ->
      let (strm__ : _ Stream.t) = strm in
      let buf = Plexing.Lexbuf.add '.' buf in
      let buf = dotsymbolchar_star buf strm__ in
      keyword_or_error ctx (bp, Stream.count strm__) (Plexing.Lexbuf.get buf)
;;


let next_token_after_spaces ctx bp buf (strm__ : _ Stream.t) =
  match Stream.peek strm__ with
    Some ('A'..'Z' as c) ->
      Stream.junk strm__;
      let buf = ident (Plexing.Lexbuf.add c buf) strm__ in
      let id = Plexing.Lexbuf.get buf in
      (try "", ctx.find_kwd id with Not_found -> "UIDENT", id)
  | _ ->
      match
        try Some (greek_letter buf strm__) with Stream.Failure -> None
      with
        Some buf ->
          let buf = ident buf strm__ in "GIDENT", Plexing.Lexbuf.get buf
      | _ ->
          match
            try
              Some
                (match Stream.peek strm__ with
                   Some ('a'..'z' | '_' as c) ->
                     Stream.junk strm__; Plexing.Lexbuf.add c buf
                 | _ -> misc_letter buf strm__)
            with Stream.Failure -> None
          with
            Some buf ->
              let buf = ident buf strm__ in
              begin try keyword ctx buf strm__ with
                Stream.Failure -> raise (Stream.Error "")
              end
          | _ ->
              match Stream.peek strm__ with
                Some ('1'..'9' as c) ->
                  Stream.junk strm__; number (Plexing.Lexbuf.add c buf) strm__
              | Some '0' ->
                  Stream.junk strm__;
                  begin match Stream.peek strm__ with
                    Some ('o' | 'O' as c) ->
                      Stream.junk strm__;
                      digits octal
                        (Plexing.Lexbuf.add c (Plexing.Lexbuf.add '0' buf))
                        strm__
                  | Some ('x' | 'X' as c) ->
                      Stream.junk strm__;
                      hex_number
                        (Plexing.Lexbuf.add c (Plexing.Lexbuf.add '0' buf))
                        strm__
                  | Some ('b' | 'B' as c) ->
                      Stream.junk strm__;
                      digits binary
                        (Plexing.Lexbuf.add c (Plexing.Lexbuf.add '0' buf))
                        strm__
                  | _ -> number (Plexing.Lexbuf.add '0' buf) strm__
                  end
              | Some '\'' ->
                  Stream.junk strm__;
                  begin match Stream.npeek 3 strm__ with
                    ['\\'; 'a'..'z'; 'a'..'z'] ->
                      keyword_or_error ctx (bp, Stream.count strm__) "'"
                  | _ ->
                      match
                        try Some (char ctx bp buf strm__) with
                          Stream.Failure -> None
                      with
                        Some buf -> "CHAR", Plexing.Lexbuf.get buf
                      | _ ->
                          keyword_or_error ctx (bp, Stream.count strm__) "'"
                  end
              | Some '"' ->
                  Stream.junk strm__;
                  let buf = string ctx bp buf strm__ in
                  "STRING", Plexing.Lexbuf.get buf
              | Some '$' -> Stream.junk strm__; dollar ctx bp buf strm__
              | Some
                  ('=' | '@' | '^' | '&' | '+' | '-' | '*' | '/' |
                   '%' as c) ->
                  Stream.junk strm__;
                  let buf = ident2 (Plexing.Lexbuf.add c buf) strm__ in
                  keyword_or_error ctx (bp, Stream.count strm__)
                    (Plexing.Lexbuf.get buf)
              | Some '!' ->
                  Stream.junk strm__;
                  let buf =
                    hash_follower_chars (Plexing.Lexbuf.add '!' buf) strm__
                  in
                  keyword_or_error ctx (bp, Stream.count strm__)
                    (Plexing.Lexbuf.get buf)
              | Some '~' ->
                  Stream.junk strm__;
                  begin try
                    match Stream.peek strm__ with
                      Some ('a'..'z' as c) ->
                        Stream.junk strm__;
                        let buf = ident (Plexing.Lexbuf.add c buf) strm__ in
                        tildeident buf strm__
                    | Some '_' ->
                        Stream.junk strm__;
                        let buf = ident (Plexing.Lexbuf.add '_' buf) strm__ in
                        tildeident buf strm__
                    | _ -> tilde ctx bp (Plexing.Lexbuf.add '~' buf) strm__
                  with Stream.Failure -> raise (Stream.Error "")
                  end
              | Some '?' ->
                  Stream.junk strm__;
                  begin match Stream.peek strm__ with
                    Some ('a'..'z' as c) ->
                      Stream.junk strm__;
                      let buf = ident (Plexing.Lexbuf.add c buf) strm__ in
                      questionident buf strm__
                  | _ -> question ctx bp (Plexing.Lexbuf.add '?' buf) strm__
                  end
              | Some '<' -> Stream.junk strm__; less ctx bp buf strm__
              | Some ':' ->
                  Stream.junk strm__;
                  begin match Stream.peek strm__ with
                    Some ']' ->
                      Stream.junk strm__;
                      keyword_or_error ctx (bp, Stream.count strm__)
                        (Plexing.Lexbuf.get
                           (Plexing.Lexbuf.add ']'
                              (Plexing.Lexbuf.add ':' buf)))
                  | Some ':' ->
                      Stream.junk strm__;
                      keyword_or_error ctx (bp, Stream.count strm__)
                        (Plexing.Lexbuf.get
                           (Plexing.Lexbuf.add ':'
                              (Plexing.Lexbuf.add ':' buf)))
                  | Some '=' ->
                      Stream.junk strm__;
                      keyword_or_error ctx (bp, Stream.count strm__)
                        (Plexing.Lexbuf.get
                           (Plexing.Lexbuf.add '='
                              (Plexing.Lexbuf.add ':' buf)))
                  | Some '>' ->
                      Stream.junk strm__;
                      keyword_or_error ctx (bp, Stream.count strm__)
                        (Plexing.Lexbuf.get
                           (Plexing.Lexbuf.add '>'
                              (Plexing.Lexbuf.add ':' buf)))
                  | _ ->
                      keyword_or_error ctx (bp, Stream.count strm__)
                        (Plexing.Lexbuf.get (Plexing.Lexbuf.add ':' buf))
                  end
              | Some '>' ->
                  Stream.junk strm__;
                  begin match Stream.peek strm__ with
                    Some ']' ->
                      Stream.junk strm__;
                      keyword_or_error ctx (bp, Stream.count strm__)
                        (Plexing.Lexbuf.get
                           (Plexing.Lexbuf.add ']'
                              (Plexing.Lexbuf.add '>' buf)))
                  | Some '}' ->
                      Stream.junk strm__;
                      keyword_or_error ctx (bp, Stream.count strm__)
                        (Plexing.Lexbuf.get
                           (Plexing.Lexbuf.add '}'
                              (Plexing.Lexbuf.add '>' buf)))
                  | _ ->
                      let buf = ident2 (Plexing.Lexbuf.add '>' buf) strm__ in
                      keyword_or_error ctx (bp, Stream.count strm__)
                        (Plexing.Lexbuf.get buf)
                  end
              | Some '|' ->
                  Stream.junk strm__;
                  begin match Stream.peek strm__ with
                    Some ']' ->
                      Stream.junk strm__;
                      keyword_or_error ctx (bp, Stream.count strm__)
                        (Plexing.Lexbuf.get
                           (Plexing.Lexbuf.add ']'
                              (Plexing.Lexbuf.add '|' buf)))
                  | Some '}' ->
                      Stream.junk strm__;
                      keyword_or_error ctx (bp, Stream.count strm__)
                        (Plexing.Lexbuf.get
                           (Plexing.Lexbuf.add '}'
                              (Plexing.Lexbuf.add '|' buf)))
                  | _ ->
                      let buf = ident2 (Plexing.Lexbuf.add '|' buf) strm__ in
                      keyword_or_error ctx (bp, Stream.count strm__)
                        (Plexing.Lexbuf.get buf)
                  end
              | Some '[' ->
                  Stream.junk strm__;
                  begin match Stream.npeek 2 strm__ with
                    ['<'; '<'] | ['<'; ':'] ->
                      keyword_or_error ctx (bp, Stream.count strm__)
                        (Plexing.Lexbuf.get (Plexing.Lexbuf.add '[' buf))
                  | _ ->
                      match Stream.peek strm__ with
                        Some '@' ->
                          Stream.junk strm__;
                          begin match Stream.peek strm__ with
                            Some '@' ->
                              Stream.junk strm__;
                              begin match Stream.peek strm__ with
                                Some '@' ->
                                  Stream.junk strm__;
                                  keyword_or_error ctx
                                    (bp, Stream.count strm__)
                                    (Plexing.Lexbuf.get
                                       (Plexing.Lexbuf.add '@'
                                          (Plexing.Lexbuf.add '@'
                                             (Plexing.Lexbuf.add '@'
                                                (Plexing.Lexbuf.add '['
                                                   buf)))))
                              | _ ->
                                  keyword_or_error ctx
                                    (bp, Stream.count strm__)
                                    (Plexing.Lexbuf.get
                                       (Plexing.Lexbuf.add '@'
                                          (Plexing.Lexbuf.add '@'
                                             (Plexing.Lexbuf.add '[' buf))))
                              end
                          | _ ->
                              keyword_or_error ctx (bp, Stream.count strm__)
                                (Plexing.Lexbuf.get
                                   (Plexing.Lexbuf.add '@'
                                      (Plexing.Lexbuf.add '[' buf)))
                          end
                      | Some '%' ->
                          Stream.junk strm__;
                          begin match Stream.peek strm__ with
                            Some '%' ->
                              Stream.junk strm__;
                              keyword_or_error ctx (bp, Stream.count strm__)
                                (Plexing.Lexbuf.get
                                   (Plexing.Lexbuf.add '%'
                                      (Plexing.Lexbuf.add '%'
                                         (Plexing.Lexbuf.add '[' buf))))
                          | _ ->
                              keyword_or_error ctx (bp, Stream.count strm__)
                                (Plexing.Lexbuf.get
                                   (Plexing.Lexbuf.add '%'
                                      (Plexing.Lexbuf.add '[' buf)))
                          end
                      | Some '|' ->
                          Stream.junk strm__;
                          keyword_or_error ctx (bp, Stream.count strm__)
                            (Plexing.Lexbuf.get
                               (Plexing.Lexbuf.add '|'
                                  (Plexing.Lexbuf.add '[' buf)))
                      | Some '<' ->
                          Stream.junk strm__;
                          keyword_or_error ctx (bp, Stream.count strm__)
                            (Plexing.Lexbuf.get
                               (Plexing.Lexbuf.add '<'
                                  (Plexing.Lexbuf.add '[' buf)))
                      | Some ':' ->
                          Stream.junk strm__;
                          keyword_or_error ctx (bp, Stream.count strm__)
                            (Plexing.Lexbuf.get
                               (Plexing.Lexbuf.add ':'
                                  (Plexing.Lexbuf.add '[' buf)))
                      | _ ->
                          keyword_or_error ctx (bp, Stream.count strm__)
                            (Plexing.Lexbuf.get (Plexing.Lexbuf.add '[' buf))
                  end
              | Some '{' ->
                  Stream.junk strm__;
                  begin try
                    match Stream.npeek 2 strm__ with
                      ['<'; '<'] | ['<'; ':'] ->
                        keyword_or_error ctx (bp, Stream.count strm__)
                          (Plexing.Lexbuf.get (Plexing.Lexbuf.add '{' buf))
                    | _ ->
                        match Stream.peek strm__ with
                          Some '<' ->
                            Stream.junk strm__;
                            keyword_or_error ctx (bp, Stream.count strm__)
                              (Plexing.Lexbuf.get
                                 (Plexing.Lexbuf.add '<'
                                    (Plexing.Lexbuf.add '{' buf)))
                        | Some '%' ->
                            Stream.junk strm__;
                            begin try
                              zerobuf
                                (quoted_extension ctx
                                   (bp, Stream.count strm__))
                                buf strm__
                            with Stream.Failure -> raise (Stream.Error "")
                            end
                        | Some ':' ->
                            Stream.junk strm__;
                            keyword_or_error ctx (bp, Stream.count strm__)
                              (Plexing.Lexbuf.get
                                 (Plexing.Lexbuf.add ':'
                                    (Plexing.Lexbuf.add '{' buf)))
                        | _ ->
                            keyword_or_error_or_rawstring ctx bp
                              ((bp, Stream.count strm__),
                               Plexing.Lexbuf.get buf)
                              (Plexing.Lexbuf.add '{' buf) strm__
                  with Stream.Failure -> raise (Stream.Error "")
                  end
              | Some '.' ->
                  Stream.junk strm__;
                  begin match Stream.peek strm__ with
                    Some '.' ->
                      Stream.junk strm__;
                      keyword_or_error ctx (bp, Stream.count strm__) ".."
                  | _ ->
                      match
                        try
                          Some
                            (dotsymbolchar (Plexing.Lexbuf.add '.' buf)
                               strm__)
                        with Stream.Failure -> None
                      with
                        Some buf ->
                          let buf =
                            try symbolchar_star buf strm__ with
                              Stream.Failure -> raise (Stream.Error "")
                          in
                          keyword_or_error ctx (bp, Stream.count strm__)
                            (Plexing.Lexbuf.get buf)
                      | _ ->
                          let id =
                            if ctx.specific_space_dot && ctx.after_space then
                              " ."
                            else "."
                          in
                          keyword_or_error ctx (bp, Stream.count strm__) id
                  end
              | Some ';' ->
                  Stream.junk strm__;
                  begin match Stream.peek strm__ with
                    Some ';' ->
                      Stream.junk strm__;
                      keyword_or_error ctx (bp, Stream.count strm__) ";;"
                  | _ -> keyword_or_error ctx (bp, Stream.count strm__) ";"
                  end
              | _ ->
                  try utf8_equiv ctx bp buf strm__ with
                    Stream.Failure ->
                      match
                        try Some (misc_punct buf strm__) with
                          Stream.Failure -> None
                      with
                        Some buf ->
                          let buf = ident2 buf strm__ in
                          keyword_or_error ctx (bp, Stream.count strm__)
                            (Plexing.Lexbuf.get buf)
                      | _ ->
                          match Stream.peek strm__ with
                            Some '\\' ->
                              Stream.junk strm__;
                              let buf = ident3 buf strm__ in
                              "LIDENT", Plexing.Lexbuf.get buf
                          | Some '#' ->
                              Stream.junk strm__;
                              let buf =
                                hash_follower_chars
                                  (Plexing.Lexbuf.add '#' buf) strm__
                              in
                              keyword_or_error ctx (bp, Stream.count strm__)
                                (Plexing.Lexbuf.get buf)
                          | _ ->
                              let buf = any ctx buf strm__ in
                              keyword_or_error ctx (bp, Stream.count strm__)
                                (Plexing.Lexbuf.get buf)
;;

let get_comment buf strm = Plexing.Lexbuf.get buf;;

let rec next_token ctx buf (strm__ : _ Stream.t) =
  let bp = Stream.count strm__ in
  match Stream.peek strm__ with
    Some ('\n' | '\r' as c) ->
      Stream.junk strm__;
      let s = strm__ in
      let ep = Stream.count strm__ in
      if c = '\n' then incr !(Plexing.line_nb);
      !(Plexing.bol_pos) := ep;
      ctx.set_line_nb ();
      ctx.after_space <- true;
      next_token ctx (Plexing.Lexbuf.add c buf) s
  | Some (' ' | '\t' | '\026' | '\012' as c) ->
      Stream.junk strm__;
      let s = strm__ in
      ctx.after_space <- true; next_token ctx (Plexing.Lexbuf.add c buf) s
  | Some '#' when bp = !(!(Plexing.bol_pos)) ->
      Stream.junk strm__;
      let s = strm__ in
      let comm = get_comment buf () in
      if linedir 1 s then
        let buf = any_to_nl (Plexing.Lexbuf.add '#' buf) s in
        incr !(Plexing.line_nb);
        !(Plexing.bol_pos) := Stream.count s;
        ctx.set_line_nb ();
        ctx.after_space <- true;
        next_token ctx buf s
      else
        let loc = ctx.make_lined_loc (bp, bp + 1) comm in
        keyword_or_error ctx (bp, bp + 1) "#", loc
  | Some '(' ->
      Stream.junk strm__;
      begin match Stream.peek strm__ with
        Some '*' ->
          Stream.junk strm__;
          let buf =
            comment ctx bp
              (Plexing.Lexbuf.add '*' (Plexing.Lexbuf.add '(' buf)) strm__
          in
          let s = strm__ in
          ctx.set_line_nb (); ctx.after_space <- true; next_token ctx buf s
      | _ ->
          let ep = Stream.count strm__ in
          let loc = ctx.make_lined_loc (bp, ep) (Plexing.Lexbuf.get buf) in
          keyword_or_error ctx (bp, ep) "(", loc
      end
  | _ ->
      let comm = get_comment buf strm__ in
      try
        match
          try
            Some (next_token_after_spaces ctx bp Plexing.Lexbuf.empty strm__)
          with Stream.Failure -> None
        with
          Some tok ->
            let ep = Stream.count strm__ in
            let loc = ctx.make_lined_loc (bp, max (bp + 1) ep) comm in
            tok, loc
        | _ ->
            let _ = Stream.empty strm__ in
            let loc = ctx.make_lined_loc (bp, bp + 1) comm in ("EOI", ""), loc
      with Stream.Failure -> raise (Stream.Error "")
;;

let next_token_fun ctx glexr (cstrm, s_line_nb, s_bol_pos) =
  try
    begin match !(Plexing.restore_lexing_info) with
      Some (line_nb, bol_pos) ->
        s_line_nb := line_nb;
        s_bol_pos := bol_pos;
        Plexing.restore_lexing_info := None
    | None -> ()
    end;
    Plexing.line_nb := s_line_nb;
    Plexing.bol_pos := s_bol_pos;
    let comm_bp = Stream.count cstrm in
    ctx.set_line_nb ();
    ctx.after_space <- false;
    let (r, loc) = next_token ctx Plexing.Lexbuf.empty cstrm in
    begin match !glexr.Plexing.tok_comm with
      Some list ->
        if Ploc.first_pos loc > comm_bp then
          let comm_loc = Ploc.make_unlined (comm_bp, Ploc.last_pos loc) in
          !glexr.Plexing.tok_comm <- Some (comm_loc :: list)
    | None -> ()
    end;
    r, loc
  with Stream.Error str ->
    err ctx (Stream.count cstrm, Stream.count cstrm + 1) str
;;

let make_ctx kwd_table =
  let line_nb = ref 0 in
  let bol_pos = ref 0 in
  {after_space = false; dollar_for_antiquotation = !dollar_for_antiquotation;
   simplest_raw_strings = !simplest_raw_strings;
   specific_space_dot = !specific_space_dot;
   find_kwd = Hashtbl.find kwd_table;
   line_cnt =
     (fun bp1 c ->
        match c with
          '\n' | '\r' ->
            if c = '\n' then incr !(Plexing.line_nb);
            !(Plexing.bol_pos) := bp1 + 1
        | c -> ());
   set_line_nb =
     (fun () ->
        line_nb := !(!(Plexing.line_nb)); bol_pos := !(!(Plexing.bol_pos)));
   make_lined_loc =
     fun loc comm ->
       Ploc.make_loc !(Plexing.input_file) !line_nb !bol_pos loc comm}
;;

let func ctx kwd_table glexr =
  Plexing.lexer_func_of_parser (next_token_fun ctx glexr)
;;

let rec check_keyword_stream (strm__ : _ Stream.t) =
  let _ = check Plexing.Lexbuf.empty strm__ in
  let _ =
    try Stream.empty strm__ with Stream.Failure -> raise (Stream.Error "")
  in
  true
and check buf (strm__ : _ Stream.t) =
  match
    try
      Some
        (match Stream.peek strm__ with
           Some ('A'..'Z' | 'a'..'z' as c) ->
             Stream.junk strm__; Plexing.Lexbuf.add c buf
         | _ -> misc_letter buf strm__)
    with Stream.Failure -> None
  with
    Some buf -> check_ident buf strm__
  | _ ->
      match Stream.peek strm__ with
        Some
          ('!' | '?' | '~' | '=' | '@' | '^' | '&' | '+' | '-' | '*' | '/' |
           '%' | '.' as c) ->
          Stream.junk strm__; check_ident2 (Plexing.Lexbuf.add c buf) strm__
      | Some '$' ->
          Stream.junk strm__; check_ident2 (Plexing.Lexbuf.add '$' buf) strm__
      | Some '<' ->
          Stream.junk strm__;
          begin match Stream.npeek 1 strm__ with
            [':'] | ['<'] -> Plexing.Lexbuf.add '<' buf
          | _ -> check_ident2 (Plexing.Lexbuf.add '<' buf) strm__
          end
      | Some ':' ->
          Stream.junk strm__;
          begin match Stream.peek strm__ with
            Some ']' ->
              Stream.junk strm__;
              Plexing.Lexbuf.add ']' (Plexing.Lexbuf.add ':' buf)
          | Some ':' ->
              Stream.junk strm__;
              Plexing.Lexbuf.add ':' (Plexing.Lexbuf.add ':' buf)
          | Some '=' ->
              Stream.junk strm__;
              Plexing.Lexbuf.add '=' (Plexing.Lexbuf.add ':' buf)
          | Some '>' ->
              Stream.junk strm__;
              Plexing.Lexbuf.add '>' (Plexing.Lexbuf.add ':' buf)
          | _ -> Plexing.Lexbuf.add ':' buf
          end
      | Some '>' ->
          Stream.junk strm__;
          begin match Stream.peek strm__ with
            Some ']' ->
              Stream.junk strm__;
              Plexing.Lexbuf.add ']' (Plexing.Lexbuf.add '>' buf)
          | Some '}' ->
              Stream.junk strm__;
              Plexing.Lexbuf.add '}' (Plexing.Lexbuf.add '>' buf)
          | _ -> check_ident2 (Plexing.Lexbuf.add '>' buf) strm__
          end
      | Some '|' ->
          Stream.junk strm__;
          begin match Stream.peek strm__ with
            Some ']' ->
              Stream.junk strm__;
              Plexing.Lexbuf.add ']' (Plexing.Lexbuf.add '|' buf)
          | Some '}' ->
              Stream.junk strm__;
              Plexing.Lexbuf.add '}' (Plexing.Lexbuf.add '|' buf)
          | _ -> check_ident2 (Plexing.Lexbuf.add '|' buf) strm__
          end
      | Some '[' ->
          Stream.junk strm__;
          begin match Stream.npeek 2 strm__ with
            ['<'; '<'] | ['<'; ':'] -> Plexing.Lexbuf.add '[' buf
          | _ ->
              match Stream.peek strm__ with
                Some '@' ->
                  Stream.junk strm__;
                  begin match Stream.peek strm__ with
                    Some '@' ->
                      Stream.junk strm__;
                      begin match Stream.peek strm__ with
                        Some '@' ->
                          Stream.junk strm__;
                          Plexing.Lexbuf.add '@'
                            (Plexing.Lexbuf.add '@'
                               (Plexing.Lexbuf.add '@'
                                  (Plexing.Lexbuf.add '[' buf)))
                      | _ ->
                          Plexing.Lexbuf.add '@'
                            (Plexing.Lexbuf.add '@'
                               (Plexing.Lexbuf.add '[' buf))
                      end
                  | _ -> Plexing.Lexbuf.add '@' (Plexing.Lexbuf.add '[' buf)
                  end
              | Some '%' ->
                  Stream.junk strm__;
                  begin match Stream.peek strm__ with
                    Some '%' ->
                      Stream.junk strm__;
                      Plexing.Lexbuf.add '%'
                        (Plexing.Lexbuf.add '%' (Plexing.Lexbuf.add '[' buf))
                  | _ -> Plexing.Lexbuf.add '%' (Plexing.Lexbuf.add '[' buf)
                  end
              | Some '|' ->
                  Stream.junk strm__;
                  Plexing.Lexbuf.add '|' (Plexing.Lexbuf.add '[' buf)
              | Some '<' ->
                  Stream.junk strm__;
                  Plexing.Lexbuf.add '<' (Plexing.Lexbuf.add '[' buf)
              | Some ':' ->
                  Stream.junk strm__;
                  Plexing.Lexbuf.add ':' (Plexing.Lexbuf.add '[' buf)
              | _ -> Plexing.Lexbuf.add '[' buf
          end
      | Some '{' ->
          Stream.junk strm__;
          begin match Stream.npeek 2 strm__ with
            ['<'; '<'] | ['<'; ':'] -> Plexing.Lexbuf.add '{' buf
          | _ ->
              match Stream.peek strm__ with
                Some '|' ->
                  Stream.junk strm__;
                  Plexing.Lexbuf.add '|' (Plexing.Lexbuf.add '{' buf)
              | Some '<' ->
                  Stream.junk strm__;
                  Plexing.Lexbuf.add '<' (Plexing.Lexbuf.add '{' buf)
              | Some ':' ->
                  Stream.junk strm__;
                  Plexing.Lexbuf.add ':' (Plexing.Lexbuf.add '{' buf)
              | _ -> Plexing.Lexbuf.add '{' buf
          end
      | Some ';' ->
          Stream.junk strm__;
          begin match Stream.peek strm__ with
            Some ';' ->
              Stream.junk strm__;
              Plexing.Lexbuf.add ';' (Plexing.Lexbuf.add ';' buf)
          | _ -> Plexing.Lexbuf.add ';' buf
          end
      | _ ->
          match
            try Some (misc_punct buf strm__) with Stream.Failure -> None
          with
            Some buf -> check_ident2 buf strm__
          | _ ->
              match Stream.peek strm__ with
                Some c -> Stream.junk strm__; Plexing.Lexbuf.add c buf
              | _ -> raise Stream.Failure
and check_ident buf (strm__ : _ Stream.t) =
  match
    try
      Some
        (match Stream.peek strm__ with
           Some ('A'..'Z' | 'a'..'z' | '0'..'9' | '_' | '\'' as c) ->
             Stream.junk strm__; Plexing.Lexbuf.add c buf
         | _ -> misc_letter buf strm__)
    with Stream.Failure -> None
  with
    Some buf -> check_ident buf strm__
  | _ -> buf
and check_ident2 buf (strm__ : _ Stream.t) =
  match
    try
      Some
        (match Stream.peek strm__ with
           Some
             ('!' | '?' | '~' | '=' | '@' | '^' | '&' | '+' | '-' | '*' |
              '/' | '%' | '.' | ':' | '<' | '>' | '|' as c) ->
             Stream.junk strm__; Plexing.Lexbuf.add c buf
         | _ -> misc_punct buf strm__)
    with Stream.Failure -> None
  with
    Some buf -> check_ident2 buf strm__
  | _ -> buf
;;

let check_keyword ctx s =
  if ctx.simplest_raw_strings && (s = "{|" || s = "|}") then false
  else try check_keyword_stream (Stream.of_string s) with _ -> false
;;

let error_no_respect_rules p_con p_prm =
  raise
    (Plexing.Error
       ("the token " ^
        (if p_con = "" then "\"" ^ p_prm ^ "\""
         else if p_prm = "" then p_con
         else p_con ^ " \"" ^ p_prm ^ "\"") ^
        " does not respect Plexer rules"))
;;

let using_token ctx kwd_table (p_con, p_prm) =
  match p_con with
    "" ->
      if not (hashtbl_mem kwd_table p_prm) then
        if check_keyword ctx p_prm then Hashtbl.add kwd_table p_prm p_prm
        else error_no_respect_rules p_con p_prm
  | "LIDENT" ->
      if p_prm = "" then ()
      else
        begin match p_prm.[0] with
          'A'..'Z' -> error_no_respect_rules p_con p_prm
        | _ -> ()
        end
  | "UIDENT" ->
      if p_prm = "" then ()
      else
        begin match p_prm.[0] with
          'a'..'z' -> error_no_respect_rules p_con p_prm
        | _ -> ()
        end
  | "TILDEIDENT" | "TILDEIDENTCOLON" | "QUESTIONIDENT" |
    "QUESTIONIDENTCOLON" | "INT" | "INT_l" | "INT_L" | "INT_n" | "FLOAT" |
    "QUOTEDEXTENSION" | "CHAR" | "STRING" | "QUOTATION" | "GIDENT" |
    "ANTIQUOT" | "ANTIQUOT_LOC" | "EOI" ->
      ()
  | _ ->
      raise
        (Plexing.Error
           ("the constructor \"" ^ p_con ^ "\" is not recognized by Plexer"))
;;

let removing_token kwd_table (p_con, p_prm) =
  match p_con with
    "" -> Hashtbl.remove kwd_table p_prm
  | _ -> ()
;;

let text =
  function
    "", t -> "'" ^ t ^ "'"
  | "LIDENT", "" -> "lowercase identifier"
  | "LIDENT", t -> "'" ^ t ^ "'"
  | "UIDENT", "" -> "uppercase identifier"
  | "UIDENT", t -> "'" ^ t ^ "'"
  | "INT", "" -> "integer"
  | "INT", s -> "'" ^ s ^ "'"
  | "FLOAT", "" -> "float"
  | "STRING", "" -> "string"
  | "CHAR", "" -> "char"
  | "QUOTATION", "" -> "quotation"
  | "ANTIQUOT", k -> "antiquot \"" ^ k ^ "\""
  | "EOI", "" -> "end of input"
  | con, "" -> con
  | con, prm -> con ^ " \"" ^ prm ^ "\""
;;

let eq_before_colon p e =
  let rec loop i =
    if i == String.length e then
      failwith "Internal error in Plexer: incorrect ANTIQUOT"
    else if i == String.length p then e.[i] == ':'
    else if p.[i] == e.[i] then loop (i + 1)
    else false
  in
  loop 0
;;

let after_colon e =
  try
    let i = String.index e ':' in
    String.sub e (i + 1) (String.length e - i - 1)
  with Not_found -> ""
;;

let after_colon_except_last e =
  try
    let i = String.index e ':' in
    String.sub e (i + 1) (String.length e - i - 2)
  with Not_found -> ""
;;

let tok_match =
  function
    "ANTIQUOT", p_prm ->
      if p_prm <> "" && (p_prm.[0] = '~' || p_prm.[0] = '?') then
        if p_prm.[String.length p_prm - 1] = ':' then
          let p_prm = String.sub p_prm 0 (String.length p_prm - 1) in
          function
            "ANTIQUOT", prm ->
              if prm <> "" && prm.[String.length prm - 1] = ':' then
                if eq_before_colon p_prm prm then after_colon_except_last prm
                else raise Stream.Failure
              else raise Stream.Failure
          | _ -> raise Stream.Failure
        else
          function
            "ANTIQUOT", prm ->
              if prm <> "" && prm.[String.length prm - 1] = ':' then
                raise Stream.Failure
              else if eq_before_colon p_prm prm then after_colon prm
              else raise Stream.Failure
          | _ -> raise Stream.Failure
      else
        (function
           "ANTIQUOT", prm when eq_before_colon p_prm prm -> after_colon prm
         | _ -> raise Stream.Failure)
  | "LIDENT", p_prm ->
      (* also treats the case when a LIDENT is also a keyword *)
      (fun (con, prm) ->
         if con = "LIDENT" then
           if p_prm = "" || prm = p_prm then prm else raise Stream.Failure
         else if con = "" && prm = p_prm then prm
         else raise Stream.Failure)
  | "UIDENT", p_prm ->
      (* also treats the case when a UIDENT is also a keyword *)
      (fun (con, prm) ->
         if con = "UIDENT" then
           if p_prm = "" || prm = p_prm then prm else raise Stream.Failure
         else if con = "" && prm = p_prm then prm
         else raise Stream.Failure)
  | tok -> Plexing.default_match tok
;;

let gmake () =
  let kwd_table = Hashtbl.create 301 in
  let ctx = make_ctx kwd_table in
  let glexr =
    ref
      {Plexing.tok_func =
        (fun _ -> raise (Match_failure ("plexer.ml", 1016, 25)));
       tok_using = (fun _ -> raise (Match_failure ("plexer.ml", 1016, 45)));
       tok_removing =
         (fun _ -> raise (Match_failure ("plexer.ml", 1016, 68)));
       tok_match = (fun _ -> raise (Match_failure ("plexer.ml", 1017, 18)));
       tok_text = (fun _ -> raise (Match_failure ("plexer.ml", 1017, 37)));
       tok_comm = None}
  in
  let glex =
    {Plexing.tok_func = func ctx kwd_table glexr;
     tok_using = using_token ctx kwd_table;
     tok_removing = removing_token kwd_table; tok_match = tok_match;
     tok_text = text; tok_comm = None}
  in
  glexr := glex; glex
;;
