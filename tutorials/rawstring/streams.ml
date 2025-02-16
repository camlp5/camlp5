(* camlp5r *)
(* streams.ml,v *)

open OUnit2;
open OUnitTest;

module LB = Plexing.Lexbuf ;

value rec ws =
  lexer
  [ [' '/ | '\t'/ | '\n'/] [ ws | ]
  ]
;
value ws_question = lexer [
  ws
|
]
;

module type SIMPLEST_STREAM = sig
  exception Failure ;
  exception Error of string ;
  type t 'a = 'b constraint 'a = char ;
  value peek : t 'a -> option 'a ;
  value junk : t 'a -> unit ;
  value npeek : int -> t 'a -> list 'a ;
  value of_string : string -> t char ;
end ;

module ImmutStream = struct
  exception Failure = Stream.Failure ;
  exception Error = Stream.Error ;
  type t 'a = { ofs : mutable int ; strm : Stream.t 'a } constraint 'a = char ;

  value wrap strm = { ofs = 0 ; strm =strm } ;

  value peek strm =
    let l = Stream.npeek (strm.ofs+1) strm.strm in
    if List.length l < strm.ofs+1 then
      None
    else Some List.(hd (rev l)) ;

  value junk strm = strm.ofs := 1 + strm.ofs ;

  value rec nthtail l = fun [
    0 -> l
  | n -> nthtail (List.tl l) (n-1)
  ]
  ;

  value npeek n strm =
    let l = Stream.npeek (strm.ofs + n) strm.strm in
    let llen = List.length l in
    if llen < strm.ofs then []
    else nthtail l strm.ofs
  ;

  value of_string s = s |> Stream.of_string |> wrap ;

end ;

module RawString(S : SIMPLEST_STREAM) = struct
module Stream = S ;
value delim_char = lexer [
  'a'-'z'/
| '_'/
]
;

value rec delim = lexer [
  delim_char [ delim | ]
]
;

value raw_string_starter_p = lexer [
  delim "|"/ -> True
| -> False
]
;

value simplest_raw_string_starter_p = lexer [
  delim "|"/ -> True
| "|"/ -> True
| -> False
]
;



end ;

module MutStream = struct
  include Stream ;
  type t 'a = Stream.t 'a constraint 'a = char ;
end ;

module Imm = RawString(ImmutStream) ;
module Mut = RawString(MutStream) ;

module Manual = struct

value rec last = fun [
    [] -> failwith "last"
  | [x] -> x
  | [x::l] -> last l
]
;
value stream_peek_nth n strm =
  let l = Stream.npeek n strm in
  if List.length l = n then
    Some (last l)
  else None
;

value raw_string_starter_p simplest_raw_strings strm =
  let rec predrec n =
    match stream_peek_nth n strm with
      [ None -> False
      | Some ('a'..'z' | '_') ->
         predrec (n+1)
      | Some '|' when simplest_raw_strings || n > 1 -> True
      | Some _ -> False ]
  in predrec 1
;

value rec rawstring1 delimtok (ofs, delim) buf =
  parser [
      [: `c  when String.get delim ofs = c && ofs+1 = String.length delim :] ->
      let buf = $add c in
      let s = $buf in
      let slen = String.length s in
      (delimtok, String.sub s 0 (slen - (String.length delim)))

    | [: `c when String.get delim ofs = c ; strm :] ->
       rawstring1 delimtok (ofs+1, delim) ($add c) strm

    | [: `c when String.get delim ofs <> c && String.get delim 0 = c ; strm :] ->
      rawstring1 delimtok (1,delim) ($add c) strm

    | [: `c when String.get delim ofs <> c && String.get delim 0 <> c ; strm :] ->
      rawstring1 delimtok (0,delim) ($add c) strm
    ]
;

value start_rawstring1 delimtok (ofs, delim) _ strm =
  rawstring1 delimtok (ofs, delim) $empty strm
;

value rec rawstring0 = lexer [
  '|' (start_rawstring1 $buf (0, "|" ^ $buf ^ "}"))
| ['a'-'z'|'_'] rawstring0
]
;

end ;

open Manual ;
value rec token = lexer [
  ws token
| "{"/ rawstring0
]
;

value pa0 pafun s =
  s |> Stream.of_string |> pafun LB.empty ;

value pa_string pafun s =
  s |> pa0 pafun |> LB.get ;

value imm_pa0 pafun s =
  s |> ImmutStream.of_string |> pafun LB.empty ;

value imm_pa_string pafun s =
  s |> imm_pa0 pafun |> LB.get ;

value suite = "pa_lexer" >::: [
  "simplest" >:: (fun [ _ -> do {
    assert_equal "" (pa_string ws_question "")
  ; assert_equal ("","foo") (pa0 token "{|foo|}")
  ; assert_equal True (imm_pa0 Imm.raw_string_starter_p "bar|foo||bar}")
  ; assert_equal True (imm_pa0 Imm.simplest_raw_string_starter_p "|foo||}")
  ; assert_equal ("bar","foo") (pa0 token "{bar|foo|bar}")
  ; assert_equal ("bar","foo|bar") (pa0 token "{bar|foo|bar|bar}")
  }])
]
;

value _ = 
if not Sys.interactive.val then
  run_test_tt_main suite
else ()
;
