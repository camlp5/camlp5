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

value rec ident =
  lexer
  [ [ 'A'-'Z' | 'a'-'z' | '0'-'9' | '_' | ''' ] ident! | ]
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

value raw_string_starter = lexer [
  delim ["|"/ -> True | -> False]
| -> False
]
;

value raw_string_starter_p strm = raw_string_starter $empty strm ;

value simplest_raw_string_starter = lexer [
  delim [ "|"/ -> True | -> False ]
| "|"/ -> True
| -> False
]
;

value simplest_raw_string_starter_p strm = simplest_raw_string_starter $empty strm ;

end ;

module MutStream = struct
  include Stream ;
  type t 'a = Stream.t 'a constraint 'a = char ;
end ;

module Imm = RawString(ImmutStream) ;
module Mut = RawString(MutStream) ;

value rec rawstring1 delimtok (ofs, delim) = lexer [
  _ as c when (String.get delim ofs = c && ofs+1 = String.length delim) ->
    let s = $buf in
    let slen = String.length s in
    (delimtok, String.sub s 0 (slen - (String.length delim)))

| _ as c when (String.get delim ofs = c) (rawstring1 delimtok (ofs+1, delim))

| _ as c when (String.get delim ofs <> c && String.get delim 0 = c) (rawstring1 delimtok (1,delim))

| _ as c when (String.get delim ofs <> c && String.get delim 0 <> c) (rawstring1 delimtok (0,delim))
]
;

value zerobuf f buf strm =
  f $empty strm
;

value rec rawstring0 = lexer [
  '|' (zerobuf (rawstring1 $buf (0, "|" ^ $buf ^ "}")))
| ['a'-'z'|'_'] rawstring0
]
;

value keyword_or_rawstring simplest_raw_strings buf strm =
  let pred =
    if simplest_raw_strings then
      Imm.simplest_raw_string_starter_p
    else
      Imm.raw_string_starter_p in
  if not (pred (ImmutStream.wrap strm)) then
    (parser [
         [: `'|' when not simplest_raw_strings :] -> ("", "{|")
       | [: :] -> ("", "{")
       ]) strm
  else
    let (_,s) = rawstring0 $empty strm in
    ("RAWSTRING", String.escaped s)
;

value rec extattrident =
  lexer
  [ ident [ "." extattrident | ] ]
;

value quoted_extension1 extid buf strm =
  let (delim, s) = rawstring0 $empty strm in
  ("QUOTEDEXTENSION", extid^":"^(String.escaped s))
;

value quoted_extension0 extid =
  lexer
  [ ws (zerobuf (quoted_extension1 extid))
  | (zerobuf (quoted_extension1 extid))
  ]
;

value quoted_extension =
  lexer [
    extattrident (zerobuf (quoted_extension0 $buf))
  ]
;

value rec token simplest_raw_strings = lexer [
  ws (token simplest_raw_strings)
| "{%"/ (zerobuf quoted_extension)
| '{' / (keyword_or_rawstring simplest_raw_strings)
]
;

value pa0 pafun s =
  s |> Stream.of_string |> pafun LB.empty ;

value pa_string pafun s =
  s |> pa0 pafun |> LB.get ;

value imm_pa0 pafun s =
  s |> ImmutStream.of_string |> pafun LB.empty ;

value imm_pred pred s =
  s |> ImmutStream.of_string |> pred ;

value imm_pa_string pafun s =
  s |> imm_pa0 pafun |> LB.get ;

value suite = "pa_lexer" >::: [
  "simplest" >:: (fun [ _ -> do {
    assert_equal True (imm_pred Imm.raw_string_starter_p "bar|foo||bar}")
  ; assert_equal False (imm_pred Imm.raw_string_starter_p "|foo||}")
  ; assert_equal True (imm_pred Imm.simplest_raw_string_starter_p "|foo||}")
  ; assert_equal True (imm_pred Imm.simplest_raw_string_starter_p "bar|foo||bar}")

  ; assert_equal ("RAWSTRING","foo") (pa0 (token True) "{|foo|}")
  ; assert_equal ("RAWSTRING","") (pa0 (token True) "{||}")
  ; assert_equal ("","{|") (pa0 (token False) "{|foo|}")
  ; assert_equal ("","{") (pa0 (token False) "{foo")
  ; assert_equal ("RAWSTRING","foo") (pa0 (token True) "{bar|foo|bar}")
  ; assert_equal ("RAWSTRING","foo") (pa0 (token False) "{bar|foo|bar}")
  ; assert_equal ("RAWSTRING","foo|bar") (pa0 (token True)  "{bar|foo|bar|bar}")
  ; assert_equal ("RAWSTRING","foo|bar") (pa0 (token False)  "{bar|foo|bar|bar}")

  ; assert_equal ("QUOTEDEXTENSION","bar:foo") (pa0 (token True) "{%bar|foo|}")
  ; assert_equal ("QUOTEDEXTENSION","bar:foo") (pa0 (token True) "{%bar bar|foo|bar}")
  ; assert_equal ("QUOTEDEXTENSION","bar.buzz.goo:foo") (pa0 (token True) "{%bar.buzz.goo bar|foo|bar}")

  }])
]
;

value _ = 
if not Sys.interactive.val then
  run_test_tt_main suite
else ()
;
