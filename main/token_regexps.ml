(* camlp5r *)
(* token_regexps.ml,v *)

#load "pa_extend.cmo";

open Asttools ;
open Brzozowski ;

module StringBaseToken = struct
  include String ;
  value hash = Hashtbl.hash;
  value print s =
    Printf.sprintf "\"%s\"" (String.escaped s) ;
end ;
module StringRegexp = Regexp(StringBaseToken) ;
module SBSyn = RESyntax(StringBaseToken)(StringRegexp) ;

value compile rex =
  let toks = StringRegexp.tokens rex in
  let module StringToken = struct
      include StringBaseToken ;
      value foreach f = do {
        List.iter f toks ;
        f "EOI" 
      }
      ;
      end in
  let module BEval = Eval(StringToken)(StringRegexp) in
  let dfa = BEval.dfa rex in
  fun input -> BEval.exec dfa input
;

value convert_token = fun [
      ("",s) -> Some s
    | ("ANTIQUOT", s) -> s |> Plexer.parse_antiquot |> option_map fst
    | ("ANTIQUOT_LOC", s) -> s |> Plexer.parse_antiloc |> option_map snd3
    | (s, _) -> Some s
]
;

value nondestructive_token_stream_to_string_seq ~{convert} strm =
  let rec trec ofs () =
    let l = Stream.npeek ofs strm in
    if List.length l = ofs then
      let tok = fst (sep_last l) in
      match convert tok with [
          None -> Seq.Nil
        | Some s -> Seq.Cons s (trec (ofs+1))
        ]
    else Seq.Nil
  in trec 1
;

value check_regexp ?{convert=convert_token} rex =
  let e = compile rex in
  fun strm ->
  match e (nondestructive_token_stream_to_string_seq ~{convert=convert} strm) with [
    None -> False
  | Some _ -> True
  ]
;

value g = Grammar.gcreate (Plexer.gmake ());
value e = Grammar.Entry.create g "regexp";

value concatenation l =
  List.fold_left SBSyn.(fun e1 e2 -> e1 @@ e2) (List.hd l) (List.tl l)
;

type astre = [
  TOK of string
| DISJ of list astre
| CONJ of list astre
| CONC of list astre
| STAR of astre
| NEG of astre
| EPS
]
;

value rec conv = fun [
    TOK x -> SBSyn.token (Scanf.unescaped x)
  | DISJ l -> SBSyn.disjunction (List.map conv l)
  | CONJ l -> SBSyn.conjunction (List.map conv l)
  | CONC l -> concatenation (List.map conv l)
  | STAR x -> SBSyn.star (conv x)
  | NEG x -> SBSyn.neg (conv x)
  | EPS -> SBSyn.epsilon
]
;

EXTEND
  GLOBAL: e ;
  e: [ [ x = e5 -> conv x ] ] ;
  e5: [ [ l = LIST1 e4 SEP "|" -> DISJ l ] ] ;

  e4: [ [ l = LIST1 e3 SEP "&" -> CONJ l ] ] ;

  e3: [ [ l = LIST1 e2 -> CONC l ] ] ;

  e2: [ [ "~"; x = e1 -> NEG x | x = e1 -> x ] ] ;

  e1: [ [ x = e0; "*" -> STAR x | x = e0 -> x ] ] ;

  e0:
    [ [ x = STRING -> TOK x
      | "("; x = e5; ")" -> x
      | "eps" -> EPS
      ]
    ]
  ;
END;


value parse s =
  Grammar.Entry.parse e (Stream.of_string s)
;
