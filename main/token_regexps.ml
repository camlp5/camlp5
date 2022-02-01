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

module Compile(R : sig value rex : StringRegexp.regexp ; end) = struct
  value toks = StringRegexp.tokens R.rex ;
  module StringToken = struct
    include StringBaseToken ;
    value foreach f = do {
      List.iter f toks ;
      f "EOI" 
    }
    ;
  end ;
  module BEval = Eval(StringToken)(StringRegexp) ;
  value dfa = BEval.dfa R.rex ;
  value exec input = BEval.exec dfa input ;
end
;

value compile rex =
  let module C = Compile(struct value rex = rex ; end) in
  C.exec
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
| LETIN of string and astre and astre
| ID of string
]
;

value conv x =
  let rec convrec env = fun [
        TOK x -> SBSyn.token (Scanf.unescaped x)
      | DISJ l -> SBSyn.disjunction (List.map (convrec env) l)
      | CONJ l -> SBSyn.conjunction (List.map (convrec env) l)
      | CONC l -> concatenation (List.map (convrec env) l)
      | STAR x -> SBSyn.star (convrec env x)
      | NEG x -> SBSyn.neg (convrec env x)
      | EPS -> SBSyn.epsilon
      | LETIN s e1 e2 ->
         convrec [(s,convrec env e1) :: env] e2
      | ID s -> match List.assoc s env with [
                    exception Not_found -> failwith Fmt.(str "Token_regexps.conv: unrecognized ID: %s" s)
                            | e -> e
                  ]
      ]
  in convrec [] x
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
      | "let" ; s=LIDENT ; "=" ; re1 = e5 ; "in" ; re2 = e5 -> LETIN s re1 re2
      | x = LIDENT -> ID x
      ]
    ]
  ;
END;


value parse s =
  try
    Grammar.Entry.parse e (Stream.of_string s)
  with [
      Ploc.Exc loc exc as exc0 -> do { Fmt.(pf stderr "Fatal error in Token_regexps.parse(%a): %s: %a\n"
                                              Dump.string s (Ploc.string_of_location loc) exn exc) ;
                                       raise exc0 }
    ]
;
