(* camlp5r *)
(* token_regexps.ml,v *)

#load "pa_extend.cmo";

open Asttools ;
open Brzozowski ;

module PatternBaseToken = struct
  type t = [ CLS of string | SPCL of string ] ;
  value hash = Hashtbl.hash;
  value print = fun [
      SPCL s -> Printf.sprintf "\"%s\"" (String.escaped s)
    | CLS ty -> Printf.sprintf "%s" ty
    ]
  ;
  value compare t1 t2 = match (t1, t2) with [
    (CLS s1, CLS s2) -> String.compare s1 s2
  | (SPCL s1, SPCL s2) -> String.compare s1 s2
  | (CLS _, SPCL _) -> -1
  | (SPCL _, CLS _) -> 1
  ]
  ;                            
  value equal t1 t2 = 0 = compare t1 t2 ;
end ;
module PatternRegexp = Regexp(PatternBaseToken) ;
module PSyn = RESyntax(PatternBaseToken)(PatternRegexp) ;

module Compile(R : sig value rex : PatternRegexp.regexp ;
                       value extra : list PatternBaseToken.t ;
                   end) = struct
  value toks = (PatternRegexp.tokens R.rex @ R.extra)
               |> sort PatternBaseToken.compare
               |> ListAux.uniq PatternBaseToken.compare ;
  module PatternToken = struct
    include PatternBaseToken ;
    value foreach f = do {
      List.iter f toks ;
      f (CLS "EOI")
    }
    ;
  end ;
  module BEval = Eval(PatternToken)(PatternRegexp) ;
  value dfa = BEval.dfa R.rex ;
  value exec input = BEval.exec dfa input ;
end
;

value compile rex =
  let module C = Compile(struct value rex = rex ; value extra = [] ; end) in
  C.exec
;

value convert_token =
  let open PatternBaseToken in
  fun [
      ("",s) -> Some (SPCL s)
    | ("ANTIQUOT", s) -> s |> Plexer.parse_antiquot |> option_map fst |> option_map (fun s -> SPCL s)
    | ("ANTIQUOT_LOC", s) -> s |> Plexer.parse_antiloc |> option_map snd3 |> option_map (fun s -> SPCL s)
    | (s, _) -> Some (CLS s)
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
  List.fold_left PSyn.(fun e1 e2 -> e1 @@ e2) (List.hd l) (List.tl l)
;

type astre = [
  Special of string
| Class of string
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
  let open PatternBaseToken in
  let rec convrec env = fun [
        Special x -> PSyn.token (SPCL (Scanf.unescaped x))
      | Class x -> PSyn.token (CLS (Scanf.unescaped x))
      | DISJ l -> PSyn.disjunction (List.map (convrec env) l)
      | CONJ l -> PSyn.conjunction (List.map (convrec env) l)
      | CONC l -> concatenation (List.map (convrec env) l)
      | STAR x -> PSyn.star (convrec env x)
      | NEG x -> PSyn.neg (convrec env x)
      | EPS -> PSyn.epsilon
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
    [ [ x = STRING -> Special x
      | x = UIDENT -> Class x
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
