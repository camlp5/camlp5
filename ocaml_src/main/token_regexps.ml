(* camlp5r *)
(* token_regexps.ml,v *)

(* #load "pa_extend.cmo" *)

open Asttools;;
open Brzozowski;;

module StringBaseToken =
  struct
    include String;;
    let hash = Hashtbl.hash;;
    let print s = Printf.sprintf "\"%s\"" (String.escaped s);;
  end
;;
module StringRegexp = Regexp (StringBaseToken);;
module SBSyn = RESyntax (StringBaseToken) (StringRegexp);;

let compile rex =
  let toks = StringRegexp.tokens rex in
  let module StringToken =
    struct
      include StringBaseToken;;
      let foreach f = List.iter f toks; f "EOI";;
    end
  in
  let module BEval = Eval (StringToken) (StringRegexp) in
  let dfa = BEval.dfa rex in fun input -> BEval.exec dfa input
;;

let convert_token =
  function
    "", s -> Some s
  | "ANTIQUOT", s -> (s |> Plexer.parse_antiquot) |> option_map fst
  | "ANTIQUOT_LOC", s -> (s |> Plexer.parse_antiloc) |> option_map snd3
  | s, _ -> Some s
;;

let nondestructive_token_stream_to_string_seq ~convert strm =
  let rec trec ofs () =
    let l = Stream.npeek ofs strm in
    if List.length l = ofs then
      let tok = fst (sep_last l) in
      match convert tok with
        None -> Seq.Nil
      | Some s -> Seq.Cons (s, trec (ofs + 1))
    else Seq.Nil
  in
  trec 1
;;

let check_regexp ?(convert = convert_token) rex =
  let e = compile rex in
  fun strm ->
    match
      e (nondestructive_token_stream_to_string_seq ~convert:convert strm)
    with
      None -> false
    | Some _ -> true
;;

let g = Grammar.gcreate (Plexer.gmake ());;
let e = Grammar.Entry.create g "regexp";;

let concatenation l =
  List.fold_left SBSyn.(fun e1 e2 -> e1 @@ e2) (List.hd l) (List.tl l)
;;

type astre =
    TOK of string
  | DISJ of astre list
  | CONJ of astre list
  | CONC of astre list
  | STAR of astre
  | NEG of astre
  | EPS
  | LETIN of string * astre * astre
  | ID of string
;;

let conv x =
  let rec convrec env =
    function
      TOK x -> SBSyn.token (Scanf.unescaped x)
    | DISJ l -> SBSyn.disjunction (List.map (convrec env) l)
    | CONJ l -> SBSyn.conjunction (List.map (convrec env) l)
    | CONC l -> concatenation (List.map (convrec env) l)
    | STAR x -> SBSyn.star (convrec env x)
    | NEG x -> SBSyn.neg (convrec env x)
    | EPS -> SBSyn.epsilon
    | LETIN (s, e1, e2) -> convrec ((s, convrec env e1) :: env) e2
    | ID s ->
        match List.assoc s env with
          exception Not_found ->
            failwith Fmt.(str "Token_regexps.conv: unrecognized ID: %s" s)
        | e -> e
  in
  convrec [] x
;;

Grammar.safe_extend
  (let _ = (e : 'e Grammar.Entry.e) in
   let grammar_entry_create s =
     Grammar.create_local_entry (Grammar.of_entry e) s
   in
   let e5 : 'e5 Grammar.Entry.e = grammar_entry_create "e5"
   and e4 : 'e4 Grammar.Entry.e = grammar_entry_create "e4"
   and e3 : 'e3 Grammar.Entry.e = grammar_entry_create "e3"
   and e2 : 'e2 Grammar.Entry.e = grammar_entry_create "e2"
   and e1 : 'e1 Grammar.Entry.e = grammar_entry_create "e1"
   and e0 : 'e0 Grammar.Entry.e = grammar_entry_create "e0" in
   [Grammar.extension (e : 'e Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_nterm (e5 : 'e5 Grammar.Entry.e)),
           "194fe98d", (fun (x : 'e5) (loc : Ploc.t) -> (conv x : 'e)))]];
    Grammar.extension (e5 : 'e5 Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_list1sep (Grammar.s_nterm (e4 : 'e4 Grammar.Entry.e))
                (Grammar.s_token ("", "|")) false),
           "194fe98d",
           (fun (l : 'e4 list) (loc : Ploc.t) -> (DISJ l : 'e5)))]];
    Grammar.extension (e4 : 'e4 Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_list1sep (Grammar.s_nterm (e3 : 'e3 Grammar.Entry.e))
                (Grammar.s_token ("", "&")) false),
           "194fe98d",
           (fun (l : 'e3 list) (loc : Ploc.t) -> (CONJ l : 'e4)))]];
    Grammar.extension (e3 : 'e3 Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_list1 (Grammar.s_nterm (e2 : 'e2 Grammar.Entry.e))),
           "194fe98d",
           (fun (l : 'e2 list) (loc : Ploc.t) -> (CONC l : 'e3)))]];
    Grammar.extension (e2 : 'e2 Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_nterm (e1 : 'e1 Grammar.Entry.e)),
           "194fe98d", (fun (x : 'e1) (loc : Ploc.t) -> (x : 'e2)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "~")))
             (Grammar.s_nterm (e1 : 'e1 Grammar.Entry.e)),
           "194fe98d", (fun (x : 'e1) _ (loc : Ploc.t) -> (NEG x : 'e2)))]];
    Grammar.extension (e1 : 'e1 Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_nterm (e0 : 'e0 Grammar.Entry.e)),
           "194fe98d", (fun (x : 'e0) (loc : Ploc.t) -> (x : 'e1)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop
                (Grammar.s_nterm (e0 : 'e0 Grammar.Entry.e)))
             (Grammar.s_token ("", "*")),
           "194fe98d", (fun _ (x : 'e0) (loc : Ploc.t) -> (STAR x : 'e1)))]];
    Grammar.extension (e0 : 'e0 Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next Grammar.r_stop (Grammar.s_token ("LIDENT", "")),
           "194fe98d", (fun (x : string) (loc : Ploc.t) -> (ID x : 'e0)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("", "let")))
                         (Grammar.s_token ("LIDENT", "")))
                      (Grammar.s_token ("", "=")))
                   (Grammar.s_nterm (e5 : 'e5 Grammar.Entry.e)))
                (Grammar.s_token ("", "in")))
             (Grammar.s_nterm (e5 : 'e5 Grammar.Entry.e)),
           "194fe98d",
           (fun (re2 : 'e5) _ (re1 : 'e5) _ (s : string) _ (loc : Ploc.t) ->
              (LETIN (s, re1, re2) : 'e0)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "eps")),
           "194fe98d", (fun _ (loc : Ploc.t) -> (EPS : 'e0)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "(")))
                (Grammar.s_nterm (e5 : 'e5 Grammar.Entry.e)))
             (Grammar.s_token ("", ")")),
           "194fe98d", (fun _ (x : 'e5) _ (loc : Ploc.t) -> (x : 'e0)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop (Grammar.s_token ("STRING", "")),
           "194fe98d", (fun (x : string) (loc : Ploc.t) -> (TOK x : 'e0)))]]]);;


let parse s =
  try Grammar.Entry.parse e (Stream.of_string s) with
    Ploc.Exc (loc, exc) as exc0 ->
      Fmt.
      (pf stderr "Fatal error in Token_regexps.parse(%a): %s: %a\n"
        Dump.string s (Ploc.string_of_location loc) exn exc);
      raise exc0
;;
