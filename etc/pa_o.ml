(* camlp5r *)
(* pa_o.ml,v *)
(* Copyright (c) INRIA 2007-2017 *)

#load "pa_extend.cmo";
#load "q_MLast.cmo";
#load "pa_macro.cmo";
#load "pa_macro_gram.cmo";
#load "q_regexp.cmo";

open Asttools;
open Pcaml;
open Mlsyntax.Original;

Pcaml.syntax_name.val := "OCaml";
Pcaml.no_constructors_arity.val := True;

do {
  let odfa = Plexer.dollar_for_antiquotation.val in
  let osrs = Plexer.simplest_raw_strings.val in
  Plexer.dollar_for_antiquotation.val := False;
  Plexer.simplest_raw_strings.val := True;
  Plexer.utf8_lexing.val := True;
  Grammar.Unsafe.gram_reinit gram (Plexer.gmake ());
  Plexer.dollar_for_antiquotation.val := odfa;
  Plexer.simplest_raw_strings.val := osrs ;
  Grammar.Unsafe.clear_entry attribute_body;
  Grammar.Unsafe.clear_entry interf;
  Grammar.Unsafe.clear_entry implem;
  Grammar.Unsafe.clear_entry top_phrase;
  Grammar.Unsafe.clear_entry use_file;
  Grammar.Unsafe.clear_entry module_type;
  Grammar.Unsafe.clear_entry module_expr;
  Grammar.Unsafe.clear_entry longident;
  Grammar.Unsafe.clear_entry longident_lident;
  Grammar.Unsafe.clear_entry extended_longident;
  Grammar.Unsafe.clear_entry sig_item;
  Grammar.Unsafe.clear_entry str_item;
  Grammar.Unsafe.clear_entry signature;
  Grammar.Unsafe.clear_entry structure;
  Grammar.Unsafe.clear_entry expr;
  Grammar.Unsafe.clear_entry patt;
  Grammar.Unsafe.clear_entry ctyp;
  Grammar.Unsafe.clear_entry let_binding;
  Grammar.Unsafe.clear_entry type_decl;
  Grammar.Unsafe.clear_entry type_extension;
  Grammar.Unsafe.clear_entry extension_constructor;
  Grammar.Unsafe.clear_entry constructor_declaration;
  Grammar.Unsafe.clear_entry label_declaration;
  Grammar.Unsafe.clear_entry match_case;
  Grammar.Unsafe.clear_entry with_constr;
  Grammar.Unsafe.clear_entry poly_variant;
  Grammar.Unsafe.clear_entry class_type;
  Grammar.Unsafe.clear_entry class_expr;
  Grammar.Unsafe.clear_entry class_expr_simple;
  Grammar.Unsafe.clear_entry alg_attribute;
  Grammar.Unsafe.clear_entry alg_attributes;
  Grammar.Unsafe.clear_entry ext_attributes;
  Grammar.Unsafe.clear_entry class_sig_item;
  Grammar.Unsafe.clear_entry class_str_item
};

Pcaml.parse_interf.val := Grammar.Entry.parse interf;
Pcaml.parse_implem.val := Grammar.Entry.parse implem;

value error loc msg = Ploc.raise loc (Failure msg);

value mklistexp loc last =
  loop True where rec loop top =
    fun
    [ [] ->
        match last with
        [ Some e -> e
        | None -> <:expr< [] >> ]
    | [e1 :: el] ->
        let loc =
          if top then loc else Ploc.encl (MLast.loc_of_expr e1) loc
        in
        <:expr< [$e1$ :: $loop False el$] >> ]
;

value mklistpat loc last =
  loop True where rec loop top =
    fun
    [ [] ->
        match last with
        [ Some p -> p
        | None -> <:patt< [] >> ]
    | [p1 :: pl] ->
        let loc =
          if top then loc else Ploc.encl (MLast.loc_of_patt p1) loc
        in
        <:patt< [$p1$ :: $loop False pl$] >> ]
;

open Token_regexps ;
module Interp(R : sig value rexs : string ;
                     value extra : list PatternBaseToken.t ;
                     value name : string ;
                 end) = struct
  value rex = parse R.rexs ;
  module C = Compile(struct value rex = rex ; value extra = R.extra ; end) ;
  value pred strm = check_regexp rex strm ;
  value check_f strm = if pred strm then () else raise Stream.Failure ;
  value check_not_f strm = if not(pred strm) then () else raise Stream.Failure ;
  value check = Grammar.Entry.of_parser Pcaml.gram ("check_"^R.name) check_f ;
  value check_not = Grammar.Entry.of_parser Pcaml.gram ("check_not_"^R.name) check_not_f ;
end
;
module Compiled(R : sig value rawcheck :  Stream.t (string * string) -> option int ;
                        value name : string ;
                 end) = struct
  value rawcheck = R.rawcheck ;
  value pred strm = match rawcheck strm with [ None -> False | Some _ -> True ] ;
  value check_f strm = if pred strm then () else raise Stream.Failure ;
  value check_not_f strm = if not(pred strm) then () else raise Stream.Failure ;
  value check = Grammar.Entry.of_parser Pcaml.gram ("check_"^R.name) check_f ;
  value check_not = Grammar.Entry.of_parser Pcaml.gram ("check_not_"^R.name) check_not_f ;
end
;

module CheckAdditiveRparen = Compiled(struct
  value rawcheck = <:regexp< ("+" | "-" | "+." | "-." | "+=") ")" >> ;
  value name = "additive_rparen" ;
                             end) ;
value check_additive_rparen = CheckAdditiveRparen.check ;

module CheckBangCloseParen = Compiled(struct
  value rawcheck = <:regexp< "!" ")" >> ;
  value name = "bang_close_paren" ;
                             end) ;
value check_bang_closeparen = CheckBangCloseParen.check ;

value operator_rparen = Grammar.Entry.create gram "operator_rparen";

value check_not_part_of_patt_f strm =
  let matchers = [
    (2, fun [ [("LIDENT", _); tok :: _] -> Some tok | _ -> None ])
  ; (4, fun [ [("", "("); ((""|"LETOP"|"DOTOP"|"HASHOP"|"INFIXOP0"|"INFIXOP1"|"INFIXOP2"|"INFIXOP3"|"INFIXOP4"|"PREFIXOP"), s); ("", ")"); tok :: _] when is_special_op s -> Some tok | _ -> None ])
  ; (6, fun [
              [("", "("); (""|"DOTOP", s); ("", "("); ("", ")"); ("", ")"); tok :: _] when is_special_op s -> Some tok
            | [("", "("); (""|"DOTOP", s); ("", "{"); ("", "}"); ("", ")"); tok :: _] when is_special_op s -> Some tok
            | [("", "("); (""|"DOTOP", s); ("", "["); ("", "]"); ("", ")"); tok :: _] when is_special_op s -> Some tok
            | _ -> None ])
  ; (7, fun [
              [("", "("); (""|"DOTOP", s); ("", "("); ("", ")"); ("", "<-"); ("", ")"); tok :: _] when is_special_op s -> Some tok
            | [("", "("); (""|"DOTOP", s); ("", "{"); ("", "}"); ("", "<-"); ("", ")"); tok :: _] when is_special_op s -> Some tok
            | [("", "("); (""|"DOTOP", s); ("", "["); ("", "]"); ("", "<-"); ("", ")"); tok :: _] when is_special_op s -> Some tok
            | _ -> None ])
  ; (8, fun [
              [("", "("); (""|"DOTOP", s); ("", "("); ("", ";"); ("", ".."); ("", ")"); ("", ")"); tok :: _] when is_special_op s -> Some tok
            | [("", "("); (""|"DOTOP", s); ("", "{"); ("", ";"); ("", ".."); ("", "}"); ("", ")"); tok :: _] when is_special_op s -> Some tok
            | [("", "("); (""|"DOTOP", s); ("", "["); ("", ";"); ("", ".."); ("", "]"); ("", ")"); tok :: _] when is_special_op s -> Some tok
            | _ -> None ])
  ; (9, fun [
              [("", "("); (""|"DOTOP", s); ("", "("); ("", ";"); ("", ".."); ("", ")"); ("", "<-"); ("", ")"); tok :: _] when is_special_op s -> Some tok
            | [("", "("); (""|"DOTOP", s); ("", "{"); ("", ";"); ("", ".."); ("", "}"); ("", "<-"); ("", ")"); tok :: _] when is_special_op s -> Some tok
            | [("", "("); (""|"DOTOP", s); ("", "["); ("", ";"); ("", ".."); ("", "]"); ("", "<-"); ("", ")"); tok :: _] when is_special_op s -> Some tok
            | _ -> None ])

  ] in
  let rec crec i = fun [
    [ (n,_) :: _ ] as ml when i < n ->
      let l = stream_npeek i strm in
      let last = fst (sep_last l) in
      if last = ("EOI","") || last = ("",";;") then raise Stream.Failure
      else crec (i+1) ml
  | [ (n, f) :: t ] ->
      match f (stream_npeek n strm) with [
        None -> crec (i+1) t
      | Some tok -> tok
     ]
  | [] -> raise Stream.Failure
  ] in
  let tok = crec 1 matchers in
  match tok with
    [ ("", "," | "as" | "|" | "::") -> raise Stream.Failure
    | _ -> () ]
;

value check_not_part_of_patt =
  Grammar.Entry.of_parser gram "check_not_part_of_patt"
    check_not_part_of_patt_f
;

value test_constr_decl_f strm =
  match Stream.npeek 1 strm with
    [ [("UIDENT", _)] ->
      match Stream.npeek 2 strm with
        [ [_; ("", ".")] -> raise Stream.Failure
        | [_; ("", "(")] -> raise Stream.Failure
        | [_ :: _] -> ()
        | _ -> raise Stream.Failure ]
      | [("", ("true"|"false")) :: _] -> ()
      | [("", "|")] -> ()
      | [("", "[")] ->
        match Stream.npeek 2 strm with
          [ [_; ("", "]")] -> ()
          | _ -> raise Stream.Failure ]
        | _ -> raise Stream.Failure ]
;

value test_constr_decl =
  Grammar.Entry.of_parser gram "test_constr_decl"
    test_constr_decl_f
;

value stream_peek_nth n (strm : Stream.t (string * string)) =
  loop n (Stream.npeek n strm) where rec loop n =
    fun
    [ [] -> None
    | [x] -> if n == 1 then Some (x : (string * string)) else None
    | [_ :: l] -> loop (n - 1) l ]
;

(* horrible hack to be able to parse class_types *)

value test_ctyp_minusgreater =
  Grammar.Entry.of_parser gram "test_ctyp_minusgreater"
    (fun strm ->
       let rec skip_simple_ctyp n =
         match stream_peek_nth n strm with
         [ Some ("", "->") -> n
         | Some ("", "[" | "[<") ->
             skip_simple_ctyp (ignore_upto "]" (n + 1) + 1)
         | Some ("", "(") -> skip_simple_ctyp (ignore_upto ")" (n + 1) + 1)
         | Some
             ("",
              "as" | "'" | ":" | "*" | "." | "#" | "<" | ">" | ".." | ";" |
              "_") ->
             skip_simple_ctyp (n + 1)
         | Some ("QUESTIONIDENT" | "LIDENT" | "UIDENT", _) ->
             skip_simple_ctyp (n + 1)
         | Some _ | None -> raise Stream.Failure ]
       and ignore_upto end_kwd n =
         match stream_peek_nth n strm with
         [ Some ("", prm) when prm = end_kwd -> n
         | Some ("", "[" | "[<") ->
             ignore_upto end_kwd (ignore_upto "]" (n + 1) + 1)
         | Some ("", "(") -> ignore_upto end_kwd (ignore_upto ")" (n + 1) + 1)
         | Some _ -> ignore_upto end_kwd (n + 1)
         | None -> raise Stream.Failure ]
       in
       match Stream.peek strm with
       [ Some (("", "[") | ("LIDENT" | "UIDENT", _)) -> skip_simple_ctyp 1
       | Some ("", "object") -> raise Stream.Failure
       | _ -> 1 ])
;

value is_lbracket_f strm =
  match Stream.npeek 1 strm with [
    [("","[") ] -> True
  | _ -> False
  ]
;

value check_lbracket_f strm =
  if is_lbracket_f strm then () else raise Stream.Failure
;

value check_lbracket =
  Grammar.Entry.of_parser gram "check_lbracket"
    check_lbracket_f
;

value is_lbracketbar_f strm =
  match Stream.npeek 1 strm with [
    [("","[|") ] -> True
  | _ -> False
  ]
;

value check_lbracketbar_f strm =
  if is_lbracketbar_f strm then () else raise Stream.Failure
;

value check_lbracketbar =
  Grammar.Entry.of_parser gram "check_lbracketbar"
    check_lbracketbar_f
;


value is_lbrace_f strm =
  match Stream.npeek 1 strm with [
    [("","{") ] -> True
  | _ -> False
  ]
;

value check_lbrace_f strm =
  if is_lbrace_f strm then () else raise Stream.Failure
;

value check_lbrace =
  Grammar.Entry.of_parser gram "check_lbrace"
    check_lbrace_f
;

value is_lident_colon_f strm =
  match Stream.npeek 2 strm with [
    [("LIDENT",_) ; ("",":") :: _] -> True
  | _ -> False
  ]
;

value check_lident_colon_f strm =
  if is_lident_colon_f strm then () else raise Stream.Failure
;

value check_lident_colon =
  Grammar.Entry.of_parser gram "check_lident_colon"
    check_lident_colon_f
;

value check_not_lident_colon_f strm =
  if not (is_lident_colon_f strm) then () else raise Stream.Failure
;

value check_not_lident_colon =
  Grammar.Entry.of_parser gram "check_not_lident_colon"
    check_not_lident_colon_f
;

value test_label_eq =
  Grammar.Entry.of_parser gram "test_label_eq"
    (test 1 where rec test lev strm =
       match stream_peek_nth lev strm with
       [ Some (("UIDENT", _) | ("LIDENT", _) | ("", ".")) ->
           test (lev + 1) strm
       | Some ("ANTIQUOT_LOC", _) -> ()
       | Some ("", "=" | ";" | "}" | ":") -> ()
       | _ -> raise Stream.Failure ])
;

value test_typevar_list_dot =
  Grammar.Entry.of_parser gram "test_typevar_list_dot"
    (let rec test lev strm =
       match stream_peek_nth lev strm with
       [ Some ("", "'") -> test2 (lev + 1) strm
       | Some ("", ".") -> ()
       | _ -> raise Stream.Failure ]
     and test2 lev strm =
       match stream_peek_nth lev strm with
       [ Some ("UIDENT" | "LIDENT", _) -> test (lev + 1) strm
       | _ -> raise Stream.Failure ]
     in
     test 1)
;

value e_phony =
  Grammar.Entry.of_parser gram "e_phony"
    (parser [])
;
value p_phony =
  Grammar.Entry.of_parser gram "p_phony"
    (parser [])
;

value constr_arity = ref [("Some", 1); ("Match_Failure", 1)];

value rec is_expr_constr_call =
  fun
  [ <:expr< $longid:_$ >> -> True
  | <:expr< $e$ $_$ >> -> is_expr_constr_call e
  | _ -> False ]
;

value rec constr_expr_arity loc =
  fun
  [ <:expr< $uid:c$ >> | <:expr< $longid:_$ . $uid:c$ >> ->
      try List.assoc c constr_arity.val with [ Not_found -> 0 ]
  | _ -> 1 ]
;

value rec constr_patt_arity loc =
  fun
  [ <:patt< $uid:c$ >> ->
      try List.assoc c constr_arity.val with [ Not_found -> 0 ]

  | <:patt< $uid:_$ . $p$ >> -> constr_patt_arity loc p

  | <:patt< $longid:_$ . $uid:c$ >> ->
      try List.assoc c constr_arity.val with [ Not_found -> 0 ]
  | _ -> 1 ]
;

value get_seq =
  fun
  [ <:expr< do { $list:el$ } >> -> el
  | e -> [e] ]
;

value mem_tvar s tpl =
  List.exists (fun (t, _) -> Pcaml.unvala t = Some s) tpl
;

value choose_tvar tpl =
  let rec find_alpha v =
    let s = String.make 1 v in
    if mem_tvar s tpl then
      if v = 'z' then None else find_alpha (Char.chr (Char.code v + 1))
    else Some (String.make 1 v)
  in
  let rec make_n n =
    let v = "a" ^ string_of_int n in
    if mem_tvar v tpl then make_n (succ n) else v
  in
  match find_alpha 'a' with
  [ Some x -> x
  | None -> make_n 1 ]
;

value quotation_content s = do {
  loop 0 where rec loop i =
    if i = String.length s then ("", s)
    else if s.[i] = ':' || s.[i] = '@' then
      let i = i + 1 in
      (String.sub s 0 i, String.sub s i (String.length s - i))
    else loop (i + 1)
};

value concat_comm loc e =
  let loc =
    Ploc.with_comment loc
      (Ploc.comment loc ^ Ploc.comment (MLast.loc_of_expr e))
  in
  let floc =
    let first = ref True in
    fun loc1 ->
      if first.val then do {first.val := False; loc}
      else loc1
  in
  Reloc.expr floc 0 e
;

value rec expr_of_patt p =
  let loc = MLast.loc_of_patt p in
  match p with
  [ <:patt< $lid:x$ >> -> <:expr< $lid:x$ >>
  | <:patt< $uid:_$ . $p$ >> -> expr_of_patt p
  | _ -> Ploc.raise loc (Stream.Error "identifier expected") ]
;

value build_letop_binder loc letop b l e = do {
  let (argpat, argexp) =
    List.fold_left (fun (argpat, argexp) (andop, (pat, exp)) ->
        (<:patt< ( $argpat$, $pat$ ) >>, <:expr< $lid:andop$ $argexp$ $exp$ >>))
      b l in
  <:expr< $lid:letop$ $argexp$ (fun $argpat$ -> $e$) >>
  }
;

value is_let_exception_f strm =
  Stream.npeek 1 strm = [("","let")] &&
  match Stream.npeek 2 strm with
    [ [("", "let"); ("", "exception")] -> True
    | _ -> False ]
;

value check_let_exception_f strm =
  if is_let_exception_f strm then () else raise Stream.Failure
;

value check_let_exception =
  Grammar.Entry.of_parser gram "check_let_exception"
    check_let_exception_f
;
value is_let_not_exception_f strm =
  Stream.npeek 1 strm = [("","let")] &&
  match Stream.npeek 2 strm with
    [ [("", "let"); ("", "exception")] -> False
    | _ -> True ]
;


value check_let_not_exception_f strm =
  if is_let_not_exception_f strm then () else raise Stream.Failure
;

value check_let_not_exception =
  Grammar.Entry.of_parser gram "check_let_not_exception"
    check_let_not_exception_f
;

(* returns True if the stream is a type-decl, and not an extension.
   returns False if the stream is an extension and not a type-decl.
   Since a type-decl might not have an "=" (if it's a list of decls)
   the default is "type-decl".
*)
value word_keywordp s =
  let rec wrec = parser [
    [: `('a'..'z'|'A'..'Z'|'_'|'0'..'9') ; strm :] -> wrec strm
  | [: strm :] -> do { Stream.empty strm ; True }
  ] in
  let check = parser [
    [: `('a'..'z'|'A'..'Z'|'_') ; strm :] -> wrec strm
  | [:  :] -> False
  ] in
  try check (Stream.of_string s) && s <> "_"
  with Stream.Failure | (Stream.Error _) -> False
;

value is_type_decl_not_extension strm =
  let rec wrec n =
    match stream_peek_nth n strm with [
      None -> assert False
    | Some (
        ("","=")
      | ("",":=")
      | ("",";")
      | ("",";;")
      ) -> True
    | Some ("",s) when word_keywordp s -> True
    | Some ("EOI","") -> True
    | Some ("","+=") -> False
    | Some (
      ("",_)
      | ("UIDENT",_) | ("LIDENT",_) | ("GIDENT",_)
      | ("ANTIQUOT",_)
    ) -> wrec (n+1)
    | Some (a,b) -> raise (Stream.Error (Printf.sprintf "unexpected tokens in a type-decl/extension: (\"%s\",\"%s\")" a b))
 ]
  in wrec 1
;

value check_type_decl_f strm =
  if is_type_decl_not_extension strm then ()
  else raise Stream.Failure
;

value check_type_decl =
  Grammar.Entry.of_parser gram "check_type_decl"
    check_type_decl_f
;

value check_type_extension_f strm =
  if not (is_type_decl_not_extension strm) then ()
  else raise Stream.Failure
;

value check_type_extension =
  Grammar.Entry.of_parser gram "check_type_extension"
    check_type_extension_f
;

value check_module_alias_f = (fun strm ->
       match Stream.npeek 2 strm with
       [ [("UIDENT", _); ("", "=")] -> ()
       | _ -> raise Stream.Failure ])
;

value check_module_alias =
  Grammar.Entry.of_parser gram "check_module_alias"
    check_module_alias_f
;


value check_module_not_alias_f = (fun strm ->
       match Stream.npeek 2 strm with
       [ [("UIDENT", _); ("", "=")] -> raise Stream.Failure
       | _ -> () ])
;

value check_module_not_alias =
  Grammar.Entry.of_parser gram "check_module_not_alias"
    check_module_not_alias_f
;

value merge_left_auxiliary_attrs ~{nonterm_name} ~{left_name} ~{right_name} left_attrs right_attrs =
  match (left_attrs, right_attrs) with [
    (l1, Ploc.VaVal l2) -> Ploc.VaVal (l1@l2)
  | ([], (Ploc.VaAnt _)) -> right_attrs
  | _ -> failwith (Printf.sprintf "%s: cannot specify both %s AND %s antiquotation" nonterm_name left_name right_name)
  ]
;

value merge_right_auxiliary_attrs ~{nonterm_name} ~{left_name} ~{right_name} left_attrs right_attrs =
  match (left_attrs, right_attrs) with [
    (Ploc.VaVal l1, l2) -> Ploc.VaVal (l1@l2)
  | ((Ploc.VaAnt _), []) -> left_attrs
  | _ -> failwith (Printf.sprintf "%s: cannot specify both %s antiquotation AND %s" nonterm_name left_name right_name)
  ]
;

value check_dot_uid_f strm =
  let rec crec n =
    match stream_npeek n strm with [
      [(_, tok) :: _ ] when tok <> "." -> raise Stream.Failure
    | [("",".") ] -> crec (n+1)
    | [("",".") ; ("UIDENT",_)] -> ()
    | [("",".") ; ("ANTIQUOT_LOC",s)]
      when (match Plexer.parse_antiloc s with [ Some(_, ("uid"|"_uid"), _) -> True | _ -> False ]) -> ()
    | [("",".") ; ("","$")] -> crec (n+1)
    | [("",".") ; ("","$") ; ("LIDENT",("uid"|"_uid"))] -> crec (n+1)
    | [("",".") ; ("","$") ; ("LIDENT",("uid"|"_uid")) ; ("", ":")] -> ()
    | _ -> raise Stream.Failure
    ] in
  crec 1
;

value check_dot_uid =
  Grammar.Entry.of_parser gram "check_dot_uid"
    check_dot_uid_f
;

value is_new_type_extended strm =
  let rec isrec n =
    let l = stream_npeek n strm in
    if l = [] then False
    else match l with [
      [("","("); ("","type") :: l] ->
        match sep_last l with [
          (("",")"), l) ->
            l <> [] && List.for_all (fun [ ("LIDENT",_) -> True | _ -> False ]) l
        | (("LIDENT",_), _) -> isrec (n+1)
        | _ -> False
        ]
    | _ -> False
    ]
  in isrec 4
;

value check_new_type_extended_f strm =
  if is_new_type_extended strm then () else raise Stream.Failure
;

value check_new_type_extended =
  Grammar.Entry.of_parser gram "check_new_type_extended"
    check_new_type_extended_f
;

value check_not_new_type_extended_f strm =
  if not (is_new_type_extended strm) then () else raise Stream.Failure
;

value check_not_new_type_extended =
  Grammar.Entry.of_parser gram "check_not_new_type_extended"
    check_not_new_type_extended_f
;

value check_uident_coloneq_f strm =
  match stream_npeek 2 strm with [
    [("UIDENT",_) ; ("", ":=")] -> ()
  | [("ANTIQUOT",qs); ("", ":=")] when prefix_eq "uid:" qs || prefix_eq "_uid:" qs -> ()
  | _ -> raise Stream.Failure
  ]
;

value check_uident_coloneq =
  Grammar.Entry.of_parser gram "check_uident_coloneq"
    check_uident_coloneq_f
;

value check_colon_f strm =
  match stream_npeek 1 strm with [
    [("", ":")] -> ()
  | _ -> raise Stream.Failure
  ]
;

value check_colon =
  Grammar.Entry.of_parser gram "check_colon"
    check_colon_f
;

value check_not_colon_f strm =
  match stream_npeek 1 strm with [
    [("", ":")] -> raise Stream.Failure
  | _ -> ()
  ]
;

value check_not_colon =
  Grammar.Entry.of_parser gram "check_not_colon"
    check_not_colon_f
;

value check_and_or_in_f strm =
  match stream_npeek 1 strm with [
    [("", ("and"|"in"))] -> ()
  | _ -> raise Stream.Failure
  ]
;

value check_and_or_in =
  Grammar.Entry.of_parser gram "check_and_or_in"
    check_and_or_in_f
;

value uident_True_True_ = fun [
  "True" -> "True_"
| "False" -> "False_"
| x -> x
]
;

value make_string_extension loc s =
  let colonpos = String.index s ':' in
  let attrid = String.sub s 0 colonpos in
  let strpayload = String.sub s (colonpos+1) (String.length s - (colonpos+1)) in
  <:attribute_body< $attrid:(loc,attrid)$ $str:strpayload$ ; >>
;

value is_lparen_f strm =
  match Stream.npeek 1 strm with [
    [("","(")] -> True
  | _ -> False
  ]
;

value is_lparen_type_f strm =
  is_lparen_f strm &&
  match Stream.npeek 2 strm with [
    [("","(") ; ("","type")] -> True
  | _ -> False
  ]
;

value check_lparen_type_f strm =
  if is_lparen_type_f strm then () else raise Stream.Failure
;

value check_lparen_type =
  Grammar.Entry.of_parser gram "check_lparen_type"
    check_lparen_type_f
;

value is_type_binder_f strm = check_fsm type_binder_fsm strm ;

value check_type_binder_f strm =
  if is_type_binder_f strm then () else raise Stream.Failure
;

value check_type_binder =
  Grammar.Entry.of_parser gram "check_type_binder"
    check_type_binder_f
;

EXTEND
  GLOBAL: sig_item str_item ctyp patt expr module_type
    module_expr longident longident_lident extended_longident
    signature structure class_type class_expr class_expr_simple class_sig_item class_str_item
    let_binding type_decl type_extension extension_constructor
    constructor_declaration label_declaration
    match_case with_constr poly_variant
    attribute_body alg_attribute alg_attributes
    operator_rparen
    check_type_binder
    ext_attributes
    ;
  infix_operator0: [ [
      x = INFIXOP0 -> x
    | "!=" -> "!="
    | "<>" -> "<>"
    | "=" -> "="
    | "<" -> "<"
    | ">" -> ">"
    | "||" -> "||"
    | "or" -> "or"
    | "&" -> "&"
    | "&&" -> "&&"
    | "$" -> "$"
    ] ]
    ;
  infix_operator1: [ [
      x = INFIXOP1 -> x
    | "@" -> "@"
    | "^" -> "^"
    ] ]
    ;
  additive_operator2: [ [
      "+" -> "+"
    | "+=" -> "+="
    | "-" -> "-"
    | "+." -> "+."
    | "-." -> "-."
    ] ]
    ;
  infix_operator2: [ [
      x = INFIXOP2 -> x
    | check_additive_rparen ; x = additive_operator2 -> x
    ] ]
    ;
  infix_operator3: [ [
      x = INFIXOP3 -> x
    | "lor" -> "lor"
    | "lxor" -> "lxor"
    | "mod" -> "mod"
    | "land" -> "land"
    | "*" -> "*"
    | "/" -> "/"
    | "%" -> "%"
    ] ]
    ;
  infix_operator4: [ [
      x = INFIXOP4 -> x
    | "asr" -> "asr"
    | "lsl" -> "lsl"
    | "lsr" -> "lsr"
    | "**" -> "**"
    ] ]
    ;
  prefix_operator: [ [
      x = PREFIXOP -> x
    | check_bang_closeparen ; "!" -> "!"
    ] ]
    ;
  infix_operator: [ [ 
      x = infix_operator0 -> x
    | x = infix_operator1 -> x
    | x = infix_operator2 -> x
    | x = infix_operator3 -> x
    | x = infix_operator4 -> x
    | ":=" -> ":="
    ] ]
    ;
  operator: [ [
      x = prefix_operator -> x
    | x = infix_operator -> x
    | x = HASHOP -> x
    | op = LETOP -> op
    | op = ANDOP -> op
    | op = "::" -> op

    | op = DOTOP ; "(" ; ")" -> op ^ "()"
    | op = DOTOP ; "(" ; ")" ; "<-" -> op ^ "()<-"
    | op = DOTOP ; "(" ; ";" ; ".." ; ")" -> op ^ "(;..)"
    | op = DOTOP ; "(" ; ";" ; ".." ; ")" ; "<-" -> op ^ "(;..)<-"

    | op = DOTOP ; "{" ; "}" -> op ^ "{}"
    | op = DOTOP ; "{" ; "}" ; "<-" -> op ^ "{}<-"
    | op = DOTOP ; "{" ; ";" ; ".." ; "}" -> op ^ "{;..}"
    | op = DOTOP ; "{" ; ";" ; ".." ; "}" ; "<-" -> op ^ "{;..}<-"

    | op = DOTOP ; "[" ; "]" -> op ^ "[]"
    | op = DOTOP ; "[" ; "]" ; "<-" -> op ^ "[]<-"
    | op = DOTOP ; "[" ; ";" ; ".." ; "]" -> op ^ "[;..]"
    | op = DOTOP ; "[" ; ";" ; ".." ; "]" ; "<-" -> op ^ "[;..]<-"
    ] ]
    ;
  operator_rparen: [ [
      op = operator ; ")" -> op
    ] ]
    ;
  (* This is copied from parser.mly (nonterminal "single_attr_id") in the ocaml 4.10.0 distribution. *)
  kwd_attribute_id:
  [ [ s = [ "and" | "as" | "assert" | "begin" | "class" | "constraint" | "do" | "done"
          | "downto" | "else" | "end" | "exception" | "external" | "false" | "for"
          | "fun" | "function" | "functor" | "if" | "in" | "include" | "inherit"
          | "initializer" | "lazy" | "let" | "match" | "method" | "module" | "mutable"
          | "new" | "nonrec" | "object" | "of" | "open" | "or" | "private" | "rec"
          | "sig" | "struct" | "then" | "to" | "true" | "try" | "type" | "val" | "virtual"
          | "when" | "while" | "with" ] -> s
    ] ]
  ;
  attribute_id:
  [ [ l = LIST1 [ i = LIDENT -> i | i = UIDENT -> i ] SEP "." -> (loc, String.concat "." l)
    | s = kwd_attribute_id -> (loc, s)
    ] ]
  ;
  attribute_structure:
    [ [ st = V (LIST1 [ s = str_item; OPT ";;" → s ]) "structure" → st ] ]
  ;
  attribute_signature:
    [ [ st = V (LIST1 [ s = sig_item; OPT ";;" → s ]) "signature" → st ] ]
  ;
  attribute_body:
  [ [
      id = V attribute_id "attrid" ; st = attribute_structure ->
      <:attribute_body< $_attrid:id$ $_structure:st$ >>
    | id = V attribute_id "attrid" ->
      <:attribute_body< $_attrid:id$ >>
    | id = V attribute_id "attrid" ; ":" ; si = attribute_signature -> 
      <:attribute_body< $_attrid:id$ : $_signature:si$ >>
    | id = V attribute_id "attrid" ; ":" ; ty = V ctyp "type" -> 
      <:attribute_body< $_attrid:id$ : $_type:ty$ >>
    | id = V attribute_id "attrid" ; "?" ;  p = V patt "patt" -> 
      <:attribute_body< $_attrid:id$ ? $_patt:p$ >>
    | id = V attribute_id "attrid" ; "?" ;  p = V patt "patt"; "when"; e = V expr "expr" -> 
      <:attribute_body< $_attrid:id$ ? $_patt:p$ when $_expr:e$ >>
    ] ]
  ;
  floating_attribute:
  [ [ "[@@@" ; attr = V attribute_body "attribute"; "]" -> attr
    ] ]
  ;
  item_attribute:
  [ [ "[@@" ; attr = V attribute_body "attribute"; "]" -> attr
    ] ]
  ;
  alg_attribute:
  [ [ "[@" ; attr = V attribute_body "attribute"; "]" -> attr
    ] ]
  ;
  item_attributes:
  [ [ l = V (LIST0 item_attribute) "itemattrs" -> l ]
  ]
  ;
  alg_attributes_no_anti:
  [ [ l = (LIST0 alg_attribute) -> l ]
  ]
  ;
  alg_attributes:
  [ [ l = V alg_attributes_no_anti "algattrs" -> l ]
  ]
  ;
  item_extension:
  [ [ "[%%" ; e = V attribute_body "extension"; "]" -> e
    | s = QUOTEDITEMEXTENSION -> <:vala< make_string_extension loc s >>
    ] ]
  ;
  alg_extension:
  [ [ "[%" ; e = V attribute_body "extension"; "]" -> e
    | s = QUOTEDALGEXTENSION -> <:vala< make_string_extension loc s >>
    ] ]
  ;
  functor_parameter:
    [ [ "("; i = V uidopt "uidopt"; ":"; t = module_type; ")" -> Some(i, t)
      | IFDEF OCAML_VERSION < OCAML_4_10_0 THEN ELSE
      | "("; ")" -> None
        END
      ]
    ]
  ;
  module_expr:
    [ [ "functor"; alg_attrs = alg_attributes_no_anti; argl = LIST1 functor_parameter;
        "->"; me = SELF ->
          let me = List.fold_right (fun arg me ->
                     <:module_expr< functor $fp:arg$ -> $me$ >>)
            argl me in
          module_expr_wrap_attrs me alg_attrs
      ]
    | "alg_attribute" LEFTA
      [ e1 = SELF ; "[@" ; attr = V attribute_body "attribute"; "]" ->
        <:module_expr< $e1$ [@ $_attribute:attr$ ] >>
      ]
    | [ "struct"; alg_attrs = alg_attributes_no_anti; OPT ";;"; st = structure; "end" ->
          module_expr_wrap_attrs <:module_expr< struct $_list:st$ end >> alg_attrs ]
    | [ me1 = SELF; "."; me2 = SELF -> <:module_expr< $me1$ . $me2$ >> ]
    | [ me1 = SELF; me2 = paren_module_expr -> <:module_expr< $me1$ $me2$ >>
      | IFDEF OCAML_VERSION < OCAML_4_10_0 THEN ELSE
      | me1 = SELF; "("; ")" -> <:module_expr< $me1$ (struct end) >>
        END
      ]
    | [ i = mod_expr_ident -> i
      | me = paren_module_expr -> me
      | e = alg_extension -> <:module_expr< [% $_extension:e$ ] >>
      ] ]
  ;
  paren_module_expr:
    [
      [ "("; "val"; alg_attrs = alg_attributes_no_anti; e = expr; ":"; mt1 = module_type; ":>"; mt2 = module_type; ")" ->
         module_expr_wrap_attrs <:module_expr< (value $e$ : $mt1$ :> $mt2$) >> alg_attrs
      | "("; "val"; alg_attrs = alg_attributes_no_anti; e = expr; ":"; mt1 = module_type; ")" ->
         module_expr_wrap_attrs <:module_expr< (value $e$ : $mt1$) >> alg_attrs
      | "("; "val"; alg_attrs = alg_attributes_no_anti; e = expr; ")" ->
         module_expr_wrap_attrs <:module_expr< (value $e$) >> alg_attrs
      | "("; me = module_expr; ":"; mt = module_type; ")" ->
          <:module_expr< ( $me$ : $mt$ ) >>
      | "("; me = module_expr; ")" -> <:module_expr< $me$ >>
      ]
    ]
    ;
  structure:
    [ [ st = V (LIST0 [ s = str_item; OPT ";;" -> s ]) -> st ] ]
  ;
  mod_expr_ident:
    [ LEFTA
      [ i = SELF; "."; j = SELF -> <:module_expr< $i$ . $j$ >> ]
    | [ i = V UIDENT -> <:module_expr< $_uid:i$ >> ] ]
  ;
  uidopt:
    [ [ m = V UIDENT -> Some m
      | IFDEF OCAML_VERSION < OCAML_4_10_0 THEN ELSE
      | "_" -> None
        END
      ]
    ]
 ;
  uidopt_no_anti:
    [ [ m = UIDENT -> Some (Ploc.VaVal m)
      | IFDEF OCAML_VERSION < OCAML_4_10_0 THEN ELSE
      | "_" -> None
        END
      ]
    ]
  ;

  type_binder_opt: [ [
    check_type_binder ; ls = V (LIST1 typevar) ; "." -> ls
  | -> <:vala< [] >>
  ] ]
  ;
  ext_opt: [ [ ext = OPT [ "%" ; id = attribute_id -> id ] -> ext ] ] ;
  ext_attributes: [ [ e = ext_opt ; l = alg_attributes_no_anti -> (e, l) ] ] ;
  str_item:
    [ "top"
      [ "exception"; ext = ext_opt; ec = V extension_constructor "excon" ; attrs = item_attributes →
          str_item_to_inline <:str_item< exception $_excon:ec$ $_itemattrs:attrs$ >> ext

      | "external"; (ext,alg_attrs) = ext_attributes; i = V LIDENT "lid" ""; ":"; ls = type_binder_opt; t = ctyp; "=";
        pd = V (LIST1 STRING) ; item_attrs = item_attributes ->
          let attrs = merge_left_auxiliary_attrs ~{nonterm_name="str_item-external"} ~{left_name="algebraic attributes"} ~{right_name="item attributes"} alg_attrs item_attrs in
          str_item_to_inline <:str_item< external $_lid:i$ : $_list:ls$ . $t$ = $_list:pd$ $_itemattrs:attrs$ >> ext
      | "external"; (ext,alg_attrs) = ext_attributes; "("; i = operator_rparen; ":"; ls = type_binder_opt; t = ctyp; "=";
        pd = V (LIST1 STRING) ; item_attrs = item_attributes ->
          let attrs = merge_left_auxiliary_attrs ~{nonterm_name="str_item-external"} ~{left_name="algebraic attributes"} ~{right_name="item attributes"} alg_attrs item_attrs in
          str_item_to_inline <:str_item< external $lid:i$ : $_list:ls$ . $t$ = $_list:pd$ $_itemattrs:attrs$ >> ext
      | "include"; (ext,alg_attrs) = ext_attributes; me = module_expr ; item_attrs = item_attributes ->
          let attrs = merge_left_auxiliary_attrs ~{nonterm_name="str_item-include"} ~{left_name="algebraic attributes"} ~{right_name="item attributes"} alg_attrs item_attrs in
          str_item_to_inline <:str_item< include $me$ $_itemattrs:attrs$ >> ext
      | "module"; (ext,alg_attrs) = ext_attributes; r = V (FLAG "rec"); h = first_mod_binding ; t = LIST0 rest_mod_binding ->
          let (i,me,attrs) = h in
          let attrs = merge_left_auxiliary_attrs ~{nonterm_name="str_item-module"} ~{left_name="algebraic attributes"} ~{right_name="item attributes"} alg_attrs attrs in
          let h = (i,me,attrs) in
          str_item_to_inline <:str_item< module $_flag:r$ $list:[h::t]$ >> ext
      | "module"; "type"; (ext,alg_attrs) = ext_attributes; i = V ident ""; "="; mt = module_type ; item_attrs = item_attributes ->
          let attrs = merge_left_auxiliary_attrs ~{nonterm_name="str_item-module-type"} ~{left_name="algebraic attributes"} ~{right_name="item attributes"} alg_attrs item_attrs in
          str_item_to_inline <:str_item< module type $_:i$ = $mt$ $_itemattrs:attrs$ >> ext
      | "module"; "type"; (ext,alg_attrs) = ext_attributes; i = V ident "" ; item_attrs = item_attributes ->
          let attrs = merge_left_auxiliary_attrs ~{nonterm_name="str_item-module-type"} ~{left_name="algebraic attributes"} ~{right_name="item attributes"} alg_attrs item_attrs in
          str_item_to_inline <:str_item< module type $_:i$ = 'abstract $_itemattrs:attrs$ >> ext
      | "open"; (ext,alg_attrs) = ext_attributes; ovf = V (FLAG "!") "!"; me = module_expr ; item_attrs = item_attributes ->
          let attrs = merge_left_auxiliary_attrs ~{nonterm_name="str_item-open"} ~{left_name="algebraic attributes"} ~{right_name="item attributes"} alg_attrs item_attrs in
          str_item_to_inline <:str_item< open $_!:ovf$ $me$ $_itemattrs:attrs$ >> ext
      | "type"; (ext,attrs) = ext_attributes; check_type_decl; nr = FLAG "nonrec";
        htd = first_type_decl ; ttd = LIST0 rest_type_decl ->
          let attrs = merge_left_auxiliary_attrs ~{nonterm_name="str_item-type_decl"} ~{left_name="algebraic attributes"} ~{right_name="item attributes"} attrs htd.MLast.tdAttributes in
          let htd = {(htd) with MLast.tdAttributes = attrs } in
          let tdl = [htd :: ttd] in do {
  if List.for_all (fun td -> Pcaml.unvala td.MLast.tdIsDecl) tdl then ()
            else if List.for_all (fun td -> not (Pcaml.unvala td.MLast.tdIsDecl)) tdl then
              if nr then failwith "type-subst declaration must not specify <<nonrec>>" else ()
            else failwith "type-declaration cannot mix decl and subst" ;
            str_item_to_inline <:str_item< type $flag:nr$ $list:tdl$ >> ext
          }
      | "type"; (ext,attrs) = ext_attributes; check_type_extension ; te = type_extension →
          let attrs = merge_left_auxiliary_attrs ~{nonterm_name="str_item-type_extension"} ~{left_name="algebraic attributes"} ~{right_name="item attributes"} attrs te.MLast.teAttributes in
          let te = { (te) with MLast.teAttributes = attrs } in
          str_item_to_inline <:str_item< type $_lilongid:te.MLast.teNam$ $_list:te.MLast.tePrm$ += $_priv:te.MLast.tePrv$ [ $_list:te.MLast.teECs$ ] $_itemattrs:te.MLast.teAttributes$ >> ext

      | check_let_exception ; "let" ; "exception" ; id = V UIDENT "uid" ;
        "of" ; tyl = V (LIST1 ctyp LEVEL "apply") ; alg_attrs = alg_attributes ; "in" ; x = expr ; attrs = item_attributes ->
        let e = <:expr< let exception $_uid:id$ of $_list:tyl$ $_algattrs:alg_attrs$ in $x$ >> in
        <:str_item< $exp:e$ $_itemattrs:attrs$ >>
      | check_let_exception ; "let" ; "exception" ; id = V UIDENT "uid" ; alg_attrs = alg_attributes ;
        "in" ; x = expr ; attrs = item_attributes ->
        let e = <:expr< let exception $_uid:id$ $_algattrs:alg_attrs$ in $x$ >> in
        <:str_item< $exp:e$ $_itemattrs:attrs$ >>
      | check_let_not_exception ; "let"; (ext, alg_attrs) = ext_attributes ; r = V (FLAG "rec"); h = first_let_binding ; t = LIST0 and_let_binding; "in";
        x = expr ->
          let (a, b, item_attrs) = h in
          let attrs = merge_left_auxiliary_attrs ~{nonterm_name="let_binding"} ~{left_name="algebraic attributes"} ~{right_name="item attributes"} alg_attrs item_attrs in
          let h = (a, b, attrs) in
          let l = [h::t] in
          let e = expr_to_inline <:expr< let $_flag:r$ $list:l$ in $x$ >> ext [] in
          <:str_item< $exp:e$ >>

      | check_let_not_exception ; "let"; (ext, alg_attrs) = ext_attributes; r = V (FLAG "rec"); h = first_let_binding ; t = LIST0 and_let_binding ->
          let (a, b, item_attrs) = h in
          let attrs = merge_left_auxiliary_attrs ~{nonterm_name="let_binding"} ~{left_name="algebraic attributes"} ~{right_name="item attributes"} alg_attrs item_attrs in
          let h = (a, b, attrs) in
          let l = [h::t] in
          let si = match l with
          [ [(p, e, attrs)] ->
              match p with
              [ <:patt< _ >> -> <:str_item< $exp:e$ $_itemattrs:attrs$ >> (* TODO FIX THIS CHET *)
              | _ -> <:str_item< value $_flag:r$ $list:l$ >> ]
          | _ -> <:str_item< value $_flag:r$ $list:l$ >> ] in
          str_item_to_inline si ext

      | check_let_not_exception ; "let"; "module"; (ext,attrs) = ext_attributes; m = V uidopt "uidopt"; mb = mod_fun_binding; "in";
        e = expr ->
          let e = expr_to_inline <:expr< let module $_uidopt:m$ = $mb$ in $e$ >> ext attrs in
          <:str_item< $exp:e$ >>

      | check_let_not_exception ; "let"; "open"; ovf = V (FLAG "!") "!"; (ext, attrs) = ext_attributes; m = module_expr; "in"; e = expr ->
          let e = expr_to_inline <:expr< let open $_!:ovf$ $m$ in $e$ >> ext attrs in
          <:str_item< $exp:e$ >>

      | e = expr ; attrs = item_attributes -> <:str_item< $exp:e$ $_itemattrs:attrs$ >>
      | attr = floating_attribute -> <:str_item< [@@@ $_attribute:attr$ ] >>
      | e = item_extension ; attrs = item_attributes ->
        <:str_item< [%% $_extension:e$ ] $_itemattrs:attrs$ >>
      ] ]
  ;
  first_mod_binding:
    [ [ i = V uidopt "uidopt"; me = mod_fun_binding ; item_attrs = item_attributes ->
          (i, me, item_attrs)
      ] ]
  ;
  rest_mod_binding:
    [ [ "and"; alg_attrs = alg_attributes_no_anti; i = V uidopt "uidopt"; me = mod_fun_binding ; item_attrs = item_attributes ->
          let attrs = merge_left_auxiliary_attrs ~{nonterm_name="mod_binding"} ~{left_name="algebraic attributes"} ~{right_name="item attributes"} alg_attrs item_attrs in
          (i, me, attrs)
      ] ]
  ;
  mod_fun_binding:
    [ RIGHTA
      [ arg = V functor_parameter "functor_parameter" "fp"; mb = SELF ->
          <:module_expr< functor $_fp:arg$ -> $mb$ >>
      | ":"; mt = module_type; "="; me = module_expr ->
          <:module_expr< ( $me$ : $mt$ ) >>
      | "="; me = module_expr -> <:module_expr< $me$ >> ] ]
  ;
  (* Module types *)
  module_type:
    [ [ "functor"; alg_attrs = alg_attributes_no_anti; argl = LIST1 functor_parameter; "->";
        mt = SELF ->
          let mt = List.fold_right (fun arg mt ->
            <:module_type< functor $fp:arg$ -> $mt$ >>)
            argl mt in
          module_type_wrap_attrs mt alg_attrs
      ]
    | IFDEF OCAML_VERSION < OCAML_4_10_0 THEN ELSE
      RIGHTA [ mt1=SELF ; "->" ; mt2=SELF ->
        <:module_type< $mt1$ → $mt2$ >>
     ]
      END
    | "alg_attribute" LEFTA
      [ e1 = SELF ; "[@" ; attr = V attribute_body "attribute"; "]" ->
        <:module_type< $e1$ [@ $_attribute:attr$ ] >>
      ]
    | [ mt = SELF; "with"; wcl = V (LIST1 with_constr SEP "and") ->
          <:module_type< $mt$ with $_list:wcl$ >> ]
    | [ "sig"; alg_attrs = alg_attributes_no_anti; sg = signature; "end" ->
          module_type_wrap_attrs <:module_type< sig $_list:sg$ end >> alg_attrs
      | "module"; "type"; "of"; alg_attrs = alg_attributes_no_anti; me = module_expr ->
          module_type_wrap_attrs <:module_type< module type of $me$ >> alg_attrs
      | li = extended_longident; "."; i = V LIDENT → <:module_type< $longid:li$ . $_lid:i$ >>
      | li = extended_longident → <:module_type< $longid:li$ >>
      | i = V LIDENT → <:module_type< $_lid:i$ >>
      | e = alg_extension -> <:module_type< [% $_extension:e$ ] >>
      | "("; mt = SELF; ")" -> <:module_type< $mt$ >> ] ]
  ;
  signature:
    [ [ sg = V (LIST0 [ s = sig_item; OPT ";;" -> s ]) -> sg ] ]
  ;
  sig_item:
    [ "top"
      [ "exception"; (ext,alg_attrs0) = ext_attributes; gc = constructor_declaration ; item_attrs = item_attributes ->
          let (x1, x2, x3, x4, x5, alg_attrs1) = gc in
          let alg_attrs = merge_left_auxiliary_attrs ~{nonterm_name="sig_item-exception"} ~{left_name="algebraic attributes"} ~{right_name="item attributes"} alg_attrs0 alg_attrs1 in
          let gc = (x1, x2, x3, x4, x5, alg_attrs) in
          sig_item_to_inline (MLast.SgExc loc gc item_attrs) ext
      | "external"; (ext,alg_attrs) = ext_attributes; i = V LIDENT "lid" ""; ":"; ls = type_binder_opt; t = ctyp; "=";
        pd = V (LIST1 STRING) ; item_attrs = item_attributes ->
          let attrs = merge_left_auxiliary_attrs ~{nonterm_name="sig_item-external"} ~{left_name="algebraic attributes"} ~{right_name="item attributes"} alg_attrs item_attrs in
          sig_item_to_inline <:sig_item< external $_lid:i$ : $_list:ls$ . $t$ = $_list:pd$ $_itemattrs:attrs$ >> ext
      | "external"; (ext,alg_attrs) = ext_attributes; "("; i = operator_rparen; ":"; ls = type_binder_opt; t = ctyp; "=";
        pd = V (LIST1 STRING) ; item_attrs = item_attributes ->
          let attrs = merge_left_auxiliary_attrs ~{nonterm_name="sig_item-external"} ~{left_name="algebraic attributes"} ~{right_name="item attributes"} alg_attrs item_attrs in
          sig_item_to_inline <:sig_item< external $lid:i$ : $_list:ls$ . $t$ = $_list:pd$ $_itemattrs:attrs$ >> ext
      | "include"; (ext,alg_attrs) = ext_attributes; mt = module_type ; item_attrs = item_attributes →
          let attrs = merge_left_auxiliary_attrs ~{nonterm_name="sig_item-include"} ~{left_name="algebraic attributes"} ~{right_name="item attributes"} alg_attrs item_attrs in
          sig_item_to_inline <:sig_item< include $mt$ $_itemattrs:attrs$ >> ext

      | "module"; check_uident_coloneq ; i = V UIDENT ; ":="; li = extended_longident ; attrs = item_attributes →
        <:sig_item< module $_uid:i$ := $longid:li$ $_itemattrs:attrs$ >>

      | "module"; (ext,alg_attrs) = ext_attributes; check_module_not_alias; rf = FLAG "rec";
        h = first_mod_decl_binding ; t = LIST0 rest_mod_decl_binding ->
          let (i, mt, item_attrs) = h in
          let item_attrs = merge_left_auxiliary_attrs ~{nonterm_name="sig_item-module"} ~{left_name="algebraic attributes"} ~{right_name="item attributes"} alg_attrs item_attrs in
          let h = (i, mt, item_attrs) in
          sig_item_to_inline <:sig_item< module $flag:rf$ $list:[h::t]$ >> ext

      | "module"; (ext,alg_attrs) = ext_attributes; check_module_alias; i = V UIDENT "uid"; "="; li = longident ; item_attrs = item_attributes →
          let attrs = merge_left_auxiliary_attrs ~{nonterm_name="sig_item-module"} ~{left_name="algebraic attributes"} ~{right_name="item attributes"} alg_attrs item_attrs in
(*
MLast.SgMtyAlias loc <:vala< i >> <:vala< li >> attrs
*)
          sig_item_to_inline <:sig_item< module alias $_uid:i$ = $longid:li$ $_itemattrs:attrs$ >> ext

      | "module"; "type"; (ext,alg_attrs) = ext_attributes; i = V ident ""; "="; mt = module_type ; item_attrs = item_attributes ->
          let attrs = merge_left_auxiliary_attrs ~{nonterm_name="sig_item-module-type"} ~{left_name="algebraic attributes"} ~{right_name="item attributes"} alg_attrs item_attrs in
          sig_item_to_inline <:sig_item< module type $_:i$ = $mt$ $_itemattrs:attrs$ >> ext
      | "module"; "type"; (ext,alg_attrs) = ext_attributes; i = V ident ""; ":="; mt = module_type ; item_attrs = item_attributes ->
          let attrs = merge_left_auxiliary_attrs ~{nonterm_name="sig_item-module-type"} ~{left_name="algebraic attributes"} ~{right_name="item attributes"} alg_attrs item_attrs in
          sig_item_to_inline <:sig_item< module type $_:i$ := $mt$ $_itemattrs:attrs$ >> ext
      | "module"; "type"; (ext,alg_attrs) = ext_attributes; i = V ident "" ; item_attrs = item_attributes ->
          let attrs = merge_left_auxiliary_attrs ~{nonterm_name="sig_item-module-type"} ~{left_name="algebraic attributes"} ~{right_name="item attributes"} alg_attrs item_attrs in
          sig_item_to_inline <:sig_item< module type $_:i$ = 'abstract $_itemattrs:attrs$ >> ext
      | "open"; (ext,alg_attrs) = ext_attributes; i = extended_longident ; item_attrs = item_attributes ->
          let attrs = merge_left_auxiliary_attrs ~{nonterm_name="sig_item-open"} ~{left_name="algebraic attributes"} ~{right_name="item attributes"} alg_attrs item_attrs in
          sig_item_to_inline <:sig_item< open $longid:i$ $_itemattrs:attrs$ >> ext


      | "type"; (ext,attrs) = ext_attributes; check_type_decl; nr = V (FLAG "nonrec");
        htd = first_type_decl ; ttd = LIST0 rest_type_decl ->
          let attrs = merge_left_auxiliary_attrs ~{nonterm_name="str_item-type_decl"} ~{left_name="algebraic attributes"} ~{right_name="item attributes"} attrs htd.MLast.tdAttributes in
          let htd = {(htd) with MLast.tdAttributes = attrs } in
          sig_item_to_inline <:sig_item< type $_flag:nr$ $list:[htd::ttd]$ >> ext
      | "type"; (ext,attrs) = ext_attributes; check_type_extension ; te = type_extension →
          let attrs = merge_left_auxiliary_attrs ~{nonterm_name="str_item-type_extension"} ~{left_name="algebraic attributes"} ~{right_name="item attributes"} attrs te.MLast.teAttributes in
          let te = { (te) with MLast.teAttributes = attrs } in
          sig_item_to_inline <:sig_item< type $_lilongid:te.MLast.teNam$ $_list:te.MLast.tePrm$ += $_priv:te.MLast.tePrv$ [ $_list:te.MLast.teECs$ ] $_itemattrs:te.MLast.teAttributes$ >> ext

      | "val"; (ext,attrs1) = ext_attributes; i = V LIDENT "lid" ""; ":"; ls = type_binder_opt; t = ctyp ; attrs2 = item_attributes ->
          let attrs = merge_left_auxiliary_attrs ~{nonterm_name="sig_item"} ~{left_name="algebraic attributes"} ~{right_name="item attributes"} attrs1 attrs2 in
          let t = match Pcaml.unvala ls with [ [] -> t | _ -> <:ctyp< ! $_list:ls$ . $t$ >>] in
          sig_item_to_inline <:sig_item< value $_lid:i$ : $t$ $_itemattrs:attrs$ >> ext
      | "val"; (ext,attrs1) = ext_attributes; "("; i = operator_rparen; ":"; ls = type_binder_opt; t = ctyp ; attrs2 = item_attributes ->
          let attrs = merge_left_auxiliary_attrs ~{nonterm_name="sig_item"} ~{left_name="algebraic attributes"} ~{right_name="item attributes"} attrs1 attrs2 in
          let t = match Pcaml.unvala ls with [ [] -> t | _ -> <:ctyp< ! $_list:ls$ . $t$ >>] in
          sig_item_to_inline <:sig_item< value $lid:i$ : $t$ $_itemattrs:attrs$ >> ext
      | attr = floating_attribute -> <:sig_item< [@@@ $_attribute:attr$ ] >>
      | e = item_extension ; attrs = item_attributes ->
        <:sig_item< [%% $_extension:e$ ] $_itemattrs:attrs$ >>
      ] ]
  ;
  first_mod_decl_binding:
    [ [ i = uidopt_no_anti ; mt = module_declaration ; attrs = item_attributes -> (Ploc.VaVal i, mt, attrs) ] ]
  ;
  rest_mod_decl_binding:
    [ [ "and"; alg_attrs = alg_attributes_no_anti; i = uidopt_no_anti ; mt = module_declaration ; item_attrs = item_attributes ->
          let attrs = merge_left_auxiliary_attrs ~{nonterm_name="mod_decl_binding"} ~{left_name="algebraic attributes"} ~{right_name="item attributes"} alg_attrs item_attrs in
          (Ploc.VaVal i, mt, attrs) ] ]
  ;
  module_declaration:
    [ RIGHTA
      [ ":"; mt = module_type -> <:module_type< $mt$ >>
      | arg = V functor_parameter "functor_parameter" "fp"; mt = SELF ->
          <:module_type< functor $_fp:arg$ -> $mt$ >>
      ] ]
  ;
  (* "with" constraints (additional type equations over signature
     components) *)
  with_constr:
    [ [ "type"; tpl = V type_parameters "list"; i = V longident_lident "lilongid"; "=";
        pf = V (FLAG "private"); t = ctyp LEVEL "below_alg_attribute" ->
          <:with_constr< type $_lilongid:i$ $_list:tpl$ = $_flag:pf$ $t$ >>
      | "type"; tpl = V type_parameters "list"; i = V longident_lident "lilongid"; ":=";
        t = ctyp LEVEL "below_alg_attribute" ->
          <:with_constr< type $_lilongid:i$ $_list:tpl$ := $t$ >>
      | "module"; i = V longident "longid"; "="; me = module_expr ->
          <:with_constr< module $_longid:i$ = $me$ >>
      | "module"; i = V longident "longid"; ":="; me = module_expr ->
          <:with_constr< module $_longid:i$ := $me$ >>
      | "module"; "type"; li = V longident "longid"; "="; mt = module_type →
          <:with_constr< module type $_longid:li$ = $mt$ >>
      | "module"; "type"; li = V longident "longid"; ":="; mt = module_type →
          <:with_constr< module type $_longid:li$ := $mt$ >>
      ] ]
  ;
  andop_binding:
  [ [ op = ANDOP ; b = letop_binding -> (op, b) ] ]
  ;
  (* Core expressions *)
  expr:
    [ "top" RIGHTA
      [ e1 = SELF; ";"; e2 = SELF ->
          <:expr< do { $list:[e1 :: get_seq e2]$ } >>
      | e1 = SELF; ";" -> e1
      | el = V e_phony "list" -> <:expr< do { $_list:el$ } >> ]
    | "expr1"
      [ check_let_exception ; "let" ; "exception" ; id = V UIDENT "uid" ;
        "of" ; tyl = V (LIST1 ctyp LEVEL "apply") ; alg_attrs = alg_attributes ; "in" ; x = SELF ->
        <:expr< let exception $_uid:id$ of $_list:tyl$ $_algattrs:alg_attrs$ in $x$ >>
      | check_let_exception ; "let" ; "exception" ; id = V UIDENT "uid" ; alg_attrs = alg_attributes ;
        "in" ; x = SELF ->
        <:expr< let exception $_uid:id$ $_algattrs:alg_attrs$ in $x$ >>
      | check_let_not_exception ; "let"; (ext,alg_attrs) = ext_attributes; o = V (FLAG "rec"); h = first_let_binding ; t = LIST0 and_let_binding; "in";
        x = expr LEVEL "top" ->
          let (a, b, item_attrs) = h in
          let attrs = merge_left_auxiliary_attrs ~{nonterm_name="let_binding"} ~{left_name="algebraic attributes"} ~{right_name="item attributes"} alg_attrs item_attrs in
          let h = (a, b, attrs) in
          let l = [h::t] in
          expr_to_inline <:expr< let $_flag:o$ $list:l$ in $x$ >> ext []

      | check_let_not_exception ; "let"; "module"; (ext,attrs) = ext_attributes; m = V uidopt "uidopt"; mb = mod_fun_binding; "in";
        e = expr LEVEL "top" ->
          expr_to_inline <:expr< let module $_uidopt:m$ = $mb$ in $e$ >> ext attrs

      | check_let_not_exception ; "let"; "open"; ovf = V (FLAG "!") "!"; (ext,attrs) = ext_attributes; m = module_expr; "in"; e = expr LEVEL "top" ->
          expr_to_inline <:expr< let open $_!:ovf$ $m$ in $e$ >> ext attrs

      | letop = LETOP ; b = letop_binding ; l = (LIST0 andop_binding); "in";
        x = expr LEVEL "top" ->
          build_letop_binder loc letop b l x

      | "function"; (ext,attrs) = ext_attributes; OPT "|"; l = V (LIST1 match_case SEP "|") ->
          expr_to_inline <:expr< fun [ $_list:l$ ] >> ext attrs

      | "fun"; (ext,attrs) = ext_attributes; check_new_type_extended ;
        "("; "type"; l = LIST1 LIDENT ; ")" ; (eo, e) = fun_def ->
          if eo <> None then failwith "new-type cannot have when-clause"
          else
            let e = List.fold_right (fun id e ->
                <:expr< fun [(type $lid:id$) -> $e$] >>)
                l e in
            expr_to_inline e ext attrs

      | "fun"; (ext,attrs) = ext_attributes; check_not_new_type_extended ; p = patt LEVEL "simple";
        tyopt = OPT [ ":"; t = ctyp LEVEL "apply" -> t ] ;
        (eo, e) = fun_def ->
          let e = match tyopt with [
            None -> e
          | Some ty -> <:expr< ( $e$ : $ty$ ) >>
          ] in
          expr_to_inline <:expr< fun [$p$ $opt:eo$ -> $e$] >> ext attrs
      | "match"; (ext,attrs) = ext_attributes; e = SELF; "with"; OPT "|";
        l = V (LIST1 match_case SEP "|") ->
          expr_to_inline <:expr< match $e$ with [ $_list:l$ ] >> ext attrs
      | "try"; (ext,attrs) = ext_attributes; e = SELF; "with"; OPT "|"; l = V (LIST1 match_case SEP "|") ->
          expr_to_inline <:expr< try $e$ with [ $_list:l$ ] >> ext attrs
      | "if"; (ext,attrs) = ext_attributes; e1 = SELF; "then"; e2 = expr LEVEL "expr1"; "else";
        e3 = expr LEVEL "expr1" ->
          expr_to_inline <:expr< if $e1$ then $e2$ else $e3$ >> ext attrs
      | "if"; (ext,attrs) = ext_attributes; e1 = SELF; "then"; e2 = expr LEVEL "expr1" ->
          expr_to_inline <:expr< if $e1$ then $e2$ else () >> ext attrs
      | "for"; (ext,attrs) = ext_attributes; i = patt; "="; e1 = SELF; df = V direction_flag "to";
        e2 = SELF; "do"; e = V SELF "list"; "done" ->
          let el = Pcaml.vala_map get_seq e in
          expr_to_inline <:expr< for $i$ = $e1$ $_to:df$ $e2$ do { $_list:el$ } >> ext attrs
      | "for"; (ext,attrs) = ext_attributes; "("; i = operator_rparen; "="; e1 = SELF; df = V direction_flag "to";
        e2 = SELF; "do"; e = V SELF "list"; "done" ->
          let i = Ploc.VaVal i in
          let el = Pcaml.vala_map get_seq e in
          expr_to_inline <:expr< for $_lid:i$ = $e1$ $_to:df$ $e2$ do { $_list:el$ } >> ext attrs
      | "while"; (ext,attrs) = ext_attributes; e1 = SELF; "do"; e2 = V SELF "list"; "done" ->
          let el = Pcaml.vala_map get_seq e2 in
          expr_to_inline <:expr< while $e1$ do { $_list:el$ } >> ext attrs ]
    | "," [ e = SELF; ","; el = LIST1 NEXT SEP "," ->
          <:expr< ( $list:[e :: el]$ ) >> ]
    | ":=" NONA
      [ e1 = SELF; ":="; e2 = expr LEVEL "expr1" ->
          <:expr< $e1$ . val := $e2$ >>
      | e1 = SELF; "<-"; e2 = expr LEVEL "expr1" -> <:expr< $e1$ := $e2$ >> ]
    | "||" RIGHTA
      [ e1 = SELF; "or"; e2 = SELF -> <:expr< $lid:"or"$ $e1$ $e2$ >>
      | e1 = SELF; "||"; e2 = SELF -> <:expr< $e1$ || $e2$ >> ]
    | "&&" RIGHTA
      [ e1 = SELF; "&"; e2 = SELF -> <:expr< $lid:"&"$ $e1$ $e2$ >>
      | e1 = SELF; "&&"; e2 = SELF -> <:expr< $e1$ && $e2$ >> ]
    | "<" LEFTA
      [ e1 = SELF; "<"; e2 = SELF -> <:expr< $e1$ < $e2$ >>
      | e1 = SELF; ">"; e2 = SELF -> <:expr< $e1$ > $e2$ >>
      | e1 = SELF; "<="; e2 = SELF -> <:expr< $e1$ <= $e2$ >>
      | e1 = SELF; ">="; e2 = SELF -> <:expr< $e1$ >= $e2$ >>
      | e1 = SELF; "="; e2 = SELF -> <:expr< $e1$ = $e2$ >>
      | e1 = SELF; "<>"; e2 = SELF -> <:expr< $e1$ <> $e2$ >>
      | e1 = SELF; "=="; e2 = SELF -> <:expr< $e1$ == $e2$ >>
      | e1 = SELF; "!="; e2 = SELF -> <:expr< $e1$ != $e2$ >>
      | e1 = SELF; op = INFIXOP0; e2 = SELF -> <:expr< $lid:op$ $e1$ $e2$ >>
      | e1 = SELF; "$"; e2 = SELF -> let op = "$" in <:expr< $lid:op$ $e1$ $e2$ >> ]
    | "^" RIGHTA
      [ e1 = SELF; "^"; e2 = SELF -> <:expr< $e1$ ^ $e2$ >>
      | e1 = SELF; "@"; e2 = SELF -> <:expr< $e1$ @ $e2$ >>
      | e1 = SELF; op = INFIXOP1; e2 = SELF -> <:expr< $lid:op$ $e1$ $e2$ >> ]
    | "alg_attribute" LEFTA
      [ e1 = SELF ; "[@" ; attr = V attribute_body "attribute"; "]" ->
        <:expr< $e1$ [@ $_attribute:attr$ ] >>
      ]
    | RIGHTA
      [ e1 = SELF; "::"; e2 = SELF -> <:expr< [$e1$ :: $e2$] >> ]
    | "+" LEFTA
      [ e1 = SELF; "+"; e2 = SELF -> <:expr< $e1$ + $e2$ >>
      | e1 = SELF; "-"; e2 = SELF -> <:expr< $e1$ - $e2$ >>
      | e1 = SELF; "+."; e2 = SELF → <:expr< $e1$ +. $e2$ >>
      | e1 = SELF; "-."; e2 = SELF → <:expr< $e1$ -. $e2$ >>
      | e1 = SELF; op = INFIXOP2; e2 = SELF -> <:expr< $lid:op$ $e1$ $e2$ >> ]
    | "*" LEFTA
      [ e1 = SELF; "*"; e2 = SELF -> <:expr< $e1$ * $e2$ >>
      | e1 = SELF; "/"; e2 = SELF -> <:expr< $e1$ / $e2$ >>
      | e1 = SELF; "%"; e2 = SELF -> <:expr< $lid:"%"$ $e1$ $e2$ >>
      | e1 = SELF; "*."; e2 = SELF → <:expr< $e1$ *. $e2$ >>
      | e1 = SELF; "/."; e2 = SELF → <:expr< $e1$ /. $e2$ >>
      | e1 = SELF; "land"; e2 = SELF -> <:expr< $e1$ land $e2$ >>
      | e1 = SELF; "lor"; e2 = SELF -> <:expr< $e1$ lor $e2$ >>
      | e1 = SELF; "lxor"; e2 = SELF -> <:expr< $e1$ lxor $e2$ >>
      | e1 = SELF; "mod"; e2 = SELF -> <:expr< $e1$ mod $e2$ >>
      | e1 = SELF; op = INFIXOP3; e2 = SELF -> <:expr< $lid:op$ $e1$ $e2$ >> ]
    | "**" RIGHTA
      [ e1 = SELF; "**"; e2 = SELF -> <:expr< $e1$ ** $e2$ >>
      | e1 = SELF; "asr"; e2 = SELF -> <:expr< $e1$ asr $e2$ >>
      | e1 = SELF; "lsl"; e2 = SELF -> <:expr< $e1$ lsl $e2$ >>
      | e1 = SELF; "lsr"; e2 = SELF -> <:expr< $e1$ lsr $e2$ >>
      | e1 = SELF; op = INFIXOP4; e2 = SELF -> <:expr< $lid:op$ $e1$ $e2$ >> ]
    | "unary minus" NONA
      [ "-"; e = SELF -> <:expr< - $e$ >>
      | "-."; e = SELF -> <:expr< -. $e$ >>
      | "+"; e = SELF →
         match e with [
           <:expr< $int:_$ >> -> e
         | _ ->  <:expr< $lid:"~+"$ $e$ >>
         ]
      | "+."; e = SELF →
         match e with [
           <:expr< $flo:_$ >> -> e
         | _ -> <:expr< $lid:"~+."$ $e$ >>
         ]
      ]
    | "apply" LEFTA
      [ e1 = SELF; e2 = SELF ->
          let (e1, e2) =
            if is_expr_constr_call e1 then
              match e1 with
              [ <:expr< $e11$ $e12$ >> -> (e11, <:expr< $e12$ $e2$ >>)
              | _ -> (e1, e2) ]
            else (e1, e2)
          in
          match constr_expr_arity loc e1 with
          [ 1 -> <:expr< $e1$ $e2$ >>
          | _ ->
              match e2 with
              [ <:expr< ( $list:el$ ) >> ->
                  List.fold_left (fun e1 e2 -> <:expr< $e1$ $e2$ >>) e1 el
              | _ -> <:expr< $e1$ $e2$ >> ] ]
      | "assert"; (ext,attrs) = ext_attributes; e = SELF ->
          expr_to_inline <:expr< assert $e$ >> ext attrs
      | "lazy"; (ext,attrs) = ext_attributes; e = SELF -> 
          expr_to_inline <:expr< lazy ($e$) >> ext attrs ]
    | "." LEFTA
      [ e1 = SELF; "."; lili = V longident_lident "lilongid" ->
        <:expr< $e1$ . $_lilongid:lili$ >>
      | e1 = SELF; "."; "("; op = operator_rparen ->
          if op = "::" then
            Ploc.raise loc (Failure ".(::) (dot paren colon colon paren) cannot appear except after longident")
          else
            <:expr< $e1$ . $lid:op$ >>

      | e1 = SELF; "."; "("; e2 = SELF; ")" ->
          if expr_last_is_uid e1 then
            failwith "internal error in original-syntax parser at dot-lparen"
          else
            <:expr< $e1$ .( $e2$ ) >>

      | e1 = SELF; op = V DOTOP "dotop"; "("; el = LIST1 expr LEVEL "+" SEP ";"; ")" ->
          <:expr< $e1$ $_dotop:op$ ( $list:el$ ) >>

      | e1 = SELF; "."; "["; e2 = SELF; "]" -> <:expr< $e1$ .[ $e2$ ] >>

      | e1 = SELF; op = V DOTOP "dotop"; "["; el = LIST1 expr LEVEL "+" SEP ";"; "]" ->
          <:expr< $e1$ $_dotop:op$ [ $list:el$ ] >>

      | e1 = SELF; "."; "{"; el = LIST1 expr LEVEL "+" SEP ","; "}" ->
          <:expr< $e1$ .{ $list:el$ } >>

      | e1 = SELF; op = V DOTOP "dotop"; "{"; el = LIST1 expr LEVEL "+" SEP ";"; "}" ->
          <:expr< $e1$ $_dotop:op$ { $list:el$ } >>
      ]

    | "~-" NONA
      [ "!"; e = SELF -> <:expr< $e$ . val >>
      | "~-"; e = SELF -> <:expr< ~- $e$ >>
      | "~-."; e = SELF -> <:expr< ~-. $e$ >>
      | f = PREFIXOP; e = SELF -> <:expr< $lid:f$ $e$ >> ]
    | "simple" LEFTA
      [ s = V INT -> <:expr< $_int:s$ >>
      | s = V INT_l -> <:expr< $_int32:s$ >>
      | s = V INT_L -> <:expr< $_int64:s$ >>
      | s = V INT_n -> <:expr< $_nativeint:s$ >>
      | s = V FLOAT -> <:expr< $_flo:s$ >>
      | s = V STRING -> <:expr< $_str:s$ >>
      | c = V CHAR -> <:expr< $_chr:c$ >>
      | e = alg_extension -> <:expr< [% $_extension:e$ ] >>
      | UIDENT "True" ->  <:expr< True_ >>
      | UIDENT "False" -> <:expr< False_ >>
      | i = V LIDENT -> <:expr< $_lid:i$ >>
      | i = expr_longident -> i
      | "true" -> <:expr< True >>
      | "false" -> <:expr< False >>
      | "["; "]" -> <:expr< $uid:"[]"$ >>
      | "["; el = expr1_semi_list; "]" -> <:expr< $mklistexp loc None el$ >>
      | "[|"; "|]" -> <:expr< [| |] >>
      | "[|"; el = V expr1_semi_list "list"; "|]" ->
          <:expr< [| $_list:el$ |] >>
      | "{"; test_label_eq; lel = V lbl_expr_list "list"; "}" ->
          <:expr< { $_list:lel$ } >>
      | "{"; e = expr LEVEL "apply"; "with"; lel = V lbl_expr_list "list";
        "}" ->
          <:expr< { ($e$) with $_list:lel$ } >>
      | "("; ")" -> <:expr< $uid:"()"$ >>
      | "("; "module"; me = module_expr; ":"; mt = module_type; ")" ->
          <:expr< (module $me$ : $mt$) >>
      | "("; "module"; me = module_expr; ")" ->
          <:expr< (module $me$) >>
      | "("; op = operator_rparen ->
        if op = "::" then
          <:expr< $uid:op$ >>
        else
          <:expr< $lid:op$ >>
      | "("; el = V e_phony "list"; ")" -> <:expr< ($_list:el$) >>
      | "("; e = SELF; ":"; t = ctyp; ")" -> <:expr< ($e$ : $t$) >>
      | "("; e = SELF; ")" -> concat_comm loc <:expr< $e$ >>
      | "begin"; (ext,attrs) = ext_attributes; e = SELF; "end" -> 
          expr_to_inline (concat_comm loc <:expr< $e$ >>) ext attrs
      | "begin"; (ext,attrs) = ext_attributes; "end" -> 
          expr_to_inline <:expr< $uid:"()"$ >> ext attrs
      | x = QUOTATION ->
          let con = quotation_content x in
          Pcaml.handle_expr_quotation loc con ] ]
  ;
  let_binding:
    [ [ alg_attrs = alg_attributes_no_anti ;
        p = val_ident; check_and_or_in ->
        match p with [
            <:patt< $lid:s$ >> -> (p, <:expr< $lid:s$ >>, <:vala< alg_attrs >>)
          | _ -> failwith "let punning: binder must be a lowercase ident (variable)"
          ]
      | alg_attrs = alg_attributes_no_anti ;
        p = val_ident; check_colon ; e = fun_binding ;
        item_attrs = item_attributes ->
        let attrs = merge_left_auxiliary_attrs ~{nonterm_name="let_binding"} ~{left_name="algebraic attributes"} ~{right_name="item attributes"} alg_attrs item_attrs in
        let (p,e) = match e with [
          <:expr< ( $e$ : $t$ ) >> -> (<:patt< ($p$ : $t$) >>, e)
        | _ -> (p,e)
        ] in
        (p, e, attrs)
      | alg_attrs = alg_attributes_no_anti ;
        p = val_ident; check_not_colon ; e = fun_binding ;
        item_attrs = item_attributes ->
        let attrs = merge_left_auxiliary_attrs ~{nonterm_name="let_binding"} ~{left_name="algebraic attributes"} ~{right_name="item attributes"} alg_attrs item_attrs in
        (p, e, attrs)
      | alg_attrs = alg_attributes_no_anti ;
        p = patt; "="; e = expr ;
        item_attrs = item_attributes ->
        let attrs = merge_left_auxiliary_attrs ~{nonterm_name="let_binding"} ~{left_name="algebraic attributes"} ~{right_name="item attributes"} alg_attrs item_attrs in
        (p, e, attrs)
      | alg_attrs = alg_attributes_no_anti ;
        p = patt; ":"; t = poly_type; "="; e = expr ;
        item_attrs = item_attributes ->
        let attrs = merge_left_auxiliary_attrs ~{nonterm_name="let_binding"} ~{left_name="algebraic attributes"} ~{right_name="item attributes"} alg_attrs item_attrs in
        (p, <:expr< ( $e$ : $t$ ) >>, attrs)
      ] ]
  ;
  first_let_binding:
    [ [ p = val_ident; check_and_or_in ->
        match p with [
            <:patt< $lid:s$ >> -> (p, <:expr< $lid:s$ >>, <:vala< [] >>)
          | _ -> failwith "let punning: binder must be a lowercase ident (variable)"
          ]
      | p = val_ident; check_colon; e = fun_binding ;
        item_attrs = item_attributes ->
        let (p,e) = match e with [
          <:expr< ( $e$ : $t$ ) >> -> (<:patt< ($p$ : $t$) >>, e)
        | _ -> (p,e)
        ] in
        (p, e, item_attrs)
      | p = val_ident; check_not_colon; e = fun_binding ;
        item_attrs = item_attributes ->
        (p, e, item_attrs)
      | p = patt; "="; e = expr ;
        item_attrs = item_attributes ->
        (p, e, item_attrs)
      | p = patt; ":"; t = poly_type; "="; e = expr ;
        item_attrs = item_attributes ->
        (<:patt< ($p$ : $t$) >>, e, item_attrs)
      ] ]
  ;
  and_let_binding:
    [ [ "and"; alg_attrs = alg_attributes_no_anti ;
        p = val_ident; check_and_or_in ->
        match p with [
            <:patt< $lid:s$ >> -> (p, <:expr< $lid:s$ >>, <:vala< alg_attrs >>)
          | _ -> failwith "let punning: binder must be a lowercase ident (variable)"
          ]
      | "and"; alg_attrs = alg_attributes_no_anti ;
        p = val_ident; check_colon; e = fun_binding ;
        item_attrs = item_attributes ->
        let attrs = merge_left_auxiliary_attrs ~{nonterm_name="let_binding"} ~{left_name="algebraic attributes"} ~{right_name="item attributes"} alg_attrs item_attrs in
        let (p,e) = match e with [
          <:expr< ( $e$ : $t$ ) >> -> (<:patt< ($p$ : $t$) >>, e)
        | _ -> (p,e)
        ] in
        (p, e, attrs)
      | "and"; alg_attrs = alg_attributes_no_anti ;
        p = val_ident; check_not_colon; e = fun_binding ;
        item_attrs = item_attributes ->
        let attrs = merge_left_auxiliary_attrs ~{nonterm_name="let_binding"} ~{left_name="algebraic attributes"} ~{right_name="item attributes"} alg_attrs item_attrs in
        (p, e, attrs)
      | "and"; alg_attrs = alg_attributes_no_anti ;
        p = patt; "="; e = expr ;
        item_attrs = item_attributes ->
        let attrs = merge_left_auxiliary_attrs ~{nonterm_name="let_binding"} ~{left_name="algebraic attributes"} ~{right_name="item attributes"} alg_attrs item_attrs in
        (p, e, attrs)
      | "and"; alg_attrs = alg_attributes_no_anti ;
        p = patt; ":"; t = poly_type; "="; e = expr ;
        item_attrs = item_attributes ->
        let attrs = merge_left_auxiliary_attrs ~{nonterm_name="let_binding"} ~{left_name="algebraic attributes"} ~{right_name="item attributes"} alg_attrs item_attrs in
        (<:patt< ($p$ : $t$) >>, e, attrs)
      ] ]
  ;
  letop_binding:
    [ [ p = val_ident; e = fun_binding -> (p, e)
      | p = val_ident ->
         match p with [
             <:patt< $lid:s$ >> -> (p, <:expr< $lid:s$ >>)
           | _ -> failwith "letop punning: binder must be a lowercase ident (variable)"
           ]
      | p = patt; "="; e = expr -> (p, e)
      | p = patt; ":"; t = poly_type; "="; e = expr ->
          (<:patt< ($p$ : $t$) >>, e)
      ] ]
  ;
  val_ident:
    [ [ check_not_part_of_patt; s = LIDENT -> <:patt< $lid:s$ >>
      | check_not_part_of_patt; "(" ; op = operator_rparen ->
        if op = "::" then
          <:patt< $uid:op$ >>
        else
          <:patt< $lid:op$ >>
      ] ]
  ;
  fun_binding:
    [ RIGHTA
      [ 
        check_new_type_extended ; "("; "type"; l = LIST1 LIDENT ; ")" ; e = SELF ->
        List.fold_right (fun id e ->
            <:expr< fun [(type $lid:id$) -> $e$] >>)
          l e
      | check_not_new_type_extended ; p = patt LEVEL "simple"; e = SELF -> <:expr< fun $p$ -> $e$ >>
      | "="; e = expr -> <:expr< $e$ >>
      | ":"; t = poly_type; "="; e = expr -> <:expr< ($e$ : $t$) >>
      | ":"; t = poly_type; ":>"; t2 = poly_type ; "="; e = expr -> <:expr< ( ( $e$ : $t$ ) :> $t2$ ) >>
      | ":>"; t = poly_type; "="; e = expr -> <:expr< ($e$ :> $t$) >>
      ] ]
  ;
(* NOTE WELL: if I expand expr_or_dot into match_case and make it two rules,
 * I get errors; more evidence there's a bug in the grammar-interpreter *)
  expr_or_dot: [[ e = expr -> e | "." -> <:expr< . >> ]] ;
  match_case:
    [ [ x1 = patt; w = V (OPT [ "when"; e = expr -> e ]); "->"; e = expr_or_dot ->
          (x1, w, e)
      ] ]
  ;
  lbl_expr_list:
    [ [ le = lbl_expr; ";"; lel = SELF -> [le :: lel]
      | le = lbl_expr; ";" -> [le]
      | le = lbl_expr -> [le] ] ]
  ;
  lbl_expr:
    [ [ i = patt_label_ident ;
        tycon = OPT [ ":" ; c = ctyp -> c ];
        e = OPT [ "="; e = expr LEVEL "expr1" -> e] ->
        let last = match i with [
          <:patt< $longid:_$ . $lid:j$ >> -> j
        | <:patt< $lid:j$ >> -> j
        | _ -> failwith "internal error: lbl_expr"
        ] in
        let rhs = match e with [
          None -> <:expr< $lid:last$ >>
        | Some e -> e ] in
        let rhs = match tycon with [
          None -> rhs
        | Some ty -> <:expr< ($rhs$ : $ty$) >>
        ] in 
        (i, rhs)
      ] ]
  ;
  expr1_semi_list:
    [ [ el = LIST1 (expr LEVEL "expr1") SEP ";" OPT_SEP -> el ] ]
  ;
  fun_def:
    [ RIGHTA
      [ p = patt LEVEL "simple"; (eo, e) = SELF ->
          (None, <:expr< fun [ $p$ $opt:eo$ -> $e$ ] >>)
      | eo = OPT [ "when"; e = expr -> e ]; tyo = OPT [ ":" ; ty = ctyp LEVEL "apply" -> ty ]; "->"; e = expr ->
          let e = match tyo with [
            None -> e
          | Some ty -> <:expr< ( $e$ : $ty$ ) >> ] in
          (eo, <:expr< $e$ >>)
      ] ]
  ;
  expr_longident:
    [
      [ li = longident -> <:expr< $longid:li$ >>
      | li = longident ; "." ; "("; op = operator_rparen ->
          if op = "::" then
            <:expr< $longid:li$ . $uid:op$ >>
          else
            <:expr< $longid:li$ . $lid:op$ >>

      | li = longident ; "." ; "(" ; e = expr ; ")" -> <:expr< $longid:li$ . ( $e$ ) >>
      | li = longident ; "." ; id = V LIDENT "lid" ->
        <:expr< $longid:li$ . $_lid:id$ >>
      | li = longident ; "." ; check_lbracket ; e = expr LEVEL "simple" -> <:expr< $longid:li$ . ( $e$ ) >>
      | li = longident ; "." ; check_lbrace ; e = expr LEVEL "simple" -> <:expr< $longid:li$ . ( $e$ ) >>
      | li = longident ; "." ; check_lbracketbar ; e = expr LEVEL "simple" -> <:expr< $longid:li$ . ( $e$ ) >>
      ]
    ]
  ;
  (* Patterns *)
  patt_ident: [
    [ s = V LIDENT → <:patt< $_lid:s$ >>
    | s = V GIDENT → <:patt< $_lid:s$ >>
    | li = longident ; "." ; p = patt LEVEL "simple" → 
      match p with [
        <:patt< $uid:i$ >> ->
        let i = uident_True_True_ i in
        let li = <:extended_longident< $longid:li$ . $uid:i$ >> in
        <:patt< $longid:li$ >>
      | _ -> <:patt< $longid:li$ . $p$ >>
      ]
    | li = longident ; check_lparen_type ; "("; "type";
      loc_ids = V (LIST1 [ s = LIDENT -> (loc,s) ]) ; ")" → 
      <:patt< $longid:li$ (type $_list:loc_ids$ ) >>
    | li = longident → <:patt< $longid:li$ >>
    ]
  ]
  ;
  patt:
    [ LEFTA
      [ p1 = SELF; "as"; i = LIDENT -> <:patt< ($p1$ as $lid:i$) >>
      | p1 = SELF; "as"; "("; i = operator_rparen  -> <:patt< ($p1$ as $lid:i$) >>
      ]
    | LEFTA
      [ p1 = SELF; "|"; p2 = SELF -> <:patt< $p1$ | $p2$ >> ]
    | [ p = SELF; ","; pl = LIST1 NEXT SEP "," ->
          <:patt< ( $list:[p :: pl]$) >> ]
    | "alg_attribute" LEFTA
      [ p = SELF ; "[@" ; attr = V attribute_body "attribute"; "]" ->
        <:patt< $p$ [@ $_attribute:attr$ ] >>
      ]
  | NONA
      [ "exception"; (ext,attrs) = ext_attributes; p = SELF →
         patt_to_inline <:patt< exception $p$ >> ext attrs
      ]
  | NONA
      [ p1 = SELF; ".."; p2 = SELF -> <:patt< $p1$ .. $p2$ >> ]
    | RIGHTA
      [ p1 = SELF; "::"; p2 = SELF -> <:patt< [$p1$ :: $p2$] >> ]
    | LEFTA
      [ p1 = SELF; p2 = SELF ->
          let (p1, p2) =
            match p1 with
            [ <:patt< $p11$ $p12$ >> -> (p11, <:patt< $p12$ $p2$ >>)
            | _ -> (p1, p2) ]
          in
          match constr_patt_arity loc p1 with
          [ 1 -> <:patt< $p1$ $p2$ >>
          | n ->
              let p2 =
                match p2 with
                [ <:patt< _ >> when n > 1 ->
                    let pl =
                      loop n where rec loop n =
                        if n = 0 then [] else [<:patt< _ >> :: loop (n - 1)]
                    in
                    <:patt< ( $list:pl$ ) >>
                | _ -> p2 ]
              in
              match p2 with
              [ <:patt< ( $list:pl$ ) >> ->
                  List.fold_left (fun p1 p2 -> <:patt< $p1$ $p2$ >>) p1 pl
              | _ -> <:patt< $p1$ $p2$ >> ] ]
      | "lazy"; (ext,attrs) = ext_attributes; p = SELF -> 
          patt_to_inline <:patt< lazy $p$ >> ext attrs ]
    | "simple"
      [ p = patt_ident -> p
      | s = V INT -> <:patt< $_int:s$ >>
      | s = V INT_l -> <:patt< $_int32:s$ >>
      | s = V INT_L -> <:patt< $_int64:s$ >>
      | s = V INT_n -> <:patt< $_nativeint:s$ >>
      | "+"; s = V INT → <:patt< $_int:s$ >>
      | "+"; s = V FLOAT → <:patt< $_flo:s$ >>
      | "-"; s = INT -> <:patt< $int:"-" ^ s$ >>
      | "-"; s = INT_l -> <:patt< $int32:"-" ^ s$ >>
      | "-"; s = INT_L -> <:patt< $int64:"-" ^ s$ >>
      | "-"; s = INT_n -> <:patt< $nativeint:"-" ^ s$ >>
      | "-"; s = FLOAT -> <:patt< $flo:"-" ^ s$ >>
      | s = V FLOAT -> <:patt< $_flo:s$ >>
      | s = V STRING -> <:patt< $_str:s$ >>
      | s = V CHAR -> <:patt< $_chr:s$ >>
      | e = alg_extension -> <:patt< [% $_extension:e$ ] >>
      | UIDENT "True" -> <:patt< True_ >>
      | UIDENT "False" -> <:patt< False_ >>
      | "false" -> <:patt< False >>
      | "true" -> <:patt< True >>
      | "["; "]" -> <:patt< [] >>
      | "["; pl = patt_semi_list; "]" -> <:patt< $mklistpat loc None pl$ >>
      | "[|"; "|]" -> <:patt< [| |] >>
      | "[|"; pl = V patt_semi_list "list"; "|]" ->
          <:patt< [| $_list:pl$ |] >>
      | "{"; lpl = V lbl_patt_list "list"; "}" ->
          <:patt< { $_list:lpl$ } >>
      | "("; ")" -> <:patt< $uid:"()"$ >>
      | "("; op = operator_rparen -> 
          if op = "::" then
            <:patt< $uid:op$ >>
          else
            <:patt< $lid:op$ >>
      | "("; pl = V p_phony "list"; ")" -> <:patt< ($_list:pl$) >>
      | "("; p = SELF; ":"; t = ctyp; ")" -> <:patt< ($p$ : $t$) >>
      | "("; p = SELF; ")" -> <:patt< $p$ >>
      | "("; "type"; s = V LIDENT; ")" -> <:patt< (type $_lid:s$) >>
      | "("; "module"; s = V uidopt "uidopt"; ":"; mt = module_type; ")" ->
          <:patt< (module $_uidopt:s$ : $mt$) >>
      | "("; "module"; s = V uidopt "uidopt"; ")" ->
          <:patt< (module $_uidopt:s$) >>
      | "_" -> <:patt< _ >>
      | x = QUOTATION ->
          let con = quotation_content x in
          Pcaml.handle_patt_quotation loc con ] ]
  ;
  patt_semi_list:
    [ [ p = patt; ";"; pl = SELF -> [p :: pl]
      | p = patt; ";" -> [p]
      | p = patt -> [p] ] ]
  ;
  lbl_patt_list:
    [ [ le = lbl_patt; ";"; lel = SELF -> [le :: lel]
      | le = lbl_patt; ";" -> [le]
      | le = lbl_patt -> [le] ] ]
  ;
  lbl_patt:
    [ [ i = patt_label_ident ; tycon = OPT [ ":" ; c = ctyp -> c ]; p = OPT [ "="; p = patt -> p ] ->
        let last = match i with [
          <:patt< $longid:_$ . $lid:j$ >> -> j
        | <:patt< $lid:j$ >> -> j
        | _ -> failwith "internal error: lbl_patt"
        ] in
        let rhs = match p with [
          None -> <:patt< $lid:last$ >>
        | Some p -> p ] in 
         let rhs = match tycon with [
          None -> rhs
        | Some ty -> <:patt< ( $rhs$ : $ty$ ) >>
        ] in 
        (i, rhs)
      | "_" -> (<:patt< _ >>, <:patt< _ >>) ] ]
  ;
  patt_label_ident:
    [ RIGHTA
      [ li = longident; "."; p2 = SELF -> <:patt< $longid:li$ . $p2$ >>
      | i = LIDENT -> <:patt< $lid:i$ >>
     ] ]
  ;
  (* Type declaration *)
  type_decl:
    [ [ tpl = type_parameters; n = V type_patt; "="; pf = V (FLAG "private");
        tk = type_kind; cl = V (LIST0 constrain) ; attrs = item_attributes ->
          <:type_decl< $_tp:n$ $list:tpl$ = $_priv:pf$ $tk$ $_list:cl$ $_itemattrs:attrs$ >>
      | tpl = type_parameters; n = V type_patt; ":="; pf = V (FLAG "private");
        tk = type_kind; cl = V (LIST0 constrain) ; attrs = item_attributes ->
          <:type_decl< $_tp:n$ $list:tpl$ := $_priv:pf$ $tk$ $_list:cl$ $_itemattrs:attrs$ >>
      | tpl = type_parameters; n = V type_patt; cl = V (LIST0 constrain) ; attrs = item_attributes ->
          let tk = <:ctyp< '$choose_tvar tpl$ >> in
          <:type_decl< $_tp:n$ $list:tpl$ = $tk$ $_list:cl$ $_itemattrs:attrs$ >> ] ]
  ;
  first_type_decl:
    [ [ tpl = type_parameters; n = V type_patt; "="; pf = V (FLAG "private");
        tk = type_kind; cl = V (LIST0 constrain) ; attrs = item_attributes ->
          <:type_decl< $_tp:n$ $list:tpl$ = $_priv:pf$ $tk$ $_list:cl$ $_itemattrs:attrs$ >>
      | tpl = type_parameters; n = V type_patt; ":="; pf = V (FLAG "private");
        tk = type_kind; cl = V (LIST0 constrain) ; attrs = item_attributes ->
          <:type_decl< $_tp:n$ $list:tpl$ := $_priv:pf$ $tk$ $_list:cl$ $_itemattrs:attrs$ >>
      | tpl = type_parameters; n = V type_patt; cl = V (LIST0 constrain) ; attrs = item_attributes ->
          let tk = <:ctyp< '$choose_tvar tpl$ >> in
          <:type_decl< $_tp:n$ $list:tpl$ = $tk$ $_list:cl$ $_itemattrs:attrs$ >> ] ]
  ;
  (* Type declaration *)
  rest_type_decl:
    [ [ "and"; alg_attrs = alg_attributes_no_anti; tpl = type_parameters; n = V type_patt; "="; pf = V (FLAG "private");
        tk = type_kind; cl = V (LIST0 constrain) ; item_attrs = item_attributes ->
        let attrs = merge_left_auxiliary_attrs ~{nonterm_name="type_decl"} ~{left_name="algebraic attributes"} ~{right_name="item attributes"} alg_attrs item_attrs in
          <:type_decl< $_tp:n$ $list:tpl$ = $_priv:pf$ $tk$ $_list:cl$ $_itemattrs:attrs$ >>

      | "and"; alg_attrs = alg_attributes_no_anti; tpl = type_parameters; n = V type_patt; ":="; pf = V (FLAG "private");
        tk = type_kind; cl = V (LIST0 constrain) ; item_attrs = item_attributes ->
        let attrs = merge_left_auxiliary_attrs ~{nonterm_name="type_decl"} ~{left_name="algebraic attributes"} ~{right_name="item attributes"} alg_attrs item_attrs in
          <:type_decl< $_tp:n$ $list:tpl$ := $_priv:pf$ $tk$ $_list:cl$ $_itemattrs:attrs$ >>

      | "and"; alg_attrs = alg_attributes_no_anti; tpl = type_parameters; n = V type_patt; cl = V (LIST0 constrain) ; item_attrs = item_attributes ->
          let tk = <:ctyp< '$choose_tvar tpl$ >> in
          let attrs = merge_left_auxiliary_attrs ~{nonterm_name="type_decl"} ~{left_name="algebraic attributes"} ~{right_name="item attributes"} alg_attrs item_attrs in
          <:type_decl< $_tp:n$ $list:tpl$ = $tk$ $_list:cl$ $_itemattrs:attrs$ >> ] ]
  ;
  (* TODO FIX: this should be a longident+lid, to match ocaml's grammar *)
  type_extension:
    [ [ tpl = type_parameters; n = V longident_lident "lilongid"; "+=";
        pf = V (FLAG "private") "priv"; OPT [ "|" ] ; ecs = V (LIST1 extension_constructor SEP "|") ;
        attrs = item_attributes →
(*
          <:type_extension< $_tp:n$ $_list:tpl$ += $_priv:pf$ $tk$ $_itemattrs:attrs$ >>
*)
          {MLast.teNam=n; tePrm= <:vala< tpl >>; tePrv=pf; teAttributes=attrs; teECs = ecs }
      ] ]
  ;
  type_patt:
    [ [ n = V LIDENT -> (loc, n) ] ]
  ;
  constrain:
    [ [ "constraint"; t1 = ctyp; "="; t2 = ctyp -> (t1, t2) ] ]
  ;
  type_kind:
    [ [ test_constr_decl; OPT "|";
        cdl = LIST0 constructor_declaration SEP "|" ->
          <:ctyp< [ $list:cdl$ ] >>
      | ".." -> <:ctyp< .. >>
      | t = ctyp ->
          <:ctyp< $t$ >>
      | t = ctyp; "="; pf = FLAG "private"; "{";
        ldl = V label_declarations "list"; "}" ->
          <:ctyp< $t$ == $priv:pf$ { $_list:ldl$ } >>
      | t = ctyp; "="; pf = FLAG "private"; OPT "|";
        cdl = LIST1 constructor_declaration SEP "|" ->
          <:ctyp< $t$ == $priv:pf$ [ $list:cdl$ ] >>
      | t = ctyp; "="; pf = FLAG "private"; ".." ->
          <:ctyp< $t$ == $priv:pf$ .. >>
      | "{"; ldl = V label_declarations "list"; "}" ->
          <:ctyp< { $_list:ldl$ } >> ] ]
  ;
  type_parameters:
    [ [ -> (* empty *) []
      | tp = type_parameter -> [tp]
      | "("; tpl = LIST1 type_parameter SEP ","; ")" -> tpl ] ]
  ;
  type_parameter:
    [ [ "+"; p = V simple_type_parameter -> (p, (Some True, False))
      | "+"; "!" ; p = V simple_type_parameter -> (p, (Some True, True))
      | "-"; p = V simple_type_parameter -> (p, (Some False, False))
      | "-"; "!" ; p = V simple_type_parameter -> (p, (Some False, True))
      | "!" ; p = V simple_type_parameter -> (p, (None, True))
      | "!" ; "+" ; p = V simple_type_parameter -> (p, (Some True, True))
      | "!" ; "-" ; p = V simple_type_parameter -> (p, (Some False, True))
      | "!+" ; p = V simple_type_parameter -> (p, (Some True, True))
      | "+!" ; p = V simple_type_parameter -> (p, (Some True, True))
      | "!-" ; p = V simple_type_parameter -> (p, (Some False, True))
      | "-!" ; p = V simple_type_parameter -> (p, (Some False, True))
      | p = V simple_type_parameter -> (p, (None, False))
      ] ]
  ;
  simple_type_parameter:
    [ [ "'"; i = ident -> Some i
      | "_" -> None ] ]
  ;
  record_type:
    [ [ "{"; ldl = V label_declarations "list"; "}" ->
      <:ctyp< { $_list:ldl$ } >> ] ]
  ;
  constructor_declaration:
    [ [ ci = cons_ident; (sl, tl, rto, alg_attrs) = rest_constructor_declaration ->
          (loc, ci, sl, tl, rto, alg_attrs)
      ] ]
  ;
  rest_constructor_declaration:
    [ [ "of"; cal = V (LIST1 (ctyp LEVEL "apply") SEP "*") ; alg_attrs = alg_attributes ->
          (<:vala< [] >>, cal, <:vala< None >>, alg_attrs)
      | "of"; cdrec = record_type ; alg_attrs = alg_attributes ->
          (<:vala< [] >>, Ploc.VaVal [cdrec], <:vala< None >>, alg_attrs)

      | ":"; check_type_binder ; ls = V (LIST1 typevar) ; "." ; cal = V (LIST1 (ctyp LEVEL "apply") SEP "*"); "->"; t = ctyp ; alg_attrs = alg_attributes ->
          (ls, cal, <:vala< Some t >>, alg_attrs)
      | ":" ; cal = V (LIST1 (ctyp LEVEL "apply") SEP "*"); "->"; t = ctyp ; alg_attrs = alg_attributes ->
          (<:vala< [] >>, cal, <:vala< Some t >>, alg_attrs)

      | ":"; cal = V (LIST1 (ctyp LEVEL "apply") SEP "*") ; alg_attrs = alg_attributes ->
          let t =
            match cal with
            [ <:vala< [t] >> -> t
            | <:vala< [t :: tl] >> -> <:ctyp< ($list:[t :: tl]$) >>
            | _ -> assert False ]
          in
          (<:vala< [] >>, <:vala< [] >>, <:vala< Some t >>, alg_attrs)

      | ":"; cdrec = record_type; "->"; t = ctyp ; alg_attrs = alg_attributes ->
          (<:vala< [] >>, Ploc.VaVal [cdrec], <:vala< Some t >>, alg_attrs)

      | alg_attrs = alg_attributes ->
          (<:vala< [] >>, <:vala< [] >>, <:vala< None >>, alg_attrs) ] ]
  ;
  extension_constructor:
  [ [ attrs = alg_attributes_no_anti; ci = cons_ident; "=" ; b = V longident "longid" ; alg_attrs = alg_attributes ->
        let alg_attrs = merge_left_auxiliary_attrs ~{nonterm_name="extension_constructor"} ~{left_name="algebraic attributes"} ~{right_name="item attributes"} attrs alg_attrs in
        <:extension_constructor< $_uid:ci$ = $_longid:b$ $_algattrs:alg_attrs$ >>

    | attrs = alg_attributes_no_anti; ci = cons_ident; (sl, tl, rto, alg_attrs) = rest_constructor_declaration ->
        let alg_attrs = merge_left_auxiliary_attrs ~{nonterm_name="extension_constructor"} ~{left_name="algebraic attributes"} ~{right_name="(right) algebraic attributes"} attrs alg_attrs in
        <:extension_constructor< $_uid:ci$ of $_list:sl$ . $_list:tl$ $_rto:rto$ $_algattrs:alg_attrs$ >>
(*
      MLast.EcTuple loc (loc, ci, sl, tl, rto, alg_attrs)
 *)
    ] ]
  ;
  cons_ident:
    [ [ i = V UIDENT "uid" "" -> i
      | UIDENT "True" -> <:vala< "True_" >>
      | UIDENT "False" -> <:vala< "False_" >>
      | "true" -> <:vala< "True" >>
      | "false" -> <:vala< "False" >>
      | "["; "]" -> <:vala< "[]" >>
      | "("; ")" -> <:vala< "()" >>
      | "("; "::" ; ")" -> <:vala< "::" >>
      ] ]
  ;
  label_declarations:
    [ [ (a,b,c,d, attrs1) = label_declaration; ";"; attrs2 = alg_attributes_no_anti ; ldl = SELF ->
          let attrs = merge_right_auxiliary_attrs ~{nonterm_name="label_declarations"}
          ~{left_name="algebraic attributes"} ~{right_name="algebraic attributes"} attrs1 attrs2 in
          [(a,b,c,d, attrs) :: ldl]
      | (a,b,c,d, attrs1) = label_declaration; ";"; attrs2 = alg_attributes_no_anti ->
          let attrs = merge_right_auxiliary_attrs ~{nonterm_name="label_declarations"}
          ~{left_name="algebraic attributes"} ~{right_name="algebraic attributes"} attrs1 attrs2 in
          [(a,b,c,d, attrs)]
      | (a,b,c,d, attrs1) = label_declaration -> [(a,b,c,d, attrs1)] ] ]
  ;
  label_declaration:
    [ [ i = LIDENT; ":"; t = poly_type_below_alg_attribute ; attrs = alg_attributes -> (loc, i, False, t, attrs)
      | "mutable"; i = LIDENT; ":"; t = poly_type_below_alg_attribute ; attrs = alg_attributes -> (loc, i, True, t, attrs) ] ]
  ;
  (* Core types *)
  longident:
    [ LEFTA
      [ me1 = SELF; check_dot_uid ; "."; i = V UIDENT "uid" →
          let i = vala_map uident_True_True_ i in
          <:extended_longident< $longid:me1$ . $_uid:i$ >>
      | i = V UIDENT "uid" →
          let i = vala_map uident_True_True_ i in
          <:extended_longident< $_uid:i$ >>
      ] ]
  ;
  extended_longident:
    [ LEFTA
      [ me1 = SELF; "(" ; me2 = SELF ; ")" → <:extended_longident< $longid:me1$ ( $longid:me2$ ) >>
      | me1 = SELF; check_dot_uid ; "."; i = V UIDENT "uid" →
          let i = vala_map uident_True_True_ i in
          <:extended_longident< $longid:me1$ . $_uid:i$ >>
      ]
    | "simple"
      [ i = V UIDENT "uid" →
          let i = vala_map uident_True_True_ i in
          <:extended_longident< $_uid:i$ >>
      ] ]
  ;
  ctyp_ident:
    [ LEFTA
      [ me1 = extended_longident ; "." ; i = V LIDENT "lid" → 
          <:ctyp< $longid:me1$ . $_lid:i$ >>
      | i = V LIDENT "lid" → 
          <:ctyp< $_lid:i$ >>
      ] 
    ]
  ;
  ctyp:
    [ 
      "alg_attribute" LEFTA
      [ ct = SELF ; "[@" ; attr = V attribute_body "attribute"; "]" ->
        <:ctyp< $ct$ [@ $_attribute:attr$ ] >>
      ]
    | "below_alg_attribute" [ t = NEXT -> t ]

    | [ t1 = SELF; "as"; "'"; i = ident -> <:ctyp< $t1$ as '$i$ >> ]
    | "arrow" RIGHTA
      [ t1 = SELF; "->"; t2 = SELF -> <:ctyp< $t1$ -> $t2$ >> ]
    | "star"
      [ t = SELF; "*"; tl = LIST1 (ctyp LEVEL "apply") SEP "*" ->
          <:ctyp< ( $list:[t :: tl]$ ) >> ]
    | "apply"
      [ t1 = SELF; t2 = SELF -> <:ctyp< $t2$ $t1$ >> ]
    | "ctyp2" LEFTA
      [ t = ctyp_ident → t ]
    | "simple"
      [ "'"; i = V ident "" -> <:ctyp< '$_:i$ >>
      | "_" -> <:ctyp< _ >>
      | e = alg_extension -> <:ctyp< [% $_extension:e$ ] >>
      | "("; "module"; (ext,attrs) = ext_attributes; mt = module_type; ")" -> 
          let mt = module_type_wrap_attrs mt attrs in
          let ct = <:ctyp< ( module $mt$ ) >> in
          ctyp_to_inline ct ext []

      | "("; t = SELF; ","; tl = LIST1 ctyp SEP ","; ")";
        i = ctyp LEVEL "ctyp2" ->
          List.fold_left (fun c a -> <:ctyp< $c$ $a$ >>) i [t :: tl]
      | "("; t = SELF; ")" -> <:ctyp< $t$ >> ] ]
  ;
  (* Identifiers *)
  ident:
    [ [ i = LIDENT -> i
      | i = UIDENT -> i ] ]
  ;
  (* Miscellaneous *)
  direction_flag:
    [ [ "to" -> True
      | "downto" -> False ] ]
  ;
  (* Objects and Classes *)
  str_item:
    [ [ "class"; ext = ext_opt; cd = V (LIST1 class_declaration SEP "and") ->
          str_item_to_inline <:str_item< class $_list:cd$ >> ext
      | "class"; "type"; ext = ext_opt; ctd = V (LIST1 class_type_declaration SEP "and") ->
          str_item_to_inline <:str_item< class type $_list:ctd$ >> ext ] ]
  ;
  sig_item:
    [ [ "class"; ext = ext_opt; cd = V (LIST1 class_description SEP "and") ->
          sig_item_to_inline <:sig_item< class $_list:cd$ >> ext
      | "class"; "type"; ext = ext_opt; ctd = V (LIST1 class_type_declaration SEP "and") ->
          sig_item_to_inline <:sig_item< class type $_list:ctd$ >> ext ] ]
  ;
  (* Class expressions *)
  class_declaration:
    [ [ alg_attrs = alg_attributes_no_anti; vf = V (FLAG "virtual"); ctp = class_type_parameters; i = V LIDENT;
        cfb = class_fun_binding ; item_attrs = item_attributes ->
          let attrs = merge_left_auxiliary_attrs ~{nonterm_name="class-decl"} ~{left_name="algebraic attributes"} ~{right_name="item attributes"} alg_attrs item_attrs in
          {MLast.ciLoc = loc; MLast.ciVir = vf; MLast.ciPrm = ctp;
           MLast.ciNam = i; MLast.ciExp = cfb; MLast.ciAttributes = attrs} ] ]
  ;
  class_fun_binding:
    [ [ "="; ce = class_expr -> ce
      | ":"; ct = class_type; "="; ce = class_expr ->
          <:class_expr< ($ce$ : $ct$) >>
      | p = patt LEVEL "simple"; cfb = SELF ->
          <:class_expr< fun $p$ -> $cfb$ >> ] ]
  ;
  class_type_parameters:
    [ [ -> (loc, <:vala< [] >>)
      | "["; tpl = V (LIST1 type_parameter SEP ","); "]" -> (loc, tpl) ] ]
  ;
  class_fun_def:
    [ [ p = patt LEVEL "simple"; "->"; ce = class_expr ->
          <:class_expr< fun $p$ -> $ce$ >>
      | p = patt LEVEL "simple"; cfd = SELF ->
          <:class_expr< fun $p$ -> $cfd$ >> ] ]
  ;
  class_expr:
    [ "top"
      [ "fun"; alg_attrs = alg_attributes_no_anti ;
        cfd = class_fun_def -> class_expr_wrap_attrs cfd alg_attrs
      | "let"; rf = V (FLAG "rec"); lb = V (LIST1 let_binding SEP "and");
        "in"; ce = SELF ->
          <:class_expr< let $_flag:rf$ $_list:lb$ in $ce$ >>
      | "let"; "open"; ovf = V (FLAG "!") "!"; alg_attrs = alg_attributes_no_anti; i = extended_longident; "in"; ce = SELF →
          class_expr_wrap_attrs <:class_expr< let open $_!:ovf$ $longid:i$ in $ce$ >> alg_attrs
      ]
    | "alg_attribute" LEFTA
      [ ct = SELF ; "[@" ; attr = V attribute_body "attribute"; "]" ->
        <:class_expr< $ct$ [@ $_attribute:attr$ ] >>
      ]
    | "extension" NONA [
         e = alg_extension -> <:class_expr< [% $_extension:e$ ] >>
      | e = NEXT -> e
      ]
    | [ ce = class_expr_apply -> ce ]
    ]
    ;
  class_expr_apply:
    [ "apply" LEFTA
      [ ce = SELF; e = expr LEVEL "label" ->
          <:class_expr< $ce$ $e$ >> ]
    | [ ce = class_expr_simple -> ce ]
    ]
    ;
  class_expr_simple:
    [ "simple"
      [ "["; ct = ctyp; ","; ctcl = LIST1 ctyp SEP ","; "]";
        cli = V longident_lident "lilongid" ->
          <:class_expr< [ $list:[ct :: ctcl]$ ] $_lilongid:cli$ >>

      | "["; ct = ctyp; "]"; cli = V longident_lident "lilongid" ->
          <:class_expr< [ $ct$ ] $_lilongid:cli$ >>
      | cli = V longident_lident "lilongid" -> 
          <:class_expr< $_lilongid:cli$ >>
      | "object"; alg_attrs = alg_attributes_no_anti; cspo = V (OPT class_self_patt);
        cf = V class_structure "list"; "end" ->
          class_expr_wrap_attrs <:class_expr< object $_opt:cspo$ $_list:cf$ end >> alg_attrs
      | "("; ce = class_expr; ":"; ct = class_type; ")" ->
          <:class_expr< ($ce$ : $ct$) >>
      | "("; ce = class_expr; ")" -> ce
      ] ]
  ;
  class_structure:
    [ [ cf = LIST0 class_str_item -> cf ] ]
  ;
  class_self_patt:
    [ [ "("; p = patt; ")" -> p
      | "("; p = patt; ":"; t = ctyp; ")" -> <:patt< ($p$ : $t$) >> ] ]
  ;
  priv_virt:
  [ [
      "private" ; "virtual" -> (True, True)
    | "private" -> (True, False)
    | "virtual"; "private" -> (True, True)
    | "virtual" -> (False, True)
    | -> (False, False)
    ] ]
  ;
  class_str_item:
    [ [ "inherit"; ovf = V (FLAG "!") "!"; alg_attrs = alg_attributes_no_anti; ce = class_expr; pb = V (OPT [ "as"; i = LIDENT -> i ]) ; item_attrs = item_attributes ->
          let attrs = merge_left_auxiliary_attrs ~{nonterm_name="cstr-inherit"} ~{left_name="algebraic attributes"} ~{right_name="item attributes"} alg_attrs item_attrs in
          <:class_str_item< inherit $_!:ovf$ $ce$ $_opt:pb$ $_itemattrs:attrs$ >>

      | "val"; ov = V (FLAG "!") "!"; alg_attrs = alg_attributes_no_anti; (mf, vf) = mut_virt; lab = V LIDENT "lid" ""; e = cvalue_binding_or_ctyp ; item_attrs = item_attributes ->
          let attrs = merge_left_auxiliary_attrs ~{nonterm_name="cstr-inherit"} ~{left_name="algebraic attributes"} ~{right_name="item attributes"} alg_attrs item_attrs in
          match (vf, e) with [
            (False, Left e) ->
              <:class_str_item< value $_!:ov$ $flag:mf$ $_lid:lab$ = $e$ $_itemattrs:attrs$ >>
          | (True, Left _) -> Ploc.raise loc (Stream.Error "val with definition cannot be virtual")
          | (False, Right _) -> Ploc.raise loc (Stream.Error "val without definition must be virtual")
          | (True, Right t) ->
              if Pcaml.unvala ov then
                Ploc.raise loc (Stream.Error "virtual value cannot override")
              else
                <:class_str_item< value virtual $flag:mf$ $_lid:lab$ : $t$ $_itemattrs:attrs$ >>
          ]
      | "method"; ov = V (FLAG "!") "!"; alg_attrs = alg_attributes_no_anti; (pf, vf) = priv_virt; l = V LIDENT "lid" ""; ":"; t = poly_type_below_alg_attribute ; item_attrs = item_attributes ->
          if Pcaml.unvala ov then
            Ploc.raise loc (Stream.Error "method without definition is not being overriden!")
          else if not vf then
            Ploc.raise loc (Stream.Error "method without definition must be virtual")
          else
            let attrs = merge_left_auxiliary_attrs ~{nonterm_name="cstr-inherit"} ~{left_name="algebraic attributes"} ~{right_name="item attributes"} alg_attrs item_attrs in
            <:class_str_item< method virtual $flag:pf$ $_lid:l$ : $t$ $_itemattrs:attrs$ >>

      | "method"; ov = V (FLAG "!") "!"; alg_attrs = alg_attributes_no_anti; (pf, vf) = priv_virt; l = V LIDENT "lid" ""; ":"; t = poly_type_below_alg_attribute; "="; e = expr ; item_attrs = item_attributes ->
          let attrs = merge_left_auxiliary_attrs ~{nonterm_name="cstr-inherit"} ~{left_name="algebraic attributes"} ~{right_name="item attributes"} alg_attrs item_attrs in
          <:class_str_item< method $_!:ov$ $priv:pf$ $_lid:l$ : $t$ = $e$ $_itemattrs:attrs$ >>

      | "method"; ov = V (FLAG "!") "!"; alg_attrs = alg_attributes_no_anti; (pf, vf) = priv_virt; l = V LIDENT "lid" ""; sb = fun_binding ; item_attrs = item_attributes ->
          let attrs = merge_left_auxiliary_attrs ~{nonterm_name="cstr-inherit"} ~{left_name="algebraic attributes"} ~{right_name="item attributes"} alg_attrs item_attrs in
          <:class_str_item< method $_!:ov$ $priv:pf$ $_lid:l$ = $sb$ $_itemattrs:attrs$ >>

      | "constraint"; t1 = ctyp; "="; t2 = ctyp ; attrs = item_attributes ->
          <:class_str_item< type $t1$ = $t2$ $_itemattrs:attrs$ >>
      | "initializer"; alg_attrs = alg_attributes_no_anti; se = expr ; item_attrs = item_attributes ->
          let attrs = merge_left_auxiliary_attrs ~{nonterm_name="cstr-inherit"} ~{left_name="algebraic attributes"} ~{right_name="item attributes"} alg_attrs item_attrs in
          <:class_str_item< initializer $se$ $_itemattrs:attrs$ >>
      | attr = floating_attribute -> <:class_str_item< [@@@ $_attribute:attr$ ] >>
      | e = item_extension -> <:class_str_item< [%% $_extension:e$ ] >>
      ] ]
  ;
  cvalue_binding_or_ctyp:
    [ [ "="; e = expr -> Left e
      | ":"; t = ctyp; "="; e = expr -> Left <:expr< ($e$ : $t$) >>
      | ":"; t = ctyp -> Right t
      | ":"; t = ctyp; ":>"; t2 = ctyp; "="; e = expr ->
          Left <:expr< ($e$ : $t$ :> $t2$) >>
      | ":>"; t = ctyp; "="; e = expr ->
          Left <:expr< ($e$ :> $t$) >>
      ] ]
  ;
  label:
    [ [ i = LIDENT -> i ] ]
  ;
  (* Class types *)
  class_type:
    [ [ test_ctyp_minusgreater; t = ctyp LEVEL "star"; "->"; ct = SELF ->
          <:class_type< [ $t$ ] -> $ct$ >>
      | cs = class_signature -> cs ] ]
  ;
  class_signature:
    [ "alg_attribute" LEFTA
      [ ct = SELF ; "[@" ; attr = V attribute_body "attribute"; "]" ->
        <:class_type< $ct$ [@ $_attribute:attr$ ] >>
      | "let"; "open"; ovf = V (FLAG "!") "!"; i = extended_longident; "in"; ce = SELF →
        <:class_type< let open $_!:ovf$ $longid:i$ in $ce$ >>
      ]

    | [ "["; tl = LIST1 ctyp SEP ","; "]"; id = SELF ->
          <:class_type< $id$ [ $list:tl$ ] >>
      | "object"; alg_attrs = alg_attributes_no_anti; cst = V (OPT class_self_type);
        csf = V (LIST0 class_sig_item); "end" ->
          class_type_wrap_attrs <:class_type< object $_opt:cst$ $_list:csf$ end >> alg_attrs ]
    | [ li = extended_longident; "."; i = V LIDENT → <:class_type< $longid:li$ . $_lid:i$ >>
      | i = V LIDENT → <:class_type< $_lid:i$ >>
      ] ]
  ;
  class_self_type:
    [ [ "("; t = ctyp; ")" -> t ] ]
  ;
  mut_virt:
  [ [
      "mutable" ; "virtual" -> (True, True)
    | "mutable" -> (True, False)
    | "virtual"; "mutable" -> (True, True)
    | "virtual" -> (False, True)
    | -> (False, False)
    ] ]
  ;
  class_sig_item:
    [ [ "inherit"; alg_attrs = alg_attributes_no_anti; cs = class_signature ; item_attrs = item_attributes ->
          let attrs = merge_left_auxiliary_attrs ~{nonterm_name="csig-inherit"} ~{left_name="algebraic attributes"} ~{right_name="item attributes"} alg_attrs item_attrs in
          <:class_sig_item< inherit $cs$ $_itemattrs:attrs$ >>
      | "val"; alg_attrs = alg_attributes_no_anti; (mf, vf) = mut_virt; l = V LIDENT "lid" ""; ":"; t = ctyp ; item_attrs = item_attributes ->
          let attrs = merge_left_auxiliary_attrs ~{nonterm_name="csig-inherit"} ~{left_name="algebraic attributes"} ~{right_name="item attributes"} alg_attrs item_attrs in
          <:class_sig_item< value $flag:mf$ $flag:vf$ $_lid:l$ : $t$ $_itemattrs:attrs$ >>
      | "method"; alg_attrs = alg_attributes_no_anti; "private"; "virtual"; l = V LIDENT "lid" ""; ":";
        t = poly_type_below_alg_attribute ; item_attrs = item_attributes ->
          let attrs = merge_left_auxiliary_attrs ~{nonterm_name="csig-inherit"} ~{left_name="algebraic attributes"} ~{right_name="item attributes"} alg_attrs item_attrs in
          <:class_sig_item< method virtual private $_lid:l$ : $t$ $_itemattrs:attrs$ >>
      | "method"; alg_attrs = alg_attributes_no_anti; "virtual"; "private"; l = V LIDENT "lid" ""; ":";
        t = poly_type_below_alg_attribute ; item_attrs = item_attributes ->
          let attrs = merge_left_auxiliary_attrs ~{nonterm_name="csig-inherit"} ~{left_name="algebraic attributes"} ~{right_name="item attributes"} alg_attrs item_attrs in
          <:class_sig_item< method virtual private $_lid:l$ : $t$ $_itemattrs:attrs$ >>
      | "method"; alg_attrs = alg_attributes_no_anti; "virtual"; l = V LIDENT "lid" ""; ":"; t = poly_type_below_alg_attribute ; item_attrs = item_attributes ->
          let attrs = merge_left_auxiliary_attrs ~{nonterm_name="csig-inherit"} ~{left_name="algebraic attributes"} ~{right_name="item attributes"} alg_attrs item_attrs in
          <:class_sig_item< method virtual $_lid:l$ : $t$ $_itemattrs:attrs$ >>
      | "method"; alg_attrs = alg_attributes_no_anti; "private"; l = V LIDENT "lid" ""; ":"; t = poly_type_below_alg_attribute ; item_attrs = item_attributes ->
          let attrs = merge_left_auxiliary_attrs ~{nonterm_name="csig-inherit"} ~{left_name="algebraic attributes"} ~{right_name="item attributes"} alg_attrs item_attrs in
          <:class_sig_item< method private $_lid:l$ : $t$ $_itemattrs:attrs$ >>
      | "method"; alg_attrs = alg_attributes_no_anti; l = V LIDENT "lid" ""; ":"; t = poly_type_below_alg_attribute ; item_attrs = item_attributes ->
          let attrs = merge_left_auxiliary_attrs ~{nonterm_name="csig-inherit"} ~{left_name="algebraic attributes"} ~{right_name="item attributes"} alg_attrs item_attrs in
          <:class_sig_item< method $_lid:l$ : $t$ $_itemattrs:attrs$ >>
      | "constraint"; alg_attrs = alg_attributes_no_anti; t1 = ctyp; "="; t2 = ctyp ; item_attrs = item_attributes ->
          let attrs = merge_left_auxiliary_attrs ~{nonterm_name="csig-inherit"} ~{left_name="algebraic attributes"} ~{right_name="item attributes"} alg_attrs item_attrs in
          <:class_sig_item< type $t1$ = $t2$ $_itemattrs:attrs$ >>
      | attr = floating_attribute -> <:class_sig_item< [@@@ $_attribute:attr$ ] >>
      | e = item_extension -> <:class_sig_item< [%% $_extension:e$ ] >>
      ] ]
  ;
  class_description:
    [ [ alg_attrs = alg_attributes_no_anti; vf = V (FLAG "virtual"); ctp = class_type_parameters; n = V LIDENT;
        ":"; ct = class_type ; item_attrs = item_attributes ->
          let attrs = merge_left_auxiliary_attrs ~{nonterm_name="class-description"} ~{left_name="algebraic attributes"} ~{right_name="item attributes"} alg_attrs item_attrs in
          {MLast.ciLoc = loc; MLast.ciVir = vf; MLast.ciPrm = ctp;
           MLast.ciNam = n; MLast.ciExp = ct; MLast.ciAttributes = attrs} ] ]
  ;
  class_type_declaration:
    [ [ alg_attrs = alg_attributes_no_anti; vf = V (FLAG "virtual"); ctp = class_type_parameters; n = V LIDENT;
        "="; cs = class_signature ; item_attrs = item_attributes ->
          let attrs = merge_left_auxiliary_attrs ~{nonterm_name="class-type-decl"} ~{left_name="algebraic attributes"} ~{right_name="item attributes"} alg_attrs item_attrs in
          {MLast.ciLoc = loc; MLast.ciVir = vf; MLast.ciPrm = ctp;
           MLast.ciNam = n; MLast.ciExp = cs; MLast.ciAttributes = attrs} ] ]
  ;
  (* Expressions *)
  expr: LEVEL "simple"
    [ LEFTA
      [ "new"; (ext,attrs) = ext_attributes; cli = V longident_lident "lilongid" -> 
          expr_to_inline <:expr< new $_lilongid:cli$ >> ext attrs
      | "object"; (ext,attrs) = ext_attributes; cspo = V (OPT class_self_patt);
        cf = V class_structure "list"; "end" ->
          expr_to_inline <:expr< object $_opt:cspo$ $_list:cf$ end >> ext attrs ] ]
  ;
  expr: LEVEL "."
    [ [ e = SELF; "#"; lab = V LIDENT "lid" -> <:expr< $e$ # $_lid:lab$ >>
      | e = SELF; op = HASHOP ; e2 = SELF -> <:expr< $lid:op$ $e$ $e2$ >>
      ] ]
  ;
  expr: LEVEL "simple"
    [ [ "("; e = SELF; ":"; t = ctyp; ":>"; t2 = ctyp; ")" ->
          <:expr< ($e$ : $t$ :> $t2$) >>
      | "("; e = SELF; ":>"; t = ctyp; ")" -> <:expr< ($e$ :> $t$) >>
      | "{<"; ">}" -> <:expr< {< >} >>
      | "{<"; fel = V field_expr_list "list"; ">}" ->
          <:expr< {< $_list:fel$ >} >> ] ]
  ;
  field_expr_list:
    [ [ l = label; "="; e = expr LEVEL "expr1"; ";"; fel = SELF ->
          [(l, e) :: fel]
      | l = label; "="; e = expr LEVEL "expr1"; ";" -> [(l, e)]
      | l = label; "="; e = expr LEVEL "expr1" -> [(l, e)] ] ]
  ;
  (* Core types *)
  ctyp: LEVEL "simple"
    [ [ "#"; cli = V extended_longident_lident "lilongid" ->
         <:ctyp< # $_lilongid:cli$ >>
      | "<"; ml = V meth_list "list"; v = V (FLAG ".."); ">" ->
          <:ctyp< < $_list:ml$ $_flag:v$ > >>
      | "<"; ".."; ">" ->
         <:ctyp< < .. > >>
      | "<"; ">" ->
          <:ctyp< < > >> ] ]
  ;
  meth_list:
    [ [ f = field; ";"; ml = SELF -> [f :: ml]
      | f = field; ";" -> [f]
      | f = field -> [f] ] ]
  ;
  field:
    [ [ check_lident_colon ; lab = LIDENT; ":"; t = poly_type_below_alg_attribute; alg_attrs = alg_attributes ->
       (Some lab, t, alg_attrs)
      | check_not_lident_colon ; t = poly_type_below_alg_attribute; alg_attrs = alg_attributes ->
       (None, t, alg_attrs)
      ] ]
  ;
  (* Polymorphic types *)
  typevar:
    [ [ "'"; i = ident -> i ] ]
  ;
  poly_type:
    [ [ "type"; nt = LIST1 LIDENT; "."; ct = ctyp ->
          <:ctyp< type $list:nt$ . $ct$ >>
      | test_typevar_list_dot; tpl = LIST1 typevar; "."; t2 = ctyp ->
          <:ctyp< ! $list:tpl$ . $t2$ >>
      | t = ctyp -> t ] ]
  ;
  poly_type_below_alg_attribute:
    [ [ "type"; nt = LIST1 LIDENT; "."; ct = ctyp ->
          <:ctyp< type $list:nt$ . $ct$ >>
      | test_typevar_list_dot; tpl = LIST1 typevar; "."; t2 = ctyp ->
          <:ctyp< ! $list:tpl$ . $t2$ >>
      | t = ctyp LEVEL "below_alg_attribute" -> t ] ]
  ;
  (* Identifiers *)
  longident_lident:
    [ [ li = V longident "longid"; "."; i = V LIDENT → (Some li, i)
      | i = V LIDENT → (None, i)
      ] ]
  ;
  extended_longident_lident:
    [ [ li = V extended_longident "longid"; "."; i = V LIDENT → (Some li, i)
      | i = V LIDENT → (None, i)
      ] ]
  ;
  (* Labels *)
  ctyp: AFTER "arrow"
    [ NONA
      [ i = V LIDENT; ":"; t = SELF -> <:ctyp< ~$_:i$: $t$ >>
      | i = V QUESTIONIDENTCOLON; t = SELF -> <:ctyp< ?$_:i$: $t$ >>
      | i = V QUESTIONIDENT; ":"; t = SELF -> <:ctyp< ?$_:i$: $t$ >>
      | "?" ; i = V LIDENT ; ":"; t = SELF -> <:ctyp< ?$_:i$: $t$ >>
    ] ]
  ;
  ctyp: LEVEL "simple"
    [ [ "["; OPT "|"; rfl = V (LIST1 poly_variant SEP "|"); "]" ->
          <:ctyp< [ = $_list:rfl$ ] >>
      | "["; ">"; "]" -> <:ctyp< [ > $list:[]$ ] >>
      | "["; ">"; OPT "|"; rfl = V (LIST1 poly_variant SEP "|"); "]" ->
          <:ctyp< [ > $_list:rfl$ ] >>
      | "[<"; OPT "|"; rfl = V (LIST1 poly_variant SEP "|"); "]" ->
          <:ctyp< [ < $_list:rfl$ ] >>
      | "[<"; OPT "|"; rfl = V (LIST1 poly_variant SEP "|"); ">";
        ntl = V (LIST1 name_tag); "]" ->
          <:ctyp< [ < $_list:rfl$ > $_list:ntl$ ] >> ] ]
  ;
  poly_variant:
    [ [ "`"; i = V ident "" ; alg_attrs = alg_attributes -> <:poly_variant< ` $_:i$ $_algattrs:alg_attrs$ >>
      | "`"; i = V ident ""; "of"; ao = V (FLAG "&");
        l = V (LIST1 (ctyp LEVEL "below_alg_attribute") SEP "&") ; alg_attrs = alg_attributes ->
          <:poly_variant< `$_:i$ of $_flag:ao$ $_list:l$ $_algattrs:alg_attrs$ >>
      | t = ctyp -> <:poly_variant< $t$ >> ] ]
  ;
  name_tag:
    [ [ "`"; i = ident -> i ] ]
  ;
  expr: LEVEL "expr1"
    [ [ "fun"; (ext,attrs) = ext_attributes; p = labeled_patt; (eo, e) = fun_def ->
          expr_to_inline <:expr< fun [ $p$ $opt:eo$ -> $e$ ] >> ext attrs ] ]
  ;
  expr: AFTER "apply"
    [ "label"
      [ i = V TILDEIDENTCOLON; e = SELF -> <:expr< ~{$_:i$ = $e$} >>
      | i = V TILDEIDENT -> <:expr< ~{$_:i$} >>
      | i = V QUESTIONIDENTCOLON; e = SELF -> <:expr< ?{$_:i$ = $e$} >>
      | i = V QUESTIONIDENT -> <:expr< ?{$_:i$} >> ] ]
  ;
  expr: LEVEL "simple"
    [ [ "`"; s = V ident "" -> <:expr< ` $_:s$ >> ] ]
  ;
  fun_def:
    [ [ p = labeled_patt; (eo, e) = SELF ->
          (None, <:expr< fun [ $p$ $opt:eo$ -> $e$ ] >>) ] ]
  ;
  fun_binding:
    [ [ p = labeled_patt; e = SELF -> <:expr< fun $p$ -> $e$ >> ] ]
  ;
  patt: LEVEL "simple"
    [ [ "`"; s = V ident "" -> <:patt< ` $_:s$ >>
      | "#"; lili = V extended_longident_lident "lilongid" -> <:patt< # $_lilongid:lili$ >>
      | p = labeled_patt -> p ] ]
  ;
  labeled_patt:
    [ [ i = V TILDEIDENTCOLON; p = patt LEVEL "simple" ->
           <:patt< ~{$_:i$ = $p$} >>
      | i = V TILDEIDENT ->
           <:patt< ~{$_:i$} >>
      | "~"; "("; i = LIDENT; ")" ->
           <:patt< ~{$lid:i$} >>
      | "~"; "("; i = LIDENT; ":"; t = ctyp; ")" ->
           <:patt< ~{$lid:i$ : $t$} >>
      | i = V QUESTIONIDENTCOLON; j = LIDENT ->
           <:patt< ?{$_:i$ = ?{$lid:j$}} >>
      | i = V QUESTIONIDENTCOLON; "_" ->
           <:patt< ?{$_:i$} >>
      | i = V QUESTIONIDENTCOLON; "("; p = patt; "="; e = expr; ")" ->
          <:patt< ?{$_:i$ = ?{$p$ = $e$}} >>
      | i = V QUESTIONIDENTCOLON; "("; p = patt; ":"; t = ctyp; ")" ->
          <:patt< ?{$_:i$ = ?{$p$ : $t$}} >>
      | i = V QUESTIONIDENTCOLON; "("; p = patt; ":"; t = ctyp; "=";
        e = expr; ")" ->
          <:patt< ?{$_:i$ = ?{$p$ : $t$ = $e$}} >>
      | i = V QUESTIONIDENTCOLON; "("; p = patt; ")" ->
          <:patt< ?{$_:i$ = ?{$p$}} >>
      | i = V QUESTIONIDENT -> <:patt< ?{$_:i$} >>
      | "?"; "("; i = LIDENT; "="; e = expr; ")" ->
          <:patt< ?{$lid:i$ = $e$} >>
      | "?"; "("; i = LIDENT; ":"; t = ctyp; "="; e = expr; ")" ->
          <:patt< ?{$lid:i$ : $t$ = $e$} >>
      | "?"; "("; i = LIDENT; ")" ->
          <:patt< ?{$lid:i$} >>
      | "?"; "("; i = LIDENT; ":"; t = ctyp; ")" ->
          <:patt< ?{$lid:i$ : $t$} >> ] ]
  ;
  class_type:
    [ [ i = LIDENT; ":"; t = ctyp LEVEL "apply"; "->"; ct = SELF ->
          <:class_type< [ ~$i$: $t$ ] -> $ct$ >>
      | i = V QUESTIONIDENTCOLON; t = ctyp LEVEL "apply"; "->"; ct = SELF ->
          <:class_type< [ ?$_:i$: $t$ ] -> $ct$ >>
      | i = V QUESTIONIDENT; ":"; t = ctyp LEVEL "apply"; "->"; ct = SELF ->
          <:class_type< [ ?$_:i$: $t$ ] -> $ct$ >>
      | "?"; i = V LIDENT;   ":";  t = ctyp LEVEL "apply"; "->"; ct = SELF ->
          <:class_type< [ ?$_:i$: $t$ ] -> $ct$ >>
      ] ]
  ;
  class_fun_binding:
    [ [ p = labeled_patt; cfb = SELF -> <:class_expr< fun $p$ -> $cfb$ >> ] ]
  ;
  class_fun_def:
    [ [ p = labeled_patt; "->"; ce = class_expr ->
          <:class_expr< fun $p$ -> $ce$ >>
      | p = labeled_patt; cfd = SELF ->
          <:class_expr< fun $p$ -> $cfd$ >> ] ]
  ;
END
;

(* Main entry points *)

EXTEND
  GLOBAL: interf implem use_file top_phrase expr patt;
  interf:
    [ [ si = sig_item_semi; (sil, stopped) = SELF -> ([si :: sil], stopped)
      | "#"; n = LIDENT; dp = OPT expr; ";;" ->
          ([(<:sig_item< # $lid:n$ $opt:dp$ >>, loc)], None)
      | EOI -> ([], Some loc) ] ]
  ;
  sig_item_semi:
    [ [ si = sig_item; OPT ";;" -> (si, loc) ] ]
  ;
  implem:
    [ [ si = str_item_semi; (sil, stopped) = SELF -> ([si :: sil], stopped)
      | "#"; n = LIDENT; dp = OPT expr; ";;" ->
          ([(<:str_item< # $lid:n$ $opt:dp$ >>, loc)], None)
      | EOI -> ([], Some loc) ] ]
  ;
  str_item_semi:
    [ [ /; si = str_item; OPT ";;" -> (si, loc) ] ]
  ;
  top_phrase:
    [ [ ph = phrase; ";;" -> Some ph
      | EOI -> None ] ]
  ;
  use_file:
    [ [ si = str_item; OPT ";;"; (sil, stopped) = SELF ->
          ([si :: sil], stopped)
      | "#"; n = LIDENT; dp = OPT expr; ";;" ->
          ([<:str_item< # $lid:n$ $opt:dp$ >>], True)
      | EOI -> ([], False) ] ]
  ;
  phrase:
    [ [ sti = str_item -> sti
      | "#"; n = LIDENT; dp = OPT expr ->
          <:str_item< # $lid:n$ $opt:dp$ >> ] ]
  ;
END;

Pcaml.add_option "-no_quot" (Arg.Set Plexer.no_quotations)
  "Don't parse quotations, allowing to use, e.g. \"<:>\" as token";
