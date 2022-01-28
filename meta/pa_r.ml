(* camlp5r *)
(* pa_r.ml,v *)
(* Copyright (c) INRIA 2007-2017 *)

#load "pa_extend.cmo";
#load "q_MLast.cmo";
#load "pa_macro.cmo";
#load "pa_macro_gram.cmo";

open Asttools;
open Pcaml;
open Mlsyntax.Revised;

Pcaml.syntax_name.val := "Revised";
Pcaml.no_constructors_arity.val := False;

do {
  let odfa = Plexer.dollar_for_antiquotation.val in
  let osrs = Plexer.simplest_raw_strings.val in
  Plexer.dollar_for_antiquotation.val := False;
  Plexer.simplest_raw_strings.val := False;
  Plexer.utf8_lexing.val := True;
  Grammar.Unsafe.gram_reinit gram (Plexer.gmake ());
  Plexer.dollar_for_antiquotation.val := odfa;
  Plexer.simplest_raw_strings.val := osrs ;
  Grammar.Unsafe.clear_entry attribute_body;
  Grammar.Unsafe.clear_entry interf;
  Grammar.Unsafe.clear_entry implem;
  Grammar.Unsafe.clear_entry top_phrase;
  Grammar.Unsafe.clear_entry use_file;
  Grammar.Unsafe.clear_entry functor_parameter;
  Grammar.Unsafe.clear_entry module_type;
  Grammar.Unsafe.clear_entry longident;
  Grammar.Unsafe.clear_entry longident_lident;
  Grammar.Unsafe.clear_entry extended_longident;
  Grammar.Unsafe.clear_entry module_expr;
  Grammar.Unsafe.clear_entry sig_item;
  Grammar.Unsafe.clear_entry str_item;
  Grammar.Unsafe.clear_entry signature;
  Grammar.Unsafe.clear_entry structure;
  Grammar.Unsafe.clear_entry expr;
  Grammar.Unsafe.clear_entry patt;
  Grammar.Unsafe.clear_entry ipatt;
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

Pcaml.add_option "-ignloaddir"
  (Arg.Unit (fun _ → add_directive "load" (fun _ → ())))
  "Ignore the #load directives in the input file.";

value mksequence2 loc =
  fun
  [ <:vala< [e] >> → e
  | seq → <:expr< do { $_list:seq$ } >> ]
;

value mksequence loc =
  fun
  [ [e] → e
  | el → <:expr< do { $list:el$ } >> ]
;

value mkmatchcase loc p aso w e =
  let p =
    match aso with
    [ Some p2 → <:patt< ($p$ as $p2$) >>
    | None → p ]
  in
  (p, w, e)
;

value neg_string n =
  let len = String.length n in
  if len > 0 && n.[0] = '-' then String.sub n 1 (len - 1) else "-" ^ n
;

value mklistexp loc last =
  loop True where rec loop top =
    fun
    [ [] →
        match last with
        [ Some e → e
        | None → <:expr< [] >> ]
    | [e1 :: el] →
        let loc = if top then loc else Ploc.encl (MLast.loc_of_expr e1) loc in
        <:expr< [$e1$ :: $loop False el$] >> ]
;

value mklistpat loc last =
  loop True where rec loop top =
    fun
    [ [] →
        match last with
        [ Some p → p
        | None → <:patt< $uid:"[]"$ >> ]
    | [p1 :: pl] →
        let loc = if top then loc else Ploc.encl (MLast.loc_of_patt p1) loc in
        <:patt< [$p1$ :: $loop False pl$] >> ]
;

value operator_rparen_f strm =
  let id x = x in
  let app suff s = s^suff in 
  let trials = [
    (1, Right (fun [ [(("LIDENT"|"UIDENT"),_) :: _] -> True | _ -> False ]))
  ; (2, Left (is_operator, id, [[("",")")]]))
  ; (2, Left (is_letop, id, [[("",")")]]))
  ; (2, Left (is_andop, id, [[("",")")]]))
  ; (4, Left (is_dotop, app "()", [[("","("); ("",")"); ("",")")]]))
  ; (4, Left (is_dotop, app "{}", [[("","{"); ("","}"); ("",")")]]))
  ; (4, Left (is_dotop, app "[]", [[("","["); ("","]"); ("",")")]]))

  ; (6, Left (is_dotop, app "(;..)", [[("","("); ("",";"); ("",".."); ("",")"); ("",")")]]))
  ; (6, Left (is_dotop, app "{;..}", [[("","{"); ("",";"); ("",".."); ("","}"); ("",")")]]))
  ; (6, Left (is_dotop, app "[;..]", [[("","["); ("",";"); ("",".."); ("","]"); ("",")")]]))

  ; (5, Left (is_dotop, app "()<-", [[("","("); ("",")"); ("","<-"); ("",")")]]))
  ; (5, Left (is_dotop, app "{}<-", [[("","{"); ("","}"); ("","<-"); ("",")")]]))
  ; (5, Left (is_dotop, app "[]<-", [[("","["); ("","]"); ("","<-"); ("",")")]]))

  ; (7, Left (is_dotop, app "(;..)<-", [[("","("); ("",";"); ("",".."); ("",")"); ("","<-"); ("",")")]]))
  ; (7, Left (is_dotop, app "{;..}<-", [[("","{"); ("",";"); ("",".."); ("","}"); ("","<-"); ("",")")]]))
  ; (7, Left (is_dotop, app "[;..]<-", [[("","["); ("",";"); ("",".."); ("","]"); ("","<-"); ("",")")]]))
  ] in
  let matchers = List.map (fun
    [ (n, Left (pred, xform, suffixes)) ->
      (n, Left (fun [
             [("",s) :: l] when pred s && List.mem l suffixes -> Some (xform s)
           | _ -> None]))
    | (n, Right f) -> (n, Right f)
    ]) trials in
  let (n, tok) = check_stream matchers strm in
  do { for i = 1 to n do { Stream.junk strm } ; tok }
;

value operator_rparen =
  Grammar.Entry.of_parser gram "operator_rparen"
    operator_rparen_f
;

value check_not_part_of_patt_f strm =
  let matchers = [
    (2, fun [ [("LIDENT", _); tok :: _] -> Some tok | _ -> None ])
  ; (4, fun [ [("", "("); ("", s); ("", ")"); tok :: _] when is_special_op s -> Some tok | _ -> None ])
  ; (6, fun [
              [("", "("); ("", s); ("", "("); ("", ")"); ("", ")"); tok :: _] when is_special_op s -> Some tok
            | [("", "("); ("", s); ("", "{"); ("", "}"); ("", ")"); tok :: _] when is_special_op s -> Some tok
            | [("", "("); ("", s); ("", "["); ("", "]"); ("", ")"); tok :: _] when is_special_op s -> Some tok
            | _ -> None ])
  ; (7, fun [
              [("", "("); ("", s); ("", "("); ("", ")"); ("", "<-"); ("", ")"); tok :: _] when is_special_op s -> Some tok
            | [("", "("); ("", s); ("", "{"); ("", "}"); ("", "<-"); ("", ")"); tok :: _] when is_special_op s -> Some tok
            | [("", "("); ("", s); ("", "["); ("", "]"); ("", "<-"); ("", ")"); tok :: _] when is_special_op s -> Some tok
            | _ -> None ])
  ; (8, fun [
              [("", "("); ("", s); ("", "("); ("", ";"); ("", ".."); ("", ")"); ("", ")"); tok :: _] when is_special_op s -> Some tok
            | [("", "("); ("", s); ("", "{"); ("", ";"); ("", ".."); ("", "}"); ("", ")"); tok :: _] when is_special_op s -> Some tok
            | [("", "("); ("", s); ("", "["); ("", ";"); ("", ".."); ("", "]"); ("", ")"); tok :: _] when is_special_op s -> Some tok
            | _ -> None ])
  ; (9, fun [
              [("", "("); ("", s); ("", "("); ("", ";"); ("", ".."); ("", ")"); ("", "<-"); ("", ")"); tok :: _] when is_special_op s -> Some tok
            | [("", "("); ("", s); ("", "{"); ("", ";"); ("", ".."); ("", "}"); ("", "<-"); ("", ")"); tok :: _] when is_special_op s -> Some tok
            | [("", "("); ("", s); ("", "["); ("", ";"); ("", ".."); ("", "]"); ("", "<-"); ("", ")"); tok :: _] when is_special_op s -> Some tok
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

value prefixop =
  Grammar.Entry.of_parser gram "prefixop"
    (parser
       [: `("", x) when is_prefixop x :] -> x)
;

value infixop0 =
  Grammar.Entry.of_parser gram "infixop0"
    (parser
       [: `("", x) when is_infixop0 x :] -> x)
;

value infixop1 =
  Grammar.Entry.of_parser gram "infixop1"
    (parser
       [: `("", x) when is_infixop1 x :] -> x)
;

value infixop2 =
  Grammar.Entry.of_parser gram "infixop2"
    (parser
       [: `("", x) when is_infixop2 x :] -> x)
;

value infixop3 =
  Grammar.Entry.of_parser gram "infixop3"
    (parser
       [: `("", x) when is_infixop3 x :] -> x)
;

value infixop4 =
  Grammar.Entry.of_parser gram "infixop4"
    (parser
       [: `("", x) when is_infixop4 x :] -> x)
;

value hashop =
  Grammar.Entry.of_parser gram "hashop"
    (parser
       [: `("", x) when is_hashop x :] -> x)
;

value letop =
  Grammar.Entry.of_parser gram "letop"
    (parser
       [: `("", x) when is_letop x :] -> x)
;

value andop =
  Grammar.Entry.of_parser gram "andop"
    (parser
       [: `("", x) when is_andop x :] -> x)
;

value dotop =
  Grammar.Entry.of_parser gram "dotop"
    (parser
       [: `("", x) when is_dotop x :] -> x)
;

value mktupexp loc e el = <:expr< ($list:[e::el]$) >>;
value mktuppat loc p pl = <:patt< ($list:[p::pl]$) >>;
value mktuptyp loc t tl = <:ctyp< ( $list:[t::tl]$ ) >>;

value mklabdecl loc i mf t attrs = (loc, i, mf, t, attrs);
value mkident i : string = i;

value rec generalized_type_of_type =
  fun
  [ <:ctyp< $t1$ → $t2$ >> →
      let (tl, rt) = generalized_type_of_type t2 in
      ([t1 :: tl], rt)
  | t → ([], t) ]
;

value warned = ref False;
value warning_deprecated_since_6_00 loc =
  if not warned.val then do {
    Pcaml.warning.val loc "syntax deprecated since version 6.00";
    warned.val := True
  }
  else ()
;

value build_op_attributed loc op attrs =
  List.fold_left (fun e a -> <:expr< $e$ [@ $attribute:a$ ] >>)
          <:expr< $lid:op$ >> attrs  
;

value build_letop_binder loc letop b l e =
  let (argpat, argexp) = (* TODO FIX THIS CHET *)
    List.fold_left (fun (argpat, argexp) (andop, (pat, exp)) ->
        (<:patt< ( $argpat$, $pat$ ) >>, <:expr< $lid:andop$ $argexp$ $exp$ >>))
      b l in
  <:expr< $lid:letop$ $argexp$ (fun $argpat$ -> $e$) >>
;

value check_let_exception_f = (fun strm ->
    match Stream.npeek 2 strm with
      [ [("", "let"); ("", "exception")] -> ()
      | _ -> raise Stream.Failure ])
;

value check_let_exception =
  Grammar.Entry.of_parser gram "check_let_exception"
    check_let_exception_f
;

value check_let_not_exception_f = (fun strm ->
       match Stream.npeek 2 strm with
       [ [("", "let"); ("", "exception")] -> raise Stream.Failure
       | [("", "let"); _] -> ()
       | _ -> raise Stream.Failure ])
;

value check_let_not_exception =
  Grammar.Entry.of_parser gram "check_let_not_exception"
    check_let_not_exception_f
;

value stream_peek_nth n strm =
  loop n (Stream.npeek n strm) where rec loop n =
    fun
    [ [] -> None
    | [x] -> if n == 1 then Some x else None
    | [_ :: l] -> loop (n - 1) l ]
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
    | Some ("ANTIQUOT_LOC",s)
      when (match Plexer.parse_antiloc s with [ Some(_, ("list"|"_list"|"lid"|"_lid"|"flag"|"_flag"), _) -> True | _ -> False ]) -> wrec (n+1)
    | Some ("ANTIQUOT_LOC",s)
      when (match Plexer.parse_antiloc s with [ Some(_, ("lilongid"|"_lilongid"), _) -> True | _ -> False ]) -> False
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

value check_uident_coloneq_f strm =
  match stream_npeek 2 strm with [
    [("UIDENT",_) ; ("", ":=")] -> ()
  | [("ANTIQUOT",qs); ("", ":=")] when prefix_eq "uid:" qs || prefix_eq "_uid:" qs -> ()
  | [("ANTIQUOT_LOC",s) ; ("", ":=") :: _]
    when (match Plexer.parse_antiloc s with [ Some(_, ("uid"|"_uid"), _) -> True | _ -> False ]) -> ()
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

value patt_wrap_attrs loc e l =
let rec wrec e = fun [
  [] -> e
| [h :: t] -> wrec <:patt< $e$ [@ $_attribute:h$ ] >> t
] in wrec e l
;

value patt_to_inline loc p ext attrs =
  let p = patt_wrap_attrs loc p attrs in
  match ext with [ None -> p
  | Some attrid ->
   <:patt< [% $attrid:attrid$ ? $patt:p$ ] >>
  ]
;

value class_expr_wrap_attrs loc e l =
let rec wrec e = fun [
  [] -> e
| [h :: t] -> wrec <:class_expr< $e$ [@ $_attribute:h$ ] >> t
] in wrec e l
;

value str_item_to_inline loc si ext =
  match ext with [ None -> si
  | Some attrid ->
   <:str_item< [%% $attrid:attrid$ $stri:si$ ; ] >>
  ]
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


(* -- begin copy from pa_r to q_MLast -- *)

EXTEND
  GLOBAL: sig_item str_item ctyp patt expr functor_parameter module_type
    module_expr longident longident_lident extended_longident signature
    structure class_type class_expr class_expr_simple class_sig_item class_str_item let_binding
    type_decl type_extension extension_constructor
    constructor_declaration label_declaration match_case ipatt
    with_constr poly_variant attribute_body alg_attribute alg_attributes
    check_type_decl check_type_extension check_dot_uid
    check_type_binder
    ext_attributes
    ;
  attribute_id:
  [ [ l = LIST1 [ i = LIDENT -> i | i = UIDENT -> i ] SEP "." -> (loc, String.concat "." l)
    | s = STRING -> (loc, s)
    ] ]
  ;
  attribute_structure:
    [ [ st = V (LIST1 [ s = str_item; ";" → s ]) "structure" → st ] ]
  ;
  attribute_signature:
    [ [ st = V (LIST1 [ s = sig_item; ";" → s ]) "signature" → st ] ]
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
  alg_attribute:
  [ [ "[@" ; attr = V attribute_body "attribute"; "]" -> attr
    ] ]
  ;
  item_attribute:
  [ [ "[@@" ; attr = V attribute_body "attribute"; "]" -> attr
    ] ]
  ;
  item_attributes:
  [ [ l = V (LIST0 item_attribute) "itemattrs" -> l ]
  ]
  ;
  alg_attributes:
  [ [ l = V (LIST0 alg_attribute) "algattrs" -> l ]
  ]
  ;
  alg_attributes_no_anti:
  [ [ l = (LIST0 alg_attribute) -> l ]
  ]
  ;
  item_extension:
  [ [ "[%%" ; e = V attribute_body "extension"; "]" -> e
    ] ]
  ;
  alg_extension:
  [ [ "[%" ; e = V attribute_body "extension"; "]" -> e
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
    [ [ "functor"; arg = V functor_parameter "functor_parameter" "fp"; "->";
        me = SELF →
          <:module_expr< functor $_fp:arg$ → $me$ >> ]
    | "alg_attribute" LEFTA
      [ e1 = SELF ; "[@" ; attr = V attribute_body "attribute"; "]" ->
        <:module_expr< $e1$ [@ $_attribute:attr$ ] >>
      ]
    | [ "struct"; st = structure; /; "end" →
          <:module_expr< struct $_list:st$ end >> ]
    | [ me1 = SELF; me2 = SELF → <:module_expr< $me1$ $me2$ >> ]
    | [ me1 = SELF; "."; me2 = SELF → <:module_expr< $me1$ . $me2$ >> ]
    | "simple"
      [ i = V UIDENT → <:module_expr< $_uid:i$ >>
      | "("; "value"; e = expr; ":"; mt1 = module_type; ":>"; mt2 = module_type; ")" →
          <:module_expr< (value $e$ : $mt1$ :> $mt2$) >>
      | "("; "value"; e = expr; ":"; mt1 = module_type; ")" →
          <:module_expr< (value $e$ : $mt1$) >>
      | "("; "value"; e = expr; ")" →
          <:module_expr< (value $e$) >>
      | "("; me = SELF; ":"; mt = module_type; ")" →
          <:module_expr< ( $me$ : $mt$ ) >>
      | "("; me = SELF; ")" → <:module_expr< $me$ >>
      | e = alg_extension -> <:module_expr< [% $_extension:e$ ] >>
      ] ]
  ;
  structure:
    [ [ st = V (LIST0 [ s = str_item; ";" → s ]) → st ] ]
  ;

  type_binder_opt: [ [
    check_type_binder ; ls = V (LIST1 typevar) ; "." -> ls
  | -> <:vala< [] >>
  ] ]
  ;
  str_item:
    [ "top"
      [ "declare"; st = V (LIST0 [ s = str_item; ";" → s ]); "end" →
          <:str_item< declare $_list:st$ end >>
      | "exception"; ec = V extension_constructor "excon" ; item_attrs = item_attributes →
          <:str_item< exception $_excon:ec$ $_itemattrs:item_attrs$ >>

      | "external"; i = V LIDENT "lid" ""; ":"; ls = type_binder_opt ; t = ctyp; "=";
        pd = V (LIST1 STRING) ; attrs = item_attributes →
          <:str_item< external $_lid:i$ : $_list:ls$ . $t$ = $_list:pd$ $_itemattrs:attrs$ >>

      | "external"; "("; i = operator_rparen; ":"; ls = type_binder_opt; t = ctyp; "=";
        pd = V (LIST1 STRING) ; attrs = item_attributes →
          <:str_item< external $lid:i$ : $_list:ls$ . $t$ = $_list:pd$ $_itemattrs:attrs$ >>

      | "include"; me = module_expr ; attrs = item_attributes → <:str_item< include $me$ $_itemattrs:attrs$ >>
      | "module"; r = V (FLAG "rec"); l = V (LIST1 mod_binding SEP "and") →
          <:str_item< module $_flag:r$ $_list:l$ >>
      | "module"; "type"; i = V ident "";  "="; mt = module_type ; attrs = item_attributes →
          <:str_item< module type $_:i$ = $mt$ $_itemattrs:attrs$ >>
      | "open"; ovf = V (FLAG "!") "!"; me = module_expr; attrs = item_attributes ->
          <:str_item< open $_!:ovf$ $me$ $_itemattrs:attrs$ >>
      | "type"; check_type_decl ; nrfl = V (FLAG "nonrec"); tdl = V (LIST1 type_decl SEP "and") → do {
          vala_it (fun tdl ->
            if List.exists (fun td -> not (Pcaml.unvala td.MLast.tdIsDecl)) tdl then
              failwith "type-declaration cannot mix decl and subst"
            else ()) tdl ;
            <:str_item< type $_flag:nrfl$ $_list:tdl$ >>
          }
      | "type" ; check_type_extension ; te = type_extension →
          <:str_item< type $_lilongid:te.MLast.teNam$ $_list:te.MLast.tePrm$ += $_priv:te.MLast.tePrv$ [ $_list:te.MLast.teECs$ ] $_itemattrs:te.MLast.teAttributes$ >>
      | "value"; ext = ext_opt; r = V (FLAG "rec"); l = V (LIST1 let_binding SEP "and") ->
          str_item_to_inline loc <:str_item< value $_flag:r$ $_list:l$ >> ext

      | "#"; n = V LIDENT "lid" ""; dp = V (OPT expr) →
          <:str_item< # $_lid:n$ $_opt:dp$ >>
      | "#"; s = V STRING; sil = V (LIST0 [ si = str_item → (si, loc) ]) →
          <:str_item< # $_str:s$ $_list:sil$ >>
      | e = expr ; attrs = item_attributes → <:str_item< $exp:e$ $_itemattrs:attrs$ >>
      | attr = floating_attribute -> <:str_item< [@@@ $_attribute:attr$ ] >>
      | e = item_extension ; attrs = item_attributes ->
        <:str_item< [%% $_extension:e$ ] $_itemattrs:attrs$ >>
      ] ]
  ;
  mod_binding:
    [ [ i = V uidopt "uidopt"; me = mod_fun_binding ;
        attrs = item_attributes → (i, me, attrs)
      ] ]
  ;
  mod_fun_binding:
    [ RIGHTA
      [ arg = V functor_parameter "functor_parameter" "fp"; mb = SELF →
          <:module_expr< functor $_fp:arg$ → $mb$ >>
      | ":"; mt = module_type; "="; me = module_expr →
          <:module_expr< ( $me$ : $mt$ ) >>
      | "="; me = module_expr → <:module_expr< $me$ >> ] ]
  ;
  module_type:
    [ [ "functor"; arg = V functor_parameter "functor_parameter" "fp" ; "->";
        mt = SELF →
          <:module_type< functor $_fp:arg$ → $mt$ >>
      ]
    | IFDEF OCAML_VERSION < OCAML_4_10_0 THEN ELSE
       "->" RIGHTA [ mt1=SELF ; "->" ; mt2=SELF ->
         <:module_type< $mt1$ → $mt2$ >>
       ]
      END
    | "alg_attribute" LEFTA
      [ e1 = SELF ; "[@" ; attr = V attribute_body "attribute"; "]" ->
        <:module_type< $e1$ [@ $_attribute:attr$ ] >>
      ]
    | [ mt = SELF; "with"; wcl = V (LIST1 with_constr SEP "and") →
          <:module_type< $mt$ with $_list:wcl$ >> ]
    | [ "sig"; sg = signature; /; "end" →
          <:module_type< sig $_list:sg$ end >>
      | "module"; "type"; "of"; me = module_expr →
          <:module_type< module type of $me$ >> ]
    | "simple"
      [ li = extended_longident; "."; i = V LIDENT → <:module_type< $longid:li$ . $_lid:i$ >>
      | li = extended_longident → <:module_type< $longid:li$ >>
      | i = V LIDENT → <:module_type< $_lid:i$ >>
      | e = alg_extension -> <:module_type< [% $_extension:e$ ] >>
      | "'"; i = V ident "" → <:module_type< ' $_:i$ >>
      | "("; mt = SELF; ")" → <:module_type< $mt$ >> ] ]
  ;
  signature:
    [ [ st = V (LIST0 [ s = sig_item; ";" → s ]) → st ] ]
  ;
  sig_item:
    [ "top"
      [ "declare"; st = V (LIST0 [ s = sig_item; ";" → s ]); "end" →
          <:sig_item< declare $_list:st$ end >>
      | "exception"; gc = constructor_declaration ; item_attrs = item_attributes →
          MLast.SgExc loc gc item_attrs
      | "external"; i = V LIDENT "lid" ""; ":"; ls = type_binder_opt ; t = ctyp; "=";
        pd = V (LIST1 STRING) ; attrs = item_attributes →
          <:sig_item< external $_lid:i$ : $_list:ls$ . $t$ = $_list:pd$ $_itemattrs:attrs$ >>

      | "external"; "("; i = operator_rparen; ":"; ls = type_binder_opt ; t = ctyp; "=";
        pd = V (LIST1 STRING) ; attrs = item_attributes →
          <:sig_item< external $lid:i$ : $_list:ls$ . $t$ = $_list:pd$ $_itemattrs:attrs$ >>

      | "include"; mt = module_type ; attrs = item_attributes → <:sig_item< include $mt$ $_itemattrs:attrs$ >>
      | "module"; rf = V (FLAG "rec");
        l = V (LIST1 mod_decl_binding SEP "and") →
          <:sig_item< module $_flag:rf$ $_list:l$ >>

      | "module"; check_uident_coloneq ; i = V UIDENT "uid" ; ":="; li = extended_longident ; attrs = item_attributes →
        <:sig_item< module $_uid:i$ := $longid:li$ $_itemattrs:attrs$ >>

      | "module"; "type"; i = V ident ""; "="; mt = module_type ; attrs = item_attributes →
          <:sig_item< module type $_:i$ = $mt$ $_itemattrs:attrs$ >>
      | "module"; "type"; i = V ident ""; ":="; mt = module_type ; attrs = item_attributes →
          <:sig_item< module type $_:i$ := $mt$ $_itemattrs:attrs$ >>
      | "module"; "alias"; i = V UIDENT "uid"; "="; li = V longident "longid" ; attrs = item_attributes →
          <:sig_item< module alias $_uid:i$ = $_longid:li$ $_itemattrs:attrs$ >>
      | "open"; i = extended_longident ; attrs = item_attributes → 
          <:sig_item< open $longid:i$ $_itemattrs:attrs$ >>
      | "type"; check_type_decl ; nrfl = V (FLAG "nonrec"); tdl = V (LIST1 type_decl SEP "and") → do {
            vala_it (fun tdl ->
              if List.for_all (fun td -> Pcaml.unvala td.MLast.tdIsDecl) tdl then ()
              else if List.for_all (fun td -> not (Pcaml.unvala td.MLast.tdIsDecl)) tdl then
                vala_it (fun nrfl ->
                    if nrfl then failwith "type-subst declaration must not specify <<nonrec>>" else ()) nrfl
              else failwith "type-declaration cannot mix decl and subst") tdl ;
            <:sig_item< type $_flag:nrfl$ $_list:tdl$ >>
          }
      | "type" ; check_type_extension ; te = type_extension →
          <:sig_item< type $_lilongid:te.MLast.teNam$ $_list:te.MLast.tePrm$ += $_priv:te.MLast.tePrv$ [ $_list:te.MLast.teECs$ ] $_itemattrs:te.MLast.teAttributes$ >>
      | "value"; i = V LIDENT "lid" ""; ":"; ls = type_binder_opt ; t = ctyp ; attrs = item_attributes →
        let t = match Pcaml.unvala ls with [ [] -> t | _ -> <:ctyp< ! $_list:ls$ . $t$ >> ] in
          <:sig_item< value $_lid:i$ : $t$ $_itemattrs:attrs$ >>

      | "value"; "("; i = operator_rparen; ":"; ls = type_binder_opt ; t = ctyp ; attrs = item_attributes →
        let t = match Pcaml.unvala ls with [ [] -> t | _ -> <:ctyp< ! $_list:ls$ . $t$ >> ] in
          <:sig_item< value $lid:i$ : $t$ $_itemattrs:attrs$ >>

      | "#"; n = V LIDENT "lid" ""; dp = V (OPT expr) →
          <:sig_item< # $_lid:n$ $_opt:dp$ >>
      | "#"; s = V STRING; sil = V (LIST0 [ si = sig_item → (si, loc) ]) →
          <:sig_item< # $_str:s$ $_list:sil$ >>
      | attr = floating_attribute -> <:sig_item< [@@@ $_attribute:attr$ ] >>
      | e = item_extension ; attrs = item_attributes ->
        <:sig_item< [%% $_extension:e$ ] $_itemattrs:attrs$ >>
      ] ]
  ;
  mod_decl_binding:
    [ [ i = V uidopt "uidopt"; mt = module_declaration ; attrs = item_attributes → (i, mt, attrs) ] ]
  ;
  module_declaration:
    [ RIGHTA
      [ ":"; mt = module_type → <:module_type< $mt$ >>
      | arg = V functor_parameter "functor_parameter" "fp" ; mt = SELF →
          <:module_type< functor $_fp:arg$ → $mt$ >>
 ] ]
  ;
  with_constr:
    [ [ "type"; i = V longident_lident "lilongid"; tpl = V (LIST0 type_parameter);
        "="; pf = V (FLAG "private"); t = ctyp_below_alg_attribute →
          <:with_constr< type $_lilongid:i$ $_list:tpl$ = $_flag:pf$ $t$ >>
      | "type"; i = V longident_lident "lilongid"; tpl = V (LIST0 type_parameter);
        ":="; t = ctyp_below_alg_attribute →
          <:with_constr< type $_lilongid:i$ $_list:tpl$ := $t$ >>
      | "module"; li = V longident "longid"; "="; me = module_expr →
          <:with_constr< module $_longid:li$ = $me$ >>
      | "module"; li = V longident "longid"; ":="; me = module_expr →
          <:with_constr< module $_longid:li$ := $me$ >>
      | "module"; "type"; li = V longident "longid"; "="; mt = module_type →
          <:with_constr< module type $_longid:li$ = $mt$ >>
      | "module"; "type"; li = V longident "longid"; ":="; mt = module_type →
          <:with_constr< module type $_longid:li$ := $mt$ >>
      ] ]
  ;
  uidopt:
    [ [ m = V UIDENT -> Some m
      | IFDEF OCAML_VERSION < OCAML_4_10_0 THEN ELSE
      | "_" -> None
        END
      ]
    ]
  ;
  andop_binding:
  [ [ op = andop ; b = letop_binding -> (op, b) ] ]
  ;
  ext_opt: [ [ ext = OPT [ "%" ; id = attribute_id -> id ] -> ext ] ] ;
  ext_attributes: [ [ e = ext_opt ; l = alg_attributes_no_anti -> (e, l) ] ] ;
  expr:
    [ "top" RIGHTA
      [ check_let_exception ; "let" ; "exception" ; id = V UIDENT "uid" ;
        "of" ; tyl = V (LIST1 ctyp_below_alg_attribute) ; alg_attrs = alg_attributes ; "in" ; x = SELF ->
        <:expr< let exception $_uid:id$ of $_list:tyl$ $_algattrs:alg_attrs$ in $x$ >>
      | check_let_exception ; "let" ; "exception" ; id = V UIDENT "uid" ; alg_attrs = alg_attributes ;
        "in" ; x = SELF ->
        <:expr< let exception $_uid:id$ $_algattrs:alg_attrs$ in $x$ >>

      | check_let_not_exception ; "let"; ext = ext_opt ; r = V (FLAG "rec"); l = V (LIST1 let_binding SEP "and"); "in";
        x = SELF →
          expr_to_inline <:expr< let $_flag:r$ $_list:l$ in $x$ >> ext []

      | letop = letop ; b = letop_binding ; l = LIST0 andop_binding; "in";
        x = expr LEVEL "top" ->
          build_letop_binder loc letop b l x

      | check_let_not_exception ; "let"; "module"; (ext,attrs) = ext_attributes; m = V uidopt "uidopt"; mb = mod_fun_binding; "in"; e = SELF →
          expr_to_inline <:expr< let module $_uidopt:m$ = $mb$ in $e$ >> ext attrs
      | check_let_not_exception ; "let"; "open"; ovf = V (FLAG "!") "!"; (ext,attrs) = ext_attributes; m = module_expr; "in"; e = SELF →
          expr_to_inline <:expr< let open $_!:ovf$ $m$ in $e$ >> ext attrs
      | "fun"; (ext,attrs) = ext_attributes; l = closed_case_list →
          expr_to_inline <:expr< fun [ $_list:l$ ] >> ext attrs
      | "fun"; (ext,attrs) = ext_attributes; p = ipatt; e = fun_def →
          expr_to_inline <:expr< fun $p$ → $e$ >> ext attrs
      | "match"; (ext,attrs) = ext_attributes; e = SELF; "with"; l = closed_case_list →
          expr_to_inline <:expr< match $e$ with [ $_list:l$ ] >> ext attrs
      | "match"; (ext,attrs) = ext_attributes; e = SELF; "with"; p1 = ipatt; "->"; e1 = SELF →
          expr_to_inline <:expr< match $e$ with $p1$ → $e1$ >> ext attrs
      | "try"; (ext,attrs) = ext_attributes; e = SELF; "with"; l = closed_case_list →
          expr_to_inline <:expr< try $e$ with [ $_list:l$ ] >> ext attrs
      | "try"; (ext,attrs) = ext_attributes; e = SELF; "with"; mc = match_case →
          expr_to_inline <:expr< try $e$ with [ $list:[mc]$ ] >> ext attrs
      | "if"; (ext,attrs) = ext_attributes; e1 = SELF; "then"; e2 = SELF; "else"; e3 = SELF →
          expr_to_inline <:expr< if $e1$ then $e2$ else $e3$ >> ext attrs
      | "do"; (ext,attrs) = ext_attributes; "{"; seq = V sequence "list"; "}" →
         expr_to_inline (mksequence2 loc seq) ext attrs
      | "for"; (ext,attrs) = ext_attributes; i = patt; "="; e1 = SELF; df = V direction_flag "to";
        e2 = SELF; "do"; "{"; seq = V sequence "list"; "}" →
          expr_to_inline <:expr< for $i$ = $e1$ $_to:df$ $e2$ do { $_list:seq$ } >> ext attrs
      | "while"; (ext,attrs) = ext_attributes; e = SELF; "do"; "{"; seq = V sequence "list"; "}" →
          expr_to_inline <:expr< while $e$ do { $_list:seq$ } >> ext attrs ]
    | "where"
      [ e = SELF; "where"; (ext,attrs) = ext_attributes; rf = V (FLAG "rec"); lb = let_binding →
          expr_to_inline <:expr< let $_flag:rf$ $list:[lb]$ in $e$ >> ext attrs ]
    | ":=" NONA
      [ e1 = SELF; ":="; e2 = SELF; dummy → <:expr< $e1$ := $e2$ >> ]
    | "||" RIGHTA
      [ e1 = SELF; "||"; e2 = SELF → <:expr< $e1$ || $e2$ >> ]
    | "&&" RIGHTA
      [ e1 = SELF; "&&"; e2 = SELF → <:expr< $e1$ && $e2$ >> ]
    | "<" LEFTA
      [ e1 = SELF; "<"; e2 = SELF → <:expr< $e1$ < $e2$ >>
      | e1 = SELF; ">"; e2 = SELF → <:expr< $e1$ > $e2$ >>
      | e1 = SELF; "<="; e2 = SELF → <:expr< $e1$ <= $e2$ >>
      | e1 = SELF; ">="; e2 = SELF → <:expr< $e1$ >= $e2$ >>
      | e1 = SELF; "="; e2 = SELF → <:expr< $e1$ = $e2$ >>
      | e1 = SELF; "<>"; e2 = SELF → <:expr< $e1$ <> $e2$ >>
      | e1 = SELF; "=="; e2 = SELF → <:expr< $e1$ == $e2$ >>
      | e1 = SELF; "!="; e2 = SELF → <:expr< $e1$ != $e2$ >>
      | e1 = SELF; op = infixop0; e2 = SELF -> <:expr< $lid:op$ $e1$ $e2$ >>
      ]
    | "^" RIGHTA
      [ e1 = SELF; "^"; e2 = SELF → <:expr< $e1$ ^ $e2$ >>
      | e1 = SELF; "@"; e2 = SELF → <:expr< $e1$ @ $e2$ >>
      | e1 = SELF; op = infixop1; e2 = SELF -> <:expr< $lid:op$ $e1$ $e2$ >>
      ]
    | "alg_attribute" LEFTA
      [ e1 = SELF ; "[@" ; attr = V attribute_body "attribute"; "]" ->
        <:expr< $e1$ [@ $_attribute:attr$ ] >>
      ]
    | "+" LEFTA
      [ e1 = SELF; "+"; e2 = SELF → <:expr< $e1$ + $e2$ >>
      | e1 = SELF; "-"; e2 = SELF → <:expr< $e1$ - $e2$ >>
      | e1 = SELF; "+."; e2 = SELF → <:expr< $e1$ +. $e2$ >>
      | e1 = SELF; "-."; e2 = SELF → <:expr< $e1$ -. $e2$ >>
      | e1 = SELF; op = infixop2; e2 = SELF -> <:expr< $lid:op$ $e1$ $e2$ >>
      ]
    | "*" LEFTA
      [ e1 = SELF; "*"; e2 = SELF → <:expr< $e1$ * $e2$ >>
      | e1 = SELF; "/"; e2 = SELF → <:expr< $e1$ / $e2$ >>
      | e1 = SELF; "*."; e2 = SELF → <:expr< $e1$ *. $e2$ >>
      | e1 = SELF; "/."; e2 = SELF → <:expr< $e1$ /. $e2$ >>
      | e1 = SELF; "land"; e2 = SELF → <:expr< $e1$ land $e2$ >>
      | e1 = SELF; "lor"; e2 = SELF → <:expr< $e1$ lor $e2$ >>
      | e1 = SELF; "lxor"; e2 = SELF → <:expr< $e1$ lxor $e2$ >>
      | e1 = SELF; "mod"; e2 = SELF → <:expr< $e1$ mod $e2$ >>
      | e1 = SELF; op = infixop3; e2 = SELF -> <:expr< $lid:op$ $e1$ $e2$ >>
      ]
    | "**" RIGHTA
      [ e1 = SELF; "**"; e2 = SELF → <:expr< $e1$ ** $e2$ >>
      | e1 = SELF; "asr"; e2 = SELF → <:expr< $e1$ asr $e2$ >>
      | e1 = SELF; "lsl"; e2 = SELF → <:expr< $e1$ lsl $e2$ >>
      | e1 = SELF; "lsr"; e2 = SELF → <:expr< $e1$ lsr $e2$ >>
      | e1 = SELF; op = infixop4; e2 = SELF -> <:expr< $lid:op$ $e1$ $e2$ >>
      ]
    | "unary minus" NONA
      [ "-"; e = SELF → <:expr< - $e$ >>
      | "-."; e = SELF → <:expr< -. $e$ >>
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
      [ e1 = SELF; e2 = SELF → <:expr< $e1$ $e2$ >>
      | "assert"; (ext,attrs) = ext_attributes; e = SELF →
          expr_to_inline <:expr< assert $e$ >> ext attrs
      | "lazy"; (ext,attrs) = ext_attributes; e = SELF → 
          expr_to_inline <:expr< lazy $e$ >> ext attrs ]
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

      | e1 = SELF; op = V dotop "dotop"; "("; el = V (LIST1 expr LEVEL "+" SEP ";"); ")" ->
          <:expr< $e1$ $_dotop:op$ ( $_list:el$ ) >>

      | e1 = SELF; "."; "["; e2 = SELF; "]" -> <:expr< $e1$ .[ $e2$ ] >>

      | e1 = SELF; op = V dotop "dotop"; "["; el = V (LIST1 expr LEVEL "+" SEP ";"); "]" ->
          <:expr< $e1$ $_dotop:op$ [ $_list:el$ ] >>

      | e1 = SELF; "."; "{"; el = V (LIST1 expr LEVEL "+" SEP ","); "}" ->
          <:expr< $e1$ .{ $_list:el$ } >>

      | e1 = SELF; op = V dotop "dotop"; "{"; el = V (LIST1 expr LEVEL "+" SEP ";"); "}" ->
          <:expr< $e1$ $_dotop:op$ { $_list:el$ } >>
      ]
    | "~-" NONA
      [ "~-"; e = SELF → <:expr< ~- $e$ >>
      | "~-."; e = SELF → <:expr< ~-. $e$ >>
      | f = prefixop; e = SELF -> <:expr< $lid:f$ $e$ >>
      ]
    | "simple"
      [ s = V INT → <:expr< $_int:s$ >>
      | s = V INT_l → <:expr< $_int32:s$ >>
      | s = V INT_L → <:expr< $_int64:s$ >>
      | s = V INT_n → <:expr< $_nativeint:s$ >>
      | s = V FLOAT → <:expr< $_flo:s$ >>
      | s = V STRING → <:expr< $_str:s$ >>
      | s = V CHAR → <:expr< $_chr:s$ >>
      | "." -> <:expr< . >>
      | e = alg_extension -> <:expr< [% $_extension:e$ ] >>
      | i = V LIDENT → <:expr< $_lid:i$ >>
      | i = V GIDENT → <:expr< $_lid:i$ >>
      | e = expr_longident → e
      | "["; "]" → <:expr< $uid:"[]"$ >>
      | "["; el = LIST1 expr SEP ";"; last = cons_expr_opt; "]" →
          mklistexp loc last el
      | "[|"; el = V (LIST0 expr SEP ";"); "|]" → <:expr< [| $_list:el$ |] >>
      | "{"; lel = V (LIST1 label_expr SEP ";"); "}" →
          <:expr< { $_list:lel$ } >>
      | "{"; "("; e = SELF; ")"; "with"; lel = V (LIST1 label_expr SEP ";");
        "}" →
          <:expr< { ($e$) with $_list:lel$ } >>
      | "("; ")" → <:expr< $uid:"()"$ >>
      | "("; "module"; me = module_expr; ":"; mt = module_type; ")" →
          <:expr< (module $me$ : $mt$) >>
      | "("; "module"; me = module_expr; ")" →
          <:expr< (module $me$) >>
      | "("; op = operator_rparen ->
          if op = "::" then
            <:expr< $uid:op$ >>
          else
            <:expr< $lid:op$ >>
      | "("; e = SELF; ":"; t = ctyp; ")" → <:expr< ($e$ : $t$) >>
      | "("; e = SELF; ","; el = LIST1 expr SEP ","; ")" → mktupexp loc e el
      | "("; e = SELF; ")" → <:expr< $e$ >>
      | "("; el = V (LIST1 expr SEP ","); ")" → <:expr< ($_list:el$) >> ] ]
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
  closed_case_list:
    [ [ "["; l = V (LIST0 match_case SEP "|"); "]" → l
      | "|"; l = V (LIST0 match_case SEP "|"); "end" → l ] ]
  ;
  cons_expr_opt:
    [ [ "::"; e = expr → Some e
      | → None ] ]
  ;
  dummy:
    [ [ → () ] ]
  ;
  sequence:
    [ RIGHTA
      [ "let"; rf = V (FLAG "rec"); l = V (LIST1 let_binding SEP "and");
        "in"; el = SELF →
          [<:expr< let $_flag:rf$ $_list:l$ in $mksequence loc el$ >>]
      | "let"; "module"; (ext,attrs) = ext_attributes; m = V uidopt "uidopt"; mb = mod_fun_binding; "in";
        el = SELF →
          [expr_to_inline <:expr< let module $_uidopt:m$ = $mb$ in $mksequence loc el$ >> ext attrs]
      | "let"; "open"; ovf = V (FLAG "!") "!"; (ext,attrs) = ext_attributes; m = module_expr; "in"; el = SELF →
          [expr_to_inline <:expr< let open $_!:ovf$ $m$ in $mksequence loc el$ >> ext attrs]
      | e = expr; ";"; el = SELF → [e :: el]
      | e = expr; ";" → [e]
      | e = expr → [e] ] ]
  ;
  let_binding:
    [ [ p = ipatt; check_colon ; e = fun_binding ; attrs = item_attributes →
          let (p,e) = match e with [
            <:expr< ( $e$ : $t$ ) >> -> (<:patt< ($p$ : $t$) >>, e)
          | _ -> (p,e)
          ] in
          (p, e, attrs)
      | p = ipatt; check_not_colon ; e = fun_binding ; attrs = item_attributes →
          (p, e, attrs)
      ] ]
  ;
  letop_binding:
    [ [ p = ipatt; e = fun_binding → (p, e) ] ]
  ;
  fun_binding:
    [ RIGHTA
      [ p = ipatt; e = SELF → <:expr< fun $p$ → $e$ >>
      | "="; e = expr → <:expr< $e$ >>
      | ":"; t = ctyp; "="; e = expr → <:expr< ($e$ : $t$) >> ] ]
  ;
  match_case:
    [ [ p = patt; aso = as_patt_opt; w = V (OPT when_expr); "->"; e = expr →
          mkmatchcase loc p aso w e
      ] ]
  ;
  as_patt_opt:
    [ [ "as"; p = patt → Some p
      | → None ] ]
  ;
  when_expr:
    [ [ "when"; e = expr → e ] ]
  ;
  label_expr:
    [ [ i = patt_label_ident; e = fun_binding → (i, e) ] ]
  ;
  fun_def:
    [ RIGHTA
      [ p = ipatt; e = SELF → <:expr< fun $p$ → $e$ >>
      | "->"; e = expr → e ] ]
  ;
  patt_ident: [
    [ s = V LIDENT → <:patt< $_lid:s$ >>
    | s = V GIDENT → <:patt< $_lid:s$ >>
    | li = longident ; "." ; p = patt LEVEL "simple" → 
      match p with [
        <:patt< $uid:i$ >> ->
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
      [ p1 = SELF; "|"; p2 = SELF → <:patt< $p1$ | $p2$ >> ]
    | "alg_attribute" LEFTA
      [ p = SELF ; "[@" ; attr = V attribute_body "attribute"; "]" ->
        <:patt< $p$ [@ $_attribute:attr$ ] >>
      ]
    | NONA [ "exception"; (ext,attrs) = ext_attributes; p = patt →
        patt_to_inline loc <:patt< exception $p$ >> ext attrs
      ]
    | NONA
      [ p1 = SELF; ".."; p2 = SELF → <:patt< $p1$ .. $p2$ >> ]
    | LEFTA
      [ p1 = SELF; p2 = SELF → <:patt< $p1$ $p2$ >>
      | "lazy"; (ext,attrs) = ext_attributes; p = SELF → 
          patt_to_inline loc <:patt< lazy $p$ >> ext attrs ]
    | "simple"
      [ p = patt_ident -> p
      | e = alg_extension -> <:patt< [% $_extension:e$ ] >>
      | s = V INT → <:patt< $_int:s$ >>
      | s = V INT_l → <:patt< $_int32:s$ >>
      | s = V INT_L → <:patt< $_int64:s$ >>
      | s = V INT_n → <:patt< $_nativeint:s$ >>
      | s = V FLOAT → <:patt< $_flo:s$ >>
      | s = V STRING → <:patt< $_str:s$ >>
      | s = V CHAR → <:patt< $_chr:s$ >>
      | "+"; s = V INT → <:patt< $_int:s$ >>
      | "+"; s = V FLOAT → <:patt< $_flo:s$ >>
      | "-"; s = INT → <:patt< $int:neg_string s$ >>
      | "-"; s = INT_l → <:patt< $int32:neg_string s$ >>
      | "-"; s = INT_L → <:patt< $int64:neg_string s$ >>
      | "-"; s = INT_n → <:patt< $nativeint:neg_string s$ >>
      | "-"; s = FLOAT → <:patt< $flo:neg_string s$ >>
      | "["; "]" → <:patt< $uid:"[]"$ >>
      | "["; pl = LIST1 patt SEP ";"; last = cons_patt_opt; "]" →
          mklistpat loc last pl
      | "[|"; pl = V (LIST0 patt SEP ";"); "|]" → <:patt< [| $_list:pl$ |] >>
      | "{"; lpl = V (LIST1 label_patt SEP ";"); "}" →
          <:patt< { $_list:lpl$ } >>
      | "("; op = operator_rparen ->
          if op = "::" then
            <:patt< $uid:op$ >>
          else
            <:patt< $lid:op$ >>
      | "("; p = paren_patt; ")" → p
      | "_" → <:patt< _ >> ] ]
  ;
  paren_patt:
    [ [ p = patt; ":"; t = ctyp → <:patt< ($p$ : $t$) >>
      | p = patt; "as"; p2 = patt → <:patt< ($p$ as $p2$) >>
      | p = patt; ","; pl = LIST1 patt SEP "," → mktuppat loc p pl
      | p = patt → <:patt< $p$ >>
      | pl = V (LIST1 patt SEP ",") → <:patt< ($_list:pl$) >>
      | "type"; s = V LIDENT → <:patt< (type $_lid:s$) >>
      | "module"; s = V uidopt "uidopt"; ":"; mt = module_type →
          <:patt< (module $_uidopt:s$ : $mt$) >>
      | "module"; s = V uidopt "uidopt" →
          <:patt< (module $_uidopt:s$) >>
      | → <:patt< $uid:"()"$ >>
 ] ]
  ;
  cons_patt_opt:
    [ [ "::"; p = patt → Some p
      | → None ] ]
  ;
  label_patt:
    [ [ i = patt_label_ident; "="; p = patt → (i, p) ] ]
  ;
  patt_label_ident:
    [
      [ p1 = longident; "."; p2 = SELF → <:patt< $longid:p1$ . $p2$ >>
      | i = V LIDENT → <:patt< $_lid:i$ >>
      ] ]
  ;
  ipatt:
    [ "top" LEFTA
      [ e1 = SELF ; "[@" ; attr = V attribute_body "attribute"; "]" ->
        <:patt< $e1$ [@ $_attribute:attr$ ] >>
      ]
    | "simple"
      [ p = patt_ident -> p
      | "("; op = operator_rparen ->
          if op = "::" then
            <:patt< $uid:op$ >>
          else
            <:patt< $lid:op$ >>
      | "{"; lpl = V (LIST1 label_ipatt SEP ";"); "}" →
          <:patt< { $_list:lpl$ } >>
      | "("; p = paren_ipatt; ")" → p
      | e = alg_extension -> <:patt< [% $_extension:e$ ] >>
      | "_" → <:patt< _ >> ] ]
  ;
  paren_ipatt:
    [ [ p = ipatt; ":"; t = ctyp → <:patt< ($p$ : $t$) >>
      | p = ipatt; "as"; p2 = ipatt → <:patt< ($p$ as $p2$) >>
      | p = ipatt; ","; pl = LIST1 ipatt SEP "," → mktuppat loc p pl
      | p = ipatt → <:patt< $p$ >>
      | pl = V (LIST1 ipatt SEP ",") → <:patt< ( $_list:pl$) >>
      | "type"; s = V LIDENT → <:patt< (type $_lid:s$) >>
      | "module"; s  = V uidopt "uidopt"; ":"; mt = module_type →
          <:patt< (module $_uidopt:s$ : $mt$) >>
      | "module"; s = V uidopt "uidopt" →
          <:patt< (module $_uidopt:s$) >>
      | → <:patt< $uid:"()"$ >>
 ] ]
  ;
  label_ipatt:
    [ [ i = patt_label_ident; "="; p = ipatt → (i, p) ] ]
  ;
  type_decl:
    [ [ n = V type_patt "tp"; tpl = V (LIST0 type_parameter);
        isDecl = V [ "=" -> True | ":=" -> False ] "isdecl" ;
        pf = V (FLAG "private") "priv"; tk = ctyp; cl = V (LIST0 constrain) ; attrs = item_attributes →
          <:type_decl< $_tp:n$ $_list:tpl$ $_isdecl:isDecl$ $_priv:pf$ $tk$ $_list:cl$ $_itemattrs:attrs$ >>
      ] ]
  ;
  type_extension:
    [ [ n = V longident_lident "lilongid"; tpl = V (LIST0 type_parameter); "+=";
        pf = V (FLAG "private") "priv"; "[" ; ecs = V (LIST1 extension_constructor SEP "|") ; "]" ;
        attrs = item_attributes →
          <:type_extension< $_lilongid:n$ $_list:tpl$ += $_priv:pf$ [ $_list:ecs$ ] $_itemattrs:attrs$ >>
(*
          {MLast.teNam=n; tePrm=tpl; tePrv=pf; teAttributes=attrs; teECs = ecs }
*)
      ] ]
  ;
  type_patt:
    [ [ n = V LIDENT → (loc, n) ] ]
  ;
  constrain:
    [ [ "constraint"; t1 = ctyp; "="; t2 = ctyp → (t1, t2) ] ]
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
    [ [ "'"; i = ident → Some i
      | i = GIDENT → Some (greek_ascii_equiv i)
      | "_" → None ] ]
  ;
  longident:
    [ LEFTA
      [ me1 = SELF; check_dot_uid ; "."; i = V UIDENT "uid" → <:extended_longident< $longid:me1$ . $_uid:i$ >>
      | i = V UIDENT "uid" → <:extended_longident< $_uid:i$ >>
      ] ]
  ;
  extended_longident:
    [ LEFTA
      [ me1 = SELF; "(" ; me2 = SELF ; ")" → <:extended_longident< $longid:me1$ ( $longid:me2$ ) >>
      | me1 = SELF; check_dot_uid ; "."; i = V UIDENT "uid" → <:extended_longident< $longid:me1$ . $_uid:i$ >>
      | i = V UIDENT "uid" → <:extended_longident< $_uid:i$ >>
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
    [ "top" LEFTA
      [ t1 = SELF; "=="; pf = V (FLAG "private") "priv"; t2 = SELF →
          <:ctyp< $t1$ == $_priv:pf$ $t2$ >> ]
    | "alg_attribute" LEFTA
      [ e1 = SELF ; "[@" ; attr = V attribute_body "attribute"; "]" ->
        <:ctyp< $e1$ [@ $_attribute:attr$ ] >>
      ]
    | "below_alg_attribute" [ t = NEXT -> t ]
    | "as" LEFTA
      [ t1 = SELF; "as"; t2 = SELF → <:ctyp< $t1$ as $t2$ >> ]
    | LEFTA
      [ "!"; pl = V (LIST1 typevar); "."; t = SELF →
          <:ctyp< ! $_list:pl$ . $t$ >>
      | "type"; pl = V (LIST1 LIDENT); "."; t = SELF →
          <:ctyp< type $_list:pl$ . $t$ >> ]
    | "arrow" RIGHTA
      [ t1 = SELF; "->"; t2 = SELF → <:ctyp< $t1$ → $t2$ >> ]
    | "apply" LEFTA
      [ t1 = SELF; t2 = SELF → <:ctyp< $t1$ $t2$ >> ]
    | LEFTA
      [ t = ctyp_ident → t ]
    | "simple"
      [ "'"; i = V ident "" → <:ctyp< '$_:i$ >>
      | i = GIDENT → <:ctyp< '$greek_ascii_equiv i$ >>
      | ".." -> <:ctyp< .. >>
      | "_" → <:ctyp< _ >>
      | e = alg_extension -> <:ctyp< [% $_extension:e$ ] >>
      | "(" ; "module"; mt = module_type ; ")" → <:ctyp< ( module $mt$ ) >>
      | "("; t = SELF; "*"; tl = LIST1 ctyp SEP "*"; ")" → mktuptyp loc t tl
      | "("; t = SELF; ")" → <:ctyp< $t$ >>
      | "("; tl = V (LIST1 ctyp SEP "*"); ")" → <:ctyp< ( $_list:tl$ ) >>
      | "["; cdl = V (LIST1 constructor_declaration SEP "|"); "]" →
          <:ctyp< [ $_list:cdl$ ] >>
      | "["; "|"; "]" →
          <:ctyp< [ $list:[]$ ] >>
      | "{"; ldl = V (LIST1 label_declaration SEP ";"); "}" →
          <:ctyp< { $_list:ldl$ } >> ] ]
  ;
  ctyp_below_alg_attribute:
  [ [ x = ctyp LEVEL "below_alg_attribute" -> x ]
  ]
  ;
  cons_ident:
  [ [ ci = V UIDENT "uid" "" -> ci
    | "[" ; "]" -> <:vala< "[]" >>
    | "(" ; ")" -> <:vala< "()" >>
    | "(" ; "::" ; ")" -> <:vala< "::" >>
    ] ] ;
  constructor_declaration:
    [ [ ci = cons_ident; (ls, tl,rto,attrs) = rest_constructor_declaration →
          <:constructor< $_uid:ci$ of $_list:ls$ . $_list:tl$ $_rto:rto$ $_algattrs:attrs$ >>
      ] ]
  ;
  rest_constructor_declaration:
    [ [ "of"; ls = type_binder_opt ; cal = V (LIST1 ctyp_below_alg_attribute SEP "and") ;
        rto = V (OPT [ ":"; t = ctyp_below_alg_attribute -> t ]) "rto" ; attrs = alg_attributes →
          (ls, cal, rto, attrs)
      | rto = V (OPT [ ":"; t = ctyp_below_alg_attribute -> t ]) "rto" ; attrs = alg_attributes →
          (<:vala< [] >>, <:vala< [] >>, rto, attrs)
      ] ]
  ;
  extension_constructor:
  [ [ ci = cons_ident ; "="; b = V longident "longid" ; alg_attrs = alg_attributes ->
        <:extension_constructor< $_uid:ci$ = $_longid:b$ $_algattrs:alg_attrs$ >>
    | ci = cons_ident; (ls, tl,rto,attrs) = rest_constructor_declaration →
        <:extension_constructor< $_uid:ci$ of $_list:ls$ . $_list:tl$ $_rto:rto$ $_algattrs:attrs$ >>
    ] ]
  ;

  label_declaration:
    [ [ i = LIDENT; ":"; mf = FLAG "mutable"; t = ctyp LEVEL "below_alg_attribute" ; attrs = alg_attributes →
          mklabdecl loc i mf t attrs ] ]
  ;
  ident:
    [ [ i = LIDENT → mkident i
      | i = UIDENT → mkident i ] ]
  ;
  direction_flag:
    [ [ "to" → True
      | "downto" → False ] ]
  ;
  typevar:
    [ [ "'"; i = ident → i 
      | i = GIDENT -> greek_ascii_equiv i
      ] ]
  ;
  (* Objects and Classes *)
  str_item:
    [ [ "class"; cd = V (LIST1 class_declaration SEP "and") →
          <:str_item< class $_list:cd$ >>
      | "class"; "type";
        ctd = V (LIST1 class_type_declaration SEP "and") →
          <:str_item< class type $_list:ctd$ >> ] ]
  ;
  sig_item:
    [ [ "class"; cd = V (LIST1 class_description SEP "and") →
          <:sig_item< class $_list:cd$ >>
      | "class"; "type"; ctd = V (LIST1 class_type_declaration SEP "and") →
          <:sig_item< class type $_list:ctd$ >> ] ]
  ;
  class_declaration:
    [ [ vf = V (FLAG "virtual"); i = V LIDENT; ctp = class_type_parameters;
        cfb = class_fun_binding ; attrs = item_attributes →
          {MLast.ciLoc = loc; MLast.ciVir = vf; MLast.ciPrm = ctp;
           MLast.ciNam = i; MLast.ciExp = cfb; MLast.ciAttributes = attrs} ] ]
  ;
  class_fun_binding:
    [ [ "="; ce = class_expr → ce
      | ":"; ct = class_type; "="; ce = class_expr →
          <:class_expr< ($ce$ : $ct$) >>
      | p = ipatt; cfb = SELF → <:class_expr< fun $p$ → $cfb$ >> ] ]
  ;
  class_type_parameters:
    [ [ → (loc, <:vala< [] >>)
      | "["; tpl = V (LIST1 type_parameter SEP ","); "]" → (loc, tpl) ] ]
  ;
  class_fun_def:
    [ [ p = ipatt; ce = SELF → <:class_expr< fun $p$ → $ce$ >>
      | "->"; ce = class_expr → ce ] ]
  ;
  class_expr:
    [ "top"
      [ "fun"; alg_attrs = alg_attributes_no_anti; p = ipatt; ce = class_fun_def →
          class_expr_wrap_attrs loc <:class_expr< fun $p$ → $ce$ >> alg_attrs
      | "let"; rf = V (FLAG "rec"); lb = V (LIST1 let_binding SEP "and");
        "in"; ce = SELF →
          <:class_expr< let $_flag:rf$ $_list:lb$ in $ce$ >>
      | "let"; "open"; ovf = V (FLAG "!") "!"; i = extended_longident; "in"; ce = SELF →
          <:class_expr< let open $_!:ovf$ $longid:i$ in $ce$ >>
      ]
    | "alg_attribute" LEFTA
      [ ct = SELF ; "[@" ; attr = V attribute_body "attribute"; "]" ->
        <:class_expr< $ct$ [@ $_attribute:attr$ ] >>
      ]
    | [ e = alg_extension -> <:class_expr< [% $_extension:e$ ] >>
      ]
    | [ ce = class_expr_apply -> ce ]
    ]
    ;
  class_expr_apply:
    [ "apply" LEFTA
      [ ce = SELF; e = expr LEVEL "label" →
          <:class_expr< $ce$ $exp:e$ >> ]
    | [ ce = class_expr_simple -> ce ]
    ]
    ;
  class_expr_simple:
    [ "simple"
      [ cli = V longident_lident "lilongid" →
          <:class_expr< $_lilongid:cli$ >>
      | "object"; cspo = V (OPT class_self_patt); cf = class_structure;
        "end" →
          <:class_expr< object $_opt:cspo$ $_list:cf$ end >>
      | "["; ctcl = V (LIST1 ctyp SEP ","); "]";
        cli = V longident_lident "lilongid" →
          <:class_expr< [ $_list:ctcl$ ] $_lilongid:cli$ >>
      | "("; ce = class_expr; ":"; ct = class_type; ")" →
          <:class_expr< ($ce$ : $ct$) >>
      | "("; ce = class_expr; ")" → ce
      ] ]
  ;
  class_structure:
    [ [ cf = V (LIST0 [ cf = class_str_item; ";" → cf ]) → cf ] ]
  ;
  class_self_patt:
    [ [ "("; p = patt; ")" → p
      | "("; p = patt; ":"; t = ctyp; ")" → <:patt< ($p$ : $t$) >> ] ]
  ;
  class_str_item:
    [ [ "declare"; st = V (LIST0 [ s= class_str_item; ";" → s ]); "end" →
          <:class_str_item< declare $_list:st$ end >>
      | "inherit"; ovf = V (FLAG "!") "!"; ce = class_expr; pb = V (OPT as_lident) ; attrs = item_attributes →
          <:class_str_item< inherit $_!:ovf$ $ce$ $_opt:pb$ $_itemattrs:attrs$ >>
      | "value"; ovf = V (FLAG "!") "!"; mf = V (FLAG "mutable");
        lab = V lident "lid" ""; e = cvalue_binding ; attrs = item_attributes →
          <:class_str_item< value $_!:ovf$ $_flag:mf$ $_lid:lab$ = $e$ $_itemattrs:attrs$ >>
      | "value"; "virtual"; mf = V (FLAG "mutable");
        lab = V lident "lid" ""; ":"; t = ctyp ; attrs = item_attributes →
          <:class_str_item< value virtual $_flag:mf$ $_lid:lab$ : $t$ $_itemattrs:attrs$ >>
      | "method"; "virtual"; pf = V (FLAG "private"); l = V lident "lid" "";
        ":"; t = ctyp ; attrs = item_attributes →
          <:class_str_item< method virtual $_flag:pf$ $_lid:l$ : $t$ $_itemattrs:attrs$ >>
      | "method"; ovf = V (FLAG "!") "!"; pf = V (FLAG "private") "priv";
        l = V lident "lid" ""; topt = V (OPT polyt); e = fun_binding ; attrs = item_attributes →
          <:class_str_item<
            method $_!:ovf$ $_priv:pf$ $_lid:l$ $_opt:topt$ = $e$ $_itemattrs:attrs$ >>
      | "type"; t1 = ctyp; "="; t2 = ctyp ; attrs = item_attributes →
          <:class_str_item< type $t1$ = $t2$ $_itemattrs:attrs$ >>
      | "initializer"; se = expr ; attrs = item_attributes → <:class_str_item< initializer $se$ $_itemattrs:attrs$ >>
      | attr = floating_attribute -> <:class_str_item< [@@@ $_attribute:attr$ ] >>
      | e = item_extension -> <:class_str_item< [%% $_extension:e$ ] >>
      ] ]
  ;
  as_lident:
    [ [ "as"; i = LIDENT → mkident i ] ]
  ;
  polyt:
    [ [ ":"; t = ctyp → t ] ]
  ;
  cvalue_binding:
    [ [ "="; e = expr → e
      | ":"; t = ctyp; "="; e = expr → <:expr< ($e$ : $t$) >>
      | ":"; t = ctyp; ":>"; t2 = ctyp; "="; e = expr →
          <:expr< ($e$ : $t$ :> $t2$) >>
      | ":>"; t = ctyp; "="; e = expr → <:expr< ($e$ :> $t$) >> ] ]
  ;
  lident:
    [ [ i = LIDENT → mkident i ] ]
  ;
  class_type:
    [ "top" RIGHTA
      [ "["; t = ctyp; "]"; "->"; ct = SELF →
          <:class_type< [ $t$ ] → $ct$ >>
      | "let"; "open"; ovf = V (FLAG "!") "!"; i = extended_longident; "in"; ce = SELF →
          <:class_type< let open $_!:ovf$ $longid:i$ in $ce$ >>
      ]
    | "alg_attribute" LEFTA
      [ ct = SELF ; "[@" ; attr = V attribute_body "attribute"; "]" ->
        <:class_type< $ct$ [@ $_attribute:attr$ ] >>
      ]

    | [ "object"; cst = V (OPT class_self_type);
        csf = V (LIST0 [ csf = class_sig_item; ";" → csf ]); "end" →
          <:class_type< object $_opt:cst$ $_list:csf$ end >>
      | ct = SELF; "["; tl = V (LIST1 ctyp SEP ","); "]" →
          <:class_type< $ct$ [ $_list:tl$ ] >> ]
    | "simple"
      [ li = extended_longident; "."; i = V LIDENT → <:class_type< $longid:li$ . $_lid:i$ >>
      | i = V LIDENT → <:class_type< $_lid:i$ >>
      | "("; ct = SELF; ")" → ct
      | e = alg_extension -> <:class_type< [% $_extension:e$ ] >>
 ] ]
  ;
  class_self_type:
    [ [ "("; t = ctyp; ")" → t ] ]
  ;
  class_sig_item:
    [ [ "declare"; st = V (LIST0 [ s = class_sig_item; ";" → s ]); "end" →
          <:class_sig_item< declare $_list:st$ end >>
      | "inherit"; cs = class_type ; attrs = item_attributes →
          <:class_sig_item< inherit $cs$ $_itemattrs:attrs$ >>
      | "value"; mf = V (FLAG "mutable"); vf = V (FLAG "virtual"); l = V lident "lid" ""; ":";
        t = ctyp ; attrs = item_attributes →
          <:class_sig_item< value $_flag:mf$ $_flag:vf$  $_lid:l$ : $t$ $_itemattrs:attrs$ >>
      | "method"; "virtual"; pf = V (FLAG "private"); l = V lident "lid" "";
        ":"; t = ctyp ; attrs = item_attributes →
          <:class_sig_item< method virtual $_flag:pf$ $_lid:l$ : $t$ $_itemattrs:attrs$ >>
      | "method"; pf = V (FLAG "private"); l = V lident "lid" ""; ":";
        t = ctyp ; attrs = item_attributes →
          <:class_sig_item< method $_flag:pf$ $_lid:l$ : $t$ $_itemattrs:attrs$ >>
      | "type"; t1 = ctyp; "="; t2 = ctyp ; attrs = item_attributes →
          <:class_sig_item< type $t1$ = $t2$ $_itemattrs:attrs$ >>
      | attr = floating_attribute -> <:class_sig_item< [@@@ $_attribute:attr$ ] >>
      | e = item_extension -> <:class_sig_item< [%% $_extension:e$ ] >>
      ] ]
  ;
  class_description:
    [ [ vf = V (FLAG "virtual"); n = V LIDENT; ctp = class_type_parameters;
        ":"; ct = class_type ; attrs = item_attributes →
          {MLast.ciLoc = loc; MLast.ciVir = vf; MLast.ciPrm = ctp;
           MLast.ciNam = n; MLast.ciExp = ct; MLast.ciAttributes = attrs} ] ]
  ;
  class_type_declaration:
    [ [ vf = V (FLAG "virtual"); n = V LIDENT; ctp = class_type_parameters;
        "="; cs = class_type ; attrs = item_attributes →
          {MLast.ciLoc = loc; MLast.ciVir = vf; MLast.ciPrm = ctp;
           MLast.ciNam = n; MLast.ciExp = cs; MLast.ciAttributes = attrs} ] ]
  ;
  expr: LEVEL "apply"
    [ LEFTA
      [ "new"; (ext,attrs) = ext_attributes; cli = V longident_lident "lilongid" → 
          expr_to_inline <:expr< new $_lilongid:cli$ >> ext attrs
      | "object"; (ext,attrs) = ext_attributes; cspo = V (OPT class_self_patt); cf = class_structure;
        "end" →
          expr_to_inline <:expr< object $_opt:cspo$ $_list:cf$ end >> ext attrs ] ]
  ;
  expr: LEVEL "."
    [ [ e = SELF; "#"; lab = V lident "lid" "" →
          <:expr< $e$ # $_lid:lab$ >>
      | e = SELF; op = hashop ; e2 = SELF -> <:expr< $lid:op$ $e$ $e2$ >>
      ] ]
  ;
  expr: LEVEL "simple"
    [ [ "("; e = SELF; ":"; t = ctyp; ":>"; t2 = ctyp; ")" →
          <:expr< ($e$ : $t$ :> $t2$ ) >>
      | "("; e = SELF; ":>"; t = ctyp; ")" → <:expr< ($e$ :> $t$) >>
      | "{<"; fel = V (LIST0 field_expr SEP ";"); ">}" →
          <:expr< {< $_list:fel$ >} >> ] ]
  ;
  field_expr:
    [ [ l = lident; "="; e = expr → (l, e) ] ]
  ;
  ctyp: LEVEL "simple"
    [ [ "#"; cli = V extended_longident_lident "lilongid" → <:ctyp< # $_lilongid:cli$ >>

      | "<"; ml = V (LIST0 field SEP ";"); v = V (FLAG ".."); ">" →
          <:ctyp< < $_list:ml$ $_flag:v$ > >> ] ]
  ;
  field:
    [ [ check_lident_colon ; lab = LIDENT; ":"; t = ctyp_below_alg_attribute; alg_attrs = alg_attributes →
        (Some (mkident lab), t, alg_attrs)
      | check_not_lident_colon ; t = ctyp_below_alg_attribute; alg_attrs = alg_attributes ->
        (None, t, alg_attrs)
      ] ]
  ;
  longident_lident:
    [ [ li = V longident "longid" ; "."; i = V LIDENT → (Some li, i)
      | i = V LIDENT → (None, i)
      ] ]
  ;
  extended_longident_lident:
    [ [ li = V extended_longident "longid" ; "."; i = V LIDENT → (Some li, i)
      | i = V LIDENT → (None, i)
      ] ]
  ;
  (* Labels *)
  ctyp: AFTER "arrow"
    [ NONA
      [ i = V TILDEIDENTCOLON; t = SELF → <:ctyp< ~$_:i$: $t$ >>
      | i = V QUESTIONIDENTCOLON; t = SELF → <:ctyp< ?$_:i$: $t$ >> ] ]
  ;
  ctyp: LEVEL "simple"
    [ [ "["; "="; rfl = poly_variant_list; "]" →
          <:ctyp< [ = $_list:rfl$ ] >>
      | "["; ">"; rfl = poly_variant_list; "]" →
          <:ctyp< [ > $_list:rfl$ ] >>
      | "["; "<"; rfl = poly_variant_list; "]" →
          <:ctyp< [ < $_list:rfl$ ] >>
      | "["; "<"; rfl = poly_variant_list; ">"; ntl = V (LIST1 name_tag);
        "]" →
          <:ctyp< [ < $_list:rfl$ > $_list:ntl$ ] >> ] ]
  ;
  poly_variant_list:
    [ [ rfl = V (LIST0 poly_variant SEP "|") → rfl ] ]
  ;
  poly_variant:
    [ [ "`"; i = V ident "" ; attrs = alg_attributes → <:poly_variant< ` $_:i$ $_algattrs:attrs$ >>
      | "`"; i = V ident ""; "of"; ao = V (FLAG "&");
        l = V (LIST1 ctyp_below_alg_attribute SEP "&") ; attrs = alg_attributes →
          <:poly_variant< ` $_:i$ of $_flag:ao$ $_list:l$ $_algattrs:attrs$ >>
      | t = ctyp → <:poly_variant< $t$ >> ] ]
  ;
  name_tag:
    [ [ "`"; i = ident → i ] ]
  ;
  patt: LEVEL "simple"
    [ [ "`"; s = V ident "" → <:patt< ` $_:s$ >>
      | "#"; lili = V extended_longident_lident "lilongid" → <:patt< # $_lilongid:lili$ >>
      | "~"; "{"; lppo = V (LIST1 patt_tcon_opt_eq_patt SEP ";"); "}" →
          <:patt< ~{$_list:lppo$} >>
      | "?"; "{"; p = patt_tcon; eo = V (OPT [ "="; e = expr → e ]); "}" →
          <:patt< ?{$p$ $_opt:eo$ } >>
      | i = V TILDEIDENTCOLON; p = SELF →
          let _ = warning_deprecated_since_6_00 loc in
          <:patt< ~{$_lid:i$ = $p$} >>
      | i = V TILDEIDENT →
          let _ = warning_deprecated_since_6_00 loc in
          <:patt< ~{$_lid:i$} >>
      | p = patt_option_label →
          let _ = warning_deprecated_since_6_00 loc in
          p ] ]
  ;
  patt_tcon_opt_eq_patt:
    [ [ p = patt_tcon; po = V (OPT [ "="; p = patt → p ]) → (p, po) ] ]
  ;
  patt_tcon:
    [ [ p = patt → p
      | p = patt; ":"; t = ctyp → <:patt< ($p$ : $t$) >> ] ]
  ;
  ipatt:
    [ [ "~"; "{"; lppo = V (LIST1 ipatt_tcon_opt_eq_patt SEP ";"); "}" →
          <:patt< ~{$_list:lppo$} >>
      | "?"; "{"; p = ipatt_tcon; eo = V (OPT [ "="; e = expr → e ]); "}" →
          <:patt< ?{$p$ $_opt:eo$ } >>

      | i = V TILDEIDENTCOLON; p = SELF →
          let _ = warning_deprecated_since_6_00 loc in
          <:patt< ~{$_lid:i$ = $p$} >>
      | i = V TILDEIDENT →
          let _ = warning_deprecated_since_6_00 loc in
          <:patt< ~{$_lid:i$} >>
      | p = patt_option_label →
          let _ = warning_deprecated_since_6_00 loc in
          p ] ]
  ;
  ipatt_tcon_opt_eq_patt:
    [ [ p = ipatt_tcon; po = V (OPT [ "="; p = patt → p ]) → (p, po) ] ]
  ;
  ipatt_tcon:
    [ [ p = ipatt → p
      | p = ipatt; ":"; t = ctyp → <:patt< ($p$ : $t$) >> ] ]
  ;
  patt_option_label:
    [ [ i = V QUESTIONIDENTCOLON; "("; j = V LIDENT; ":"; t = ctyp; "=";
        e = expr; ")" →
          <:patt< ?{$_lid:i$ : $t$ = ?{$_lid:j$ = $e$}} >>
      | i = V QUESTIONIDENTCOLON; "("; j = V LIDENT; ":"; t = ctyp; ")" →
          <:patt< ?{$_lid:i$ : $t$ = ?{$_lid:j$}} >>
      | i = V QUESTIONIDENTCOLON; "("; j = V LIDENT; "="; e = expr; ")" →
          <:patt< ?{$_lid:i$ = ?{$_lid:j$ = $e$}} >>
      | i = V QUESTIONIDENTCOLON; "("; j = V LIDENT; ")" →
          <:patt< ?{$_lid:i$ = $_lid:j$} >>
      | i = V QUESTIONIDENT →
          <:patt< ?{$_lid:i$} >>
      | "?"; "("; i = V LIDENT; ":"; t = ctyp; "="; e = expr; ")" →
          <:patt< ?{$_lid:i$ : $t$ = $e$} >>
      | "?"; "("; i = V LIDENT; ":"; t = ctyp; ")" →
          <:patt< ?{$_lid:i$ : $t$} >>
      | "?"; "("; i = V LIDENT; "="; e = expr; ")" →
          <:patt< ?{$_lid:i$ = $e$} >>
      | "?"; "("; i = V LIDENT; ")" →
          <:patt< ?{$_lid:i$} >> ] ]
  ;
  expr: AFTER "apply"
    [ "label" NONA
      [ "~"; "{"; lpeo = V (LIST1 ipatt_tcon_fun_binding SEP ";"); "}" →
          <:expr< ~{$_list:lpeo$ } >>
      | "?"; "{"; p = ipatt_tcon; eo = V (OPT fun_binding); "}" →
          <:expr< ?{$p$ $_opt:eo$ } >>
      | i = V TILDEIDENTCOLON; e = SELF →
          let _ = warning_deprecated_since_6_00 loc in
          <:expr< ~{$_lid:i$ = $e$} >>
      | i = V TILDEIDENT →
          let _ = warning_deprecated_since_6_00 loc in
          <:expr< ~{$_lid:i$} >>
      | i = V QUESTIONIDENTCOLON; e = SELF →
          let _ = warning_deprecated_since_6_00 loc in
          <:expr< ?{$_lid:i$ = $e$} >>
      | i = V QUESTIONIDENT →
          let _ = warning_deprecated_since_6_00 loc in
          <:expr< ?{$_lid:i$} >> ] ]
  ;
  ipatt_tcon_fun_binding:
    [ [ p = ipatt_tcon; eo = V (OPT fun_binding) → (p, eo) ] ]
  ;
  expr: LEVEL "simple"
    [ [ "`"; s = V ident "" → <:expr< ` $_:s$ >> ] ]
  ;
  (* -- cut 1 begin -- *)
  expr: [[]];
END;

(* -- cut 2 end -- *)
(* -- end copy from pa_r to q_MLast -- *)

value quotation_content s =
  loop 0 where rec loop i =
    if i = String.length s then ("", s)
    else if s.[i] = ':' || s.[i] = '@' then
      let i = i + 1 in
      (String.sub s 0 i, String.sub s i (String.length s - i))
    else loop (i + 1)
;

EXTEND
  GLOBAL: interf implem use_file top_phrase expr patt;
  interf:
    [ [ "#"; n = V LIDENT; dp = OPT expr; ";" →
          ([(<:sig_item< # $_lid:n$ $opt:dp$ >>, loc)], None)
      | si = sig_item_semi; (sil, stopped) = SELF →
          ([si :: sil], stopped)
      | EOI →
          ([], Some loc) ] ]
  ;
  sig_item_semi:
    [ [ si = sig_item; ";" → (si, loc) ] ]
  ;
  implem:
    [ [ "#"; n = V LIDENT; dp = OPT expr; ";" →
          ([(<:str_item< # $_lid:n$ $opt:dp$ >>, loc)], None)
      | si = str_item_semi; (sil, stopped) = SELF →
          ([si :: sil], stopped)
      | EOI →
          ([], Some loc) ] ]
  ;
  str_item_semi:
    [ [ si = str_item; ";" → (si, loc) ] ]
  ;
  top_phrase:
    [ [ ph = phrase → Some ph
      | EOI → None ] ]
  ;
  use_file:
    [ [ "#"; n = LIDENT; dp = OPT expr; ";" →
          ([<:str_item< # $lid:n$ $opt:dp$ >>], True)
      | si = str_item; ";"; (sil, stopped) = SELF → ([si :: sil], stopped)
      | EOI → ([], False) ] ]
  ;
  phrase:
    [ [ "#"; n = LIDENT; dp = OPT expr; ";" →
          <:str_item< # $lid:n$ $opt:dp$ >>
      | sti = str_item; ";" → sti ] ]
  ;
  expr: LEVEL "simple"
    [ [ x = QUOTATION →
          let con = quotation_content x in
          Pcaml.handle_expr_quotation loc con ] ]
  ;
  patt: LEVEL "simple"
    [ [ x = QUOTATION →
          let con = quotation_content x in
          Pcaml.handle_patt_quotation loc con ] ]
  ;
END;
