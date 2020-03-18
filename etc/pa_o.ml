(* camlp5r *)
(* pa_o.ml,v *)
(* Copyright (c) INRIA 2007-2017 *)

#load "pa_extend.cmo";
#load "q_MLast.cmo";
#load "pa_macro.cmo";
#load "pa_macro_gram.cmo";

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
  Grammar.Unsafe.clear_entry alg_attribute;
  Grammar.Unsafe.clear_entry alg_attributes;
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

value operator_rparen =
  Grammar.Entry.of_parser gram "operator_rparen"
    (fun strm ->
       match Stream.npeek 2 strm with
         [ [("", s); ("", ")")] when
                is_operator s || is_letop s || is_andop s -> do {
           Stream.junk strm;
           Stream.junk strm;
           s
         }
       | _ -> raise Stream.Failure ])
;

value check_not_part_of_patt =
  Grammar.Entry.of_parser gram "check_not_part_of_patt"
    (fun strm ->
       let tok =
         match Stream.npeek 4 strm with
         [ [("LIDENT", _); tok :: _] -> tok
         | [("", "("); ("", s); ("", ")"); tok] when is_operator s || is_letop s || is_andop s -> tok
         | _ -> raise Stream.Failure ]
       in
       match tok with
       [ ("", "," | "as" | "|" | "::") -> raise Stream.Failure
       | _ -> () ])
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

value test_constr_decl =
  Grammar.Entry.of_parser gram "test_constr_decl"
    (fun strm ->
       match Stream.npeek 1 strm with
       [ [("UIDENT", _)] ->
           match Stream.npeek 2 strm with
           [ [_; ("", ".")] -> raise Stream.Failure
           | [_; ("", "(")] -> raise Stream.Failure
           | [_ :: _] -> ()
           | _ -> raise Stream.Failure ]
       | [("", "|")] -> ()
       | _ -> raise Stream.Failure ])
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
  [ <:expr< $uid:_$ >> -> True
  | <:expr< $uid:_$.$e$ >> -> is_expr_constr_call e
  | <:expr< $e$ $_$ >> -> is_expr_constr_call e
  | _ -> False ]
;

value rec constr_expr_arity loc =
  fun
  [ <:expr< $uid:c$ >> ->
      try List.assoc c constr_arity.val with [ Not_found -> 0 ]
  | <:expr< $uid:_$.$e$ >> -> constr_expr_arity loc e
  | _ -> 1 ]
;

value rec constr_patt_arity loc =
  fun
  [ <:patt< $uid:c$ >> ->
      try List.assoc c constr_arity.val with [ Not_found -> 0 ]
  | <:patt< $uid:_$.$p$ >> -> constr_patt_arity loc p
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

value lbl_expr = Grammar.Entry.create Pcaml.gram "lbl_expr";
value lbl_expr_list = Grammar.Entry.create Pcaml.gram "lbl_expr_list";

value check_let_exception =
  Grammar.Entry.of_parser gram "check_let_exception"
    (fun strm ->
       match Stream.npeek 2 strm with
       [ [("", "let"); ("", "exception")] -> ()
       | _ -> raise Stream.Failure ])
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
  try check (Stream.of_string s)
  with Stream.Failure | (Stream.Error _) -> False
;

value is_type_decl_not_extension strm =
  let rec wrec n =
    match stream_peek_nth n strm with [
      None -> assert False
    | Some (
        ("","=")
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
       match Stream.npeek 3 strm with
       [ [("", "module"); ("UIDENT", _); ("", "=")] -> ()
       | _ -> raise Stream.Failure ])
;

value check_module_alias =
  Grammar.Entry.of_parser gram "check_module_alias"
    check_module_alias_f
;


value check_module_not_alias_f = (fun strm ->
       match Stream.npeek 3 strm with
       [ [("", "module"); ("UIDENT", _); ("", "=")] -> raise Stream.Failure
       | [("", "module") :: _] -> ()
       | _ -> raise Stream.Failure ])
;

value check_module_not_alias =
  Grammar.Entry.of_parser gram "check_module_not_alias"
    check_module_not_alias_f
;

value expr_wrap_attrs loc e l =
let rec wrec e = fun [
  [] -> e
| [h :: t] -> wrec <:expr< $e$ [@ $_attribute:h$ ] >> t
] in wrec e l
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
  match Stream.npeek 5 strm with [
    [("",".") ; ("UIDENT",_) :: _] -> ()
  | [("",".") ; ("","$") ; ("LIDENT",("uid"|"_uid")) ; ("", ":") ; ("LIDENT", _) :: _] -> ()
  | _ -> raise Stream.Failure
  ]
;

value check_dot_uid =
  Grammar.Entry.of_parser gram "check_dot_uid"
    check_dot_uid_f
;

value expr_to_inline loc e ext attrs =
  let e = expr_wrap_attrs loc e attrs in
  match ext with [ None -> e
  | Some attrid ->
   <:expr< [% $attrid:attrid$ $exp:e$ ; ] >>
  ]
;

value str_item_to_inline loc si ext =
  match ext with [ None -> si
  | Some attrid ->
   <:str_item< [%% $attrid:attrid$ $stri:si$ ; ] >>
  ]
;

EXTEND
  GLOBAL: sig_item str_item ctyp patt expr module_type
    module_expr extended_longident
    signature structure class_type class_expr class_sig_item class_str_item
    let_binding type_decl type_extension extension_constructor
    constructor_declaration label_declaration
    match_case with_constr poly_variant lbl_expr lbl_expr_list
    attribute_body alg_attribute alg_attributes
    ;
  attribute_id:
  [ [ l = LIST1 [ i = LIDENT -> i | i = UIDENT -> i ] SEP "." -> String.concat "." l
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
    [ [ "functor"; arg = V functor_parameter "functor_parameter" "fp";
        "->"; me = SELF ->
          <:module_expr< functor $_fp:arg$ -> $me$ >> ]
    | "alg_attribute" LEFTA
      [ e1 = SELF ; "[@" ; attr = V attribute_body "attribute"; "]" ->
        <:module_expr< $e1$ [@ $_attribute:attr$ ] >>
      ]
    | [ "struct"; OPT ";;"; st = structure; "end" ->
          <:module_expr< struct $_list:st$ end >> ]
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
      [  "("; "val"; e = expr; ":"; mt1 = module_type; ":>"; mt2 = module_type; ")" ->
         <:module_expr< (value $e$ : $mt1$ :> $mt2$) >>
      |  "("; "val"; e = expr; ":"; mt1 = module_type; ")" ->
         <:module_expr< (value $e$ : $mt1$) >>
      | "("; "val"; e = expr; ")" ->
         <:module_expr< (value $e$) >>
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
  extension_constructor:
  [ [ ci = cons_ident ; b = rebind_exn ; alg_attrs = alg_attributes ->
        <:extension_constructor< $_uid:ci$ = $_list:b$ $_algattrs:alg_attrs$ >>
    | ci = cons_ident; "of"; tl = V (LIST1 (ctyp LEVEL "apply") SEP "*") ; alg_attrs = alg_attributes ->
        <:extension_constructor< $_uid:ci$ of $_list:tl$ $_algattrs:alg_attrs$ >>

    | ci = cons_ident; "of"; cdrec = record_type ; alg_attrs = alg_attributes ->
        <:extension_constructor< $_uid:ci$ of $list:[cdrec]$ $_algattrs:alg_attrs$ >>

    | ci = cons_ident ; alg_attrs = alg_attributes ->
        <:extension_constructor< $_uid:ci$ $_algattrs:alg_attrs$ >>
    ] ]
  ;
  ext_opt: [ [ ext = OPT [ "%" ; id = attribute_id -> id ] -> ext ] ] ;
  ext_attributes: [ [ e = ext_opt ; l = alg_attributes_no_anti -> (e, l) ] ] ;
  str_item:
    [ "top"
      [ "exception"; ec = V extension_constructor "excon" ; item_attrs = item_attributes →
          <:str_item< exception $_excon:ec$ $_itemattrs:item_attrs$ >>

      | "external"; i = V LIDENT "lid" ""; ":"; t = ctyp; "=";
        pd = V (LIST1 STRING) ; attrs = item_attributes ->
          <:str_item< external $_lid:i$ : $t$ = $_list:pd$ $_itemattrs:attrs$ >>
      | "external"; "("; i = operator_rparen; ":"; t = ctyp; "=";
        pd = V (LIST1 STRING) ; attrs = item_attributes ->
          <:str_item< external $lid:i$ : $t$ = $_list:pd$ $_itemattrs:attrs$ >>
      | "include"; me = module_expr ; attrs = item_attributes -> <:str_item< include $me$ $_itemattrs:attrs$ >>
      | "module"; r = V (FLAG "rec"); l = V (LIST1 mod_binding SEP "and") ->
          <:str_item< module $_flag:r$ $_list:l$ >>
      | "module"; "type"; i = V ident ""; "="; mt = module_type ; attrs = item_attributes ->
          <:str_item< module type $_:i$ = $mt$ $_itemattrs:attrs$ >>
      | "module"; "type"; i = V ident "" ; attrs = item_attributes ->
          <:str_item< module type $_:i$ $_itemattrs:attrs$ >>
      | "open"; ovf = V (FLAG "!") "!"; me = module_expr ; attrs = item_attributes ->
          <:str_item< open $_!:ovf$ $me$ $_itemattrs:attrs$ >>
      | "type"; check_type_decl; nr = V (FLAG "nonrec"); tdl = V (LIST1 type_decl SEP "and") ->
          <:str_item< type $_flag:nr$ $_list:tdl$ >>
      | "type" ; check_type_extension ; te = type_extension →
          <:str_item< type $_tp:te.MLast.teNam$ $_list:te.MLast.tePrm$ += $_priv:te.MLast.tePrv$ $_list:te.MLast.teECs$ $_itemattrs:te.MLast.teAttributes$ >>

      | check_let_exception ; "let" ; "exception" ; id = V UIDENT ;
        "of" ; tyl = V (LIST1 ctyp LEVEL "apply") ; alg_attrs = alg_attributes ; "in" ; x = expr ; attrs = item_attributes ->
        let e = <:expr< let exception $_:id$ of $_list:tyl$ $_algattrs:alg_attrs$ in $x$ >> in
        <:str_item< $exp:e$ $_itemattrs:attrs$ >>
      | check_let_exception ; "let" ; "exception" ; id = V UIDENT ; alg_attrs = alg_attributes ;
        "in" ; x = expr ; attrs = item_attributes ->
        let e = <:expr< let exception $_:id$ $_algattrs:alg_attrs$ in $x$ >> in
        <:str_item< $exp:e$ $_itemattrs:attrs$ >>
      | check_let_not_exception ; "let"; ext = ext_opt ; r = V (FLAG "rec"); l = V (LIST1 let_binding SEP "and"); "in";
        x = expr ->
          let e = expr_to_inline loc <:expr< let $_flag:r$ $_list:l$ in $x$ >> ext [] in
          <:str_item< $exp:e$ >>

      | check_let_not_exception ; "let"; ext = ext_opt; r = V (FLAG "rec"); l = V (LIST1 let_binding SEP "and") ->
          let si = match l with
          [ <:vala< [(p, e, attrs)] >> ->
              match p with
              [ <:patt< _ >> -> <:str_item< $exp:e$ >> (* TODO FIX THIS CHET *)
              | _ -> <:str_item< value $_flag:r$ $_list:l$ >> ]
          | _ -> <:str_item< value $_flag:r$ $_list:l$ >> ] in
          str_item_to_inline loc si ext

      | check_let_not_exception ; "let"; "module"; (ext,attrs) = ext_attributes; m = V uidopt "uidopt"; mb = mod_fun_binding; "in";
        e = expr ->
          let e = expr_to_inline loc <:expr< let module $_uidopt:m$ = $mb$ in $e$ >> ext attrs in
          <:str_item< $exp:e$ >>

      | check_let_not_exception ; "let"; "open"; (ext, attrs) = ext_attributes; m = module_expr; "in"; e = expr ->
          let e = expr_to_inline loc <:expr< let open $m$ in $e$ >> ext attrs in
          <:str_item< $exp:e$ >>

      | e = expr ; attrs = item_attributes -> <:str_item< $exp:e$ $_itemattrs:attrs$ >>
      | attr = floating_attribute -> <:str_item< [@@@ $_attribute:attr$ ] >>
      | e = item_extension -> <:str_item< [%% $_extension:e$ ] >>
      ] ]
  ;
  rebind_exn:
    [ [ "="; sl = V mod_ident "list" -> sl ] ]
  ;
  mod_binding:
    [ [ i = V uidopt "uidopt"; me = mod_fun_binding ;
        attrs = item_attributes -> (i, me, attrs) ] ]
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
    [ [ "functor"; arg = V functor_parameter "functor_parameter" "fp"; "->";
        mt = SELF ->
          <:module_type< functor $_fp:arg$ -> $mt$ >>
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
    | [ "sig"; sg = signature; "end" ->
          <:module_type< sig $_list:sg$ end >>
      | "module"; "type"; "of"; me = module_expr ->
          <:module_type< module type of $me$ >>
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
      [ "exception"; (_, c, tl, _) = constructor_declaration_sans_alg_attrs ; alg_attrs = alg_attributes ; item_attrs = item_attributes ->
          <:sig_item< exception $_uid:c$ of $_list:tl$ $_algattrs:alg_attrs$ $_itemattrs:item_attrs$ >>
      | "external"; i = V LIDENT "lid" ""; ":"; t = ctyp; "=";
        pd = V (LIST1 STRING) ; attrs = item_attributes ->
          <:sig_item< external $_lid:i$ : $t$ = $_list:pd$ $_itemattrs:attrs$ >>
      | "external"; "("; i = operator_rparen; ":"; t = ctyp; "=";
        pd = V (LIST1 STRING) ; attrs = item_attributes ->
          <:sig_item< external $lid:i$ : $t$ = $_list:pd$ $_itemattrs:attrs$ >>
      | "include"; mt = module_type ; attrs = item_attributes →
          <:sig_item< include $mt$ $_itemattrs:attrs$ >>
      | check_module_not_alias; "module"; rf = FLAG "rec";
        l = LIST1 mod_decl_binding SEP "and" ->
          <:sig_item< module $flag:rf$ $list:l$ >>
      | check_module_alias; "module"; i = UIDENT; "="; li = mod_ident ; attrs = item_attributes →
          <:sig_item< module alias $i$ = $li$ $_itemattrs:attrs$ >>
      | "module"; "type"; i = V ident ""; "="; mt = module_type ; attrs = item_attributes ->
          <:sig_item< module type $_:i$ = $mt$ $_itemattrs:attrs$ >>
      | "module"; "type"; i = V ident "" ; attrs = item_attributes ->
          <:sig_item< module type $_:i$ $_itemattrs:attrs$ >>
      | "open"; i = extended_longident ; attrs = item_attributes ->
          <:sig_item< open $longid:i$ $_itemattrs:attrs$ >>
      | "type"; check_type_decl ; nrfl = V (FLAG "nonrec"); tdl = V (LIST1 type_decl SEP "and") ->
          <:sig_item< type $_flag:nrfl$ $_list:tdl$ >>
      | "type" ; check_type_extension ; te = type_extension →
          <:sig_item< type $_tp:te.MLast.teNam$ $_list:te.MLast.tePrm$ += $_priv:te.MLast.tePrv$ $_list:te.MLast.teECs$ $_itemattrs:te.MLast.teAttributes$ >>

      | "val"; attrs1 = alg_attributes_no_anti; i = V LIDENT "lid" ""; ":"; t = ctyp ; attrs2 = item_attributes ->
          let attrs = merge_left_auxiliary_attrs ~{nonterm_name="sig_item"} ~{left_name="algebraic attributes"} ~{right_name="item attributes"} attrs1 attrs2 in
          <:sig_item< value $_lid:i$ : $t$ $_itemattrs:attrs$ >>
      | "val"; attrs1 = alg_attributes_no_anti; "("; i = operator_rparen; ":"; t = ctyp ; attrs2 = item_attributes ->
          let attrs = merge_left_auxiliary_attrs ~{nonterm_name="sig_item"} ~{left_name="algebraic attributes"} ~{right_name="item attributes"} attrs1 attrs2 in
          <:sig_item< value $lid:i$ : $t$ $_itemattrs:attrs$ >>
      | attr = floating_attribute -> <:sig_item< [@@@ $_attribute:attr$ ] >>
      | e = item_extension -> <:sig_item< [%% $_extension:e$ ] >>
      ] ]
  ;
  mod_decl_binding:
    [ [ i = uidopt_no_anti ; mt = module_declaration ; attrs = item_attributes -> (Ploc.VaVal i, mt, attrs) ] ]
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
    [ [ "type"; tpl = V type_parameters "list"; i = V mod_ident ""; "=";
        pf = V (FLAG "private"); t = ctyp LEVEL "below_alg_attribute" ->
          <:with_constr< type $_:i$ $_list:tpl$ = $_flag:pf$ $t$ >>
      | "type"; tpl = V type_parameters "list"; i = V mod_ident ""; ":=";
        t = ctyp LEVEL "below_alg_attribute" ->
          <:with_constr< type $_:i$ $_list:tpl$ := $t$ >>
      | "module"; i = V mod_ident ""; "="; me = module_expr ->
          <:with_constr< module $_:i$ = $me$ >>
      | "module"; i = V mod_ident ""; ":="; me = module_expr ->
          <:with_constr< module $_:i$ := $me$ >> ] ]
  ;
  andop_binding:
  [ [ op = andop ; b = letop_binding -> (op, b) ] ]
  ;
  (* Core expressions *)
  expr:
    [ "top" RIGHTA
      [ e1 = SELF; ";"; e2 = SELF ->
          <:expr< do { $list:[e1 :: get_seq e2]$ } >>
      | e1 = SELF; ";" -> e1
      | el = V e_phony "list" -> <:expr< do { $_list:el$ } >> ]
    | "expr1"
      [ check_let_exception ; "let" ; "exception" ; id = V UIDENT ;
        "of" ; tyl = V (LIST1 ctyp LEVEL "apply") ; alg_attrs = alg_attributes ; "in" ; x = SELF ->
        <:expr< let exception $_:id$ of $_list:tyl$ $_algattrs:alg_attrs$ in $x$ >>
      | check_let_exception ; "let" ; "exception" ; id = V UIDENT ; alg_attrs = alg_attributes ;
        "in" ; x = SELF ->
        <:expr< let exception $_:id$ $_algattrs:alg_attrs$ in $x$ >>
      | check_let_not_exception ; "let"; ext = ext_opt; o = V (FLAG "rec"); l = V (LIST1 let_binding SEP "and"); "in";
        x = expr LEVEL "top" ->
          expr_to_inline loc <:expr< let $_flag:o$ $_list:l$ in $x$ >> ext []

      | check_let_not_exception ; "let"; "module"; (ext,attrs) = ext_attributes; m = V uidopt "uidopt"; mb = mod_fun_binding; "in";
        e = expr LEVEL "top" ->
          expr_to_inline loc <:expr< let module $_uidopt:m$ = $mb$ in $e$ >> ext attrs

      | check_let_not_exception ; "let"; "open"; (ext,attrs) = ext_attributes; m = module_expr; "in"; e = expr LEVEL "top" ->
          expr_to_inline loc <:expr< let open $m$ in $e$ >> ext attrs

      | letop = letop ; b = letop_binding ; l = (LIST0 andop_binding); "in";
        x = expr LEVEL "top" ->
          build_letop_binder loc letop b l x

      | "function"; OPT "|"; l = V (LIST1 match_case SEP "|") ->
          <:expr< fun [ $_list:l$ ] >>
      | "fun"; p = patt LEVEL "simple"; (eo, e) = fun_def ->
          <:expr< fun [$p$ $opt:eo$ -> $e$] >>
      | "match"; e = SELF; "with"; OPT "|";
        l = V (LIST1 match_case SEP "|") ->
          <:expr< match $e$ with [ $_list:l$ ] >>
      | "try"; e = SELF; "with"; OPT "|"; l = V (LIST1 match_case SEP "|") ->
          <:expr< try $e$ with [ $_list:l$ ] >>
      | "if"; e1 = SELF; "then"; e2 = expr LEVEL "expr1"; "else";
        e3 = expr LEVEL "expr1" ->
          <:expr< if $e1$ then $e2$ else $e3$ >>
      | "if"; e1 = SELF; "then"; e2 = expr LEVEL "expr1" ->
          <:expr< if $e1$ then $e2$ else () >>
      | "for"; i = patt; "="; e1 = SELF; df = V direction_flag "to";
        e2 = SELF; "do"; e = V SELF "list"; "done" ->
          let el = Pcaml.vala_map get_seq e in
          <:expr< for $i$ = $e1$ $_to:df$ $e2$ do { $_list:el$ } >>
      | "for"; "("; i = operator_rparen; "="; e1 = SELF; df = V direction_flag "to";
        e2 = SELF; "do"; e = V SELF "list"; "done" ->
          let i = Ploc.VaVal i in
          let el = Pcaml.vala_map get_seq e in
          <:expr< for $_lid:i$ = $e1$ $_to:df$ $e2$ do { $_list:el$ } >>
      | "while"; e1 = SELF; "do"; e2 = V SELF "list"; "done" ->
          let el = Pcaml.vala_map get_seq e2 in
          <:expr< while $e1$ do { $_list:el$ } >> ]
    | [ e = SELF; ","; el = LIST1 NEXT SEP "," ->
          <:expr< ( $list:[e :: el]$ ) >> ]
    | ":=" NONA
      [ e1 = SELF; ":="; e2 = expr LEVEL "expr1" ->
          <:expr< $e1$.val := $e2$ >>
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
      | e1 = SELF; op = infixop0; e2 = SELF -> <:expr< $lid:op$ $e1$ $e2$ >> ]
    | "^" RIGHTA
      [ e1 = SELF; "^"; e2 = SELF -> <:expr< $e1$ ^ $e2$ >>
      | e1 = SELF; "@"; e2 = SELF -> <:expr< $e1$ @ $e2$ >>
      | e1 = SELF; op = infixop1; e2 = SELF -> <:expr< $lid:op$ $e1$ $e2$ >> ]
    | "alg_attribute" LEFTA
      [ e1 = SELF ; "[@" ; attr = V attribute_body "attribute"; "]" ->
        <:expr< $e1$ [@ $_attribute:attr$ ] >>
      ]
    | RIGHTA
      [ e1 = SELF; "::"; e2 = SELF -> <:expr< [$e1$ :: $e2$] >> ]
    | "+" LEFTA
      [ e1 = SELF; "+"; e2 = SELF -> <:expr< $e1$ + $e2$ >>
      | e1 = SELF; "-"; e2 = SELF -> <:expr< $e1$ - $e2$ >>
      | e1 = SELF; op = infixop2; e2 = SELF -> <:expr< $lid:op$ $e1$ $e2$ >> ]
    | "*" LEFTA
      [ e1 = SELF; "*"; e2 = SELF -> <:expr< $e1$ * $e2$ >>
      | e1 = SELF; "/"; e2 = SELF -> <:expr< $e1$ / $e2$ >>
      | e1 = SELF; "%"; e2 = SELF -> <:expr< $lid:"%"$ $e1$ $e2$ >>
      | e1 = SELF; "land"; e2 = SELF -> <:expr< $e1$ land $e2$ >>
      | e1 = SELF; "lor"; e2 = SELF -> <:expr< $e1$ lor $e2$ >>
      | e1 = SELF; "lxor"; e2 = SELF -> <:expr< $e1$ lxor $e2$ >>
      | e1 = SELF; "mod"; e2 = SELF -> <:expr< $e1$ mod $e2$ >>
      | e1 = SELF; op = infixop3; e2 = SELF -> <:expr< $lid:op$ $e1$ $e2$ >> ]
    | "**" RIGHTA
      [ e1 = SELF; "**"; e2 = SELF -> <:expr< $e1$ ** $e2$ >>
      | e1 = SELF; "asr"; e2 = SELF -> <:expr< $e1$ asr $e2$ >>
      | e1 = SELF; "lsl"; e2 = SELF -> <:expr< $e1$ lsl $e2$ >>
      | e1 = SELF; "lsr"; e2 = SELF -> <:expr< $e1$ lsr $e2$ >>
      | e1 = SELF; op = infixop4; e2 = SELF -> <:expr< $lid:op$ $e1$ $e2$ >> ]
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
      | "assert"; e = SELF -> <:expr< assert $e$ >>
      | "lazy"; e = SELF -> <:expr< lazy ($e$) >> ]
    | "." LEFTA
      [ e1 = SELF; "."; "("; op = operator_rparen ->
          <:expr< $e1$ .( $lid:op$ ) >>
      | e1 = SELF; "."; "("; e2 = SELF; ")" ->
          <:expr< $e1$ .( $e2$ ) >>
      | e1 = SELF; "."; "["; e2 = SELF; "]" -> <:expr< $e1$ .[ $e2$ ] >>
      | e = SELF; "."; "{"; el = V (LIST1 expr LEVEL "+" SEP ","); "}" ->
          <:expr< $e$ .{ $_list:el$ } >>
      | e1 = SELF; "."; e2 = SELF ->
          let rec loop m =
            fun
            [ <:expr< $x$ . $y$ >> -> loop <:expr< $m$ . $x$ >> y
            | e -> <:expr< $m$ . $e$ >> ]
          in
          loop e1 e2 ]
    | "~-" NONA
      [ "!"; e = SELF -> <:expr< $e$ . val >>
      | "~-"; e = SELF -> <:expr< ~- $e$ >>
      | "~-."; e = SELF -> <:expr< ~-. $e$ >>
      | f = prefixop; e = SELF -> <:expr< $lid:f$ $e$ >> ]
    | "simple" LEFTA
      [ s = V INT -> <:expr< $_int:s$ >>
      | s = V INT_l -> <:expr< $_int32:s$ >>
      | s = V INT_L -> <:expr< $_int64:s$ >>
      | s = V INT_n -> <:expr< $_nativeint:s$ >>
      | s = V FLOAT -> <:expr< $_flo:s$ >>
      | s = V STRING -> <:expr< $_str:s$ >>
      | c = V CHAR -> <:expr< $_chr:c$ >>
      | e = alg_extension -> <:expr< [% $_extension:e$ ] >>
      | UIDENT "True" -> <:expr< True_ >>
      | UIDENT "False" -> <:expr< False_ >>
      | i = expr_ident -> i
      | "false" -> <:expr< False >>
      | "true" -> <:expr< True >>
      | "["; "]" -> <:expr< [] >>
      | "["; el = expr1_semi_list; "]" -> <:expr< $mklistexp loc None el$ >>
      | "[|"; "|]" -> <:expr< [| |] >>
      | "[|"; el = V expr1_semi_list "list"; "|]" ->
          <:expr< [| $_list:el$ |] >>
      | "{"; test_label_eq; lel = V lbl_expr_list "list"; "}" ->
          <:expr< { $_list:lel$ } >>
      | "{"; e = expr LEVEL "apply"; "with"; lel = V lbl_expr_list "list";
        "}" ->
          <:expr< { ($e$) with $_list:lel$ } >>
      | "("; ")" -> <:expr< () >>
      | "("; "module"; me = module_expr; ":"; mt = module_type; ")" ->
          <:expr< (module $me$ : $mt$) >>
      | "("; "module"; me = module_expr; ")" ->
          <:expr< (module $me$) >>
      | "("; op = operator_rparen -> <:expr< $lid:op$ >>
      | "("; el = V e_phony "list"; ")" -> <:expr< ($_list:el$) >>
      | "("; e = SELF; ":"; t = ctyp; ")" -> <:expr< ($e$ : $t$) >>
      | "("; e = SELF; ")" -> concat_comm loc <:expr< $e$ >>
      | "begin"; e = SELF; "end" -> concat_comm loc <:expr< $e$ >>
      | "begin"; "end" -> <:expr< () >>
      | x = QUOTATION ->
          let con = quotation_content x in
          Pcaml.handle_expr_quotation loc con ] ]
  ;
  let_binding:
    [ [ alg_attrs = alg_attributes_no_anti ;
        p = val_ident; e = fun_binding ;
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
  letop_binding:
    [ [ p = val_ident; e = fun_binding -> (p, e)
      | p = patt; "="; e = expr -> (p, e)
      | p = patt; ":"; t = poly_type; "="; e = expr ->
          (<:patt< ($p$ : $t$) >>, e)
      ] ]
  ;
  val_ident:
    [ [ check_not_part_of_patt; s = LIDENT -> <:patt< $lid:s$ >>
      | check_not_part_of_patt; "(" ; op = operator_rparen -> <:patt< $lid:op$ >>
      ] ]
  ;
  fun_binding:
    [ RIGHTA
      [ p = patt LEVEL "simple"; e = SELF -> <:expr< fun $p$ -> $e$ >>
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
        let rhs = match e with [
          None -> expr_of_patt i
        | Some e -> e
        ] in
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
      | eo = OPT [ "when"; e = expr -> e ]; "->"; e = expr ->
          (eo, <:expr< $e$ >>) ] ]
  ;
  expr_ident:
    [ RIGHTA
      [ i = V LIDENT -> <:expr< $_lid:i$ >>
      | i = V UIDENT -> <:expr< $_uid:i$ >>
      | i = V UIDENT; "."; j = SELF ->
          let rec loop m =
            fun
            [ <:expr< $x$ . $y$ >> -> loop <:expr< $m$ . $x$ >> y
            | e -> <:expr< $m$ . $e$ >> ]
          in
          loop <:expr< $_uid:i$ >> j
      | i = V UIDENT; "."; "("; j = operator_rparen ->
          <:expr< $_uid:i$ . $lid:j$ >>
      | i = V UIDENT; "."; "("; e = expr; ")" ->
          <:expr< $_uid:i$ . ( $e$ ) >>
      | i = V UIDENT; "."; "["; el = expr1_semi_list; "]" ->
          <:expr< $_uid:i$ . ( $exp:mklistexp loc None el$ ) >>
      | i = V UIDENT; "."; "[|"; el = V expr1_semi_list "list"; "|]" ->
          <:expr< $_uid:i$ . ( [| $_list:el$ |] ) >>

      | i = V UIDENT; "."; "{<"; ">}" -> <:expr< $_uid:i$ . ( {< >} ) >>
      | i = V UIDENT; "."; "{<"; fel = V field_expr_list "list"; ">}" ->
          <:expr< $_uid:i$ . ( {< $_list:fel$ >} ) >>

      | i = V UIDENT; "."; "{"; test_label_eq ; lel = V lbl_expr_list "list"; "}" ->
          <:expr< $_uid:i$ . ({ $_list:lel$ }) >>
      | i = V UIDENT; "."; "{"; e = expr LEVEL "apply"; "with"; lel = V lbl_expr_list "list";
        "}" ->
          <:expr< $_uid:i$ . ({ ($e$) with $_list:lel$ }) >>
      ] ]
  ;
  (* Patterns *)
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
      [ "exception"; p = SELF →
         <:patt< exception $p$ >>
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
      | "lazy"; p = SELF -> <:patt< lazy $p$ >> ]
    | LEFTA
      [ p1 = SELF; "."; p2 = SELF -> <:patt< $p1$ . $p2$ >> ]
(*
    | "lazy" [
        "lazy"; p = SELF -> <:patt< lazy $p$ >>
      ]
*)
    | "simple"
      [ s = V LIDENT -> <:patt< $_lid:s$ >>
      | s = V UIDENT -> <:patt< $_uid:s$ >>
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
      | "("; ")" -> <:patt< () >>
      | "("; op = operator_rparen -> <:patt< $lid:op$ >>
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
        let rec loop = fun [
          <:patt< $_$ . $p$ >> -> loop p
        | p -> p
        ] in
        let rhs = match p with [
          None -> loop i
        | Some p -> p
        ] in
        let rhs = match tycon with [
          None -> rhs
        | Some ty -> <:patt< ($rhs$ : $ty$) >>
        ] in (i, rhs)
      | "_" -> (<:patt< _ >>, <:patt< _ >>) ] ]
  ;
  patt_label_ident:
    [ LEFTA
      [ p1 = SELF; "."; p2 = SELF -> <:patt< $p1$ . $p2$ >> ]
    | RIGHTA
      [ i = UIDENT -> <:patt< $uid:i$ >>
      | i = LIDENT -> <:patt< $lid:i$ >> ] ]
  ;
  (* Type declaration *)
  type_decl:
    [ [ tpl = type_parameters; n = V type_patt; "="; pf = V (FLAG "private");
        tk = type_kind; cl = V (LIST0 constrain) ; attrs = item_attributes ->
          <:type_decl< $_tp:n$ $list:tpl$ = $_priv:pf$ $tk$ $_list:cl$ $_itemattrs:attrs$ >>
      | tpl = type_parameters; n = V type_patt; cl = V (LIST0 constrain) ; attrs = item_attributes ->
          let tk = <:ctyp< '$choose_tvar tpl$ >> in
          <:type_decl< $_tp:n$ $list:tpl$ = $tk$ $_list:cl$ $_itemattrs:attrs$ >> ] ]
  ;
  (* TODO FIX: this should be a longident+lid, to match ocaml's grammar *)
  type_extension:
    [ [ tpl = type_parameters; n = V mod_ident_patt "tp"; "+=";
        pf = V (FLAG "private") "priv"; OPT [ "|" ] ; ecs = V (LIST1 extension_constructor SEP "|") ;
        attrs = item_attributes →
(*
          <:type_extension< $_tp:n$ $_list:tpl$ += $_priv:pf$ $tk$ $_itemattrs:attrs$ >>
*)
          {MLast.teNam=n; tePrm= <:vala< tpl >>; tePrv=pf; teAttributes=attrs; teECs = ecs }
      ] ]
  ;
  mod_ident_patt:
    [ [ n = V mod_ident → (loc, n) ] ]
  ;
  type_patt:
    [ [ n = V LIDENT -> (loc, n) ] ]
  ;
  constrain:
    [ [ "constraint"; t1 = ctyp; "="; t2 = ctyp -> (t1, t2) ] ]
  ;
  type_kind:
    [ [ test_constr_decl; OPT "|";
        cdl = LIST1 constructor_declaration SEP "|" ->
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
    [ [ "+"; p = V simple_type_parameter -> (p, Some True)
      | "-"; p = V simple_type_parameter -> (p, Some False)
      | p = V simple_type_parameter -> (p, None) ] ]
  ;
  simple_type_parameter:
    [ [ "'"; i = ident -> Some i
      | "_" -> None ] ]
  ;
  record_type:
    [ [ "{"; ldl = V label_declarations "list"; "}" ->
      <:ctyp< { $_list:ldl$ } >> ] ]
  ;
  constructor_declaration_sans_alg_attrs:
    [ [ ci = cons_ident; "of"; cal = V (LIST1 (ctyp LEVEL "apply") SEP "*") ->
          (loc, ci, cal, None)
      | ci = cons_ident; "of"; cdrec = record_type ->
          (loc, ci, Ploc.VaVal [cdrec], None)
      | ci = cons_ident; ":"; cal = V (LIST1 (ctyp LEVEL "apply") SEP "*");
        "->"; t = ctyp ->
          (loc, ci, cal, Some t)
      | ci = cons_ident; ":"; cal = V (LIST1 (ctyp LEVEL "apply") SEP "*") ->
          let t =
            match cal with
            [ <:vala< [t] >> -> t
            | <:vala< [t :: tl] >> -> <:ctyp< ($list:[t :: tl]$) >>
            | _ -> assert False ]
          in
          (loc, ci, <:vala< [] >>, Some t)
      | ci = cons_ident -> (loc, ci, <:vala< [] >>, None) ] ]
  ;
  constructor_declaration:
    [ [ ci = cons_ident; "of"; cal = V (LIST1 (ctyp LEVEL "apply") SEP "*") ; alg_attrs = alg_attributes ->
          (loc, ci, cal, None, alg_attrs)
      | ci = cons_ident; "of"; cdrec = record_type ; alg_attrs = alg_attributes ->
          (loc, ci, Ploc.VaVal [cdrec], None, alg_attrs)
      | ci = cons_ident; ":"; cal = V (LIST1 (ctyp LEVEL "apply") SEP "*");
        "->"; t = ctyp ; alg_attrs = alg_attributes ->
          (loc, ci, cal, Some t, alg_attrs)
      | ci = cons_ident; ":"; cal = V (LIST1 (ctyp LEVEL "apply") SEP "*") ; alg_attrs = alg_attributes ->
          let t =
            match cal with
            [ <:vala< [t] >> -> t
            | <:vala< [t :: tl] >> -> <:ctyp< ($list:[t :: tl]$) >>
            | _ -> assert False ]
          in
          (loc, ci, <:vala< [] >>, Some t, alg_attrs)
      | ci = cons_ident; alg_attrs = alg_attributes ->
          (loc, ci, <:vala< [] >>, None, alg_attrs) ] ]
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
  extended_longident:
    [ LEFTA
      [ me1 = SELF; "(" ; me2 = SELF ; ")" → <:extended_longident< $longid:me1$ ( $longid:me2$ ) >>
      | me1 = SELF; check_dot_uid ; "."; i = V UIDENT "uid" → <:extended_longident< $longid:me1$ . $_uid:i$ >>
      ]
    | "simple"
      [ i = V UIDENT "uid" → <:extended_longident< $_uid:i$ >>
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
      | "("; "module"; mt = module_type; ")" -> <:ctyp< module $mt$ >>
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
  mod_ident:
    [ RIGHTA
      [ i = UIDENT -> [i]
      | i = LIDENT -> [i]
      | i = UIDENT; "."; j = SELF -> [i :: j] ] ]
  ;
  (* Miscellaneous *)
  direction_flag:
    [ [ "to" -> True
      | "downto" -> False ] ]
  ;
  (* Objects and Classes *)
  str_item:
    [ [ "class"; cd = V (LIST1 class_declaration SEP "and") ->
          <:str_item< class $_list:cd$ >>
      | "class"; "type"; ctd = V (LIST1 class_type_declaration SEP "and") ->
          <:str_item< class type $_list:ctd$ >> ] ]
  ;
  sig_item:
    [ [ "class"; cd = V (LIST1 class_description SEP "and") ->
          <:sig_item< class $_list:cd$ >>
      | "class"; "type"; ctd = V (LIST1 class_type_declaration SEP "and") ->
          <:sig_item< class type $_list:ctd$ >> ] ]
  ;
  (* Class expressions *)
  class_declaration:
    [ [ vf = V (FLAG "virtual"); ctp = class_type_parameters; i = V LIDENT;
        cfb = class_fun_binding ; attrs = item_attributes ->
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
      [ "fun"; cfd = class_fun_def -> cfd
      | "let"; rf = V (FLAG "rec"); lb = V (LIST1 let_binding SEP "and");
        "in"; ce = SELF ->
          <:class_expr< let $_flag:rf$ $_list:lb$ in $ce$ >> ]
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
        ci = class_longident ->
          <:class_expr< [ $list:[ct :: ctcl]$ ] $list:ci$ >>
      | "["; ct = ctyp; "]"; ci = class_longident ->
          <:class_expr< [ $ct$ ] $list:ci$ >>
      | ci = class_longident -> <:class_expr< $list:ci$ >>
      | "object"; cspo = V (OPT class_self_patt);
        cf = V class_structure "list"; "end" ->
          <:class_expr< object $_opt:cspo$ $_list:cf$ end >>
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
  class_str_item:
    [ [ "inherit"; ovf = V (FLAG "!") "!"; ce = class_expr; pb = V (OPT [ "as"; i = LIDENT -> i ]) ; attrs = item_attributes ->
          <:class_str_item< inherit $_!:ovf$ $ce$ $_opt:pb$ $_itemattrs:attrs$ >>
      | "val"; ov = V (FLAG "!") "!"; mf = V (FLAG "mutable");
        lab = V LIDENT "lid" ""; e = cvalue_binding ; attrs = item_attributes ->
          <:class_str_item< value $_!:ov$ $_flag:mf$ $_lid:lab$ = $e$ $_itemattrs:attrs$ >>
      | "val"; ov = V (FLAG "!") "!"; mf = V (FLAG "mutable");
        "virtual"; lab = V LIDENT "lid" ""; ":"; t = ctyp ; attrs = item_attributes ->
          if Pcaml.unvala ov then
            Ploc.raise loc (Stream.Error "virtual value cannot override")
          else
            <:class_str_item< value virtual $_flag:mf$ $_lid:lab$ : $t$ $_itemattrs:attrs$ >>
      | "val"; "virtual"; mf = V (FLAG "mutable"); lab = V LIDENT "lid" "";
        ":"; t = ctyp ; attrs = item_attributes ->
          <:class_str_item< value virtual $_flag:mf$ $_lid:lab$ : $t$ $_itemattrs:attrs$ >>
      | "method"; "private"; "virtual"; l = V LIDENT "lid" ""; ":";
        t = poly_type_below_alg_attribute ; attrs = item_attributes ->
          <:class_str_item< method virtual private $_lid:l$ : $t$ $_itemattrs:attrs$ >>
      | "method"; "virtual"; "private"; l = V LIDENT "lid" ""; ":";
        t = poly_type_below_alg_attribute ; attrs = item_attributes ->
          <:class_str_item< method virtual private $_lid:l$ : $t$ $_itemattrs:attrs$ >>
      | "method"; "virtual"; l = V LIDENT "lid" ""; ":"; t = poly_type_below_alg_attribute ; attrs = item_attributes ->
          <:class_str_item< method virtual $_lid:l$ : $t$ $_itemattrs:attrs$ >>
      | "method"; ov = V (FLAG "!") "!"; "private"; l = V LIDENT "lid" "";
        ":"; t = poly_type_below_alg_attribute; "="; e = expr ; attrs = item_attributes ->
          <:class_str_item< method $_!:ov$ private $_lid:l$ : $t$ = $e$ $_itemattrs:attrs$ >>
      | "method"; ov = V (FLAG "!") "!"; "private"; l = V LIDENT "lid" "";
        sb = fun_binding ; attrs = item_attributes ->
          <:class_str_item< method $_!:ov$ private $_lid:l$ = $sb$ $_itemattrs:attrs$ >>
      | "method"; ov = V (FLAG "!") "!"; l = V LIDENT "lid" ""; ":";
        t = poly_type_below_alg_attribute; "="; e = expr ; attrs = item_attributes ->
          <:class_str_item< method $_!:ov$ $_lid:l$ : $t$ = $e$ $_itemattrs:attrs$ >>
      | "method"; ov = V (FLAG "!") "!"; l = V LIDENT "lid" "";
        sb = fun_binding ; attrs = item_attributes ->
          <:class_str_item< method $_!:ov$ $_lid:l$ = $sb$ $_itemattrs:attrs$ >>
      | "constraint"; t1 = ctyp; "="; t2 = ctyp ; attrs = item_attributes ->
          <:class_str_item< type $t1$ = $t2$ $_itemattrs:attrs$ >>
      | "initializer"; se = expr ; attrs = item_attributes -> <:class_str_item< initializer $se$ $_itemattrs:attrs$ >>
      | attr = floating_attribute -> <:class_str_item< [@@@ $_attribute:attr$ ] >>
      | e = item_extension -> <:class_str_item< [%% $_extension:e$ ] >>
      ] ]
  ;
  cvalue_binding:
    [ [ "="; e = expr -> e
      | ":"; t = ctyp; "="; e = expr -> <:expr< ($e$ : $t$) >>
      | ":"; t = ctyp; ":>"; t2 = ctyp; "="; e = expr ->
          <:expr< ($e$ : $t$ :> $t2$) >>
      | ":>"; t = ctyp; "="; e = expr ->
          <:expr< ($e$ :> $t$) >> ] ]
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
      ]

    | [ "["; tl = LIST1 ctyp SEP ","; "]"; id = SELF ->
          <:class_type< $id$ [ $list:tl$ ] >>
      | "object"; cst = V (OPT class_self_type);
        csf = V (LIST0 class_sig_item); "end" ->
          <:class_type< object $_opt:cst$ $_list:csf$ end >> ]
    | [ li = extended_longident; "."; i = V LIDENT → <:class_type< $longid:li$ . $_lid:i$ >>
      | li = extended_longident → <:class_type< $longid:li$ >>
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
    [ [ "inherit"; cs = class_signature ; attrs = item_attributes ->
          <:class_sig_item< inherit $cs$ $_itemattrs:attrs$ >>
      | "val"; (mf, vf) = mut_virt; l = V LIDENT "lid" ""; ":"; t = ctyp ; attrs = item_attributes ->
        <:class_sig_item< value $flag:mf$ $flag:vf$ $_lid:l$ : $t$ $_itemattrs:attrs$ >>
      | "method"; "private"; "virtual"; l = V LIDENT "lid" ""; ":";
        t = poly_type_below_alg_attribute ; attrs = item_attributes ->
          <:class_sig_item< method virtual private $_lid:l$ : $t$ $_itemattrs:attrs$ >>
      | "method"; "virtual"; "private"; l = V LIDENT "lid" ""; ":";
        t = poly_type_below_alg_attribute ; attrs = item_attributes ->
          <:class_sig_item< method virtual private $_lid:l$ : $t$ $_itemattrs:attrs$ >>
      | "method"; "virtual"; l = V LIDENT "lid" ""; ":"; t = poly_type_below_alg_attribute ; attrs = item_attributes ->
          <:class_sig_item< method virtual $_lid:l$ : $t$ $_itemattrs:attrs$ >>
      | "method"; "private"; l = V LIDENT "lid" ""; ":"; t = poly_type_below_alg_attribute ; attrs = item_attributes ->
          <:class_sig_item< method private $_lid:l$ : $t$ $_itemattrs:attrs$ >>
      | "method"; l = V LIDENT "lid" ""; ":"; t = poly_type_below_alg_attribute ; attrs = item_attributes ->
          <:class_sig_item< method $_lid:l$ : $t$ $_itemattrs:attrs$ >>
      | "constraint"; t1 = ctyp; "="; t2 = ctyp ; attrs = item_attributes ->
          <:class_sig_item< type $t1$ = $t2$ $_itemattrs:attrs$ >>
      | attr = floating_attribute -> <:class_sig_item< [@@@ $_attribute:attr$ ] >>
      | e = item_extension -> <:class_sig_item< [%% $_extension:e$ ] >>
      ] ]
  ;
  class_description:
    [ [ vf = V (FLAG "virtual"); ctp = class_type_parameters; n = V LIDENT;
        ":"; ct = class_type ; attrs = item_attributes ->
          {MLast.ciLoc = loc; MLast.ciVir = vf; MLast.ciPrm = ctp;
           MLast.ciNam = n; MLast.ciExp = ct; MLast.ciAttributes = attrs} ] ]
  ;
  class_type_declaration:
    [ [ vf = V (FLAG "virtual"); ctp = class_type_parameters; n = V LIDENT;
        "="; cs = class_signature ; attrs = item_attributes ->
          {MLast.ciLoc = loc; MLast.ciVir = vf; MLast.ciPrm = ctp;
           MLast.ciNam = n; MLast.ciExp = cs; MLast.ciAttributes = attrs} ] ]
  ;
  (* Expressions *)
  expr: LEVEL "simple"
    [ LEFTA
      [ "new"; i = V class_longident "list" -> <:expr< new $_list:i$ >>
      | "object"; cspo = V (OPT class_self_patt);
        cf = V class_structure "list"; "end" ->
          <:expr< object $_opt:cspo$ $_list:cf$ end >> ] ]
  ;
  expr: LEVEL "."
    [ [ e = SELF; "#"; lab = V LIDENT "lid" -> <:expr< $e$ # $_lid:lab$ >>
      | e = SELF; op = hashop ; e2 = SELF -> <:expr< $lid:op$ $e$ $e2$ >>
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
    [ [ "#"; id = V class_longident "list" ->
         <:ctyp< # $_list:id$ >>
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
    [ [ lab = LIDENT; ":"; t = poly_type_below_alg_attribute -> (lab, t) ] ]
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
  class_longident:
    [ [ m = UIDENT; "."; l = SELF -> [m :: l]
      | i = LIDENT -> [i] ] ]
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
    [ [ "fun"; p = labeled_patt; (eo, e) = fun_def ->
          <:expr< fun [ $p$ $opt:eo$ -> $e$ ] >> ] ]
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
      | "#"; t = V mod_ident "list" "" -> <:patt< # $_list:t$ >>
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
