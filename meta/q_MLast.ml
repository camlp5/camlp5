(* camlp5r *)
(* q_MLast.ml,v *)
(* Copyright (c) INRIA 2007-2017 *)

#load "pa_extend.cmo";
#load "pa_extend_m.cmo";
#load "q_MLast.cmo";
#load "pa_macro.cmo";

open Asttools ;
open Mlsyntax.Original ;

value gram = Grammar.gcreate (Plexer.gmake ());

value antiquot k loc s f =
  let shift_bp =
    if k = "" then String.length "$"
    else String.length "$" + String.length k + String.length ":"
  in
  let shift_ep = String.length "$" in
  let loc =
    Ploc.make_loc (Ploc.file_name loc) (Ploc.line_nb loc) (Ploc.bol_pos loc)
      (Ploc.first_pos loc + shift_bp, Ploc.last_pos loc - shift_ep) ""
  in
  try (loc, Grammar.Entry.parse f (Stream.of_string s)) with
  [ Ploc.Exc loc1 exc ->
      let shift = Ploc.first_pos loc in
      let loc =
        Ploc.make_loc (Ploc.file_name loc)
          (Ploc.line_nb loc + Ploc.line_nb loc1 - 1)
          (if Ploc.line_nb loc1 = 1 then Ploc.bol_pos loc
           else shift + Ploc.bol_pos loc1)
          (shift + Ploc.first_pos loc1,
           shift + Ploc.last_pos loc1) ""
      in
      raise (Ploc.Exc loc exc) ]
;

module Qast =
  struct
    type t =
      [ Node of string and list t
      | List of list t
      | Tuple of list t
      | Option of option t
      | Int of string
      | Str of string
      | Bool of bool
      | Cons of t and t
      | Apply of string and list t
      | Record of list (string * t)
      | Loc
      | TrueLoc
      | VaAnt of string and MLast.loc and string
      | VaVal of t ]
    ;
    value loc = Ploc.dummy;
    value expr_node m n =
      let l = Versdep.split_on_char '.' n in
      let li = match (m, l) with [
        ("", [n]) -> <:longident< $uid:n$ >>
      | (m, [n]) -> <:longident< $uid:m$ . $uid:n$ >>
      | (_, [_ :: _]) ->
        (longident_of_string_list loc l)
      | (_,[]) -> assert False
      ] in
      <:expr< $longid:li$ >>
    ;
    value patt_node m n =
      let l = Versdep.split_on_char '.' n in
      let li = match (m, l) with [
        ("", [n]) -> <:longident< $uid:n$ >>
      | (m, [n]) -> <:longident< $uid:m$ . $uid:n$ >>
      | (_, [_ :: _]) ->
        (longident_of_string_list loc l)
      | (_,[]) -> assert False
      ] in
      <:patt< $longid:li$ >>
    ;
    value patt_label m n =
      if m = "" then <:patt< $lid:n$ >> else <:patt< $uid:m$ . $lid:n$ >>
    ;
    value rec to_expr m =
      fun
      [ Node n al ->
          List.fold_left (fun e a -> <:expr< $e$ $to_expr m a$ >>)
            (expr_node m n) al
      | List al ->
          List.fold_right (fun a e -> <:expr< [$to_expr m a$ :: $e$] >>) al
            <:expr< [] >>
      | Tuple al -> <:expr< ($list:List.map (to_expr m) al$) >>
      | Option None -> <:expr< None >>
      | Option (Some a) -> <:expr< Some $to_expr m a$ >>
      | Int s -> <:expr< $int:s$ >>
      | Str s -> <:expr< $str:s$ >>
      | Bool True -> <:expr< True >>
      | Bool False -> <:expr< False >>
      | Cons a1 a2 -> <:expr< [$to_expr m a1$ :: $to_expr m a2$] >>
      | Apply f al ->
          List.fold_left (fun e a -> <:expr< $e$ $to_expr m a$ >>)
            <:expr< $lid:f$ >> al
      | Record lal -> <:expr< {$list:List.map (to_expr_label m) lal$} >>
      | Loc | TrueLoc -> <:expr< $lid:Ploc.name.val$ >>
      | VaAnt k loc x ->
          let (loc, e) = antiquot k loc x Pcaml.expr_eoi in
          <:expr< $anti:e$ >>
      | VaVal a ->
          let e = to_expr m a in
          if Pcaml.strict_mode.val then
            match e with
            [ <:expr< $anti:ee$ >> ->
                let loc = MLast.loc_of_expr ee in
                let ee = <:expr< Ploc.VaVal $ee$ >> in
                let loc = MLast.loc_of_expr e in
                <:expr< $anti:ee$ >>
            | _ -> <:expr< Ploc.VaVal $e$ >> ]
          else e ]
    and to_expr_label m (l, e) = (patt_label m l, to_expr m e);
    value rec to_patt m =
      fun
      [ Node n al ->
          List.fold_left (fun e a -> <:patt< $e$ $to_patt m a$ >>)
            (patt_node m n) al
      | List al ->
          List.fold_right (fun a p -> <:patt< [$to_patt m a$ :: $p$] >>) al
            <:patt< [] >>
      | Tuple al -> <:patt< ($list:List.map (to_patt m) al$) >>
      | Option None -> <:patt< None >>
      | Option (Some a) -> <:patt< Some $to_patt m a$ >>
      | Int s -> <:patt< $int:s$ >>
      | Str s -> <:patt< $str:s$ >>
      | Bool True -> <:patt< True >>
      | Bool False -> <:patt< False >>
      | Cons a1 a2 -> <:patt< [$to_patt m a1$ :: $to_patt m a2$] >>
      | Apply _ _ -> failwith "bad pattern"
      | Record lal -> <:patt< {$list:List.map (to_patt_label m) lal$} >>
      | Loc -> <:patt< _ >>
      | TrueLoc -> <:patt< $lid:Ploc.name.val$ >>
      | VaAnt k loc x ->
          let (loc, e) = antiquot k loc x Pcaml.patt_eoi in
          <:patt< $anti:e$ >>
      | VaVal a ->
          let p = to_patt m a in
          if Pcaml.strict_mode.val then
            match p with
            [ <:patt< $anti:pp$ >> ->
                let loc = MLast.loc_of_patt pp in
                let pp = <:patt< Ploc.VaVal $pp$ >> in
                let loc = MLast.loc_of_patt p in
                <:patt< $anti:pp$ >>
            | _ -> <:patt< Ploc.VaVal $p$ >> ]
          else p ]
    and to_patt_label m (l, a) = (patt_label m l, to_patt m a);
  end
;

value sig_item = Grammar.Entry.create gram "sig_item";
value str_item = Grammar.Entry.create gram "str_item";
value ctyp = Grammar.Entry.create gram "type";
value patt = Grammar.Entry.create gram "patt";
value expr = Grammar.Entry.create gram "expr";

value functor_parameter = Grammar.Entry.create gram "functor_parameter";
value module_type = Grammar.Entry.create gram "module_type";
value longident = Grammar.Entry.create gram "longident";
value extended_longident = Grammar.Entry.create gram "extended_longident";
value module_expr = Grammar.Entry.create gram "module_expr";

value structure = Grammar.Entry.create gram "structure";
value signature = Grammar.Entry.create gram "signature";

value class_type = Grammar.Entry.create gram "class_type";
value class_expr = Grammar.Entry.create gram "class_expr";
value class_sig_item = Grammar.Entry.create gram "class_sig_item";
value class_str_item = Grammar.Entry.create gram "class_str_item";

value ipatt = Grammar.Entry.create gram "ipatt";
value let_binding = Grammar.Entry.create gram "let_binding";
value type_decl = Grammar.Entry.create gram "type_decl";
value type_extension = Grammar.Entry.create gram "type_extension";
value extension_constructor = Grammar.Entry.create gram "extension_constructor";
value match_case = Grammar.Entry.create gram "match_case";
value constructor_declaration =
  Grammar.Entry.create gram "constructor_declaration";
value label_declaration =
  Grammar.Entry.create gram "label_declaration";

value with_constr = Grammar.Entry.create gram "with_constr";
value poly_variant = Grammar.Entry.create gram "poly_variant";
value attribute_body = Grammar.Entry.create gram "attribute_body";
value ctyp_ident = Grammar.Entry.create gram "ctyp_ident";

value mksequence2 _ =
  fun
  [ Qast.VaVal (Qast.List [e]) -> e
  | el -> Qast.Node "ExSeq" [Qast.Loc; el] ]
;

value mksequence _ =
  fun
  [ Qast.List [e] -> e
  | el -> Qast.Node "ExSeq" [Qast.Loc; Qast.VaVal el] ]
;

value mkmatchcase _ p aso w e =
  let p =
    match aso with
    [ Qast.Option (Some p2) -> Qast.Node "PaAli" [Qast.Loc; p; p2]
    | Qast.Option None -> p
    | _ -> Qast.Node "PaAli" [Qast.Loc; p; aso] ]
  in
  Qast.Tuple [p; w; e]
;

value neg_string n =
  let x =
    let len = String.length n in
    if len > 0 && n.[0] = '-' then String.sub n 1 (len - 1)
    else "-" ^ n
  in
  Qast.Str x
;

value mklistexp _ last =
  loop True where rec loop top =
    fun
    [ [] ->
        match last with
        [ Qast.Option (Some e) -> e
        | Qast.Option None ->
            Qast.Node "ExLong" [Qast.Loc; Qast.Node "LiUid" [Qast.Loc; Qast.VaVal (Qast.Str "[]")]]
        | a -> a ]
    | [e1 :: el] ->
        Qast.Node "ExApp"
          [Qast.Loc;
           Qast.Node "ExApp"
             [Qast.Loc;
              Qast.Node "ExLong" [Qast.Loc; Qast.Node "LiUid" [Qast.Loc; Qast.VaVal (Qast.Str "::")]]; e1];
           loop False el] ]
;

value mklistpat _ last =
  loop True where rec loop top =
    fun
    [ [] ->
        match last with
        [ Qast.Option (Some p) -> p
        | Qast.Option None ->
          Qast.Node "PaLong" [Qast.Loc; Qast.Node "LiUid" [Qast.Loc; Qast.VaVal (Qast.Str "[]")];
            Qast.VaVal (Qast.List [])]
        | a -> a ]
    | [p1 :: pl] ->
        Qast.Node "PaApp"
          [Qast.Loc;
           Qast.Node "PaApp"
             [Qast.Loc;
              Qast.Node "PaLong" [Qast.Loc; Qast.Node "LiUid" [Qast.Loc; Qast.VaVal (Qast.Str "::")];
                                   Qast.VaVal (Qast.List [])]; p1];
           loop False pl] ]
;

value mktupexp _ e el =
  Qast.Node "ExTup" [Qast.Loc; Qast.VaVal (Qast.Cons e (Qast.List el))]
;

value mktuppat _ p pl =
  Qast.Node "PaTup" [Qast.Loc; Qast.VaVal (Qast.Cons p (Qast.List pl))]
;

value mktuptyp _ t tl =
  Qast.Node "TyTup" [Qast.Loc; Qast.VaVal (Qast.Cons t (Qast.List tl))]
;

value mklabdecl _ i mf t attrs = Qast.Tuple [Qast.Loc; Qast.Str i; Qast.Bool mf; t; attrs];
value mkident i = Qast.Str i;

value generalized_type_of_type t =
  let rec gen =
    fun
    [ Qast.Node "TyArr" [_; t1; t2] ->
        let (tl, rt) = gen t2 in
        ([t1 :: tl], rt)
    | t ->
        ([], t) ]
  in
  let (tl, rt) = gen t in
  (Qast.List tl, rt)
;

value greek_ascii_equiv s = Qast.Str (Pcaml.greek_ascii_equiv s);

value warned = ref False;
value warning_deprecated_since_6_00 loc =
  if not warned.val then do {
    Pcaml.warning.val loc "syntax deprecated since version 6.00";
    warned.val := True
  }
  else ()
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
  try check (Stream.of_string s)
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

value stream_npeek n (strm  : Stream.t (string * string)) =
  Stream.npeek n strm
;

value check_dot_uid_f strm =
  match stream_npeek 5 strm with [
    [("",".") ; ("UIDENT",_) :: _] -> ()
  | [("",".") ; ("ANTIQUOT", qs) :: _]
    when prefix_eq "longid:" qs || prefix_eq "_longid:" qs
         || prefix_eq "uid:" qs || prefix_eq "_uid:" qs
    -> ()
  | [("",".") ; ("","$") ; ("LIDENT",("uid"|"_uid"|"longid"|"_longid")) ; ("", ":") ; ("LIDENT", _) :: _] -> ()
  | _ -> raise Stream.Failure
  ]
;

value check_dot_uid =
  Grammar.Entry.of_parser gram "check_dot_uid"
    check_dot_uid_f
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

value dotop =
  Grammar.Entry.of_parser gram "dotop"
    (parser
       [: `("", x) when is_dotop x :] -> Qast.Str x)
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
    module_expr longident extended_longident
    signature structure class_type class_expr class_sig_item
    class_str_item let_binding type_decl type_extension extension_constructor
    constructor_declaration
    label_declaration match_case ipatt with_constr poly_variant attribute_body
    check_type_decl check_type_extension check_dot_uid ctyp_ident
    check_type_binder
    ;
  attribute_id:
  [ [ l = LIST1 [ i = LIDENT -> i | i = UIDENT -> i ] SEP "." ->
      Qast.Tuple [Qast.Loc; Qast.Str (String.concat "." l)]
    | s = STRING -> Qast.Tuple [Qast.Loc; Qast.Str s]
    ] ]
  ;
  attribute_structure:
    [ [ st = SV (LIST1 [ s = str_item; ";" → s ]) "structure" → st ] ]
  ;
  attribute_signature:
    [ [ st = SV (LIST1 [ s = sig_item; ";" → s ]) "signature" → st ] ]
  ;
  attribute_body:
  [ [ id = SV attribute_id "attrid" ; st = attribute_structure ->
      Qast.Tuple [id; Qast.Node "StAttr" [Qast.Loc; st]]
    | id = SV attribute_id "attrid" ->
      Qast.Tuple [id; Qast.Node "StAttr" [Qast.Loc; Qast.VaVal (Qast.List [])]]
    | id = SV attribute_id "attrid" ; ":" ; si = attribute_signature -> 
      Qast.Tuple [id; Qast.Node "SiAttr" [Qast.Loc; si]]
    | id = SV attribute_id "attrid" ; ":" ; ty = SV ctyp "type" -> 
      Qast.Tuple [id; Qast.Node "TyAttr" [Qast.Loc; ty]]
    | id = SV attribute_id "attrid" ; "?" ;  p = SV patt "patt" -> 
      Qast.Tuple [id; Qast.Node "PaAttr" [Qast.Loc; p; Qast.Option None]]
    | id = SV attribute_id "attrid" ; "?" ;  p = SV patt "patt"; "when"; e = SV expr "expr" -> 
      Qast.Tuple [id; Qast.Node "PaAttr" [Qast.Loc; p; Qast.Option (Some e)]]
    ] ]
  ;
  floating_attribute:
  [ [ "[@@@" ; attr = SV attribute_body "attribute"; "]" -> attr
    ] ]
  ;
  item_attribute:
  [ [ "[@@" ; attr = SV attribute_body "attribute"; "]" -> attr
    ] ]
  ;
  alg_attribute:
  [ [ "[@" ; attr = SV attribute_body "attribute"; "]" -> attr
    ] ]
  ;
  item_attributes:
  [ [ l = SV (LIST0 item_attribute) "itemattrs" -> l ]
  ]
  ;
  alg_attributes:
  [ [ l = SV (LIST0 alg_attribute) "algattrs" -> l ]
  ]
  ;
  item_extension:
  [ [ "[%%" ; e = SV attribute_body "extension"; "]" -> e
    ] ]
  ;
  alg_extension:
  [ [ "[%" ; e = SV attribute_body "extension"; "]" -> e
    ] ]
  ;
  functor_parameter:
   [ [ "(" ; i = SV uidopt "uidopt"; ":"; t = module_type ; ")" →
                Qast.Option (Some (Qast.Tuple [i; t]))
     | "(" ; ")" → Qast.Option None ] ]
   ;
  module_expr:
    [ [ "functor"; arg = SV functor_parameter "functor_parameter" "fp"; "->";
        me = SELF →
          Qast.Node "MeFun" [Qast.Loc; arg; me] ]
    | "alg_attribute" LEFTA
      [ e = SELF ; "[@" ; attr = SV attribute_body "attribute"; "]" ->
        Qast.Node "MeAtt" [Qast.Loc; e; attr]
      ]
    | [ "struct"; st = structure; /; "end" →
          Qast.Node "MeStr" [Qast.Loc; st] ]
    | [ me1 = SELF; me2 = SELF → Qast.Node "MeApp" [Qast.Loc; me1; me2] ]
    | [ me1 = SELF; "."; me2 = SELF → Qast.Node "MeAcc" [Qast.Loc; me1; me2] ]
    | "simple"
      [ i = SV UIDENT → Qast.Node "MeUid" [Qast.Loc; i]
      | "("; "value"; e = expr; ":"; mt1 = module_type; ":>"; mt2 = module_type; ")" →
          Qast.Node "MeUnp" [Qast.Loc; e; Qast.Option (Some mt1); Qast.Option (Some mt2)]
      | "("; "value"; e = expr; ":"; mt = module_type; ")" →
          Qast.Node "MeUnp" [Qast.Loc; e; Qast.Option (Some mt); Qast.Option None]
      | "("; "value"; e = expr; ")" →
          Qast.Node "MeUnp" [Qast.Loc; e; Qast.Option None; Qast.Option None]
      | "("; me = SELF; ":"; mt = module_type; ")" →
          Qast.Node "MeTyc" [Qast.Loc; me; mt]
      | "("; me = SELF; ")" → me
      | e = alg_extension -> Qast.Node "MeExten" [Qast.Loc; e]
      ] ]
  ;
  structure:
    [ [ st = SV (LIST0 [ s = str_item; ";" → s ]) → st ] ]
  ;

  type_binder_opt: [ [
    check_type_binder ; ls = SV (LIST1 typevar) ; "." -> ls
  | -> Qast.VaVal (Qast.List [])
  ] ]
  ;
  str_item:
    [ "top" LEFTA
      [ si = SELF ; "[@@" ; attr = SV attribute_body "attribute"; "]" ->
        Qast.Node "StAtt" [Qast.Loc; si; attr]
      ]
    | "simple"
      [ "declare"; st = SV (LIST0 [ s = str_item; ";" → s ]); "end" →
          Qast.Node "StDcl" [Qast.Loc; st]
      | "exception"; ec = SV extension_constructor "excon" ; item_attrs = item_attributes →
          Qast.Node "StExc" [Qast.Loc; ec; item_attrs]

      | "external"; i = SV LIDENT; ":"; ls = type_binder_opt; t = ctyp; "=";
        pd = SV (LIST1 STRING) ; attrs = item_attributes →
          Qast.Node "StExt" [Qast.Loc; i; ls; t; pd; attrs]
      | "include"; me = module_expr ; attrs = item_attributes → Qast.Node "StInc" [Qast.Loc; me; attrs]
      | "module"; r = SV (FLAG "rec"); l = SV (LIST1 mod_binding SEP "and") →
          Qast.Node "StMod" [Qast.Loc; r; l]
      | "module"; "type"; i = SV ident ""; "="; mt = module_type ; attrs = item_attributes →
          Qast.Node "StMty" [Qast.Loc; i; mt; attrs]
      | "open"; ovf = SV (FLAG "!") "!"; me = module_expr ; attrs = item_attributes →
          Qast.Node "StOpn" [Qast.Loc; ovf; me; attrs]
      | "type" ; check_type_decl ; nrfl = SV (FLAG "nonrec");
        tdl = SV (LIST1 type_decl SEP "and") →
          Qast.Node "StTyp" [Qast.Loc; nrfl; tdl]
      | "type" ; check_type_extension ; te = type_extension →
          Qast.Node "StTypExten" [Qast.Loc; te]
      | "value"; r = SV (FLAG "rec"); l = SV (LIST1 let_binding SEP "and") →
          Qast.Node "StVal" [Qast.Loc; r; l]
      | "#"; n = SV LIDENT; dp = SV (OPT expr) →
          Qast.Node "StDir" [Qast.Loc; n; dp]
      | "#"; s = SV STRING;
        sil = SV (LIST0 [ si = str_item → Qast.Tuple [si; Qast.Loc] ]) →
          Qast.Node "StUse" [Qast.Loc; s; sil]
      | e = expr ; attrs = item_attributes → Qast.Node "StExp" [Qast.Loc; e; attrs]
      | attr = floating_attribute -> Qast.Node "StFlAtt" [Qast.Loc; attr]
      | e = item_extension ; attrs = item_attributes -> Qast.Node "StExten" [Qast.Loc; e; attrs]
      ] ]
  ;
  mod_binding:
    [ [ i = SV uidopt "uidopt"; me = mod_fun_binding ; attrs = item_attributes →
        Qast.Tuple [i; me; attrs] ] ]
  ;
  mod_fun_binding:
    [ RIGHTA
      [ arg = SV functor_parameter "functor_parameter" "fp"; mb = SELF →
          Qast.Node "MeFun" [Qast.Loc; arg; mb]
      | ":"; mt = module_type; "="; me = module_expr →
          Qast.Node "MeTyc" [Qast.Loc; me; mt]
      | "="; me = module_expr → me ] ]
  ;
  module_type:
    [ [ "functor"; arg = SV functor_parameter "functor_parameter" "fp"; "->";
        mt = SELF →
          Qast.Node "MtFun" [Qast.Loc; arg; mt] ]
    | "->" RIGHTA
        [ mt1=SELF ; "->" ; mt2=SELF →
                    Qast.Node "MtFun"
                      [Qast.Loc;
                       Qast.VaVal
                         (Qast.Option
                            (Some (Qast.Tuple [Qast.VaVal (Qast.Option None); mt1])));
                       mt2] ]
    | "alg_attribute" LEFTA
      [ e = SELF ; "[@" ; attr = SV attribute_body "attribute"; "]" ->
        Qast.Node "MtAtt" [Qast.Loc; e; attr]
      ]
    
    | [ mt = SELF; "with"; wcl = SV (LIST1 with_constr SEP "and") →
          Qast.Node "MtWit" [Qast.Loc; mt; wcl] ]
    | [ "sig"; sg = signature; /; "end" → Qast.Node "MtSig" [Qast.Loc; sg]
      | "module"; "type"; "of"; me = module_expr →
          Qast.Node "MtTyo" [Qast.Loc; me] ]
    | "simple"
      [ li = extended_longident; "."; i = SV LIDENT → Qast.Node "MtLongLid" [Qast.Loc; li; i]
      | li = extended_longident → Qast.Node "MtLong" [Qast.Loc; li]
      | i = SV LIDENT → Qast.Node "MtLid" [Qast.Loc; i]
      | e = alg_extension -> Qast.Node "MtExten" [Qast.Loc; e]
      | "'"; i = SV ident "" → Qast.Node "MtQuo" [Qast.Loc; i]
      | "("; mt = SELF; ")" → mt ] ]
  ;
  signature:
    [ [ st = SV (LIST0 [ s = sig_item; ";" → s ]) → st ] ]
  ;
  sig_item:
    [ "top" LEFTA
      [ si = SELF ; "[@@" ; attr = SV attribute_body "attribute"; "]" ->
        Qast.Node "SgAtt" [Qast.Loc; si; attr]
      ]
    | "simple"
      [ "declare"; st = SV (LIST0 [ s = sig_item; ";" → s ]); "end" →
          Qast.Node "SgDcl" [Qast.Loc; st]
      | "exception"; ctl = constructor_declaration ; item_attrs = item_attributes →
          Qast.Node "SgExc" [Qast.Loc; ctl; item_attrs]
      | "external"; i = SV LIDENT; ":"; ls = type_binder_opt; t = ctyp; "=";
        pd = SV (LIST1 STRING) ; attrs = item_attributes →
          Qast.Node "SgExt" [Qast.Loc; i; ls; t; pd; attrs]
      | "include"; mt = module_type ; attrs = item_attributes → Qast.Node "SgInc" [Qast.Loc; mt; attrs]
      | "module"; rf = SV (FLAG "rec");
        l = SV (LIST1 mod_decl_binding SEP "and") →
          Qast.Node "SgMod" [Qast.Loc; rf; l]
      | "module"; "alias"; i = SV UIDENT "uid"; "="; li = SV longident "longid" ; attrs = item_attributes →
          Qast.Node "SgMtyAlias" [Qast.Loc; i; li; attrs]
      | "module"; check_uident_coloneq; i = SV UIDENT "uid" ; ":=" ; li = extended_longident ; attrs = item_attributes ->
          Qast.Node "SgModSubst" [Qast.Loc; i;  li; attrs]
      | "module"; "type"; i = SV ident ""; "="; mt = module_type ; attrs = item_attributes →
          Qast.Node "SgMty" [Qast.Loc; i; mt; attrs]
      | "module"; "type"; i = SV ident ""; ":="; mt = module_type ; attrs = item_attributes →
          Qast.Node "SgMtySubst" [Qast.Loc; i; mt; attrs]
      | "open"; i = extended_longident ; attrs = item_attributes → Qast.Node "SgOpn" [Qast.Loc; i; attrs]
      | "type" ; check_type_decl ; nrfl = SV (FLAG "nonrec") ; tdl = SV (LIST1 type_decl SEP "and") →
          Qast.Node "SgTyp" [Qast.Loc; nrfl; tdl]
      | "type" ; check_type_extension ; te = type_extension →
          Qast.Node "SgTypExten" [Qast.Loc; te]
      | "value"; i = SV LIDENT; ":"; t = ctyp ; attrs = item_attributes →
          Qast.Node "SgVal" [Qast.Loc; i; t; attrs]
      | "#"; n = SV LIDENT; dp = SV (OPT expr) →
          Qast.Node "SgDir" [Qast.Loc; n; dp]
      | "#"; s = SV STRING;
        sil = SV (LIST0 [ si = sig_item → Qast.Tuple [si; Qast.Loc] ]) →
          Qast.Node "SgUse" [Qast.Loc; s; sil]
      | attr = floating_attribute -> Qast.Node "SgFlAtt" [Qast.Loc; attr]
      | e = item_extension ; attrs = item_attributes -> Qast.Node "SgExten" [Qast.Loc; e; attrs]
      ] ]
  ;
  mod_decl_binding:
    [ [ i = SV uidopt "uidopt"; mt = module_declaration ; attrs = item_attributes →
          Qast.Tuple [i; mt; attrs] ] ]
  ;
  module_declaration:
    [ RIGHTA
      [ ":"; mt = module_type → mt
      | arg = SV functor_parameter "functor_parameter" "fp"; mt = SELF →
          Qast.Node "MtFun" [Qast.Loc; arg; mt] ] ]
  ;
  with_constr:
    [ [ "type"; lili = SV longident_lident "lilongid"; tpl = SV (LIST0 type_parameter);
        "="; pf = SV (FLAG "private"); t = ctyp →
          Qast.Node "WcTyp" [Qast.Loc; lili; tpl; pf; t]
      | "type"; lili = SV longident_lident "lilongid"; tpl = SV (LIST0 type_parameter);
        ":="; t = ctyp →
          Qast.Node "WcTys" [Qast.Loc; lili; tpl; t]
      | "module"; i = SV longident "longid"; "="; me = module_expr →
          Qast.Node "WcMod" [Qast.Loc; i; me]
      | "module"; i = SV longident "longid"; ":="; me = module_expr →
          Qast.Node "WcMos" [Qast.Loc; i; me]
      | "module"; "type"; i = SV longident "longid"; "="; mt = module_type →
          Qast.Node "WcMty" [Qast.Loc; i; mt]
      | "module"; "type"; i = SV longident "longid"; ":="; mt = module_type →
          Qast.Node "WcMts" [Qast.Loc; i; mt]
      ] ]
  ;
  uidopt:
    [ [ m = SV UIDENT → Qast.Option (Some m)
      | "_" → Qast.Option None ] ]
  ;
  expr:
    [ "top" RIGHTA
      [ check_let_exception ; "let" ; "exception" ; id = SV UIDENT "uid" ;
        "of"; tyl = SV (LIST1 ctyp LEVEL "below_alg_attribute") ; alg_attrs = alg_attributes ;
        "in" ; x = SELF ->
          Qast.Node "ExLEx" [Qast.Loc ; id ; tyl ; x; alg_attrs]
      | check_let_exception ; "let" ; "exception" ; id = SV UIDENT "uid"; alg_attrs = alg_attributes ;
        "in" ; x = SELF ->
          Qast.Node "ExLEx" [Qast.Loc ; id ; Qast.VaVal(Qast.List[]) ; x; alg_attrs]
      | check_let_not_exception ; "let"; r = SV (FLAG "rec"); l = SV (LIST1 let_binding SEP "and");
        "in"; x = SELF →
          Qast.Node "ExLet" [Qast.Loc; r; l; x]
      | check_let_not_exception ; "let"; "module"; m = SV uidopt "uidopt"; mb = mod_fun_binding; "in";
        e = SELF →
          Qast.Node "ExLmd" [Qast.Loc; m; mb; e]
      | check_let_not_exception ; "let"; "open"; ovf = SV (FLAG "!") "!"; m = module_expr; "in"; e = SELF →
          Qast.Node "ExLop" [Qast.Loc; ovf; m; e]
      | "fun"; l = closed_case_list → Qast.Node "ExFun" [Qast.Loc; l]
      | "fun"; p = ipatt; e = fun_def →
          Qast.Node "ExFun"
            [Qast.Loc;
             Qast.VaVal
               (Qast.List [Qast.Tuple [p; Qast.VaVal (Qast.Option None); e]])]
      | "match"; e = SELF; "with"; l = closed_case_list →
          Qast.Node "ExMat" [Qast.Loc; e; l]
      | "match"; e = SELF; "with"; p1 = ipatt; "->"; e1 = SELF →
          Qast.Node "ExMat"
            [Qast.Loc; e;
             Qast.VaVal
               (Qast.List
                  [Qast.Tuple [p1; Qast.VaVal (Qast.Option None); e1]])]
      | "try"; e = SELF; "with"; l = closed_case_list →
          Qast.Node "ExTry" [Qast.Loc; e; l]
      | "try"; e = SELF; "with"; mc = match_case →
          Qast.Node "ExTry" [Qast.Loc; e; Qast.VaVal (Qast.List [mc])]
      | "if"; e1 = SELF; "then"; e2 = SELF; "else"; e3 = SELF →
          Qast.Node "ExIfe" [Qast.Loc; e1; e2; e3]
      | "do"; "{"; seq = SV sequence "list"; "}" → mksequence2 Qast.Loc seq
      | "for"; i = patt; "="; e1 = SELF; df = SV direction_flag "to";
        e2 = SELF; "do"; "{"; seq = SV sequence "list"; "}" →
          Qast.Node "ExFor" [Qast.Loc; i; e1; e2; df; seq]
      | "while"; e = SELF; "do"; "{"; seq = SV sequence "list"; "}" →
          Qast.Node "ExWhi" [Qast.Loc; e; seq] ]
    | "where"
      [ e = SELF; "where"; rf = SV (FLAG "rec"); lb = let_binding →
          Qast.Node "ExLet" [Qast.Loc; rf; Qast.VaVal (Qast.List [lb]); e] ]
    | ":=" NONA
      [ e1 = SELF; ":="; e2 = SELF; dummy →
          Qast.Node "ExAss" [Qast.Loc; e1; e2] ]
    | "||" RIGHTA
      [ e1 = SELF; "||"; e2 = SELF →
          Qast.Node "ExApp"
            [Qast.Loc;
             Qast.Node "ExApp"
               [Qast.Loc;
                Qast.Node "ExLid" [Qast.Loc; Qast.VaVal (Qast.Str "||")]; e1];
             e2] ]
    | "&&" RIGHTA
      [ e1 = SELF; "&&"; e2 = SELF →
          Qast.Node "ExApp"
            [Qast.Loc;
             Qast.Node "ExApp"
               [Qast.Loc;
                Qast.Node "ExLid" [Qast.Loc; Qast.VaVal (Qast.Str "&&")]; e1];
             e2] ]
    | "<" LEFTA
      [ e1 = SELF; "<"; e2 = SELF →
          Qast.Node "ExApp"
            [Qast.Loc;
             Qast.Node "ExApp"
               [Qast.Loc;
                Qast.Node "ExLid" [Qast.Loc; Qast.VaVal (Qast.Str "<")]; e1];
             e2]
      | e1 = SELF; ">"; e2 = SELF →
          Qast.Node "ExApp"
            [Qast.Loc;
             Qast.Node "ExApp"
               [Qast.Loc;
                Qast.Node "ExLid" [Qast.Loc; Qast.VaVal (Qast.Str ">")]; e1];
             e2]
      | e1 = SELF; "<="; e2 = SELF →
          Qast.Node "ExApp"
            [Qast.Loc;
             Qast.Node "ExApp"
               [Qast.Loc;
                Qast.Node "ExLid" [Qast.Loc; Qast.VaVal (Qast.Str "<=")]; e1];
             e2]
      | e1 = SELF; ">="; e2 = SELF →
          Qast.Node "ExApp"
            [Qast.Loc;
             Qast.Node "ExApp"
               [Qast.Loc;
                Qast.Node "ExLid" [Qast.Loc; Qast.VaVal (Qast.Str ">=")]; e1];
             e2]
      | e1 = SELF; "="; e2 = SELF →
          Qast.Node "ExApp"
            [Qast.Loc;
             Qast.Node "ExApp"
               [Qast.Loc;
                Qast.Node "ExLid" [Qast.Loc; Qast.VaVal (Qast.Str "=")]; e1];
             e2]
      | e1 = SELF; "<>"; e2 = SELF →
          Qast.Node "ExApp"
            [Qast.Loc;
             Qast.Node "ExApp"
               [Qast.Loc;
                Qast.Node "ExLid" [Qast.Loc; Qast.VaVal (Qast.Str "<>")]; e1];
             e2]
      | e1 = SELF; "=="; e2 = SELF →
          Qast.Node "ExApp"
            [Qast.Loc;
             Qast.Node "ExApp"
               [Qast.Loc;
                Qast.Node "ExLid" [Qast.Loc; Qast.VaVal (Qast.Str "==")]; e1];
             e2]
      | e1 = SELF; "!="; e2 = SELF →
          Qast.Node "ExApp"
            [Qast.Loc;
             Qast.Node "ExApp"
               [Qast.Loc;
                Qast.Node "ExLid" [Qast.Loc; Qast.VaVal (Qast.Str "!=")]; e1];
             e2] ]
    | "^" RIGHTA
      [ e1 = SELF; "^"; e2 = SELF →
          Qast.Node "ExApp"
            [Qast.Loc;
             Qast.Node "ExApp"
               [Qast.Loc;
                Qast.Node "ExLid" [Qast.Loc; Qast.VaVal (Qast.Str "^")]; e1];
             e2]
      | e1 = SELF; "@"; e2 = SELF →
          Qast.Node "ExApp"
            [Qast.Loc;
             Qast.Node "ExApp"
               [Qast.Loc;
                Qast.Node "ExLid" [Qast.Loc; Qast.VaVal (Qast.Str "@")]; e1];
             e2] ]
    | "alg_attribute" LEFTA
      [ e = SELF ; "[@" ; attr = SV attribute_body "attribute"; "]" ->
        Qast.Node "ExAtt" [Qast.Loc; e; attr]
      ]
    | "+" LEFTA
      [ e1 = SELF; "+"; e2 = SELF →
          Qast.Node "ExApp"
            [Qast.Loc;
             Qast.Node "ExApp"
               [Qast.Loc;
                Qast.Node "ExLid" [Qast.Loc; Qast.VaVal (Qast.Str "+")]; e1];
             e2]
      | e1 = SELF; "-"; e2 = SELF →
          Qast.Node "ExApp"
            [Qast.Loc;
             Qast.Node "ExApp"
               [Qast.Loc;
                Qast.Node "ExLid" [Qast.Loc; Qast.VaVal (Qast.Str "-")]; e1];
             e2]
      | e1 = SELF; "+."; e2 = SELF →
          Qast.Node "ExApp"
            [Qast.Loc;
             Qast.Node "ExApp"
               [Qast.Loc;
                Qast.Node "ExLid" [Qast.Loc; Qast.VaVal (Qast.Str "+.")]; e1];
             e2]
      | e1 = SELF; "-."; e2 = SELF →
          Qast.Node "ExApp"
            [Qast.Loc;
             Qast.Node "ExApp"
               [Qast.Loc;
                Qast.Node "ExLid" [Qast.Loc; Qast.VaVal (Qast.Str "-.")]; e1];
             e2] ]
    | "*" LEFTA
      [ e1 = SELF; "*"; e2 = SELF →
          Qast.Node "ExApp"
            [Qast.Loc;
             Qast.Node "ExApp"
               [Qast.Loc;
                Qast.Node "ExLid" [Qast.Loc; Qast.VaVal (Qast.Str "*")]; e1];
             e2]
      | e1 = SELF; "/"; e2 = SELF →
          Qast.Node "ExApp"
            [Qast.Loc;
             Qast.Node "ExApp"
               [Qast.Loc;
                Qast.Node "ExLid" [Qast.Loc; Qast.VaVal (Qast.Str "/")]; e1];
             e2]
      | e1 = SELF; "*."; e2 = SELF →
          Qast.Node "ExApp"
            [Qast.Loc;
             Qast.Node "ExApp"
               [Qast.Loc;
                Qast.Node "ExLid" [Qast.Loc; Qast.VaVal (Qast.Str "*.")]; e1];
             e2]
      | e1 = SELF; "/."; e2 = SELF →
          Qast.Node "ExApp"
            [Qast.Loc;
             Qast.Node "ExApp"
               [Qast.Loc;
                Qast.Node "ExLid" [Qast.Loc; Qast.VaVal (Qast.Str "/.")]; e1];
             e2]
      | e1 = SELF; "land"; e2 = SELF →
          Qast.Node "ExApp"
            [Qast.Loc;
             Qast.Node "ExApp"
               [Qast.Loc;
                Qast.Node "ExLid" [Qast.Loc; Qast.VaVal (Qast.Str "land")];
                e1];
             e2]
      | e1 = SELF; "lor"; e2 = SELF →
          Qast.Node "ExApp"
            [Qast.Loc;
             Qast.Node "ExApp"
               [Qast.Loc;
                Qast.Node "ExLid" [Qast.Loc; Qast.VaVal (Qast.Str "lor")];
                e1];
             e2]
      | e1 = SELF; "lxor"; e2 = SELF →
          Qast.Node "ExApp"
            [Qast.Loc;
             Qast.Node "ExApp"
               [Qast.Loc;
                Qast.Node "ExLid" [Qast.Loc; Qast.VaVal (Qast.Str "lxor")];
                e1];
             e2]
      | e1 = SELF; "mod"; e2 = SELF →
          Qast.Node "ExApp"
            [Qast.Loc;
             Qast.Node "ExApp"
               [Qast.Loc;
                Qast.Node "ExLid" [Qast.Loc; Qast.VaVal (Qast.Str "mod")];
                e1];
             e2] ]
    | "**" RIGHTA
      [ e1 = SELF; "**"; e2 = SELF →
          Qast.Node "ExApp"
            [Qast.Loc;
             Qast.Node "ExApp"
               [Qast.Loc;
                Qast.Node "ExLid" [Qast.Loc; Qast.VaVal (Qast.Str "**")]; e1];
             e2]
      | e1 = SELF; "asr"; e2 = SELF →
          Qast.Node "ExApp"
            [Qast.Loc;
             Qast.Node "ExApp"
               [Qast.Loc;
                Qast.Node "ExLid" [Qast.Loc; Qast.VaVal (Qast.Str "asr")];
                e1];
             e2]
      | e1 = SELF; "lsl"; e2 = SELF →
          Qast.Node "ExApp"
            [Qast.Loc;
             Qast.Node "ExApp"
               [Qast.Loc;
                Qast.Node "ExLid" [Qast.Loc; Qast.VaVal (Qast.Str "lsl")];
                e1];
             e2]
      | e1 = SELF; "lsr"; e2 = SELF →
          Qast.Node "ExApp"
            [Qast.Loc;
             Qast.Node "ExApp"
               [Qast.Loc;
                Qast.Node "ExLid" [Qast.Loc; Qast.VaVal (Qast.Str "lsr")];
                e1];
             e2] ]
    | "unary minus" NONA
      [ "-"; e = SELF →
          Qast.Node "ExApp"
            [Qast.Loc;
             Qast.Node "ExLid" [Qast.Loc; Qast.VaVal (Qast.Str "-")]; e]
      | "-."; e = SELF →
          Qast.Node "ExApp"
            [Qast.Loc;
             Qast.Node "ExLid" [Qast.Loc; Qast.VaVal (Qast.Str "-.")]; e] ]
    | "apply" LEFTA
      [ e1 = SELF; e2 = SELF → Qast.Node "ExApp" [Qast.Loc; e1; e2]
      | "assert"; e = SELF → Qast.Node "ExAsr" [Qast.Loc; e]
      | "lazy"; e = SELF → Qast.Node "ExLaz" [Qast.Loc; e] ]
    | "." LEFTA
      [ 
        e1 = SELF ; "." ; lili = SV longident_lident "lilongid" -> Qast.Node "ExFle" [Qast.Loc; e1;lili]
      | e1 = SELF; "."; "("; e2 = SELF; ")" →
          Qast.Node "ExAre" [Qast.Loc; Qast.VaVal(Qast.Str "."); e1; Qast.VaVal (Qast.List [e2])]
      | e1 = SELF; op = SV dotop "dotop"; "("; el = SV (LIST1 expr SEP ";"); ")" →
          Qast.Node "ExAre" [Qast.Loc; op; e1; el]

      | e1 = SELF; "."; "["; e2 = SELF; "]" →
          Qast.Node "ExSte" [Qast.Loc; Qast.VaVal(Qast.Str "."); e1; Qast.VaVal (Qast.List [e2])]
      | e1 = SELF; op = SV dotop "dotop"; "["; el = SV (LIST1 expr SEP ";"); "]" →
          Qast.Node "ExSte" [Qast.Loc; op; e1; el]

      | e = SELF; "."; "{"; el = SV (LIST1 expr SEP ","); "}" →
          Qast.Node "ExBae" [Qast.Loc; Qast.VaVal(Qast.Str "."); e; el]
      | e = SELF; op = SV dotop "dotop"; "{"; el = SV (LIST1 expr SEP ";"); "}" →
          Qast.Node "ExBae" [Qast.Loc; op; e; el]
      ]
    | "~-" NONA
      [ "~-"; e = SELF →
          Qast.Node "ExApp"
            [Qast.Loc;
             Qast.Node "ExLid" [Qast.Loc; Qast.VaVal (Qast.Str "~-")]; e]
      | "~-."; e = SELF →
          Qast.Node "ExApp"
            [Qast.Loc;
             Qast.Node "ExLid" [Qast.Loc; Qast.VaVal (Qast.Str "~-.")]; e] ]
    | "simple"
      [ s = SV INT → Qast.Node "ExInt" [Qast.Loc; s; Qast.Str ""]
      | s = SV INT_l → Qast.Node "ExInt" [Qast.Loc; s; Qast.Str "l"]
      | s = SV INT_L → Qast.Node "ExInt" [Qast.Loc; s; Qast.Str "L"]
      | s = SV INT_n → Qast.Node "ExInt" [Qast.Loc; s; Qast.Str "n"]
      | s = SV FLOAT → Qast.Node "ExFlo" [Qast.Loc; s]
      | s = SV STRING → Qast.Node "ExStr" [Qast.Loc; s]
      | s = SV CHAR → Qast.Node "ExChr" [Qast.Loc; s]
      | e = alg_extension -> Qast.Node "ExExten" [Qast.Loc; e]
      | i = SV LIDENT → Qast.Node "ExLid" [Qast.Loc; i]
      | i = SV GIDENT → Qast.Node "ExLid" [Qast.Loc; i]
      | i = longident → Qast.Node "ExLong" [Qast.Loc; i]
      | i = longident ; "." ; "(" ; e = expr ; ")" → Qast.Node "ExOpen" [Qast.Loc; i; e]
      | "." -> Qast.Node "ExUnr" [Qast.Loc]
      | "["; "]" → Qast.Node "ExLong" [Qast.Loc; Qast.Node "LiUid" [Qast.Loc; Qast.VaVal (Qast.Str "[]")]]
      | "["; el = LIST1 expr SEP ";"; last = cons_expr_opt; "]" →
          mklistexp Qast.Loc last el
      | "[|"; el = SV (LIST0 expr SEP ";"); "|]" →
          Qast.Node "ExArr" [Qast.Loc; el]
      | "{"; lel = SV (LIST1 label_expr SEP ";"); "}" →
          Qast.Node "ExRec" [Qast.Loc; lel; Qast.Option None]
      | "{"; "("; e = SELF; ")"; "with"; lel = SV (LIST1 label_expr SEP ";");
        "}" →
          Qast.Node "ExRec" [Qast.Loc; lel; Qast.Option (Some e)]
      | "("; ")" → Qast.Node "ExLong" [Qast.Loc; Qast.Node "LiUid" [Qast.Loc; Qast.VaVal (Qast.Str "()")]]
      | "("; "module"; me = module_expr; ":"; mt = module_type; ")" →
          Qast.Node "ExPck" [Qast.Loc; me; Qast.Option (Some mt)]
      | "("; "module"; me = module_expr; ")" →
          Qast.Node "ExPck" [Qast.Loc; me; Qast.Option None]
      | "("; e = SELF; ":"; t = ctyp; ")" → Qast.Node "ExTyc" [Qast.Loc; e; t]
      | "("; e = SELF; ","; el = LIST1 expr SEP ","; ")" →
          mktupexp Qast.Loc e el
      | "("; e = SELF; ")" → e
      | "("; el = SV (LIST1 expr SEP ","); ")" →
          Qast.Node "ExTup" [Qast.Loc; el] ] ]
  ;
  closed_case_list:
    [ [ "["; l = SV (LIST0 match_case SEP "|"); "]" → l
      | "|"; l = SV (LIST0 match_case SEP "|"); "end" → l ] ]
  ;
  cons_expr_opt:
    [ [ "::"; e = expr → Qast.Option (Some e)
      | → Qast.Option None ] ]
  ;
  dummy:
    [ [ → () ] ]
  ;
  sequence:
    [ RIGHTA
      [ "let"; rf = SV (FLAG "rec"); l = SV (LIST1 let_binding SEP "and");
        "in"; el = SELF →
          Qast.List
            [Qast.Node "ExLet" [Qast.Loc; rf; l; mksequence Qast.Loc el]]
      | "let"; "module"; m = SV uidopt "uidopt"; mb = mod_fun_binding; "in";
        el = SELF →
          Qast.List
            [Qast.Node "ExLmd" [Qast.Loc; m; mb; mksequence Qast.Loc el]]
      | "let"; "open"; ovf = SV (FLAG "!") "!"; m = module_expr; "in"; el = SELF →
          Qast.List [Qast.Node "ExLop" [Qast.Loc; ovf; m; mksequence Qast.Loc el]]
      | e = expr; ";"; el = SELF → Qast.Cons e el
      | e = expr; ";" → Qast.List [e]
      | e = expr → Qast.List [e] ] ]
  ;
  let_binding:
    [ [ p = ipatt; e = fun_binding ; attrs = item_attributes → Qast.Tuple [p; e; attrs] ] ]
  ;
  fun_binding:
    [ RIGHTA
      [ p = ipatt; e = SELF →
          Qast.Node "ExFun"
            [Qast.Loc;
             Qast.VaVal
               (Qast.List [Qast.Tuple [p; Qast.VaVal (Qast.Option None); e]])]
      | "="; e = expr → e
      | ":"; t = ctyp; "="; e = expr → Qast.Node "ExTyc" [Qast.Loc; e; t] ] ]
  ;
  match_case:
    [ [ p = patt; aso = as_patt_opt; w = SV (OPT when_expr); "->"; e = expr →
          mkmatchcase Qast.Loc p aso w e
      ] ]
  ;
  as_patt_opt:
    [ [ "as"; p = patt → Qast.Option (Some p)
      | → Qast.Option None ] ]
  ;
  when_expr:
    [ [ "when"; e = expr → e ] ]
  ;
  label_expr:
    [ [ i = patt_label_ident; e = fun_binding → Qast.Tuple [i; e] ] ]
  ;
  fun_def:
    [ RIGHTA
      [ p = ipatt; e = SELF →
          Qast.Node "ExFun"
            [Qast.Loc;
             Qast.VaVal
               (Qast.List [Qast.Tuple [p; Qast.VaVal (Qast.Option None); e]])]
      | "->"; e = expr → e ] ]
  ;
  patt_ident: [
    [ s = SV LIDENT → Qast.Node "PaLid" [Qast.Loc; s]
    | s = SV GIDENT → Qast.Node "PaLid" [Qast.Loc; s]
    | li = longident ; "." ; p = patt LEVEL "simple" → 
      Qast.Node "PaPfx" [Qast.Loc; li; p]
    | li = longident ; check_lparen_type ; "("; "type";
      loc_ids = SV (LIST1 [ s = LIDENT -> Qast.Tuple [Qast.Loc; Qast.Str s] ]) ; ")" → 
      Qast.Node "PaLong" [Qast.Loc; li; loc_ids]
    | li = longident → 
      Qast.Node "PaLong" [Qast.Loc; li; Qast.VaVal (Qast.List [])]
    ]
  ]
  ;
  patt:
    [ LEFTA
      [ p1 = SELF; "|"; p2 = SELF → Qast.Node "PaOrp" [Qast.Loc; p1; p2] ]
    | "alg_attribute" LEFTA
      [ p1 = SELF ; "[@" ; attr = SV attribute_body "attribute"; "]" ->
        Qast.Node "PaAtt" [Qast.Loc; p1; attr]
      ]
    | NONA
      [ "exception"; p = SELF → Qast.Node "PaExc" [Qast.Loc; p] ]

    | NONA
      [ p1 = SELF; ".."; p2 = SELF → Qast.Node "PaRng" [Qast.Loc; p1; p2] ]
    | LEFTA
      [ p1 = SELF; p2 = SELF → Qast.Node "PaApp" [Qast.Loc; p1; p2]
      | "lazy"; p = SELF → Qast.Node "PaLaz" [Qast.Loc; p] ]
    | "simple"
      [ 
        e = alg_extension -> Qast.Node "PaExten" [Qast.Loc; e]
      | p = patt_ident -> p
      | s = SV INT → Qast.Node "PaInt" [Qast.Loc; s; Qast.Str ""]
      | s = SV INT_l → Qast.Node "PaInt" [Qast.Loc; s; Qast.Str "l"]
      | s = SV INT_L → Qast.Node "PaInt" [Qast.Loc; s; Qast.Str "L"]
      | s = SV INT_n → Qast.Node "PaInt" [Qast.Loc; s; Qast.Str "n"]
      | s = SV FLOAT → Qast.Node "PaFlo" [Qast.Loc; s]
      | s = SV STRING → Qast.Node "PaStr" [Qast.Loc; s]
      | s = SV CHAR → Qast.Node "PaChr" [Qast.Loc; s]
      | "-"; s = INT →
          Qast.Node "PaInt" [Qast.Loc; Qast.VaVal (neg_string s); Qast.Str ""]
      | "-"; s = INT_l →
          Qast.Node "PaInt"
            [Qast.Loc; Qast.VaVal (neg_string s); Qast.Str "l"]
      | "-"; s = INT_L →
          Qast.Node "PaInt"
            [Qast.Loc; Qast.VaVal (neg_string s); Qast.Str "L"]
      | "-"; s = INT_n →
          Qast.Node "PaInt"
            [Qast.Loc; Qast.VaVal (neg_string s); Qast.Str "n"]
      | "-"; s = FLOAT →
          Qast.Node "PaFlo" [Qast.Loc; Qast.VaVal (neg_string s)]
      | "["; "]" → Qast.Node "PaLong" [Qast.Loc; Qast.Node "LiUid" [Qast.Loc; Qast.VaVal (Qast.Str "[]")];
                                        Qast.VaVal (Qast.List [])]
      | "["; pl = LIST1 patt SEP ";"; last = cons_patt_opt; "]" →
          mklistpat Qast.Loc last pl
      | "[|"; pl = SV (LIST0 patt SEP ";"); "|]" →
          Qast.Node "PaArr" [Qast.Loc; pl]
      | "{"; lpl = SV (LIST1 label_patt SEP ";"); "}" →
          Qast.Node "PaRec" [Qast.Loc; lpl]
      | "("; p = paren_patt; ")" → p
      | "_" → Qast.Node "PaAny" [Qast.Loc] ] ]
  ;
  paren_patt:
    [ [ p = patt; ":"; t = ctyp → Qast.Node "PaTyc" [Qast.Loc; p; t]
      | p = patt; "as"; p2 = patt → Qast.Node "PaAli" [Qast.Loc; p; p2]
      | p = patt; ","; pl = LIST1 patt SEP "," → mktuppat Qast.Loc p pl
      | p = patt → p
      | pl = SV (LIST1 patt SEP ",") → Qast.Node "PaTup" [Qast.Loc; pl]
      | "type"; s = SV LIDENT → Qast.Node "PaNty" [Qast.Loc; s]
      | "module"; s = SV uidopt "uidopt"; ":"; mt = module_type →
          Qast.Node "PaUnp" [Qast.Loc; s; Qast.Option (Some mt)]
      | "module"; s = SV uidopt "uidopt" →
          Qast.Node "PaUnp" [Qast.Loc; s; Qast.Option None]
      | → 
Qast.Node "PaLong" [Qast.Loc; Qast.Node "LiUid" [Qast.Loc; (Qast.VaVal (Qast.Str "()"))];
                     Qast.VaVal (Qast.List [])]
      ] ]
  ;
  cons_patt_opt:
    [ [ "::"; p = patt → Qast.Option (Some p)
      | → Qast.Option None ] ]
  ;
  label_patt:
    [ [ i = patt_label_ident; "="; p = patt → Qast.Tuple [i; p] ] ]
  ;
  patt_label_ident:
    [ LEFTA
      [ p1 = longident; "."; p2 = SELF → Qast.Node "PaPfx" [Qast.Loc; p1; p2]
      | p1 = longident → Qast.Node "PaLong" [Qast.Loc; p1;
                                              Qast.VaVal (Qast.List [])]
      | i = SV LIDENT → Qast.Node "PaLid" [Qast.Loc; i]
      | "_" → Qast.Node "PaAny" [Qast.Loc]
      ] ]
  ;
  ipatt:
    [ [ "{"; lpl = SV (LIST1 label_ipatt SEP ";"); "}" →
          Qast.Node "PaRec" [Qast.Loc; lpl]
      | "("; p = paren_ipatt; ")" → p
      | e = alg_extension -> Qast.Node "PaExten" [Qast.Loc; e]
      | s = SV LIDENT → Qast.Node "PaLid" [Qast.Loc; s]
      | s = SV GIDENT → Qast.Node "PaLid" [Qast.Loc; s]
      | "_" → Qast.Node "PaAny" [Qast.Loc] ] ]
  ;
  paren_ipatt:
    [ [ p = ipatt; ":"; t = ctyp → Qast.Node "PaTyc" [Qast.Loc; p; t]
      | p = ipatt; "as"; p2 = ipatt → Qast.Node "PaAli" [Qast.Loc; p; p2]
      | p = ipatt; ","; pl = LIST1 ipatt SEP "," → mktuppat Qast.Loc p pl
      | p = ipatt → p
      | pl = SV (LIST1 ipatt SEP ",") → Qast.Node "PaTup" [Qast.Loc; pl]
      | "type"; s = SV LIDENT → Qast.Node "PaNty" [Qast.Loc; s]
      | "module"; s = SV uidopt "uidopt"; ":"; mt = module_type →
          Qast.Node "PaUnp" [Qast.Loc; s; Qast.Option (Some mt)]
      | "module"; s = SV uidopt "uidopt" →
          Qast.Node "PaUnp" [Qast.Loc; s; Qast.Option None]

      | → Qast.Node "PaLong" [Qast.Loc; Qast.Node "LiUid" [Qast.Loc; Qast.VaVal (Qast.Str "()")];
                               Qast.VaVal (Qast.List [])] ] ]
  ;
  label_ipatt:
    [ [ i = patt_label_ident; "="; p = ipatt → Qast.Tuple [i; p] ] ]
  ;
  type_decl:
    [ [ n = SV type_patt "tp"; tpl = SV (LIST0 type_parameter);
        isDecl = SV [ "=" -> Qast.Bool True | ":=" -> Qast.Bool False ] "isdecl";
        pf = SV (FLAG "private") "priv"; tk = ctyp;
        cl = SV (LIST0 constrain) ; attrs = item_attributes →
          Qast.Record
            [("tdIsDecl", isDecl); ("tdNam", n); ("tdPrm", tpl); ("tdPrv", pf); ("tdDef", tk);
             ("tdCon", cl); ("tdAttributes", attrs)] ] ]
  ;
  (* TODO FIX: this should be a longident+lid, to match ocaml's grammar *)
  type_extension:
    [ [ n = SV longident_lident "lilongid"; tpl = SV (LIST0 type_parameter); "+=";
        pf = SV (FLAG "private") "priv"; "[" ; ecs = SV (LIST1 extension_constructor SEP "|") ; "]" ;
        attrs = item_attributes →
          Qast.Record
            [("teNam", n); ("tePrm", tpl); ("tePrv", pf);
             ("teECs", ecs);
             ("teAttributes", attrs)] ] ]
  ;
  type_patt:
    [ [ n = SV LIDENT → Qast.Tuple [Qast.Loc; n] ] ]
  ;
  constrain:
    [ [ "constraint"; t1 = ctyp; "="; t2 = ctyp → Qast.Tuple [t1; t2] ] ]
  ;
  type_parameter:
    [ [ "+"; p = SV simple_type_parameter →
          Qast.Tuple [p; Qast.Option (Some (Qast.Bool True))]
      | "-"; p = SV simple_type_parameter →
          Qast.Tuple [p; Qast.Option (Some (Qast.Bool False))]
      | p = SV simple_type_parameter → Qast.Tuple [p; Qast.Option None] ] ]
  ;
  simple_type_parameter:
    [ [ "'"; i = ident → Qast.Option (Some i)
      | i = GIDENT → Qast.Option (Some (greek_ascii_equiv i))
      | "_" → Qast.Option None ] ]
  ;
  longident:
    [ LEFTA
      [ me1 = SELF; check_dot_uid ; "."; i = SV UIDENT "uid" → Qast.Node "LiAcc" [Qast.Loc; me1; i]
      ]
    | "simple"
      [ i = SV UIDENT "uid" → Qast.Node "LiUid" [Qast.Loc; i]
      ] ]
  ;
  extended_longident:
    [ LEFTA
      [ me1 = SELF; "(" ; me2 = SELF ; ")" → Qast.Node "LiApp" [Qast.Loc; me1; me2]
      | me1 = SELF; check_dot_uid ; "."; i = SV UIDENT "uid" → Qast.Node "LiAcc" [Qast.Loc; me1; i]
      ]
    | "simple"
      [ i = SV UIDENT "uid" → Qast.Node "LiUid" [Qast.Loc; i]
      ] ]
  ;
  ctyp_ident:
    [ LEFTA
      [ me1 = extended_longident ; "." ; i = SV LIDENT "lid" → 
          Qast.Node "TyAcc" [Qast.Loc; me1; i]
      | i = SV LIDENT "lid" → 
          Qast.Node "TyLid" [Qast.Loc; i]
      ] 
    ]
  ;
  ctyp:
    [ "top" LEFTA
      [ t1 = SELF; "=="; pf = SV (FLAG "private") "priv"; t2 = SELF →
          Qast.Node "TyMan" [Qast.Loc; t1; pf; t2] ]
    | "alg_attribute" LEFTA
      [ t1 = SELF ; "[@" ; attr = SV attribute_body "attribute"; "]" ->
        Qast.Node "TyAtt" [Qast.Loc; t1; attr]
      ]
    | "below_alg_attribute" [ t = NEXT -> t ]
    | "as" LEFTA
      [ t1 = SELF; "as"; t2 = SELF → Qast.Node "TyAli" [Qast.Loc; t1; t2] ]
    | LEFTA
      [ "!"; pl = SV (LIST1 typevar); "."; t = SELF →
          Qast.Node "TyPol" [Qast.Loc; pl; t]
      | "type"; pl = SV (LIST1 LIDENT); "."; t = SELF →
          Qast.Node "TyPot" [Qast.Loc; pl; t] ]
    | "arrow" RIGHTA
      [ t1 = SELF; "->"; t2 = SELF → Qast.Node "TyArr" [Qast.Loc; t1; t2] ]
    | "apply" LEFTA
      [ t1 = SELF; t2 = SELF → Qast.Node "TyApp" [Qast.Loc; t1; t2] ]
    | LEFTA
      [ t = ctyp_ident → t ]
    | "simple"
      [ "'"; i = SV ident "" → Qast.Node "TyQuo" [Qast.Loc; i]
      | i = GIDENT →
          Qast.Node "TyQuo" [Qast.Loc; Qast.VaVal (greek_ascii_equiv i)]
      | ".." -> Qast.Node "TyOpn" [Qast.Loc]
      | "_" → Qast.Node "TyAny" [Qast.Loc]
      | e = alg_extension -> Qast.Node "TyExten" [Qast.Loc; e]
      | "("; "module"; mt = module_type ; ")" → Qast.Node "TyPck" [Qast.Loc; mt]
      | "("; t = SELF; "*"; tl = LIST1 ctyp SEP "*"; ")" →
          mktuptyp Qast.Loc t tl
      | "("; t = SELF; ")" → t
      | "("; tl = SV (LIST1 ctyp SEP "*"); ")" →
          Qast.Node "TyTup" [Qast.Loc; tl]
      | "["; cdl = SV (LIST0 constructor_declaration SEP "|"); "]" →
          Qast.Node "TySum" [Qast.Loc; cdl]
      | "{"; ldl = SV (LIST1 label_declaration SEP ";"); "}" →
          Qast.Node "TyRec" [Qast.Loc; ldl] ] ]
  ;
  cons_ident:
  [ [ ci = SV UIDENT -> ci
    ] ] ;
  constructor_declaration:
    [ [ ci = cons_ident; l = rest_constructor_declaration →
          Qast.Tuple [Qast.Loc; ci :: l] ] ]
  ;
  rest_constructor_declaration:
    [ [ "of"; ls = type_binder_opt; cal = SV (LIST1 ctyp SEP "and") ;
        rto = SV (OPT [ ":" ; t = ctyp -> t ]) "rto" ; alg_attrs = alg_attributes →
          [ls; cal; rto; alg_attrs]
      | rto = SV (OPT [ ":" ; t = ctyp -> t ]) "rto" ; alg_attrs = alg_attributes →
          [Qast.VaVal (Qast.List[]); Qast.VaVal (Qast.List []); rto; alg_attrs]
      ] ]
  ;
  extension_constructor:
  [ [ ci = cons_ident ; "="; b = SV longident "longid" ; alg_attrs = alg_attributes ->
        Qast.Node "EcRebind" [Qast.Loc; ci; b; alg_attrs]
    | ci = cons_ident; l = rest_constructor_declaration →
        Qast.Node "EcTuple" [Qast.Loc; Qast.Tuple [Qast.Loc; ci :: l]]
    ] ]
  ;
  label_declaration:
    [ [ i = LIDENT; ":"; mf = FLAG "mutable"; t = ctyp LEVEL "below_alg_attribute" ; alg_attrs = alg_attributes →
          mklabdecl Qast.Loc i mf t alg_attrs ] ]
  ;
  ident:
    [ [ i = LIDENT → mkident i
      | i = UIDENT → mkident i ] ]
  ;
  direction_flag:
    [ [ "to" → Qast.Bool True
      | "downto" → Qast.Bool False ] ]
  ;
  typevar:
    [ [ "'"; i = ident → i ] ]
  ;
  (* Objects and Classes *)
  str_item:
    [ [ "class"; cd = SV (LIST1 class_declaration SEP "and") →
          Qast.Node "StCls" [Qast.Loc; cd]
      | "class"; "type"; ctd = SV (LIST1 class_type_declaration SEP "and") →
          Qast.Node "StClt" [Qast.Loc; ctd] ] ]
  ;
  sig_item:
    [ [ "class"; cd = SV (LIST1 class_description SEP "and") →
          Qast.Node "SgCls" [Qast.Loc; cd]
      | "class"; "type"; ctd = SV (LIST1 class_type_declaration SEP "and") →
          Qast.Node "SgClt" [Qast.Loc; ctd] ] ]
  ;
  class_declaration:
    [ [ vf = SV (FLAG "virtual"); i = SV LIDENT; ctp = class_type_parameters;
        cfb = class_fun_binding ; attrs = item_attributes →
          Qast.Record
            [("ciLoc", Qast.Loc); ("ciVir", vf); ("ciPrm", ctp); ("ciNam", i);
             ("ciExp", cfb); ("ciAttributes", attrs)] ] ]
  ;
  class_fun_binding:
    [ [ "="; ce = class_expr → ce
      | ":"; ct = class_type; "="; ce = class_expr →
          Qast.Node "CeTyc" [Qast.Loc; ce; ct]
      | p = ipatt; cfb = SELF → Qast.Node "CeFun" [Qast.Loc; p; cfb] ] ]
  ;
  class_type_parameters:
    [ [ → Qast.Tuple [Qast.Loc; Qast.VaVal (Qast.List [])]
      | "["; tpl = SV (LIST1 type_parameter SEP ","); "]" →
          Qast.Tuple [Qast.Loc; tpl] ] ]
  ;
  class_fun_def:
    [ [ p = ipatt; ce = SELF → Qast.Node "CeFun" [Qast.Loc; p; ce]
      | "->"; ce = class_expr → ce ] ]
  ;
  class_expr:
    [ "top"
      [ "fun"; p = ipatt; ce = class_fun_def →
          Qast.Node "CeFun" [Qast.Loc; p; ce]
      | "let"; rf = SV (FLAG "rec"); lb = SV (LIST1 let_binding SEP "and");
        "in"; ce = SELF →
          Qast.Node "CeLet" [Qast.Loc; rf; lb; ce]
      | "let"; "open"; ovf = SV (FLAG "!") "!"; i = extended_longident; "in"; ce = SELF →
          Qast.Node "CeLop" [Qast.Loc; ovf; i; ce]
      ]
    | "alg_attribute" LEFTA
      [ t1 = SELF ; "[@" ; attr = SV attribute_body "attribute"; "]" ->
        Qast.Node "CeAtt" [Qast.Loc; t1; attr]
      ]

    | "apply" LEFTA
      [ ce = SELF; e = expr LEVEL "label" →
          Qast.Node "CeApp" [Qast.Loc; ce; e] ]
    | "alg_attribute" LEFTA
      [ t1 = SELF ; "[@" ; attr = SV attribute_body "attribute"; "]" ->
        Qast.Node "CeAtt" [Qast.Loc; t1; attr]
      ]

    | "simple"
      [ cli = SV longident_lident "lilongid" →
          Qast.Node "CeCon" [Qast.Loc; cli; Qast.VaVal (Qast.List [])]
      | "object"; cspo = SV (OPT class_self_patt); cf = class_structure;
        "end" →
          Qast.Node "CeStr" [Qast.Loc; cspo; cf]
      | "["; ctcl = SV (LIST1 ctyp SEP ","); "]";
        cli = SV longident_lident "lilongid" →
          Qast.Node "CeCon" [Qast.Loc; cli; ctcl]
      | "("; ce = SELF; ":"; ct = class_type; ")" →
          Qast.Node "CeTyc" [Qast.Loc; ce; ct]
      | "("; ce = SELF; ")" → ce
      | e = alg_extension -> Qast.Node "CeExten" [Qast.Loc; e]
      ] ]
  ;
  class_structure:
    [ [ cf = SV (LIST0 [ cf = class_str_item; ";" → cf ]) → cf ] ]
  ;
  class_self_patt:
    [ [ "("; p = patt; ")" → p
      | "("; p = patt; ":"; t = ctyp; ")" →
          Qast.Node "PaTyc" [Qast.Loc; p; t] ] ]
  ;
  class_str_item:
    [ [ "declare"; st = SV (LIST0 [ s = class_str_item; ";" → s ]); "end" →
          Qast.Node "CrDcl" [Qast.Loc; st]
      | "inherit"; ovf = SV (FLAG "!") "!"; ce = class_expr; pb = SV (OPT as_lident) ; attrs = item_attributes →
          Qast.Node "CrInh" [Qast.Loc; ovf ; ce; pb; attrs]
      | "value"; ovf = SV (FLAG "!") "!"; mf = SV (FLAG "mutable");
        lab = SV lident "lid" ""; e = cvalue_binding ; attrs = item_attributes →
          Qast.Node "CrVal" [Qast.Loc; ovf; mf; lab; e; attrs]
      | "value"; "virtual"; mf = SV (FLAG "mutable");
        lab = SV lident "lid" ""; ":"; t = ctyp ; attrs = item_attributes →
          Qast.Node "CrVav" [Qast.Loc; mf; lab; t; attrs]
      | "method"; "virtual"; pf = SV (FLAG "private"); l = SV lident "lid" "";
        ":"; t = ctyp ; attrs = item_attributes →
          Qast.Node "CrVir" [Qast.Loc; pf; l; t; attrs]
      | "method"; ovf = SV (FLAG "!") "!"; pf = SV (FLAG "private") "priv";
        l = SV lident "lid" ""; topt = SV (OPT polyt); e = fun_binding ; attrs = item_attributes →
          Qast.Node "CrMth" [Qast.Loc; ovf; pf; l; topt; e; attrs]
      | "type"; t1 = ctyp; "="; t2 = ctyp ; attrs = item_attributes →
          Qast.Node "CrCtr" [Qast.Loc; t1; t2; attrs]
      | "initializer"; se = expr ; attrs = item_attributes → Qast.Node "CrIni" [Qast.Loc; se; attrs]
      | attr = floating_attribute -> Qast.Node "CrFlAtt" [Qast.Loc; attr]
      | e = item_extension -> Qast.Node "CrExten" [Qast.Loc; e]
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
      | ":"; t = ctyp; "="; e = expr → Qast.Node "ExTyc" [Qast.Loc; e; t]
      | ":"; t = ctyp; ":>"; t2 = ctyp; "="; e = expr →
          Qast.Node "ExCoe" [Qast.Loc; e; Qast.Option (Some t); t2]
      | ":>"; t = ctyp; "="; e = expr →
          Qast.Node "ExCoe" [Qast.Loc; e; Qast.Option None; t] ] ]
  ;
  lident:
    [ [ i = LIDENT → mkident i ] ]
  ;
  class_type:
    [ "top" RIGHTA
      [ "["; t = ctyp; "]"; "->"; ct = SELF →
          Qast.Node "CtFun" [Qast.Loc; t; ct]
      | "let"; "open"; ovf = SV (FLAG "!") "!"; i = extended_longident; "in"; ce = SELF →
          Qast.Node "CtLop" [Qast.Loc; ovf; i; ce]
      ]
    | "alg_attribute" LEFTA
      [ t1 = SELF ; "[@" ; attr = SV attribute_body "attribute"; "]" ->
        Qast.Node "CtAtt" [Qast.Loc; t1; attr]
      ]

    | [ "object"; cst = SV (OPT class_self_type);
        csf = SV (LIST0 [ csf = class_sig_item; ";" → csf ]); "end" →
          Qast.Node "CtSig" [Qast.Loc; cst; csf]
      | ct = SELF; "["; tl = SV (LIST1 ctyp SEP ","); "]" →
          Qast.Node "CtCon" [Qast.Loc; ct; tl] ]
    | "simple"
      [ li = extended_longident; "."; i = SV LIDENT → Qast.Node "CtLongLid" [Qast.Loc; li; i]
      | i = SV LIDENT → Qast.Node "CtLid" [Qast.Loc; i]
      | "("; ct = SELF; ")" → ct
      | e = alg_extension -> Qast.Node "CtExten" [Qast.Loc; e]
      ] ]
  ;
  class_self_type:
    [ [ "("; t = ctyp; ")" → t ] ]
  ;
  class_sig_item:
    [ [ "declare"; st = SV (LIST0 [ s = class_sig_item; ";" → s ]); "end" →
          Qast.Node "CgDcl" [Qast.Loc; st]
      | "inherit"; cs = class_type ; attrs = item_attributes → Qast.Node "CgInh" [Qast.Loc; cs; attrs]
      | "value"; mf = SV (FLAG "mutable"); vf = SV (FLAG "virtual"); l = SV lident "lid" ""; ":";
        t = ctyp ; attrs = item_attributes →
          Qast.Node "CgVal" [Qast.Loc; mf; vf; l; t; attrs]
      | "method"; "virtual"; pf = SV (FLAG "private"); l = SV lident "lid" "";
        ":"; t = ctyp ; attrs = item_attributes →
          Qast.Node "CgVir" [Qast.Loc; pf; l; t; attrs]
      | "method"; pf = SV (FLAG "private"); l = SV lident "lid" ""; ":";
        t = ctyp ; attrs = item_attributes →
          Qast.Node "CgMth" [Qast.Loc; pf; l; t; attrs]
      | "type"; t1 = ctyp; "="; t2 = ctyp ; attrs = item_attributes →
          Qast.Node "CgCtr" [Qast.Loc; t1; t2; attrs]
      | attr = floating_attribute -> Qast.Node "CgFlAtt" [Qast.Loc; attr]
      | e = item_extension -> Qast.Node "CgExten" [Qast.Loc; e]
      ] ]
  ;
  class_description:
    [ [ vf = SV (FLAG "virtual"); n = SV LIDENT; ctp = class_type_parameters;
        ":"; ct = class_type ; attrs = item_attributes →
          Qast.Record
            [("ciLoc", Qast.Loc); ("ciVir", vf); ("ciPrm", ctp); ("ciNam", n);
             ("ciExp", ct); ("ciAttributes", attrs)] ] ]
  ;
  class_type_declaration:
    [ [ vf = SV (FLAG "virtual"); n = SV LIDENT; ctp = class_type_parameters;
        "="; cs = class_type ; attrs = item_attributes →
          Qast.Record
            [("ciLoc", Qast.Loc); ("ciVir", vf); ("ciPrm", ctp); ("ciNam", n);
             ("ciExp", cs); ("ciAttributes", attrs)] ] ]
  ;
  expr: LEVEL "apply"
    [ LEFTA
      [ "new"; cli = SV longident_lident "lilongid" → Qast.Node "ExNew" [Qast.Loc; cli]
      | "object"; cspo = SV (OPT class_self_patt); cf = class_structure;
        "end" →
          Qast.Node "ExObj" [Qast.Loc; cspo; cf] ] ]
  ;
  expr: LEVEL "."
    [ [ e = SELF; "#"; lab = SV lident "lid" "" →
          Qast.Node "ExSnd" [Qast.Loc; e; lab] ] ]
  ;
  expr: LEVEL "simple"
    [ [ "("; e = SELF; ":"; t = ctyp; ":>"; t2 = ctyp; ")" →
          Qast.Node "ExCoe" [Qast.Loc; e; Qast.Option (Some t); t2]
      | "("; e = SELF; ":>"; t = ctyp; ")" →
          Qast.Node "ExCoe" [Qast.Loc; e; Qast.Option None; t]
      | "{<"; fel = SV (LIST0 field_expr SEP ";"); ">}" →
          Qast.Node "ExOvr" [Qast.Loc; fel] ] ]
  ;
  field_expr:
    [ [ l = lident; "="; e = expr → Qast.Tuple [l; e] ] ]
  ;
  ctyp: LEVEL "simple"
    [ [ "#"; cli = SV extended_longident_lident "lilongid" → Qast.Node "TyCls" [Qast.Loc; cli]
      | "<"; ml = SV (LIST0 field SEP ";"); v = SV (FLAG ".."); ">" →
          Qast.Node "TyObj" [Qast.Loc; ml; v] ] ]
  ;
  field:
    [ [ lab = LIDENT; ":"; t = ctyp ; alg_attrs = alg_attributes → Qast.Tuple [mkident lab; t; alg_attrs] ] ]
  ;
  longident_lident:
    [ [ li = SV longident "longid"; "."; i = SV LIDENT → Qast.Tuple [Qast.Option (Some li); i]
      | i = SV LIDENT → Qast.Tuple [Qast.Option None; i]
      ] ]
  ;
  extended_longident_lident:
    [ [ li = SV extended_longident "longid"; "."; i = SV LIDENT → Qast.Tuple [Qast.Option (Some li); i]
      | i = SV LIDENT → Qast.Tuple [Qast.Option None; i]
      ] ]
  ;
  (* Labels *)
  ctyp: AFTER "arrow"
    [ NONA
      [ i = SV TILDEIDENTCOLON "~:" a_tic; t = SELF →
          Qast.Node "TyLab" [Qast.Loc; i; t]
      | i = SV QUESTIONIDENTCOLON "?:" a_qic; t = SELF →
          Qast.Node "TyOlb" [Qast.Loc; i; t] ] ]
  ;
  ctyp: LEVEL "simple"
    [ [ "["; "="; rfl = poly_variant_list; "]" →
          Qast.Node "TyVrn" [Qast.Loc; rfl; Qast.Option None]
      | "["; ">"; rfl = poly_variant_list; "]" →
          Qast.Node "TyVrn"
            [Qast.Loc; rfl; Qast.Option (Some (Qast.Option None))]
      | "["; "<"; rfl = poly_variant_list; "]" →
          Qast.Node "TyVrn"
            [Qast.Loc; rfl;
             Qast.Option
               (Some (Qast.Option (Some (Qast.VaVal (Qast.List [])))))]
      | "["; "<"; rfl = poly_variant_list; ">"; ntl = SV (LIST1 name_tag);
        "]" →
          Qast.Node "TyVrn"
            [Qast.Loc; rfl; Qast.Option (Some (Qast.Option (Some ntl)))] ] ]
  ;
  poly_variant_list:
    [ [ rfl = SV (LIST0 poly_variant SEP "|") → rfl ] ]
  ;
  poly_variant:
    [ [ "`"; i = SV ident "" ; alg_attrs = alg_attributes →
          Qast.Node "PvTag"
            [Qast.Loc; i; Qast.VaVal (Qast.Bool True);
             Qast.VaVal (Qast.List []); alg_attrs]
      | "`"; i = SV ident ""; "of"; ao = SV (FLAG "&");
        l = SV (LIST1 (ctyp LEVEL "below_alg_attribute") SEP "&") ; alg_attrs = alg_attributes →
          Qast.Node "PvTag" [Qast.Loc; i; ao; l; alg_attrs]
      | t = ctyp → Qast.Node "PvInh" [Qast.Loc; t] ] ]
  ;
  name_tag:
    [ [ "`"; i = ident → i ] ]
  ;
  patt: LEVEL "simple"
    [ [ "`"; s = SV ident "" → Qast.Node "PaVrn" [Qast.Loc; s]
      | "#"; lili = SV extended_longident_lident "lilongid" → Qast.Node "PaTyp" [Qast.Loc; lili]
      | "~"; "{"; lppo = SV (LIST1 patt_tcon_opt_eq_patt SEP ";"); "}" →
          Qast.Node "PaLab" [Qast.Loc; lppo]
      | "?"; "{"; p = patt_tcon; eo = SV (OPT [ "="; e = expr → e ]); "}" →
          Qast.Node "PaOlb" [Qast.Loc; p; eo]
      | i = SV TILDEIDENTCOLON "~:" a_tic; p = SELF →
          let _ = warning_deprecated_since_6_00 loc in
          Qast.Node "PaLab"
            [Qast.Loc;
             Qast.VaVal
               (Qast.List
                  [Qast.Tuple
                     [Qast.Node "PaLid" [Qast.Loc; i];
                      Qast.VaVal (Qast.Option (Some p))]])]
      | i = SV TILDEIDENT "~" a_ti →
          let _ = warning_deprecated_since_6_00 loc in
          Qast.Node "PaLab"
            [Qast.Loc;
             Qast.VaVal
               (Qast.List
                  [Qast.Tuple
                     [Qast.Node "PaLid" [Qast.Loc; i];
                      Qast.VaVal (Qast.Option None)]])]
      | p = patt_option_label →
          let _ = warning_deprecated_since_6_00 loc in
          p ] ]
  ;
  patt_tcon_opt_eq_patt:
    [ [ p = patt_tcon; po = SV (OPT [ "="; p = patt → p ]) →
          Qast.Tuple [p; po] ] ]
  ;
  patt_tcon:
    [ [ p = patt → p
      | p = patt; ":"; t = ctyp → Qast.Node "PaTyc" [Qast.Loc; p; t] ] ]
  ;
  ipatt:
    [ [ "~"; "{"; lppo = SV (LIST1 ipatt_tcon_opt_eq_patt SEP ";"); "}" →
          Qast.Node "PaLab" [Qast.Loc; lppo]
      | "?"; "{"; p = ipatt_tcon; eo = SV (OPT [ "="; e = expr → e ]); "}" →
          Qast.Node "PaOlb" [Qast.Loc; p; eo]
      | i = SV TILDEIDENTCOLON "~:" a_tic; p = SELF →
          let _ = warning_deprecated_since_6_00 loc in
          Qast.Node "PaLab"
            [Qast.Loc;
             Qast.VaVal
               (Qast.List
                  [Qast.Tuple
                     [Qast.Node "PaLid" [Qast.Loc; i];
                      Qast.VaVal (Qast.Option (Some p))]])]
      | i = SV TILDEIDENT "~" a_ti →
          let _ = warning_deprecated_since_6_00 loc in
          Qast.Node "PaLab"
            [Qast.Loc;
             Qast.VaVal
               (Qast.List
                  [Qast.Tuple
                     [Qast.Node "PaLid" [Qast.Loc; i];
                      Qast.VaVal (Qast.Option None)]])]
      | p = patt_option_label →
          let _ = warning_deprecated_since_6_00 loc in
          p ] ]
  ;
  ipatt_tcon_opt_eq_patt:
    [ [ p = ipatt_tcon; po = SV (OPT [ "="; p = patt → p ]) →
          Qast.Tuple [p; po] ] ]
  ;
  ipatt_tcon:
    [ [ p = ipatt → p
      | p = ipatt; ":"; t = ctyp → Qast.Node "PaTyc" [Qast.Loc; p; t] ] ]
  ;
  patt_option_label:
    [ [ i = SV QUESTIONIDENTCOLON "?:" a_qic; "("; j = SV LIDENT; ":";
        t = ctyp; "="; e = expr; ")" →
          Qast.Node "PaOlb"
            [Qast.Loc;
             Qast.Node "PaTyc" [Qast.Loc; Qast.Node "PaLid" [Qast.Loc; i]; t];
             Qast.VaVal
               (Qast.Option
                  (Some
                     (Qast.Node "ExOlb"
                        [Qast.Loc; Qast.Node "PaLid" [Qast.Loc; j];
                         Qast.VaVal (Qast.Option (Some e))])))]
      | i = SV QUESTIONIDENTCOLON "?:" a_qic; "("; j = SV LIDENT; ":";
        t = ctyp; ")" →
          Qast.Node "PaOlb"
            [Qast.Loc;
             Qast.Node "PaTyc" [Qast.Loc; Qast.Node "PaLid" [Qast.Loc; i]; t];
             Qast.VaVal
               (Qast.Option
                  (Some
                     (Qast.Node "ExOlb"
                        [Qast.Loc; Qast.Node "PaLid" [Qast.Loc; j];
                         Qast.VaVal (Qast.Option None)])))]
      | i = SV QUESTIONIDENTCOLON "?:" a_qic; "("; j = SV LIDENT; "=";
        e = expr; ")" →
          Qast.Node "PaOlb"
            [Qast.Loc; Qast.Node "PaLid" [Qast.Loc; i];
             Qast.VaVal
               (Qast.Option
                  (Some
                     (Qast.Node "ExOlb"
                        [Qast.Loc; Qast.Node "PaLid" [Qast.Loc; j];
                         Qast.VaVal (Qast.Option (Some e))])))]
      | i = SV QUESTIONIDENTCOLON "?:" a_qic; "("; j = SV LIDENT; ")" →
          Qast.Node "PaOlb"
            [Qast.Loc; Qast.Node "PaLid" [Qast.Loc; i];
             Qast.VaVal
               (Qast.Option (Some (Qast.Node "ExLid" [Qast.Loc; j])))]
      | i = SV QUESTIONIDENT "?" a_qi →
          Qast.Node "PaOlb"
            [Qast.Loc; Qast.Node "PaLid" [Qast.Loc; i];
             Qast.VaVal (Qast.Option None)]
      | "?"; "("; i = SV LIDENT; ":"; t = ctyp; "="; e = expr; ")" →
          Qast.Node "PaOlb"
            [Qast.Loc;
             Qast.Node "PaTyc" [Qast.Loc; Qast.Node "PaLid" [Qast.Loc; i]; t];
             Qast.VaVal (Qast.Option (Some e))]
      | "?"; "("; i = SV LIDENT; ":"; t = ctyp; ")" →
          Qast.Node "PaOlb"
            [Qast.Loc;
             Qast.Node "PaTyc" [Qast.Loc; Qast.Node "PaLid" [Qast.Loc; i]; t];
             Qast.VaVal (Qast.Option None)]
      | "?"; "("; i = SV LIDENT; "="; e = expr; ")" →
          Qast.Node "PaOlb"
            [Qast.Loc; Qast.Node "PaLid" [Qast.Loc; i];
             Qast.VaVal (Qast.Option (Some e))]
      | "?"; "("; i = SV LIDENT; ")" →
          Qast.Node "PaOlb"
            [Qast.Loc; Qast.Node "PaLid" [Qast.Loc; i];
             Qast.VaVal (Qast.Option None)] ] ]
  ;
  expr: AFTER "apply"
    [ "label" NONA
      [ "~"; "{"; lpeo = SV (LIST1 ipatt_tcon_fun_binding SEP ";"); "}" →
          Qast.Node "ExLab" [Qast.Loc; lpeo]
      | "?"; "{"; p = ipatt_tcon; eo = SV (OPT fun_binding); "}" →
          Qast.Node "ExOlb" [Qast.Loc; p; eo]
      | i = SV TILDEIDENTCOLON "~:" a_tic; e = SELF →
          let _ = warning_deprecated_since_6_00 loc in
          Qast.Node "ExLab"
            [Qast.Loc;
             Qast.VaVal
               (Qast.List
                  [Qast.Tuple
                     [Qast.Node "PaLid" [Qast.Loc; i];
                      Qast.VaVal (Qast.Option (Some e))]])]
      | i = SV TILDEIDENT "~" a_ti →
          let _ = warning_deprecated_since_6_00 loc in
          Qast.Node "ExLab"
            [Qast.Loc;
             Qast.VaVal
               (Qast.List
                  [Qast.Tuple
                     [Qast.Node "PaLid" [Qast.Loc; i];
                      Qast.VaVal (Qast.Option None)]])]
      | i = SV QUESTIONIDENTCOLON "?:" a_qic; e = SELF →
          let _ = warning_deprecated_since_6_00 loc in
          Qast.Node "ExOlb"
            [Qast.Loc; Qast.Node "PaLid" [Qast.Loc; i];
             Qast.VaVal (Qast.Option (Some e))]
      | i = SV QUESTIONIDENT "?" a_qi →
          let _ = warning_deprecated_since_6_00 loc in
          Qast.Node "ExOlb"
            [Qast.Loc; Qast.Node "PaLid" [Qast.Loc; i];
             Qast.VaVal (Qast.Option None)] ] ]
  ;
  ipatt_tcon_fun_binding:
    [ [ p = ipatt_tcon; eo = SV (OPT fun_binding) → Qast.Tuple [p; eo] ] ]
  ;
  expr: LEVEL "simple"
    [ [ "`"; s = SV ident "" → Qast.Node "ExVrn" [Qast.Loc; s] ] ]
  ;
  (* -- end copy from pa_r to q_MLast -- *)
  a_ti:
    [ [ "~"; a = ANTIQUOT -> Qast.VaAnt "~" loc a ] ]
  ;
  a_tic:
    [ [ "~"; a = ANTIQUOT; ":" -> Qast.VaAnt "~" loc a ] ]
  ;
  a_qi:
    [ [ "?"; a = ANTIQUOT -> Qast.VaAnt "?" loc a ] ]
  ;
  a_qic:
    [ [ "?"; a = ANTIQUOT; ":" -> Qast.VaAnt "?" loc a ] ]
  ;
END;

(* Antiquotations *)

value antiquot_xtr loc n a =
  if Pcaml.strict_mode.val then
    Qast.Node n [Qast.Loc; Qast.VaAnt "xtr" loc a; Qast.Option None]
  else
    Qast.Apply "failwith" [Qast.Str "antiquotation not authorized"]
;

EXTEND
  module_expr: LEVEL "simple"
    [ [ a = ANTIQUOT "mexp" -> Qast.VaAnt "mexp" loc a
      | a = ANTIQUOT "xtr" -> antiquot_xtr loc "MeXtr" a
      | a = ANTIQUOT -> Qast.VaAnt "" loc a ] ]
  ;
  longident: LEVEL "simple"
    [ [ a = ANTIQUOT "longid" -> Qast.VaAnt "longid" loc a ] ]
  ;
  extended_longident: LEVEL "simple"
    [ [ a = ANTIQUOT "longid" -> Qast.VaAnt "longid" loc a
      ] ]
  ;
  str_item: LEVEL "top"
    [ [ a = ANTIQUOT "stri" -> Qast.VaAnt "stri" loc a
      | a = ANTIQUOT "xtr" -> antiquot_xtr loc "StXtr" a
      | a = ANTIQUOT -> Qast.VaAnt "" loc a ] ]
  ;
  module_type: LEVEL "simple"
    [ [ a = ANTIQUOT "mtyp" -> Qast.VaAnt "mtyp" loc a
      | a = ANTIQUOT "xtr" -> antiquot_xtr loc "MtXtr" a
      | a = ANTIQUOT -> Qast.VaAnt "" loc a ] ]
  ;
  sig_item: LEVEL "top"
    [ [ a = ANTIQUOT "sigi" -> Qast.VaAnt "sigi" loc a
      | a = ANTIQUOT "xtr" -> antiquot_xtr loc "SgXtr" a
      | a = ANTIQUOT -> Qast.VaAnt "" loc a ] ]
  ;
  expr: LEVEL "simple"
    [ [ a = ANTIQUOT "exp" -> Qast.VaAnt "exp" loc a
      | a = ANTIQUOT "" -> Qast.VaAnt "" loc a
      | a = ANTIQUOT "xtr" -> antiquot_xtr loc "ExXtr" a
      | a = ANTIQUOT "anti" ->
          Qast.Node "ExAnt" [Qast.Loc; Qast.VaAnt "anti" loc a] ] ]
  ;
  patt: LEVEL "simple"
    [ [ a = ANTIQUOT "pat" -> Qast.VaAnt "pat" loc a
      | a = ANTIQUOT -> Qast.VaAnt "" loc a
      | a = ANTIQUOT "xtr" -> antiquot_xtr loc "PaXtr" a
      | a = ANTIQUOT "anti" ->
          Qast.Node "PaAnt" [Qast.Loc; Qast.VaAnt "anti" loc a] ] ]
  ;
  ipatt:
    [ [ a = ANTIQUOT "pat" -> Qast.VaAnt "pat" loc a
      | a = ANTIQUOT "xtr" -> antiquot_xtr loc "PaXtr" a
      | a = ANTIQUOT -> Qast.VaAnt "" loc a
      | a = ANTIQUOT "anti" ->
          Qast.Node "PaAnt" [Qast.Loc; Qast.VaAnt "anti" loc a] ] ]
  ;
  ctyp: LEVEL "simple"
    [ [ a = ANTIQUOT "typ" -> Qast.VaAnt "typ" loc a
      | a = ANTIQUOT "xtr" -> antiquot_xtr loc "TyXtr" a
      | a = ANTIQUOT -> Qast.VaAnt "" loc a
      ] ]
  ;
  class_expr: LEVEL "simple"
    [ [ a = ANTIQUOT "xtr" -> antiquot_xtr loc "CeXtr" a
      | a = ANTIQUOT -> Qast.VaAnt "" loc a ] ]
  ;
  class_str_item:
    [ [ a = ANTIQUOT -> Qast.VaAnt "" loc a ] ]
  ;
  class_sig_item:
    [ [ a = ANTIQUOT -> Qast.VaAnt "" loc a ] ]
  ;
  class_type: LEVEL "simple"
    [ [ a = ANTIQUOT "xtr" -> antiquot_xtr loc "CtXtr" a
      | a = ANTIQUOT -> Qast.VaAnt "" loc a ] ]
  ;
END;

value quot_mod = ref [];
value any_quot_mod = ref "MLast";

value set_qmod s = do {
  match try Some (String.index s ',') with [ Not_found -> None ] with
  [ Some i ->
      let q = String.sub s 0 i in
      let m = String.sub s (i + 1) (String.length s - i - 1) in
      quot_mod.val := [(q, m) :: quot_mod.val]
  | None ->
      any_quot_mod.val := s ]
};

Pcaml.add_directive "qmod"
  (fun
   [ Some <:expr< $str:s$ >> -> set_qmod s
   | Some _ | None -> failwith "bad directive 1" ])
;

value separate_locate s =
  let len = String.length s in
  if len > 0 && s.[0] = '@' then (String.sub s 1 (len - 1), True)
  else (s, False)
;

value apply_entry e q =
  let f s = Grammar.Entry.parse e (Stream.of_string s) in
  let m () =
    try List.assoc q quot_mod.val with
    [ Not_found -> any_quot_mod.val ]
  in
  let expr s =
    let (s, locate) = separate_locate s in
    Qast.to_expr (m ()) (f s)
  in
  let patt s =
    let (s, locate) = separate_locate s in
    let qast =
      let qast = f s in
      if locate then
        match qast with
        [ Qast.Node n [Qast.Loc :: nl] -> Qast.Node n [Qast.TrueLoc :: nl]
        | Qast.Tuple [Qast.Loc :: nl] -> Qast.Tuple [Qast.TrueLoc :: nl]
        | x -> x ]
      else qast
    in
    Qast.to_patt (m ()) qast
  in
  Quotation.ExAst (expr, patt)
;

let attribute_body_eoi = Grammar.Entry.create gram "attribute_body_eoi" in
let class_expr_eoi = Grammar.Entry.create gram "class_expr_eoi" in
let class_sig_item_eoi = Grammar.Entry.create gram "class_sig_item_eoi" in
let class_str_item_eoi = Grammar.Entry.create gram "class_str_item_eoi" in
let class_type_eoi = Grammar.Entry.create gram "class_type_eoi" in
let ctyp_eoi = Grammar.Entry.create gram "ctyp_eoi" in
let expr_eoi = Grammar.Entry.create gram "expr_eoi" in
let extended_longident_eoi = Grammar.Entry.create gram "extended_longident_eoi" in
let extension_constructor_eoi = Grammar.Entry.create gram "extension_constructor_eoi" in
let constructor_eoi = Grammar.Entry.create gram "constructor_eoi" in
let longident_eoi = Grammar.Entry.create gram "longident_eoi" in
let module_expr_eoi = Grammar.Entry.create gram "module_expr_eoi" in
let module_type_eoi = Grammar.Entry.create gram "module_type_eoi" in
let patt_eoi = Grammar.Entry.create gram "patt_eoi" in
let poly_variant_eoi = Grammar.Entry.create gram "poly_variant_eoi" in
let sig_item_eoi = Grammar.Entry.create gram "sig_item_eoi" in
let str_item_eoi = Grammar.Entry.create gram "str_item_eoi" in
let type_decl_eoi = Grammar.Entry.create gram "type_decl_eoi" in
let type_extension_eoi = Grammar.Entry.create gram "type_extension_eoi" in
let with_constr_eoi = Grammar.Entry.create gram "with_constr_eoi" in
do {
  EXTEND
    attribute_body_eoi: [ [ x = attribute_body; EOI -> x ] ];
    class_expr_eoi: [ [ x = class_expr; EOI -> x ] ];
    class_sig_item_eoi: [ [ x = class_sig_item; EOI -> x ] ];
    class_str_item_eoi: [ [ x = class_str_item; EOI -> x ] ];
    class_type_eoi: [ [ x = class_type; EOI -> x ] ];
    ctyp_eoi: [ [ x = ctyp; EOI -> x ] ];
    expr_eoi: [ [ x = expr; EOI -> x ] ];
    extended_longident_eoi: [ [ x = extended_longident; EOI -> x ] ];
    extension_constructor_eoi: [ [ x = extension_constructor; EOI -> x ] ];
    constructor_eoi: [ [ x = constructor_declaration; EOI -> x ] ];
    longident_eoi: [ [ x = longident; EOI -> x ] ];
    module_expr_eoi: [ [ x = module_expr; EOI -> x ] ];
    module_type_eoi: [ [ x = module_type; EOI -> x ] ];
    patt_eoi: [ [ x = patt; EOI -> x ] ];
    poly_variant_eoi: [ [ x = poly_variant; EOI -> x ] ];
    sig_item_eoi: [ [ x = sig_item; EOI -> x ] ];
    str_item_eoi: [ [ x = str_item; EOI -> x ] ];
    type_decl_eoi: [ [ x = type_decl; EOI -> x ] ];
    type_extension_eoi: [ [ x = type_extension; EOI -> x ] ];
    with_constr_eoi: [ [ x = with_constr; EOI -> x ] ];
  END;
  List.iter (fun (q, f) -> Quotation.add q (f q))
    [
      ("attribute_body", apply_entry attribute_body_eoi);
      ("class_expr", apply_entry class_expr_eoi);
      ("class_sig_item", apply_entry class_sig_item_eoi);
      ("class_str_item", apply_entry class_str_item_eoi);
      ("class_type", apply_entry class_type_eoi);
      ("ctyp", apply_entry ctyp_eoi);
      ("expr", apply_entry expr_eoi);
      ("extended_longident", apply_entry extended_longident_eoi);
      ("extension_constructor", apply_entry extension_constructor_eoi);
      ("constructor", apply_entry constructor_eoi);
      ("longident", apply_entry longident_eoi);
      ("module_expr", apply_entry module_expr_eoi);
      ("module_type", apply_entry module_type_eoi);
      ("patt", apply_entry patt_eoi);
      ("poly_variant", apply_entry poly_variant_eoi);
      ("sig_item", apply_entry sig_item_eoi);
      ("str_item", apply_entry str_item_eoi);
      ("type_decl", apply_entry type_decl_eoi);
      ("type_extension", apply_entry type_extension_eoi);
      ("with_constr", apply_entry with_constr_eoi)
    ];
};

do {
  let expr_eoi = Grammar.Entry.create Pcaml.gram "expr_eoi" in
  EXTEND
    expr_eoi:
      [ [ e = Pcaml.expr; EOI ->
            let loc = Ploc.make_unlined (0, 0) in
            if Pcaml.strict_mode.val then <:expr< Ploc.VaVal $anti:e$ >>
            else <:expr< $anti:e$ >>
        | a = ANTIQUOT_LOC; EOI ->
            let loc = Ploc.make_unlined (0, 0) in
            if Pcaml.strict_mode.val then
              let a =
                let i = String.index a ':' in
                let i = String.index_from a (i + 1) ':' in
                let a = String.sub a (i + 1) (String.length a - i - 1) in
                Grammar.Entry.parse Pcaml.expr_eoi (Stream.of_string a)
              in
              <:expr< Ploc.VaAnt $anti:a$ >>
            else <:expr< failwith "antiquot" >> ] ]
    ;
  END;
  let expr s =
    Ploc.call_with Plexer.force_antiquot_loc True
      (Grammar.Entry.parse expr_eoi) (Stream.of_string s)
  in
  let patt_eoi = Grammar.Entry.create Pcaml.gram "patt_eoi" in
  EXTEND
    patt_eoi:
      [ [ p = Pcaml.patt; EOI ->
            let loc = Ploc.make_unlined (0, 0) in
            if Pcaml.strict_mode.val then <:patt< Ploc.VaVal $anti:p$ >>
            else <:patt< $anti:p$ >>
        | a = ANTIQUOT_LOC; EOI ->
            let loc = Ploc.make_unlined (0, 0) in
            if Pcaml.strict_mode.val then
              let a =
                let i = String.index a ':' in
                let i = String.index_from a (i + 1) ':' in
                let a = String.sub a (i + 1) (String.length a - i - 1) in
                Grammar.Entry.parse Pcaml.patt_eoi (Stream.of_string a)
              in
              <:patt< Ploc.VaAnt $anti:a$ >>
            else <:patt< _ >> ] ]
    ;
  END;
  let patt s =
    Ploc.call_with Plexer.force_antiquot_loc True
      (Grammar.Entry.parse patt_eoi) (Stream.of_string s)
  in
  Quotation.add "vala" (Quotation.ExAst (expr, patt));
};
