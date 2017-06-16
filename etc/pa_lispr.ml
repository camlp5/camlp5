(* camlp5 pa_r.cmo pa_rp.cmo pa_extend.cmo q_MLast.cmo pr_dump.cmo *)
(* pa_lisp.ml,v *)
(* Copyright (c) INRIA 2007-2017 *)

open Pcaml;
open Versdep;

type choice α β =
  [ Left of α
  | Right of β ]
;

(* Buffer *)

module Buff =
  struct
    value buff = ref (string_create 80);
    value store len x = do {
      if len >= string_length buff.val then
        buff.val :=
          string_cat buff.val (string_create (string_length buff.val))
      else ();
      string_set buff.val len x;
      succ len
    };
    value get len = bytes_to_string (string_sub buff.val 0 len);
  end
;

(* Lexer *)

value rec skip_to_eol len =
  parser
  [ [: `('\n' | '\r' as c) :] -> Buff.store len c
  | [: `c :] ->
      let s = strm__ in
      skip_to_eol (Buff.store len c) s ]
;

value no_ident = ['('; ')'; ' '; '\t'; '\n'; '\r'; ';'];

value rec ident len =
  parser
    [: :] ->
      match Stream.peek strm__ with
      [ Some x when not (List.mem x no_ident) → do {
          Stream.junk strm__;
          let s = strm__ in
          ident (Buff.store len x) s
        }
      | _ → Buff.get len ]
;

value rec string len =
  parser
  [ [: `'"' :] -> Buff.get len
  | [: `'\\'; `c :] ->
      let s = strm__ in
      string (Buff.store (Buff.store len '\\') c) s
  | [: `x :] ->
      let s = strm__ in
      string (Buff.store len x) s ]
;

value rec number len =
  parser
  [ [: `('0'..'9' as c) :] ->
      let s = strm__ in
      number (Buff.store len c) s
  | [: :] -> ("INT", Buff.get len) ]
;

value char_or_quote_id x =
  parser
  [ [: `''' :] -> ("CHAR", String.make 1 x)
  | [: :] ->
      let s = strm__ in
      let len = Buff.store (Buff.store 0 ''') x in
      ("LIDENT", ident len s) ]
;

value rec char len =
  parser
  [ [: `''' :] -> len
  | [: `x :] ->
      let s = strm__ in
      char (Buff.store len x) s ]
;

value quote =
  parser
  [ [: `'\\'; len = char (Buff.store 0 '\\') :] -> ("CHAR", Buff.get len)
  | [: `x :] ->
      let s = strm__ in
      char_or_quote_id x s ]
;

value rec next_token_after_spaces kwt =
  parser bp
  [ [: `'(' :] -> (("", "("), (bp, bp + 1))
  | [: `')' :] -> (("", ")"), (bp, bp + 1))
  | [: `'"'; s = string 0 :] ->
      let ep = Stream.count strm__ in
      (("STRING", s), (bp, ep))
  | [: `'''; tok = quote :] ->
      let ep = Stream.count strm__ in
      (tok, (bp, ep))
  | [: `'<'; tok = less :] ->
      let ep = Stream.count strm__ in
      (tok, (bp, ep))
  | [: `('0'..'9' as c); n = number (Buff.store 0 c) :] ->
      let ep = Stream.count strm__ in
      (n, (bp, ep))
  | [: `x; s = ident (Buff.store 0 x) :] ->
      let ep = Stream.count strm__ in
      let con =
        try do {
          (Hashtbl.find kwt s : unit);
          ""
        }
        with
        [ Not_found →
            match x with
            [ 'A'..'Z' → "UIDENT"
            | _ → "LIDENT" ] ]
      in
      ((con, s), (bp, ep))
  | [: :] -> (("EOI", ""), (bp, bp + 1)) ]
and less =
  parser
  [ [: `':'; lab = label 0; `'<' ? "'<' expected"; q = quotation 0 :] ->
      ("QUOT", lab ^ ":" ^ q)
  | [: :] -> ("LIDENT", "<") ]
and label len =
  parser
  [ [: `('a'..'z' | 'A'..'Z' | '_' as c) :] ->
      let s = strm__ in
      label (Buff.store len c) s
  | [: :] -> Buff.get len ]
and quotation len =
  parser
  [ [: `'>' :] ->
      let s = strm__ in
      quotation_greater len s
  | [: `x :] ->
      let s = strm__ in
      quotation (Buff.store len x) s
  | [: :] -> failwith "quotation not terminated" ]
and quotation_greater len =
  parser
  [ [: `'>' :] -> Buff.get len
  | [: a = quotation (Buff.store len '>') :] -> a ]
;

value get_buff len _ = Buff.get len;

value rec lexer len kwt =
  parser bp
  [ [: `(' ' | '\t' | '\n' | '\r' as c) :] ->
      let s = strm__ in
      lexer (Buff.store len c) kwt s
  | [: `';'; a = semi (Buff.store len ';') kwt bp :] -> a
  | [: comm = get_buff len; a = next_token_after_spaces kwt :] -> (comm, a) ]
and semi len kwt bp =
  parser
  [ [: `';'; len = skip_to_eol (Buff.store len ';') :] ->
      let s = strm__ in
      lexer len kwt s
  | [: :] ->
      let ep = Stream.count strm__ in
      (Buff.get len, (("", ";"), (bp, ep))) ]
;

value lexer_using kwt (con, prm) =
  match con with
  [ "CHAR" | "EOI" | "INT" | "LIDENT" | "QUOT" | "STRING" | "UIDENT" → ()
  | "ANTIQUOT" | "ANTIQUOT_LOC" → ()
  | "" → try Hashtbl.find kwt prm with [ Not_found → Hashtbl.add kwt prm () ]
  | _ →
      raise
        (Plexing.Error
           ("the constructor \"" ^ con ^ "\" is not recognized by Plexer")) ]
;

value lexer_text (con, prm) =
  if con = "" then "'" ^ prm ^ "'"
  else if prm = "" then con
  else con ^ " \"" ^ prm ^ "\""
;

value lexer_gmake () =
  let kwt = Hashtbl.create 89
  and lexer2 kwt (s, _, _) =
    let (comm, (t, loc)) = lexer 0 kwt s in
    (t, Ploc.make_loc Plexing.input_file.val 0 0 loc comm)
  in
  {Plexing.tok_func = Plexing.lexer_func_of_parser (lexer2 kwt);
   Plexing.tok_using = lexer_using kwt; Plexing.tok_removing = fun [];
   Plexing.tok_match = Plexing.default_match; Plexing.tok_text = lexer_text;
   Plexing.tok_comm = None}
;

(* Building AST *)

type sexpr =
  [ Sexpr of MLast.loc and list sexpr
  | Satom of MLast.loc and atom and string
  | Squot of MLast.loc and string and string ]
and atom = [ Alid | Auid | Aint | Achar | Astring ];

value error_loc loc err = Ploc.raise loc (Stream.Error (err ^ " expected"));
value error se err =
  let loc =
    match se with [ Satom loc _ _ | Sexpr loc _ | Squot loc _ _ → loc ]
  in
  error_loc loc err
;

value expr_id loc s =
  match s.[0] with
  [ 'A'..'Z' → <:expr< $uid:s$ >>
  | _ → <:expr< $lid:s$ >> ]
;

value patt_id loc s =
  match s.[0] with
  [ 'A'..'Z' → <:patt< $uid:s$ >>
  | _ → <:patt< $lid:s$ >> ]
;

value ctyp_id loc s =
  match s.[0] with
  [ ''' →
      let s = String.sub s 1 (String.length s - 1) in
      <:ctyp< '$s$ >>
  | 'A'..'Z' → <:ctyp< $uid:s$ >>
  | _ → <:ctyp< $lid:s$ >> ]
;

value strm_n = "strm__";
value peek_fun loc = <:expr< Stream.peek >>;
value junk_fun loc = <:expr< Stream.junk >>;

value rec module_expr_se =
  fun
  [ Sexpr loc [Satom _ Alid "struct" :: sl] →
      let mel = List.map str_item_se sl in
      <:module_expr< struct $list:mel$ end >>
  | Satom loc Auid s → <:module_expr< $uid:s$ >>
  | se → error se "module expr" ]
and str_item_se se =
  match se with
  [ Satom loc _ _ | Squot loc _ _ →
      let e = expr_se se in
      <:str_item< $exp:e$ >>
  | Sexpr loc [Satom _ Alid "module"; Satom _ Auid i; se] →
      let mb = module_binding_se se in
      <:str_item< module $uid:i$ = $mb$ >>
  | Sexpr loc [Satom _ Alid "open"; Satom _ Auid s] →
      let s = [s] in
      <:str_item< open $s$ >>
  | Sexpr loc [Satom _ Alid "type" :: sel] →
      let tdl = type_declaration_list_se sel in
      <:str_item< type $list:tdl$ >>
  | Sexpr loc [Satom _ Alid "value" :: sel] →
      let (r, sel) =
        match sel with
        [ [Satom _ Alid "rec" :: sel] → (True, sel)
        | _ → (False, sel) ]
      in
      let lbs = value_binding_se sel in
      <:str_item< value $flag:r$ $list:lbs$ >>
  | Sexpr loc _ →
      let e = expr_se se in
      <:str_item< $exp:e$ >> ]
and value_binding_se =
  fun
  [ [se1; se2 :: sel] → [(ipatt_se se1, expr_se se2) :: value_binding_se sel]
  | [] → []
  | [se :: _] → error se "value_binding" ]
and module_binding_se se = module_expr_se se
and expr_se =
  fun
  [ Satom loc (Alid | Auid) s → expr_ident_se loc s
  | Satom loc Aint s → <:expr< $int:s$ >>
  | Satom loc Achar s → <:expr< $chr:s$ >>
  | Satom loc Astring s → <:expr< $str:s$ >>
  | Sexpr loc [] → <:expr< () >>
  | Sexpr loc [Satom _ Alid "if"; se; se1] →
      let e = expr_se se in
      let e1 = expr_se se1 in
      <:expr< if $e$ then $e1$ else () >>
  | Sexpr loc [Satom _ Alid "if"; se; se1; se2] →
      let e = expr_se se in
      let e1 = expr_se se1 in
      let e2 = expr_se se2 in
      <:expr< if $e$ then $e1$ else $e2$ >>
  | Sexpr loc [Satom loc1 Alid "lambda"] → <:expr< fun [] >>
  | Sexpr loc [Satom loc1 Alid "lambda"; sep :: sel] →
      let e = progn_se loc1 sel in
      match ipatt_opt_se sep with
      [ Left p → <:expr< fun $p$ -> $e$ >>
      | Right (se, sel) →
          List.fold_right
            (fun se e →
               let p = ipatt_se se in
               <:expr< fun $p$ -> $e$ >>)
            [se :: sel] e ]
  | Sexpr loc [Satom _ Alid "lambda_match" :: sel] →
      let pel = List.map (match_case loc) sel in
      <:expr< fun [ $list:pel$ ] >>
  | Sexpr loc [Satom _ Alid "let" :: sel] →
      let (r, sel) =
        match sel with
        [ [Satom _ Alid "rec" :: sel] → (True, sel)
        | _ → (False, sel) ]
      in
      match sel with
      [ [Sexpr _ sel1 :: sel2] →
          let lbs = List.map let_binding_se sel1 in
          let e = progn_se loc sel2 in
          <:expr< let $flag:r$ $list:lbs$ in $e$ >>
      | [se :: _] → error se "let_binding"
      | _ → error_loc loc "let_binding" ]
  | Sexpr loc [Satom _ Alid "let*" :: sel] →
      match sel with
      [ [Sexpr _ sel1 :: sel2] →
          List.fold_right
            (fun se ek →
               let (p, e) = let_binding_se se in
               <:expr< let $p$ = $e$ in $ek$ >>)
            sel1 (progn_se loc sel2)
      | [se :: _] → error se "let_binding"
      | _ → error_loc loc "let_binding" ]
  | Sexpr loc [Satom _ Alid "match"; se :: sel] →
      let e = expr_se se in
      let pel = List.map (match_case loc) sel in
      <:expr< match $e$ with [ $list:pel$ ] >>
  | Sexpr loc [Satom _ Alid "parser" :: sel] →
      let e =
        match sel with
        [ [(Satom _ _ _ as se) :: sel] →
            let p = patt_se se in
            let pc = parser_cases_se loc sel in
            <:expr< let $p$ = Stream.count $lid:strm_n$ in $pc$ >>
        | _ → parser_cases_se loc sel ]
      in
      <:expr< fun ($lid:strm_n$ : Stream.t _) -> $e$ >>
  | Sexpr loc [Satom _ Alid "try"; se :: sel] →
      let e = expr_se se in
      let pel = List.map (match_case loc) sel in
      <:expr< try $e$ with [ $list:pel$ ] >>
  | Sexpr loc [Satom _ Alid "progn" :: sel] →
      let el = List.map expr_se sel in
      <:expr< do { $list:el$ } >>
  | Sexpr loc [Satom _ Alid "while"; se :: sel] →
      let e = expr_se se in
      let el = List.map expr_se sel in
      <:expr< while $e$ do { $list:el$ } >>
  | Sexpr loc [Satom _ Alid ":="; se1; se2] →
      let e2 = expr_se se2 in
      match expr_se se1 with
      [ <:expr< $uid:"()"$ $e1$ $i$ >> → <:expr< $e1$.($i$) := $e2$ >>
      | e1 → <:expr< $e1$ := $e2$ >> ]
  | Sexpr loc [Satom _ Alid "[]"; se1; se2] →
      let e1 = expr_se se1 in
      let e2 = expr_se se2 in
      <:expr< $e1$.[$e2$] >>
  | Sexpr loc [Satom _ Alid "," :: sel] →
      let el = List.map expr_se sel in
      <:expr< ( $list:el$ ) >>
  | Sexpr loc [Satom _ Alid "{}" :: sel] →
      let lel = List.map (label_expr_se loc) sel in
      <:expr< { $list:lel$ } >>
  | Sexpr loc [Satom _ Alid ":"; se1; se2] →
      let e = expr_se se1 in
      let t = ctyp_se se2 in
      <:expr< ( $e$ : $t$ ) >>
  | Sexpr loc [Satom _ Alid "list" :: sel] →
      loop sel where rec loop =
        fun
        [ [] → <:expr< [] >>
        | [se1; Satom _ Alid "::"; se2] →
            let e = expr_se se1 in
            let el = expr_se se2 in
            <:expr< [$e$ :: $el$] >>
        | [se :: sel] →
            let e = expr_se se in
            let el = loop sel in
            <:expr< [$e$ :: $el$] >> ]
  | Sexpr loc [se :: sel] →
      List.fold_left
        (fun e se →
           let e1 = expr_se se in
           <:expr< $e$ $e1$ >>)
        (expr_se se) sel
  | Squot loc typ txt → Pcaml.handle_expr_quotation loc (typ, txt) ]
and progn_se loc =
  fun
  [ [] → <:expr< () >>
  | [se] → expr_se se
  | sel →
      let el = List.map expr_se sel in
      <:expr< do { $list:el$ } >> ]
and let_binding_se =
  fun
  [ Sexpr loc [se1; se2] → (ipatt_se se1, expr_se se2)
  | se → error se "let_binding" ]
and match_case loc =
  fun
  [ Sexpr _ [se1; se2] → (patt_se se1, <:vala< None >>, expr_se se2)
  | Sexpr _ [se1; sew; se2] →
      (patt_se se1, <:vala< (Some (expr_se sew)) >>, expr_se se2)
  | se → error se "match_case" ]
and label_expr_se loc =
  fun
  [ Sexpr _ [se1; se2] → (patt_se se1, expr_se se2)
  | se → error se "label_expr" ]
and expr_ident_se loc s =
  if s.[0] = '<' then <:expr< $lid:s$ >>
  else
    loop 0 0 where rec loop ibeg i =
      if i = String.length s then
        if i > ibeg then expr_id loc (String.sub s ibeg (i - ibeg))
        else
          Ploc.raise (Ploc.sub loc (i - 1) 1) (Stream.Error "expr expected")
      else if s.[i] = '.' then
        if i > ibeg then
          let e1 = expr_id loc (String.sub s ibeg (i - ibeg)) in
          let e2 = loop (i + 1) (i + 1) in
          <:expr< $e1$ . $e2$ >>
        else
          Ploc.raise (Ploc.sub loc (i - 1) 1) (Stream.Error "expr expected")
      else loop ibeg (i + 1)
and parser_cases_se loc =
  fun
  [ [] → <:expr< raise Stream.Failure >>
  | [Sexpr loc [Sexpr _ spsel :: act] :: sel] →
      let ekont _ = parser_cases_se loc sel in
      let act =
        match act with
        [ [se] → expr_se se
        | [sep; se] →
            let p = patt_se sep in
            let e = expr_se se in
            <:expr< let $p$ = Stream.count $lid:strm_n$ in $e$ >>
        | _ → error_loc loc "parser_case" ]
      in
      stream_pattern_se loc act ekont spsel
  | [se :: _] → error se "parser_case" ]
and stream_pattern_se loc act ekont =
  fun
  [ [] → act
  | [se :: sel] →
      let ckont err = <:expr< raise (Stream.Error $err$) >> in
      let skont = stream_pattern_se loc act ckont sel in
      stream_pattern_component skont ekont <:expr< "" >> se ]
and stream_pattern_component skont ekont err =
  fun
  [ Sexpr loc [Satom _ Alid "`"; se :: wol] →
      let wo =
        match wol with
        [ [se] → Some (expr_se se)
        | [] → None
        | _ → error_loc loc "stream_pattern_component" ]
      in
      let e = peek_fun loc in
      let p = patt_se se in
      let j = junk_fun loc in
      let k = ekont err in
      <:expr< match $e$ $lid:strm_n$ with
       [ Some $p$ $opt:wo$ -> do { $j$ $lid:strm_n$ ; $skont$ }
       | _ -> $k$ ] >>
  | Sexpr loc [se1; se2] →
      let p = patt_se se1 in
      let e =
        let e = expr_se se2 in
        <:expr< try Some ($e$ $lid:strm_n$) with [ Stream.Failure -> None ] >>
      in
      let k = ekont err in
      <:expr< match $e$ with [ Some $p$ -> $skont$ | _ -> $k$ ] >>
  | Sexpr loc [Satom _ Alid "?"; se1; se2] →
      stream_pattern_component skont ekont (expr_se se2) se1
  | Satom loc Alid s → <:expr< let $lid:s$ = $lid:strm_n$ in $skont$ >>
  | se → error se "stream_pattern_component" ]
and patt_se =
  fun
  [ Satom loc Alid "_" → <:patt< _ >>
  | Satom loc (Alid | Auid) s → patt_ident_se loc s
  | Satom loc Aint s → <:patt< $int:s$ >>
  | Satom loc Achar s → <:patt< $chr:s$ >>
  | Satom loc Astring s → <:patt< $str:s$ >>
  | Sexpr loc [Satom _ Alid "or"; se :: sel] →
      List.fold_left
        (fun p se →
           let p1 = patt_se se in
           <:patt< $p$ | $p1$ >>)
        (patt_se se) sel
  | Sexpr loc [Satom _ Alid "range"; se1; se2] →
      let p1 = patt_se se1 in
      let p2 = patt_se se2 in
      <:patt< $p1$ .. $p2$ >>
  | Sexpr loc [Satom _ Alid "," :: sel] →
      let pl = List.map patt_se sel in
      <:patt< ( $list:pl$ ) >>
  | Sexpr loc [Satom _ Alid "as"; se1; se2] →
      let p1 = patt_se se1 in
      let p2 = patt_se se2 in
      <:patt< ($p1$ as $p2$) >>
  | Sexpr loc [Satom _ Alid "list" :: sel] →
      loop sel where rec loop =
        fun
        [ [] → <:patt< [] >>
        | [se1; Satom _ Alid "::"; se2] →
            let p = patt_se se1 in
            let pl = patt_se se2 in
            <:patt< [$p$ :: $pl$] >>
        | [se :: sel] →
            let p = patt_se se in
            let pl = loop sel in
            <:patt< [$p$ :: $pl$] >> ]
  | Sexpr loc [se :: sel] →
      List.fold_left
        (fun p se →
           let p1 = patt_se se in
           <:patt< $p$ $p1$ >>)
        (patt_se se) sel
  | Sexpr loc [] → <:patt< () >>
  | Squot loc typ txt → Pcaml.handle_patt_quotation loc (typ, txt) ]
and patt_ident_se loc s =
  loop 0 0 where rec loop ibeg i =
    if i = String.length s then
      if i > ibeg then patt_id loc (String.sub s ibeg (i - ibeg))
      else Ploc.raise (Ploc.sub loc (i - 1) 1) (Stream.Error "patt expected")
    else if s.[i] = '.' then
      if i > ibeg then
        let p1 = patt_id loc (String.sub s ibeg (i - ibeg)) in
        let p2 = loop (i + 1) (i + 1) in
        <:patt< $p1$ . $p2$ >>
      else Ploc.raise (Ploc.sub loc (i - 1) 1) (Stream.Error "patt expected")
    else loop ibeg (i + 1)
and ipatt_se se =
  match ipatt_opt_se se with
  [ Left p → p
  | Right (se, _) → error se "ipatt" ]
and ipatt_opt_se =
  fun
  [ Satom loc Alid "_" → Left <:patt< _ >>
  | Satom loc Alid s → Left <:patt< $lid:s$ >>
  | Sexpr loc [Satom _ Alid "," :: sel] →
      let pl = List.map ipatt_se sel in
      Left <:patt< ( $list:pl$ ) >>
  | Sexpr loc [] → Left <:patt< () >>
  | Sexpr loc [se :: sel] → Right (se, sel)
  | se → error se "ipatt" ]
and type_declaration_list_se =
  fun
  [ [se1; se2 :: sel] →
      let (n1, loc1, tpl) =
        match se1 with
        [ Sexpr _ [Satom loc Alid n :: sel] →
            (n, loc, List.map type_parameter_se sel)
        | Satom loc Alid n → (n, loc, [])
        | se → error se "type declaration" ]
      in
      let empty = [] in
      let n = (loc1, <:vala< n1 >>) in
      let td =
        {MLast.tdNam = <:vala< n >>; MLast.tdPrm = <:vala< tpl >>;
         MLast.tdPrv = <:vala< False >>; MLast.tdDef = ctyp_se se2;
         MLast.tdCon = <:vala< empty >>}
      in
      [td :: type_declaration_list_se sel]
  | [] → []
  | [se :: _] → error se "type_decl" ]
and type_parameter_se =
  fun
  [ Satom _ Alid s when String.length s >= 2 && s.[0] = ''' →
      let s = String.sub s 1 (String.length s - 1) in
      (<:vala< (Some s) >>, None)
  | se → error se "type_parameter" ]
and ctyp_se =
  fun
  [ Sexpr loc [Satom _ Alid "sum" :: sel] →
      let cdl = List.map constructor_declaration_se sel in
      <:ctyp< [ $list:cdl$ ] >>
  | Sexpr loc [se :: sel] →
      List.fold_left
        (fun t se →
           let t2 = ctyp_se se in
           <:ctyp< $t$ $t2$ >>)
        (ctyp_se se) sel
  | Satom loc (Alid | Auid) s → ctyp_ident_se loc s
  | se → error se "ctyp" ]
and ctyp_ident_se loc s =
  loop 0 0 where rec loop ibeg i =
    if i = String.length s then
      if i > ibeg then ctyp_id loc (String.sub s ibeg (i - ibeg))
      else Ploc.raise (Ploc.sub loc (i - 1) 1) (Stream.Error "ctyp expected")
    else if s.[i] = '.' then
      if i > ibeg then
        let t1 = ctyp_id loc (String.sub s ibeg (i - ibeg)) in
        let t2 = loop (i + 1) (i + 1) in
        <:ctyp< $t1$ . $t2$ >>
      else Ploc.raise (Ploc.sub loc (i - 1) 1) (Stream.Error "ctyp expected")
    else loop ibeg (i + 1)
and constructor_declaration_se =
  fun
  [ Sexpr loc [Satom _ Auid ci :: sel] →
      (loc, <:vala< ci >>, <:vala< (List.map ctyp_se sel) >>, None)
  | se → error se "constructor_declaration" ]
;

value top_phrase_se se =
  match se with
  [ Satom loc _ _ | Squot loc _ _ → str_item_se se
  | Sexpr loc [Satom _ Alid s :: sl] →
      if s.[0] = '#' then
        let n = String.sub s 1 (String.length s - 1) in
        match sl with
        [ [Satom _ Astring s] → <:str_item< # $lid:n$ $str:s$ >>
        | _ → match () with [] ]
      else str_item_se se
  | Sexpr loc _ → str_item_se se ]
;

(* Parser *)

value phony_quot = ref False;
Pcaml.add_option "-phony_quot" (Arg.Set phony_quot) "phony quotations";

Pcaml.no_constructors_arity.val := False;

do {
  Grammar.Unsafe.gram_reinit gram (lexer_gmake ());
  Grammar.Unsafe.clear_entry interf;
  Grammar.Unsafe.clear_entry implem;
  Grammar.Unsafe.clear_entry top_phrase;
  Grammar.Unsafe.clear_entry use_file;
  Grammar.Unsafe.clear_entry module_type;
  Grammar.Unsafe.clear_entry module_expr;
  Grammar.Unsafe.clear_entry sig_item;
  Grammar.Unsafe.clear_entry str_item;
  Grammar.Unsafe.clear_entry expr;
  Grammar.Unsafe.clear_entry patt;
  Grammar.Unsafe.clear_entry ctyp;
  Grammar.Unsafe.clear_entry let_binding;
  Grammar.Unsafe.clear_entry class_type;
  Grammar.Unsafe.clear_entry class_expr;
  Grammar.Unsafe.clear_entry class_sig_item;
  Grammar.Unsafe.clear_entry class_str_item
};

Pcaml.parse_interf.val := Grammar.Entry.parse interf;
Pcaml.parse_implem.val := Grammar.Entry.parse implem;

value sexpr = Grammar.Entry.create gram "sexpr";
value atom = Grammar.Entry.create gram "atom";

EXTEND
  implem:
    [ [ st = LIST0 [ s = str_item -> (s, loc) ]; eoi_loc = [ EOI -> loc ] ->
          (st, Some eoi_loc) ] ]
  ;
  top_phrase:
    [ [ se = sexpr -> Some (top_phrase_se se)
      | EOI -> None ] ]
  ;
  use_file:
    [ [ l = LIST0 sexpr; EOI -> (List.map top_phrase_se l, False) ] ]
  ;
  str_item:
    [ [ se = sexpr -> str_item_se se
      | e = expr -> <:str_item< $exp:e$ >> ] ]
  ;
  expr:
    [ "top"
      [ se = sexpr -> expr_se se ] ]
  ;
  patt:
    [ [ se = sexpr -> patt_se se ] ]
  ;
  sexpr:
    [ [ "("; sl = LIST0 sexpr; ")" -> Sexpr loc sl
      | a = atom -> Satom loc Alid a
      | s = LIDENT -> Satom loc Alid s
      | s = UIDENT -> Satom loc Auid s
      | s = INT -> Satom loc Aint s
      | s = CHAR -> Satom loc Achar s
      | s = STRING -> Satom loc Astring s
      | s = QUOT ->
          let i = String.index s ':' in
          let typ = String.sub s 0 i in
          let txt = String.sub s (i + 1) (String.length s - i - 1) in
          if phony_quot.val then
            Satom loc Alid ("<:" ^ typ ^ "<" ^ txt ^ ">>")
          else Squot loc typ txt ] ]
  ;
  atom:
    [ [ "_" -> "_"
      | "," -> ","
      | "=" -> "="
      | ":" -> ":"
      | "." -> "." ] ]
  ;
END;
