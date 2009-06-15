(* camlp5r pa_extend.cmo q_MLast.cmo *)
(* $Id: pa_r.ml,v 1.87 2007/09/15 05:34:12 deraugla Exp $ *)
(* Copyright (c) INRIA 2007 *)

open Pcaml;

Pcaml.syntax_name.val := "Revised";
Pcaml.no_constructors_arity.val := False;

do {
  let odfa = Plexer.dollar_for_antiquotation.val in
  Plexer.dollar_for_antiquotation.val := False;
  Grammar.Unsafe.gram_reinit gram (Plexer.gmake ());
  Plexer.dollar_for_antiquotation.val := odfa;
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
  Grammar.Unsafe.clear_entry type_declaration;
  Grammar.Unsafe.clear_entry constructor_declaration;
  Grammar.Unsafe.clear_entry match_case;
  Grammar.Unsafe.clear_entry with_constr;
  Grammar.Unsafe.clear_entry poly_variant;
  Grammar.Unsafe.clear_entry class_type;
  Grammar.Unsafe.clear_entry class_expr;
  Grammar.Unsafe.clear_entry class_sig_item;
  Grammar.Unsafe.clear_entry class_str_item
};

Pcaml.parse_interf.val := Grammar.Entry.parse interf;
Pcaml.parse_implem.val := Grammar.Entry.parse implem;

value mksequence2 loc =
  fun
  [ <:vala< [e] >> -> e
  | seq -> <:expr< do { $alist:seq$ } >> ]
;

value mksequence loc =
  fun
  [ [e] -> e
  | el -> <:expr< do { $list:el$ } >> ]
;

value mkmatchcase loc p aso w e =
  let p =
    match aso with
    [ Some p2 -> <:patt< ($p$ as $p2$) >>
    | _ -> p ]
  in
  (p, w, e)
;
      
value neg_string n =
  let len = String.length n in
  if len > 0 && n.[0] = '-' then String.sub n 1 (len - 1)
  else "-" ^ n
;

value mkumin loc f arg =
  match arg with
  [ <:expr< $int:n$ >> -> <:expr< $int:neg_string n$ >>
  | <:expr< $flo:n$ >> -> <:expr< $flo:neg_string n$ >>
  | _ ->
      let f = "~" ^ f in
      <:expr< $lid:f$ $arg$ >> ]
;

value mkuminpat loc f is_int n =
  if is_int then <:patt< $int:neg_string n$ >>
  else <:patt< $flo:neg_string n$ >>
;

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

value append_elem el e = el @ [e];

value ipatt = Grammar.Entry.create gram "ipatt";

EXTEND
  GLOBAL: sig_item str_item ctyp patt expr module_type module_expr class_type
    class_expr class_sig_item class_str_item let_binding type_declaration
    constructor_declaration match_case ipatt with_constr poly_variant;
  module_expr:
    [ [ "functor"; "("; i = V UIDENT; ":"; t = module_type; ")"; "->";
        me = SELF ->
          <:module_expr< functor ( $auid:i$ : $t$ ) -> $me$ >>
      | "struct"; st = V LIST0 [ s = str_item; ";" -> s ]; "end" ->
          <:module_expr< struct $alist:st$ end >> ]
    | [ me1 = SELF; me2 = SELF -> <:module_expr< $me1$ $me2$ >> ]
    | [ me1 = SELF; "."; me2 = SELF -> <:module_expr< $me1$ . $me2$ >> ]
    | "simple"
      [ i = V UIDENT -> <:module_expr< $auid:i$ >>
      | "("; me = SELF; ":"; mt = module_type; ")" ->
          <:module_expr< ( $me$ : $mt$ ) >>
      | "("; me = SELF; ")" -> <:module_expr< $me$ >> ] ]
  ;
  str_item:
    [ "top"
      [ "declare"; st = V LIST0 [ s = str_item; ";" -> s ]; "end" ->
          <:str_item< declare $alist:st$ end >>
      | "exception"; (_, c, tl) = constructor_declaration; b = rebind_exn ->
          <:str_item< exception $auid:c$ of $alist:tl$ = $a:b$ >>
      | "external"; i = V LIDENT; ":"; t = ctyp; "="; pd = V LIST1 STRING ->
          <:str_item< external $alid:i$ : $t$ = $alist:pd$ >>
      | "include"; me = module_expr -> <:str_item< include $me$ >>
      | "module"; r = V FLAG "rec"; l = V LIST1 mod_binding SEP "and" ->
          <:str_item< module $aflag:r$ $alist:l$ >>
      | "module"; "type"; i = V UIDENT; "="; mt = module_type ->
          <:str_item< module type $auid:i$ = $mt$ >>
      | "open"; i = mod_ident2 -> <:str_item< open $a:i$ >>
      | "type"; tdl = V LIST1 type_declaration SEP "and" ->
          <:str_item< type $alist:tdl$ >>
      | "value"; r = V FLAG "rec"; l = V LIST1 let_binding SEP "and" ->
          <:str_item< value $aflag:r$ $alist:l$ >>
      | e = expr -> <:str_item< $exp:e$ >> ] ]
  ;
  rebind_exn:
    [ [ "="; a = mod_ident2 -> a
      | -> <:vala< [] >> ] ]
  ;
  mod_binding:
    [ [ i = UIDENT; me = mod_fun_binding -> (i, me) ] ]
  ;
  mod_fun_binding:
    [ RIGHTA
      [ "("; m = V UIDENT; ":"; mt = module_type; ")"; mb = SELF ->
          <:module_expr< functor ( $auid:m$ : $mt$ ) -> $mb$ >>
      | ":"; mt = module_type; "="; me = module_expr ->
          <:module_expr< ( $me$ : $mt$ ) >>
      | "="; me = module_expr -> <:module_expr< $me$ >> ] ]
  ;
  module_type:
    [ [ "functor"; "("; i = V UIDENT; ":"; t = SELF; ")"; "->"; mt = SELF ->
          <:module_type< functor ( $auid:i$ : $t$ ) -> $mt$ >> ]
    | [ mt = SELF; "with"; wcl = V LIST1 with_constr SEP "and" ->
          <:module_type< $mt$ with $alist:wcl$ >> ]
    | [ "sig"; sg = V LIST0 [ s = sig_item; ";" -> s ]; "end" ->
          <:module_type< sig $alist:sg$ end >> ]
    | [ m1 = SELF; m2 = SELF -> <:module_type< $m1$ $m2$ >> ]
    | [ m1 = SELF; "."; m2 = SELF -> <:module_type< $m1$ . $m2$ >> ]
    | "simple"
      [ i = V UIDENT -> <:module_type< $auid:i$ >>
      | i = V LIDENT -> <:module_type< $alid:i$ >>
      | "'"; i = ident2 -> <:module_type< ' $a:i$ >>
      | "("; mt = SELF; ")" -> <:module_type< $mt$ >> ] ]
  ;
  sig_item:
    [ "top"
      [ "declare"; st = V LIST0 [ s = sig_item; ";" -> s ]; "end" ->
          <:sig_item< declare $alist:st$ end >>
      | "exception"; (_, c, tl) = constructor_declaration ->
          <:sig_item< exception $auid:c$ of $alist:tl$ >>
      | "external"; i = V LIDENT; ":"; t = ctyp; "="; pd = V LIST1 STRING ->
          <:sig_item< external $alid:i$ : $t$ = $alist:pd$ >>
      | "include"; mt = module_type -> <:sig_item< include $mt$ >>
      | "module"; rf = V FLAG "rec"; l = V LIST1 mod_decl_binding SEP "and" ->
          <:sig_item< module $aflag:rf$ $alist:l$ >>
      | "module"; "type"; i = V UIDENT; "="; mt = module_type ->
          <:sig_item< module type $auid:i$ = $mt$ >>
      | "open"; i = mod_ident2 -> <:sig_item< open $a:i$ >>
      | "type"; tdl = V LIST1 type_declaration SEP "and" ->
          <:sig_item< type $alist:tdl$ >>
      | "value"; i = V LIDENT; ":"; t = ctyp ->
          <:sig_item< value $alid:i$ : $t$ >> ] ]
  ;
  mod_decl_binding:
    [ [ i = UIDENT; mt = module_declaration -> (i, mt) ] ]
  ;
  module_declaration:
    [ RIGHTA
      [ ":"; mt = module_type -> <:module_type< $mt$ >>
      | "("; i = V UIDENT; ":"; t = module_type; ")"; mt = SELF ->
          <:module_type< functor ( $auid:i$ : $t$ ) -> $mt$ >> ] ]
  ;
  with_constr:
    [ [ "type"; i = mod_ident2; tpl = V LIST0 type_parameter; "=";
        pf = V FLAG "private"; t = ctyp ->
          <:with_constr< type $a:i$ $alist:tpl$ = $aflag:pf$ $t$ >>
      | "module"; i = mod_ident2; "="; me = module_expr ->
          <:with_constr< module $a:i$ = $me$ >> ] ]
  ;
  expr:
    [ "top" RIGHTA
      [ "let"; r = V FLAG "rec"; l = V LIST1 let_binding SEP "and"; "in";
        x = SELF ->
          <:expr< let $aflag:r$ $alist:l$ in $x$ >>
      | "let"; "module"; m = V UIDENT; mb = mod_fun_binding; "in"; e = SELF ->
          <:expr< let module $auid:m$ = $mb$ in $e$ >>
      | "fun"; "["; l = V LIST0 match_case SEP "|"; "]" ->
          <:expr< fun [ $alist:l$ ] >>
      | "fun"; p = ipatt; e = fun_def -> <:expr< fun $p$ -> $e$ >>
      | "match"; e = SELF; "with"; "["; l = V LIST0 match_case SEP "|"; "]" ->
          <:expr< match $e$ with [ $alist:l$ ] >>
      | "match"; e = SELF; "with"; p1 = ipatt; "->"; e1 = SELF ->
          <:expr< match $e$ with $p1$ -> $e1$ >>
      | "try"; e = SELF; "with"; "["; l = V LIST0 match_case SEP "|"; "]" ->
          <:expr< try $e$ with [ $alist:l$ ] >>
      | "try"; e = SELF; "with"; p1 = ipatt; "->"; e1 = SELF ->
          <:expr< try $e$ with $p1$ -> $e1$ >>
      | "if"; e1 = SELF; "then"; e2 = SELF; "else"; e3 = SELF ->
          <:expr< if $e1$ then $e2$ else $e3$ >>
      | "do"; "{"; seq = sequence2; "}" -> mksequence2 loc seq
      | "for"; i = V LIDENT; "="; e1 = SELF; df = direction_flag2; e2 = SELF;
        "do"; "{"; seq = sequence2; "}" ->
          <:expr< for $alid:i$ = $e1$ $ato:df$ $e2$ do { $alist:seq$ } >>
      | "while"; e = SELF; "do"; "{"; seq = sequence2; "}" ->
          <:expr< while $e$ do { $alist:seq$ } >> ]
    | "where"
      [ e = SELF; "where"; rf = V FLAG "rec"; lb = let_binding ->
          <:expr< let $aflag:rf$ $list:[lb]$ in $e$ >> ]
    | ":=" NONA
      [ e1 = SELF; ":="; e2 = SELF; dummy -> <:expr< $e1$ := $e2$ >> ]
    | "||" RIGHTA
      [ e1 = SELF; "||"; e2 = SELF -> <:expr< $e1$ || $e2$ >> ]
    | "&&" RIGHTA
      [ e1 = SELF; "&&"; e2 = SELF -> <:expr< $e1$ && $e2$ >> ]
    | "<" LEFTA
      [ e1 = SELF; "<"; e2 = SELF -> <:expr< $e1$ < $e2$ >>
      | e1 = SELF; ">"; e2 = SELF -> <:expr< $e1$ > $e2$ >>
      | e1 = SELF; "<="; e2 = SELF -> <:expr< $e1$ <= $e2$ >>
      | e1 = SELF; ">="; e2 = SELF -> <:expr< $e1$ >= $e2$ >>
      | e1 = SELF; "="; e2 = SELF -> <:expr< $e1$ = $e2$ >>
      | e1 = SELF; "<>"; e2 = SELF -> <:expr< $e1$ <> $e2$ >>
      | e1 = SELF; "=="; e2 = SELF -> <:expr< $e1$ == $e2$ >>
      | e1 = SELF; "!="; e2 = SELF -> <:expr< $e1$ != $e2$ >> ]
    | "^" RIGHTA
      [ e1 = SELF; "^"; e2 = SELF -> <:expr< $e1$ ^ $e2$ >>
      | e1 = SELF; "@"; e2 = SELF -> <:expr< $e1$ @ $e2$ >> ]
    | "+" LEFTA
      [ e1 = SELF; "+"; e2 = SELF -> <:expr< $e1$ + $e2$ >>
      | e1 = SELF; "-"; e2 = SELF -> <:expr< $e1$ - $e2$ >>
      | e1 = SELF; "+."; e2 = SELF -> <:expr< $e1$ +. $e2$ >>
      | e1 = SELF; "-."; e2 = SELF -> <:expr< $e1$ -. $e2$ >> ]
    | "*" LEFTA
      [ e1 = SELF; "*"; e2 = SELF -> <:expr< $e1$ * $e2$ >>
      | e1 = SELF; "/"; e2 = SELF -> <:expr< $e1$ / $e2$ >>
      | e1 = SELF; "*."; e2 = SELF -> <:expr< $e1$ *. $e2$ >>
      | e1 = SELF; "/."; e2 = SELF -> <:expr< $e1$ /. $e2$ >>
      | e1 = SELF; "land"; e2 = SELF -> <:expr< $e1$ land $e2$ >>
      | e1 = SELF; "lor"; e2 = SELF -> <:expr< $e1$ lor $e2$ >>
      | e1 = SELF; "lxor"; e2 = SELF -> <:expr< $e1$ lxor $e2$ >>
      | e1 = SELF; "mod"; e2 = SELF -> <:expr< $e1$ mod $e2$ >> ]
    | "**" RIGHTA
      [ e1 = SELF; "**"; e2 = SELF -> <:expr< $e1$ ** $e2$ >>
      | e1 = SELF; "asr"; e2 = SELF -> <:expr< $e1$ asr $e2$ >>
      | e1 = SELF; "lsl"; e2 = SELF -> <:expr< $e1$ lsl $e2$ >>
      | e1 = SELF; "lsr"; e2 = SELF -> <:expr< $e1$ lsr $e2$ >> ]
    | "unary minus" NONA
      [ "-"; e = SELF -> mkumin loc "-" e
      | "-."; e = SELF -> mkumin loc "-." e ]
    | "apply" LEFTA
      [ e1 = SELF; e2 = SELF -> <:expr< $e1$ $e2$ >>
      | "assert"; e = SELF -> <:expr< assert $e$ >>
      | "lazy"; e = SELF -> <:expr< lazy $e$ >> ]
    | "." LEFTA
      [ e1 = SELF; "."; "("; e2 = SELF; ")" -> <:expr< $e1$ .( $e2$ ) >>
      | e1 = SELF; "."; "["; e2 = SELF; "]" -> <:expr< $e1$ .[ $e2$ ] >>
      | e = SELF; "."; "{"; el = V LIST1 expr SEP ","; "}" ->
          <:expr< $e$ . { $alist:el$ } >>
      | e1 = SELF; "."; e2 = SELF -> <:expr< $e1$ . $e2$ >> ]
    | "~-" NONA
      [ "~-"; e = SELF -> <:expr< ~- $e$ >>
      | "~-."; e = SELF -> <:expr< ~-. $e$ >> ]
    | "simple"
      [ s = V INT -> <:expr< $aint:s$ >>
      | s = V INT_l -> <:expr< $aint32:s$ >>
      | s = V INT_L -> <:expr< $aint64:s$ >>
      | s = V INT_n -> <:expr< $anativeint:s$ >>
      | s = V FLOAT -> <:expr< $aflo:s$ >>
      | s = V STRING -> <:expr< $astr:s$ >>
      | s = V CHAR -> <:expr< $achr:s$ >>
      | i = V LIDENT -> <:expr< $alid:i$ >>
      | i = V UIDENT -> <:expr< $auid:i$ >>
      | "["; "]" -> <:expr< [] >>
      | "["; el = LIST1 expr SEP ";"; last = cons_expr_opt; "]" ->
          mklistexp loc last el
      | "[|"; el = V LIST0 expr SEP ";"; "|]" -> <:expr< [| $alist:el$ |] >>
      | "{"; lel = V LIST1 label_expr SEP ";"; "}" ->
          <:expr< { $alist:lel$ } >>
      | "{"; "("; e = SELF; ")"; "with"; lel = V LIST1 label_expr SEP ";";
        "}" ->
          <:expr< { ($e$) with $alist:lel$ } >>
      | "("; ")" -> <:expr< () >>
      | "("; e = SELF; ":"; t = ctyp; ")" -> <:expr< ($e$ : $t$) >>
      | "("; e = SELF; ","; el = LIST1 expr SEP ","; ")" ->
          <:expr< ($list:[e::el]$) >>
      | "("; e = SELF; ")" -> <:expr< $e$ >>
      | "("; el = V LIST1 expr SEP ","; ")" -> <:expr< ($alist:el$) >> ] ]
  ;
  cons_expr_opt:
    [ [ "::"; e = expr -> Some e
      | -> None ] ]
  ;
  dummy:
    [ [ -> () ] ]
  ;
  sequence2:
    [ [ seq = sequence -> <:vala< seq >>
      | seq = V LIST1 expr SEP ";" -> seq ] ]
  ;
  sequence:
    [ [ "let"; rf = V FLAG "rec"; l = V LIST1 let_binding SEP "and"; "in";
        el = SELF ->
          [<:expr< let $aflag:rf$ $alist:l$ in $mksequence loc el$ >>]
      | e = expr; ";"; el = SELF -> [e :: el]
      | e = expr; ";" -> [e]
      | e = expr -> [e] ] ]
  ;
  let_binding:
    [ [ p = ipatt; e = fun_binding -> (p, e) ] ]
  ;
  fun_binding:
    [ RIGHTA
      [ p = ipatt; e = SELF -> <:expr< fun $p$ -> $e$ >>
      | "="; e = expr -> <:expr< $e$ >>
      | ":"; t = ctyp; "="; e = expr -> <:expr< ($e$ : $t$) >> ] ]
  ;
  match_case:
    [ [ p = patt; aso = as_patt_opt; w = OPT when_expr; "->"; e = expr ->
          mkmatchcase loc p aso w e ] ]
  ;
  as_patt_opt:
    [ [ "as"; p = patt -> Some p
      | -> None ] ]
  ;
  when_expr:
    [ [ "when"; e = expr -> e ] ]
  ;
  label_expr:
    [ [ i = patt_label_ident; e = fun_binding -> (i, e) ] ]
  ;
  fun_def:
    [ RIGHTA
      [ p = ipatt; e = SELF -> <:expr< fun $p$ -> $e$ >>
      | "->"; e = expr -> e ] ]
  ;
  patt:
    [ LEFTA
      [ p1 = SELF; "|"; p2 = SELF -> <:patt< $p1$ | $p2$ >> ]
    | NONA
      [ p1 = SELF; ".."; p2 = SELF -> <:patt< $p1$ .. $p2$ >> ]
    | LEFTA
      [ p1 = SELF; p2 = SELF -> <:patt< $p1$ $p2$ >> ]
    | LEFTA
      [ p1 = SELF; "."; p2 = SELF -> <:patt< $p1$ . $p2$ >> ]
    | "simple"
      [ s = V LIDENT -> <:patt< $alid:s$ >>
      | s = V UIDENT -> <:patt< $auid:s$ >>
      | s = V INT -> <:patt< $aint:s$ >>
      | s = V INT_l -> <:patt< $aint32:s$ >>
      | s = V INT_L -> <:patt< $aint64:s$ >>
      | s = V INT_n -> <:patt< $anativeint:s$ >>
      | s = V FLOAT -> <:patt< $aflo:s$ >>
      | s = V STRING -> <:patt< $astr:s$ >>
      | s = V CHAR -> <:patt< $achr:s$ >>
      | "-"; s = INT -> mkuminpat loc "-" True s
      | "-"; s = FLOAT -> mkuminpat loc "-" False s
      | "["; "]" -> <:patt< [] >>
      | "["; pl = LIST1 patt SEP ";"; last = cons_patt_opt; "]" ->
          mklistpat loc last pl
      | "[|"; pl = V LIST0 patt SEP ";"; "|]" -> <:patt< [| $alist:pl$ |] >>
      | "{"; lpl = V LIST1 label_patt SEP ";"; "}" ->
          <:patt< { $alist:lpl$ } >>
      | "("; p = paren_patt; ")" -> p
      | "_" -> <:patt< _ >> ] ]
  ;
  paren_patt:
    [ [ p = patt; ":"; t = ctyp -> <:patt< ($p$ : $t$) >>
      | p = patt; "as"; p2 = patt -> <:patt< ($p$ as $p2$) >>
      | p = patt; ","; pl = LIST1 patt SEP "," -> <:patt< ($list:[p::pl]$) >>
      | p = patt -> <:patt< $p$ >>
      | pl = V LIST1 patt SEP "," -> <:patt< ($alist:pl$) >>
      | -> <:patt< () >> ] ]
  ;
  cons_patt_opt:
    [ [ "::"; p = patt -> Some p
      | -> None ] ]
  ;
  label_patt:
    [ [ i = patt_label_ident; "="; p = patt -> (i, p) ] ]
  ;
  patt_label_ident:
    [ LEFTA
      [ p1 = SELF; "."; p2 = SELF -> <:patt< $p1$ . $p2$ >> ]
    | "simple" RIGHTA
      [ i = V UIDENT -> <:patt< $auid:i$ >>
      | i = V LIDENT -> <:patt< $alid:i$ >> ] ]
  ;
  ipatt:
    [ [ "{"; lpl = V LIST1 label_ipatt SEP ";"; "}" ->
          <:patt< { $alist:lpl$ } >>
      | "("; p = paren_ipatt; ")" -> p
      | s = V LIDENT -> <:patt< $alid:s$ >>
      | "_" -> <:patt< _ >> ] ]
  ;
  paren_ipatt:
    [ [ p = ipatt; ":"; t = ctyp -> <:patt< ($p$ : $t$) >>
      | p = ipatt; "as"; p2 = ipatt -> <:patt< ($p$ as $p2$) >>
      | p = ipatt; ","; pl = LIST1 ipatt SEP "," ->
          <:patt< ($list:[p::pl]$) >>
      | p = ipatt -> <:patt< $p$ >>
      | pl = V LIST1 ipatt SEP "," -> <:patt< ( $alist:pl$) >>
      | -> <:patt< () >> ] ]
  ;
  label_ipatt:
    [ [ i = patt_label_ident; "="; p = ipatt -> (i, p) ] ]
  ;
  type_declaration:
    [ [ n = type_patt; tpl = LIST0 type_parameter; "="; pf = FLAG "private";
        tk = ctyp; cl = LIST0 constrain ->
          {MLast.tdNam = n; MLast.tdPrm = tpl; MLast.tdPrv = pf;
           MLast.tdDef = tk; MLast.tdCon = cl} ] ]
  ;
  type_patt:
    [ [ n = LIDENT -> (loc, n) ] ]
  ;
  constrain:
    [ [ "constraint"; t1 = ctyp; "="; t2 = ctyp -> (t1, t2) ] ]
  ;
  type_parameter:
    [ [ i = typevar -> (i, (False, False))
      | "+"; "'"; i = ident -> (i, (True, False))
      | "-"; "'"; i = ident -> (i, (False, True)) ] ]
  ;
  ctyp:
    [ LEFTA
      [ t1 = SELF; "=="; t2 = SELF -> <:ctyp< $t1$ == $t2$ >> ]
    | LEFTA
      [ t1 = SELF; "as"; t2 = SELF -> <:ctyp< $t1$ as $t2$ >> ]
    | LEFTA
      [ "!"; pl = V LIST1 typevar; "."; t = ctyp ->
          <:ctyp< ! $alist:pl$ . $t$ >> ]
    | "arrow" RIGHTA
      [ t1 = SELF; "->"; t2 = SELF -> <:ctyp< $t1$ -> $t2$ >> ]
    | "apply" LEFTA
      [ t1 = SELF; t2 = SELF -> <:ctyp< $t1$ $t2$ >> ]
    | LEFTA
      [ t1 = SELF; "."; t2 = SELF -> <:ctyp< $t1$ . $t2$ >> ]
    | "simple"
      [ i = typevar2 -> <:ctyp< '$a:i$ >>
      | "_" -> <:ctyp< _ >>
      | i = V LIDENT -> <:ctyp< $alid:i$ >>
      | i = V UIDENT -> <:ctyp< $auid:i$ >>
      | "("; t = SELF; "*"; tl = LIST1 ctyp SEP "*"; ")" ->
          <:ctyp< ( $list:[t::tl]$ ) >>
      | "("; t = SELF; ")" -> <:ctyp< $t$ >>
      | "("; tl = V LIST1 ctyp SEP "*"; ")" -> <:ctyp< ( $alist:tl$ ) >>
      | "["; cdl = V LIST0 constructor_declaration SEP "|"; "]" ->
          <:ctyp< [ $alist:cdl$ ] >>
      | "{"; ldl = V LIST1 label_declaration SEP ";"; "}" ->
          <:ctyp< { $alist:ldl$ } >> ] ]
  ;
  constructor_declaration:
    [ [ ci = V UIDENT; "of"; cal = V LIST1 ctyp SEP "and" -> (loc, ci, cal)
      | ci = V UIDENT -> (loc, ci, <:vala< [] >>) ] ]
  ;
  label_declaration:
    [ [ i = LIDENT; ":"; mf = FLAG "mutable"; t = ctyp ->
          (loc, i, mf, t) ] ]
  ;
  ident2:
    [ [ s = ANTIQUOT_LOC -> <:vala< $s$ >>
      | s = ANTIQUOT_LOC "a" -> <:vala< $s$ >>
      | i = ident -> <:vala< i >> ] ]
  ;
  ident:
    [ [ i = LIDENT -> i
      | i = UIDENT -> i ] ]
  ;
  mod_ident2:
    [ [ sl = mod_ident -> <:vala< sl >>
      | s = ANTIQUOT_LOC "list" -> <:vala< $s$ >>
      | s = ANTIQUOT_LOC "alist" -> <:vala< $s$ >>
      | s = ANTIQUOT_LOC -> <:vala< $s$ >>
      | s = ANTIQUOT_LOC "a" -> <:vala< $s$ >> ] ]
  ;
  mod_ident:
    [ RIGHTA
      [ i = UIDENT -> [i]
      | i = LIDENT -> [i]
      | i = UIDENT; "."; j = SELF -> [i :: j] ] ]
  ;
  (* Objects and Classes *)
  str_item:
    [ [ "class"; cd = V LIST1 class_declaration SEP "and" ->
          <:str_item< class $alist:cd$ >>
      | "class"; "type"; ctd = V LIST1 class_type_declaration SEP "and" ->
          <:str_item< class type $alist:ctd$ >> ] ]
  ;
  sig_item:
    [ [ "class"; cd = V LIST1 class_description SEP "and" ->
          <:sig_item< class $alist:cd$ >>
      | "class"; "type"; ctd = V LIST1 class_type_declaration SEP "and" ->
          <:sig_item< class type $alist:ctd$ >> ] ]
  ;
  class_declaration:
    [ [ vf = FLAG "virtual"; i = LIDENT; ctp = class_type_parameters;
        cfb = class_fun_binding ->
          {MLast.ciLoc = loc; MLast.ciVir = vf; MLast.ciPrm = ctp;
           MLast.ciNam = i; MLast.ciExp = cfb} ] ]
  ;
  class_fun_binding:
    [ [ "="; ce = class_expr -> ce
      | ":"; ct = class_type; "="; ce = class_expr ->
          <:class_expr< ($ce$ : $ct$) >>
      | p = ipatt; cfb = SELF -> <:class_expr< fun $p$ -> $cfb$ >> ] ]
  ;
  class_type_parameters:
    [ [ -> (loc, [])
      | "["; tpl = LIST1 type_parameter SEP ","; "]" -> (loc, tpl) ] ]
  ;
  class_fun_def:
    [ [ p = ipatt; ce = SELF -> <:class_expr< fun $p$ -> $ce$ >>
      | "->"; ce = class_expr -> ce ] ]
  ;
  class_expr:
    [ "top"
      [ "fun"; p = ipatt; ce = class_fun_def ->
          <:class_expr< fun $p$ -> $ce$ >>
      | "let"; rf = V FLAG "rec"; lb = V LIST1 let_binding SEP "and"; "in";
        ce = SELF ->
          <:class_expr< let $aflag:rf$ $alist:lb$ in $ce$ >> ]
    | "apply" LEFTA
      [ ce = SELF; e = expr LEVEL "label" ->
          <:class_expr< $ce$ $e$ >> ]
    | "simple"
      [ ci = class_longident2; "["; ctcl = V LIST1 ctyp SEP ","; "]" ->
          <:class_expr< $alist:ci$ [ $alist:ctcl$ ] >>
      | ci = class_longident2 -> <:class_expr< $alist:ci$ >>
      | "object"; cspo = V OPT class_self_patt; cf = class_structure; "end" ->
          <:class_expr< object $aopt:cspo$ $alist:cf$ end >>
      | "("; ce = SELF; ":"; ct = class_type; ")" ->
          <:class_expr< ($ce$ : $ct$) >>
      | "("; ce = SELF; ")" -> ce ] ]
  ;
  class_structure:
    [ [ cf = V LIST0 [ cf = class_str_item; ";" -> cf ] -> cf ] ]
  ;
  class_self_patt:
    [ [ "("; p = patt; ")" -> p
      | "("; p = patt; ":"; t = ctyp; ")" -> <:patt< ($p$ : $t$) >> ] ]
  ;
  class_str_item:
    [ [ "declare"; st = V LIST0 [ s= class_str_item; ";" -> s ]; "end" ->
          <:class_str_item< declare $alist:st$ end >>
      | "inherit"; ce = class_expr; pb = V OPT as_lident ->
          <:class_str_item< inherit $ce$ $aopt:pb$ >>
      | "value"; mf = V FLAG "mutable"; lab = label2; e = cvalue_binding ->
          <:class_str_item< value $aflag:mf$ $alid:lab$ = $e$ >>
      | "method"; "virtual"; pf = V FLAG "private"; l = label2; ":";
        t = ctyp ->
          <:class_str_item< method virtual $aflag:pf$ $alid:l$ : $t$ >>
      | "method"; pf = V FLAG "private"; l = label2; topt = V OPT polyt;
        e = fun_binding ->
          <:class_str_item< method $aflag:pf$ $alid:l$ $aopt:topt$ = $e$ >>
      | "type"; t1 = ctyp; "="; t2 = ctyp ->
          <:class_str_item< type $t1$ = $t2$ >>
      | "initializer"; se = expr -> <:class_str_item< initializer $se$ >> ] ]
  ;
  as_lident:
    [ [ "as"; i = LIDENT -> i ] ]
  ;
  polyt:
    [ [ ":"; t = ctyp -> t ] ]
  ;
  cvalue_binding:
    [ [ "="; e = expr -> e
      | ":"; t = ctyp; "="; e = expr -> <:expr< ($e$ : $t$) >>
      | ":"; t = ctyp; ":>"; t2 = ctyp; "="; e = expr ->
          <:expr< ($e$ : $t$ :> $t2$) >>
      | ":>"; t = ctyp; "="; e = expr -> <:expr< ($e$ :> $t$) >> ] ]
  ;
  label2:
    [ [ i = V LIDENT -> i ] ]
  ;
  label:
    [ [ i = LIDENT -> i ] ]
  ;
  class_type:
    [ [ "["; t = ctyp; "]"; "->"; ct = SELF ->
          <:class_type< [ $t$ ] -> $ct$ >>
      | id = clty_longident2; "["; tl = V LIST1 ctyp SEP ","; "]" ->
          <:class_type< $alist:id$ [ $alist:tl$ ] >>
      | id = clty_longident2 -> <:class_type< $alist:id$ >>
      | "object"; cst = V OPT class_self_type;
        csf = V LIST0 [ csf = class_sig_item; ";" -> csf ]; "end" ->
          <:class_type< object $aopt:cst$ $alist:csf$ end >> ] ]
  ;
  class_self_type:
    [ [ "("; t = ctyp; ")" -> t ] ]
  ;
  class_sig_item:
    [ [ "declare"; st = V LIST0 [ s = class_sig_item; ";" -> s ]; "end" ->
          <:class_sig_item< declare $alist:st$ end >>
      | "inherit"; cs = class_type -> <:class_sig_item< inherit $cs$ >>
      | "value"; mf = V FLAG "mutable"; l = label2; ":"; t = ctyp ->
          <:class_sig_item< value $aflag:mf$ $alid:l$ : $t$ >>
      | "method"; "virtual"; pf = V FLAG "private"; l = label2; ":";
        t = ctyp ->
          <:class_sig_item< method virtual $aflag:pf$ $alid:l$ : $t$ >>
      | "method"; pf = V FLAG "private"; l = label2; ":"; t = ctyp ->
          <:class_sig_item< method $aflag:pf$ $alid:l$ : $t$ >>
      | "type"; t1 = ctyp; "="; t2 = ctyp ->
          <:class_sig_item< type $t1$ = $t2$ >> ] ]
  ;
  class_description:
    [ [ vf = FLAG "virtual"; n = LIDENT; ctp = class_type_parameters; ":";
        ct = class_type ->
          {MLast.ciLoc = loc; MLast.ciVir = vf; MLast.ciPrm = ctp;
           MLast.ciNam = n; MLast.ciExp = ct} ] ]
  ;
  class_type_declaration:
    [ [ vf = FLAG "virtual"; n = LIDENT; ctp = class_type_parameters; "=";
        cs = class_type ->
          {MLast.ciLoc = loc; MLast.ciVir = vf; MLast.ciPrm = ctp;
           MLast.ciNam = n; MLast.ciExp = cs} ] ]
  ;
  expr: LEVEL "apply"
    [ LEFTA
      [ "new"; i = class_longident2 -> <:expr< new $alist:i$ >>
      | "object"; cspo = V OPT class_self_patt; cf = class_structure; "end" ->
          <:expr< object $aopt:cspo$ $alist:cf$ end >> ] ]
  ;
  expr: LEVEL "."
    [ [ e = SELF; "#"; lab = label2 -> <:expr< $e$ # $alid:lab$ >> ] ]
  ;
  expr: LEVEL "simple"
    [ [ "("; e = SELF; ":"; t = ctyp; ":>"; t2 = ctyp; ")" ->
          <:expr< ($e$ : $t$ :> $t2$ ) >>
      | "("; e = SELF; ":>"; t = ctyp; ")" -> <:expr< ($e$ :> $t$) >>
      | "{<"; fel = V LIST0 field_expr SEP ";"; ">}" ->
          <:expr< {< $alist:fel$ >} >> ] ]
  ;
  field_expr:
    [ [ l = label; "="; e = expr -> (l, e) ] ]
  ;
  ctyp: LEVEL "simple"
    [ [ "#"; id = class_longident2 -> <:ctyp< # $alist:id$ >>
      | "<"; ml = V LIST0 field SEP ";"; v = V FLAG ".."; ">" ->
          <:ctyp< < $alist:ml$ $aflag:v$ > >> ] ]
  ;
  field:
    [ [ lab = LIDENT; ":"; t = ctyp -> (lab, t) ] ]
  ;
  typevar2:
    [ [ "'"; i = ident2 -> i ] ]
  ;
  typevar:
    [ [ "'"; i = ident -> i ] ]
  ;
  clty_longident2:
    [ [ v = clty_longident -> <:vala< v >>
      | s = ANTIQUOT_LOC "list" -> <:vala< $s$ >>
      | s = ANTIQUOT_LOC "alist" -> <:vala< $s$ >> ] ]
  ;
  clty_longident:
    [ [ m = UIDENT; "."; l = SELF -> [m :: l]
      | i = LIDENT -> [i] ] ]
  ;
  class_longident2:
    [ [ v = class_longident -> <:vala< v >>
      | s = ANTIQUOT_LOC "list" -> <:vala< $s$ >>
      | s = ANTIQUOT_LOC "alist" -> <:vala< $s$ >> ] ]
  ;
  class_longident:
    [ [ m = UIDENT; "."; l = SELF -> [m :: l]
      | i = LIDENT -> [i] ] ]
  ;
  (* Labels *)
  ctyp: AFTER "arrow"
    [ NONA
      [ i = tildeidentcolon; t = SELF -> <:ctyp< ~$a:i$: $t$ >>
      | i = questionidentcolon; t = SELF -> <:ctyp< ?$a:i$: $t$ >> ] ]
  ;
  tildeident:
    [ [ i = TILDEIDENT -> <:vala< i >>
      | a = TILDEANTIQUOT_LOC "a" -> <:vala< $a$ >>
      | a = TILDEANTIQUOT_LOC -> <:vala< $a$ >> ] ]
  ;
  tildeidentcolon:
    [ [ i = TILDEIDENTCOLON -> <:vala< i >>
      | a = TILDEANTIQUOTCOLON_LOC -> <:vala< $a$ >>
      | a = TILDEANTIQUOTCOLON_LOC "a" -> <:vala< $a$ >> ] ]
  ;
  questionident:
    [ [ i = QUESTIONIDENT -> <:vala< i >>
      | a = QUESTIONANTIQUOT_LOC -> <:vala< $a$ >>
      | a = QUESTIONANTIQUOT_LOC "a" -> <:vala< $a$ >> ] ]
  ;
  questionidentcolon:
    [ [ i = QUESTIONIDENTCOLON -> <:vala< i >>
      | a = QUESTIONANTIQUOTCOLON_LOC -> <:vala< $a$ >>
      | a = QUESTIONANTIQUOTCOLON_LOC "a" -> <:vala< $a$ >> ] ]
  ;
  ctyp: LEVEL "simple"
    [ [ "["; "="; rfl = poly_variant_list; "]" ->
          <:ctyp< [ = $alist:rfl$ ] >>
      | "["; ">"; rfl = poly_variant_list; "]" ->
          <:ctyp< [ > $alist:rfl$ ] >>
      | "["; "<"; rfl = poly_variant_list; "]" ->
          <:ctyp< [ < $alist:rfl$ ] >>
      | "["; "<"; rfl = poly_variant_list; ">"; ntl = V LIST1 name_tag; "]" ->
          <:ctyp< [ < $alist:rfl$ > $alist:ntl$ ] >> ] ]
  ;
  poly_variant_list:
    [ [ rfl = V LIST0 poly_variant SEP "|" -> rfl ] ]
  ;
  poly_variant:
    [ [ "`"; i = ident2 -> <:poly_variant< ` $a:i$ >>
      | "`"; i = ident2; "of"; ao = V FLAG "&"; l = V LIST1 ctyp SEP "&" ->
          <:poly_variant< ` $a:i$ of $aflag:ao$ $alist:l$ >>
      | t = ctyp -> <:poly_variant< $t$ >> ] ]
  ;
  name_tag:
    [ [ "`"; i = ident -> i ] ]
  ;
  patt: LEVEL "simple"
    [ [ "`"; s = ident2 -> <:patt< ` $a:s$ >>
      | "#"; sl = mod_ident2 -> <:patt< # $a:sl$ >>
      | i = tildeidentcolon; p = SELF -> <:patt< ~$a:i$: $p$ >>
      | i = tildeident -> <:patt< ~$a:i$ >>
      | i = questionidentcolon; "("; p = patt_tcon; eo = V OPT eq_expr; ")" ->
          <:patt< ?$a:i$: ($p$ $aopt:eo$) >>
      | i = questionident ->
          <:patt< ?$a:i$ >>
      | "?"; "("; p = patt_tcon; eo = V OPT eq_expr; ")" ->
          <:patt< ? ($p$ $aopt:eo$) >> ] ]
  ;
  patt_tcon:
    [ [ p = patt; ":"; t = ctyp -> <:patt< ($p$ : $t$) >>
      | p = patt -> p ] ]
  ;
  ipatt:
    [ [ i = tildeidentcolon; p = SELF -> <:patt< ~$a:i$: $p$ >>
      | i = tildeident -> <:patt< ~$a:i$ >>
      | i = questionidentcolon; "("; p = ipatt_tcon;
        eo = V OPT eq_expr; ")" ->
          <:patt< ?$a:i$: ($p$ $aopt:eo$) >>
      | i = questionident ->
          <:patt< ?$a:i$ >>
      | "?"; "("; p = ipatt_tcon; eo = V OPT eq_expr; ")" ->
          <:patt< ? ($p$ $aopt:eo$) >> ] ]
  ;
  ipatt_tcon:
    [ [ p = ipatt; ":"; t = ctyp -> <:patt< ($p$ : $t$) >>
      | p = ipatt -> p ] ]
  ;
  eq_expr:
    [ [ "="; e = expr -> e ] ]
  ;
  expr: AFTER "apply"
    [ "label" NONA
      [ i = tildeidentcolon; e = SELF -> <:expr< ~$a:i$: $e$ >>
      | i = tildeident -> <:expr< ~$a:i$ >>
      | i = questionidentcolon; e = SELF -> <:expr< ?$a:i$: $e$ >>
      | i = questionident -> <:expr< ?$a:i$ >> ] ]
  ;
  expr: LEVEL "simple"
    [ [ "`"; s = ident2 -> <:expr< ` $a:s$ >> ] ]
  ;
  direction_flag2:
    [ [ df = direction_flag -> <:vala< df >>
      | s = ANTIQUOT_LOC "to" -> <:vala< $s$ >>
      | s = ANTIQUOT_LOC "ato" -> <:vala< $s$ >> ] ]
  ;
  direction_flag:
    [ [ "to" -> True
      | "downto" -> False ] ]
  ;
END;

EXTEND
  GLOBAL: str_item sig_item;
  str_item:
    [ [ "#"; n = V LIDENT; dp = dir_param ->
          <:str_item< # $alid:n$ $aopt:dp$ >> ] ]
  ;
  sig_item:
    [ [ "#"; n = V LIDENT; dp = dir_param ->
          <:sig_item< # $alid:n$ $aopt:dp$ >> ] ]
  ;
  dir_param:
    [ [ a = ANTIQUOT_LOC "opt" -> <:vala< $a$ >>
      | a = ANTIQUOT_LOC "aopt" -> <:vala< $a$ >>
      | e = expr -> <:vala< Some e >>
      | -> <:vala< None >> ] ]
  ;
END;

EXTEND
  GLOBAL: interf implem use_file top_phrase expr patt;
  interf:
    [ [ "#"; n = V LIDENT; dp = OPT expr; ";" ->
          ([(<:sig_item< # $alid:n$ $opt:dp$ >>, loc)], True)
      | si = sig_item_semi; (sil, stopped) = SELF -> ([si :: sil], stopped)
      | EOI -> ([], False) ] ]
  ;
  sig_item_semi:
    [ [ si = sig_item; ";" -> (si, loc) ] ]
  ;
  implem:
    [ [ "#"; n = V LIDENT; dp = OPT expr; ";" ->
          ([(<:str_item< # $alid:n$ $opt:dp$ >>, loc)], True)
      | si = str_item_semi; (sil, stopped) = SELF -> ([si :: sil], stopped)
      | EOI -> ([], False) ] ]
  ;
  str_item_semi:
    [ [ si = str_item; ";" -> (si, loc) ] ]
  ;
  top_phrase:
    [ [ ph = phrase -> Some ph
      | EOI -> None ] ]
  ;
  use_file:
    [ [ "#"; n = LIDENT; dp = OPT expr; ";" ->
          ([<:str_item< # $lid:n$ $opt:dp$ >>], True)
      | si = str_item; ";"; (sil, stopped) = SELF -> ([si :: sil], stopped)
      | EOI -> ([], False) ] ]
  ;
  phrase:
    [ [ "#"; n = LIDENT; dp = OPT expr; ";" ->
          <:str_item< # $lid:n$ $opt:dp$ >>
      | sti = str_item; ";" -> sti ] ]
  ;
  expr: LEVEL "simple"
    [ [ x = QUOTATION ->
          let x =
            try
              let i = String.index x ':' in
              (String.sub x 0 i,
               String.sub x (i + 1) (String.length x - i - 1))
            with
            [ Not_found -> ("", x) ]
          in
          Pcaml.handle_expr_quotation loc x ] ]
  ;
  patt: LEVEL "simple"
    [ [ x = QUOTATION ->
          let x =
            try
              let i = String.index x ':' in
              (String.sub x 0 i,
               String.sub x (i + 1) (String.length x - i - 1))
            with
            [ Not_found -> ("", x) ]
          in
          Pcaml.handle_patt_quotation loc x ] ]
  ;
END;
