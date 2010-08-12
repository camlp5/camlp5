(* camlp5r *)
(* $Id: pa_r.ml,v 1.123 2010/08/12 11:39:42 deraugla Exp $ *)
(* Copyright (c) INRIA 2007-2010 *)

#load "pa_extend.cmo";
#load "q_MLast.cmo";

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
  Grammar.Unsafe.clear_entry ipatt;
  Grammar.Unsafe.clear_entry ctyp;
  Grammar.Unsafe.clear_entry let_binding;
  Grammar.Unsafe.clear_entry type_declaration;
  Grammar.Unsafe.clear_entry constructor_declaration;
  Grammar.Unsafe.clear_entry label_declaration;
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

Pcaml.add_option "-ignloaddir"
  (Arg.Unit (fun _ -> add_directive "load" (fun _ -> ())))
  "Ignore the #load directives in the input file.";

value mksequence2 loc =
  fun
  [ <:vala< [e] >> -> e
  | seq -> <:expr< do { $_list:seq$ } >> ]
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
    | None -> p ]
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

value mktupexp loc e el = <:expr< ($list:[e::el]$) >>;
value mktuppat loc p pl = <:patt< ($list:[p::pl]$) >>;
value mktuptyp loc t tl = <:ctyp< ( $list:[t::tl]$ ) >>;

value mklabdecl loc i mf t = (loc, i, mf, t);

value mkident i : string = i;

EXTEND
  GLOBAL: sig_item str_item ctyp patt expr module_type module_expr class_type
    class_expr class_sig_item class_str_item let_binding type_declaration
    constructor_declaration label_declaration match_case ipatt with_constr
    poly_variant;
  module_expr:
    [ [ "functor"; "("; i = V UIDENT "uid" ""; ":"; t = module_type; ")";
        "->"; me = SELF ->
          <:module_expr< functor ( $_uid:i$ : $t$ ) -> $me$ >>
      | "struct"; st = V (LIST0 [ s = str_item; ";" -> s ]); "end" ->
          <:module_expr< struct $_list:st$ end >> ]
    | [ me1 = SELF; me2 = SELF -> <:module_expr< $me1$ $me2$ >> ]
    | [ me1 = SELF; "."; me2 = SELF -> <:module_expr< $me1$ . $me2$ >> ]
    | "simple"
      [ i = V UIDENT -> <:module_expr< $_uid:i$ >>
      | "("; me = SELF; ":"; mt = module_type; ")" ->
          <:module_expr< ( $me$ : $mt$ ) >>
      | "("; me = SELF; ")" -> <:module_expr< $me$ >> ] ]
  ;
  str_item:
    [ "top"
      [ "declare"; st = V (LIST0 [ s = str_item; ";" -> s ]); "end" ->
          <:str_item< declare $_list:st$ end >>
      | "exception"; (_, c, tl) = constructor_declaration; b = rebind_exn ->
          <:str_item< exception $_uid:c$ of $_list:tl$ = $_:b$ >>
      | "external"; i = V LIDENT "lid" ""; ":"; t = ctyp; "=";
        pd = V (LIST1 STRING) ->
          <:str_item< external $_lid:i$ : $t$ = $_list:pd$ >>
      | "include"; me = module_expr -> <:str_item< include $me$ >>
      | "module"; r = V (FLAG "rec"); l = V (LIST1 mod_binding SEP "and") ->
          <:str_item< module $_flag:r$ $_list:l$ >>
      | "module"; "type"; i = V UIDENT "uid" ""; "="; mt = module_type ->
          <:str_item< module type $_uid:i$ = $mt$ >>
      | "open"; i = V mod_ident "list" "" -> <:str_item< open $_:i$ >>
      | "type"; tdl = V (LIST1 type_declaration SEP "and") ->
          <:str_item< type $_list:tdl$ >>
      | "value"; r = V (FLAG "rec"); l = V (LIST1 let_binding SEP "and") ->
          <:str_item< value $_flag:r$ $_list:l$ >>
      | "#"; n = V LIDENT "lid" ""; dp = V (OPT expr) ->
          <:str_item< # $_lid:n$ $_opt:dp$ >>
      | e = expr -> <:str_item< $exp:e$ >> ] ]
  ;
  rebind_exn:
    [ [ "="; a = V mod_ident "list" "" -> a
      | -> <:vala< [] >> ] ]
  ;
  mod_binding:
    [ [ i = V UIDENT; me = mod_fun_binding -> (i, me) ] ]
  ;
  mod_fun_binding:
    [ RIGHTA
      [ "("; m = V UIDENT; ":"; mt = module_type; ")"; mb = SELF ->
          <:module_expr< functor ( $_uid:m$ : $mt$ ) -> $mb$ >>
      | ":"; mt = module_type; "="; me = module_expr ->
          <:module_expr< ( $me$ : $mt$ ) >>
      | "="; me = module_expr -> <:module_expr< $me$ >> ] ]
  ;
  module_type:
    [ [ "functor"; "("; i = V UIDENT "uid" ""; ":"; t = SELF; ")"; "->";
        mt = SELF ->
          <:module_type< functor ( $_uid:i$ : $t$ ) -> $mt$ >> ]
    | [ mt = SELF; "with"; wcl = V (LIST1 with_constr SEP "and") ->
          <:module_type< $mt$ with $_list:wcl$ >> ]
    | [ "sig"; sg = V (LIST0 [ s = sig_item; ";" -> s ]); "end" ->
          <:module_type< sig $_list:sg$ end >> ]
    | [ m1 = SELF; m2 = SELF -> <:module_type< $m1$ $m2$ >> ]
    | [ m1 = SELF; "."; m2 = SELF -> <:module_type< $m1$ . $m2$ >> ]
    | "simple"
      [ i = V UIDENT -> <:module_type< $_uid:i$ >>
      | i = V LIDENT -> <:module_type< $_lid:i$ >>
      | "'"; i = V ident "" -> <:module_type< ' $_:i$ >>
      | "("; mt = SELF; ")" -> <:module_type< $mt$ >> ] ]
  ;
  sig_item:
    [ "top"
      [ "declare"; st = V (LIST0 [ s = sig_item; ";" -> s ]); "end" ->
          <:sig_item< declare $_list:st$ end >>
      | "exception"; (_, c, tl) = constructor_declaration ->
          <:sig_item< exception $_uid:c$ of $_list:tl$ >>
      | "external"; i = V LIDENT "lid" ""; ":"; t = ctyp; "=";
        pd = V (LIST1 STRING) ->
          <:sig_item< external $_lid:i$ : $t$ = $_list:pd$ >>
      | "include"; mt = module_type -> <:sig_item< include $mt$ >>
      | "module"; rf = V (FLAG "rec");
        l = V (LIST1 mod_decl_binding SEP "and") ->
          <:sig_item< module $_flag:rf$ $_list:l$ >>
      | "module"; "type"; i = V UIDENT "uid" ""; "="; mt = module_type ->
          <:sig_item< module type $_uid:i$ = $mt$ >>
      | "open"; i = V mod_ident "list" "" -> <:sig_item< open $_:i$ >>
      | "type"; tdl = V (LIST1 type_declaration SEP "and") ->
          <:sig_item< type $_list:tdl$ >>
      | "value"; i = V LIDENT "lid" ""; ":"; t = ctyp ->
          <:sig_item< value $_lid:i$ : $t$ >>
      | "#"; n = V LIDENT "lid" ""; dp = V (OPT expr) ->
          <:sig_item< # $_lid:n$ $_opt:dp$ >> ] ]
  ;
  mod_decl_binding:
    [ [ i = V UIDENT; mt = module_declaration -> (i, mt) ] ]
  ;
  module_declaration:
    [ RIGHTA
      [ ":"; mt = module_type -> <:module_type< $mt$ >>
      | "("; i = V UIDENT; ":"; t = module_type; ")"; mt = SELF ->
          <:module_type< functor ( $_uid:i$ : $t$ ) -> $mt$ >> ] ]
  ;
  with_constr:
    [ [ "type"; i = V mod_ident "list" ""; tpl = V (LIST0 type_parameter);
        "="; pf = V (FLAG "private"); t = ctyp ->
          <:with_constr< type $_:i$ $_list:tpl$ = $_flag:pf$ $t$ >>
      | "module"; i = V mod_ident "list" ""; "="; me = module_expr ->
          <:with_constr< module $_:i$ = $me$ >> ] ]
  ;
  expr:
    [ "top" RIGHTA
      [ "let"; r = V (FLAG "rec"); l = V (LIST1 let_binding SEP "and"); "in";
        x = SELF ->
          <:expr< let $_flag:r$ $_list:l$ in $x$ >>
      | "let"; "module"; m = V UIDENT; mb = mod_fun_binding; "in"; e = SELF ->
          <:expr< let module $_uid:m$ = $mb$ in $e$ >>
      | "fun"; "["; l = V (LIST0 match_case SEP "|"); "]" ->
          <:expr< fun [ $_list:l$ ] >>
      | "fun"; p = ipatt; e = fun_def -> <:expr< fun $p$ -> $e$ >>
      | "match"; e = SELF; "with"; "["; l = V (LIST0 match_case SEP "|");
        "]" ->
          <:expr< match $e$ with [ $_list:l$ ] >>
      | "match"; e = SELF; "with"; p1 = ipatt; "->"; e1 = SELF ->
          <:expr< match $e$ with $p1$ -> $e1$ >>
      | "try"; e = SELF; "with"; "["; l = V (LIST0 match_case SEP "|"); "]" ->
          <:expr< try $e$ with [ $_list:l$ ] >>
      | "try"; e = SELF; "with"; p1 = ipatt; "->"; e1 = SELF ->
          <:expr< try $e$ with $p1$ -> $e1$ >>
      | "if"; e1 = SELF; "then"; e2 = SELF; "else"; e3 = SELF ->
          <:expr< if $e1$ then $e2$ else $e3$ >>
      | "do"; "{"; seq = V sequence "list"; "}" -> mksequence2 loc seq
      | "for"; i = V LIDENT; "="; e1 = SELF; df = V direction_flag "to";
        e2 = SELF; "do"; "{"; seq = V sequence "list"; "}" ->
          <:expr< for $_lid:i$ = $e1$ $_to:df$ $e2$ do { $_list:seq$ } >>
      | "while"; e = SELF; "do"; "{"; seq = V sequence "list"; "}" ->
          <:expr< while $e$ do { $_list:seq$ } >> ]
    | "where"
      [ e = SELF; "where"; rf = V (FLAG "rec"); lb = let_binding ->
          <:expr< let $_flag:rf$ $list:[lb]$ in $e$ >> ]
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
      | e = SELF; "."; "{"; el = V (LIST1 expr SEP ","); "}" ->
          <:expr< $e$ . { $_list:el$ } >>
      | e1 = SELF; "."; e2 = SELF -> <:expr< $e1$ . $e2$ >> ]
    | "~-" NONA
      [ "~-"; e = SELF -> <:expr< ~- $e$ >>
      | "~-."; e = SELF -> <:expr< ~-. $e$ >> ]
    | "simple"
      [ s = V INT -> <:expr< $_int:s$ >>
      | s = V INT_l -> <:expr< $_int32:s$ >>
      | s = V INT_L -> <:expr< $_int64:s$ >>
      | s = V INT_n -> <:expr< $_nativeint:s$ >>
      | s = V FLOAT -> <:expr< $_flo:s$ >>
      | s = V STRING -> <:expr< $_str:s$ >>
      | s = V CHAR -> <:expr< $_chr:s$ >>
      | i = V LIDENT -> <:expr< $_lid:i$ >>
      | i = V UIDENT -> <:expr< $_uid:i$ >>
      | "["; "]" -> <:expr< [] >>
      | "["; el = LIST1 expr SEP ";"; last = cons_expr_opt; "]" ->
          mklistexp loc last el
      | "[|"; el = V (LIST0 expr SEP ";"); "|]" -> <:expr< [| $_list:el$ |] >>
      | "{"; lel = V (LIST1 label_expr SEP ";"); "}" ->
          <:expr< { $_list:lel$ } >>
      | "{"; "("; e = SELF; ")"; "with"; lel = V (LIST1 label_expr SEP ";");
        "}" ->
          <:expr< { ($e$) with $_list:lel$ } >>
      | "("; ")" -> <:expr< () >>
      | "("; e = SELF; ":"; t = ctyp; ")" -> <:expr< ($e$ : $t$) >>
      | "("; e = SELF; ","; el = LIST1 expr SEP ","; ")" -> mktupexp loc e el
      | "("; e = SELF; ")" -> <:expr< $e$ >>
      | "("; el = V (LIST1 expr SEP ","); ")" -> <:expr< ($_list:el$) >> ] ]
  ;
  cons_expr_opt:
    [ [ "::"; e = expr -> Some e
      | -> None ] ]
  ;
  dummy:
    [ [ -> () ] ]
  ;
  sequence:
    [ RIGHTA
      [ "let"; rf = V (FLAG "rec"); l = V (LIST1 let_binding SEP "and");
        "in"; el = SELF ->
          [<:expr< let $_flag:rf$ $_list:l$ in $mksequence loc el$ >>]
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
    [ [ p = patt; aso = as_patt_opt; w = V (OPT when_expr); "->"; e = expr ->
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
      [ p1 = SELF; p2 = SELF -> <:patt< $p1$ $p2$ >>
      | "lazy"; p = SELF -> <:patt< lazy $p$ >> ]
    | LEFTA
      [ p1 = SELF; "."; p2 = SELF -> <:patt< $p1$ . $p2$ >> ]
    | "simple"
      [ s = V LIDENT -> <:patt< $_lid:s$ >>
      | s = V UIDENT -> <:patt< $_uid:s$ >>
      | s = V INT -> <:patt< $_int:s$ >>
      | s = V INT_l -> <:patt< $_int32:s$ >>
      | s = V INT_L -> <:patt< $_int64:s$ >>
      | s = V INT_n -> <:patt< $_nativeint:s$ >>
      | s = V FLOAT -> <:patt< $_flo:s$ >>
      | s = V STRING -> <:patt< $_str:s$ >>
      | s = V CHAR -> <:patt< $_chr:s$ >>
      | "-"; s = INT -> mkuminpat loc "-" True s
      | "-"; s = FLOAT -> mkuminpat loc "-" False s
      | "["; "]" -> <:patt< [] >>
      | "["; pl = LIST1 patt SEP ";"; last = cons_patt_opt; "]" ->
          mklistpat loc last pl
      | "[|"; pl = V (LIST0 patt SEP ";"); "|]" -> <:patt< [| $_list:pl$ |] >>
      | "{"; lpl = V (LIST1 label_patt SEP ";"); "}" ->
          <:patt< { $_list:lpl$ } >>
      | "("; p = paren_patt; ")" -> p
      | "_" -> <:patt< _ >> ] ]
  ;
  paren_patt:
    [ [ p = patt; ":"; t = ctyp -> <:patt< ($p$ : $t$) >>
      | p = patt; "as"; p2 = patt -> <:patt< ($p$ as $p2$) >>
      | p = patt; ","; pl = LIST1 patt SEP "," -> mktuppat loc p pl
      | p = patt -> <:patt< $p$ >>
      | pl = V (LIST1 patt SEP ",") -> <:patt< ($_list:pl$) >>
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
      [ i = V UIDENT -> <:patt< $_uid:i$ >>
      | i = V LIDENT -> <:patt< $_lid:i$ >> ] ]
  ;
  ipatt:
    [ [ "{"; lpl = V (LIST1 label_ipatt SEP ";"); "}" ->
          <:patt< { $_list:lpl$ } >>
      | "("; p = paren_ipatt; ")" -> p
      | s = V LIDENT -> <:patt< $_lid:s$ >>
      | "_" -> <:patt< _ >> ] ]
  ;
  paren_ipatt:
    [ [ p = ipatt; ":"; t = ctyp -> <:patt< ($p$ : $t$) >>
      | p = ipatt; "as"; p2 = ipatt -> <:patt< ($p$ as $p2$) >>
      | p = ipatt; ","; pl = LIST1 ipatt SEP "," -> mktuppat loc p pl
      | p = ipatt -> <:patt< $p$ >>
      | pl = V (LIST1 ipatt SEP ",") -> <:patt< ( $_list:pl$) >>
      | -> <:patt< () >> ] ]
  ;
  label_ipatt:
    [ [ i = patt_label_ident; "="; p = ipatt -> (i, p) ] ]
  ;
  type_declaration:
    [ [ n = type_patt; tpl = V (LIST0 type_parameter); "=";
        pf = V (FLAG "private"); tk = ctyp; cl = V (LIST0 constrain) ->
          {MLast.tdNam = n; MLast.tdPrm = tpl; MLast.tdPrv = pf;
           MLast.tdDef = tk; MLast.tdCon = cl} ] ]
  ;
  type_patt:
    [ [ n = V LIDENT -> (loc, n) ] ]
  ;
  constrain:
    [ [ "constraint"; t1 = ctyp; "="; t2 = ctyp -> (t1, t2) ] ]
  ;
  type_parameter:
    [ [ "'"; i = V ident "" -> (i, (False, False))
      | "+"; "'"; i = V ident "" -> (i, (True, False))
      | "-"; "'"; i = V ident "" -> (i, (False, True)) ] ]
  ;
  ctyp:
    [ "top"
      LEFTA
      [ t1 = SELF; "=="; t2 = SELF -> <:ctyp< $t1$ == $t2$ >> ]
    | "as"
      LEFTA
      [ t1 = SELF; "as"; t2 = SELF -> <:ctyp< $t1$ as $t2$ >> ]
    | LEFTA
      [ "!"; pl = V (LIST1 typevar); "."; t = ctyp ->
          <:ctyp< ! $_list:pl$ . $t$ >> ]
    | "arrow" RIGHTA
      [ t1 = SELF; "->"; t2 = SELF -> <:ctyp< $t1$ -> $t2$ >> ]
    | "apply" LEFTA
      [ t1 = SELF; t2 = SELF -> <:ctyp< $t1$ $t2$ >> ]
    | LEFTA
      [ t1 = SELF; "."; t2 = SELF -> <:ctyp< $t1$ . $t2$ >> ]
    | "simple"
      [ "'"; i = V ident "" -> <:ctyp< '$_:i$ >>
      | "_" -> <:ctyp< _ >>
      | i = V LIDENT -> <:ctyp< $_lid:i$ >>
      | i = V UIDENT -> <:ctyp< $_uid:i$ >>
      | "("; t = SELF; "*"; tl = LIST1 ctyp SEP "*"; ")" -> mktuptyp loc t tl
      | "("; t = SELF; ")" -> <:ctyp< $t$ >>
      | "("; tl = V (LIST1 ctyp SEP "*"); ")" -> <:ctyp< ( $_list:tl$ ) >>
      | "["; cdl = V (LIST0 constructor_declaration SEP "|"); "]" ->
          <:ctyp< [ $_list:cdl$ ] >>
      | "{"; ldl = V (LIST1 label_declaration SEP ";"); "}" ->
          <:ctyp< { $_list:ldl$ } >> ] ]
  ;
  constructor_declaration:
    [ [ ci = V UIDENT "uid" ""; "of"; cal = V (LIST1 ctyp SEP "and") ->
          (loc, ci, cal)
      | ci = V UIDENT "uid" "" ->
          (loc, ci, <:vala< [] >>) ] ]
  ;
  label_declaration:
    [ [ i = LIDENT; ":"; mf = FLAG "mutable"; t = ctyp ->
          mklabdecl loc i mf t ] ]
  ;
  ident:
    [ [ i = LIDENT -> mkident i
      | i = UIDENT -> mkident i ] ]
  ;
  mod_ident:
    [ RIGHTA
      [ i = UIDENT -> [mkident i]
      | i = LIDENT -> [mkident i]
      | i = UIDENT; "."; j = SELF -> [mkident i :: j] ] ]
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
  class_declaration:
    [ [ vf = V (FLAG "virtual"); i = V LIDENT; ctp = class_type_parameters;
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
    [ [ -> (loc, <:vala< [] >>)
      | "["; tpl = V (LIST1 type_parameter SEP ","); "]" -> (loc, tpl) ] ]
  ;
  class_fun_def:
    [ [ p = ipatt; ce = SELF -> <:class_expr< fun $p$ -> $ce$ >>
      | "->"; ce = class_expr -> ce ] ]
  ;
  class_expr:
    [ "top"
      [ "fun"; p = ipatt; ce = class_fun_def ->
          <:class_expr< fun $p$ -> $ce$ >>
      | "let"; rf = V (FLAG "rec"); lb = V (LIST1 let_binding SEP "and");
        "in"; ce = SELF ->
          <:class_expr< let $_flag:rf$ $_list:lb$ in $ce$ >> ]
    | "apply" LEFTA
      [ ce = SELF; e = expr LEVEL "label" ->
          <:class_expr< $ce$ $e$ >> ]
    | "simple"
      [ ci = V class_longident "list"; "["; ctcl = V (LIST1 ctyp SEP ",");
        "]" ->
          <:class_expr< $_list:ci$ [ $_list:ctcl$ ] >>
      | ci = V class_longident "list" ->
          <:class_expr< $_list:ci$ >>
      | "object"; cspo = V (OPT class_self_patt); cf = class_structure;
        "end" ->
          <:class_expr< object $_opt:cspo$ $_list:cf$ end >>
      | "("; ce = SELF; ":"; ct = class_type; ")" ->
          <:class_expr< ($ce$ : $ct$) >>
      | "("; ce = SELF; ")" -> ce ] ]
  ;
  class_structure:
    [ [ cf = V (LIST0 [ cf = class_str_item; ";" -> cf ]) -> cf ] ]
  ;
  class_self_patt:
    [ [ "("; p = patt; ")" -> p
      | "("; p = patt; ":"; t = ctyp; ")" -> <:patt< ($p$ : $t$) >> ] ]
  ;
  class_str_item:
    [ [ "declare"; st = V (LIST0 [ s= class_str_item; ";" -> s ]); "end" ->
          <:class_str_item< declare $_list:st$ end >>
      | "inherit"; ce = class_expr; pb = V (OPT as_lident) ->
          <:class_str_item< inherit $ce$ $_opt:pb$ >>
      | "value"; mf = V (FLAG "mutable"); lab = V label "lid" "";
        e = cvalue_binding ->
          <:class_str_item< value $_flag:mf$ $_lid:lab$ = $e$ >>
      | "method"; "virtual"; pf = V (FLAG "private"); l = V label "lid" "";
        ":"; t = ctyp ->
          <:class_str_item< method virtual $_flag:pf$ $_lid:l$ : $t$ >>
      | "method"; pf = V (FLAG "private"); l = V label "lid" "";
        topt = V (OPT polyt); e = fun_binding ->
          <:class_str_item< method $_flag:pf$ $_lid:l$ $_opt:topt$ = $e$ >>
      | "type"; t1 = ctyp; "="; t2 = ctyp ->
          <:class_str_item< type $t1$ = $t2$ >>
      | "initializer"; se = expr -> <:class_str_item< initializer $se$ >> ] ]
  ;
  as_lident:
    [ [ "as"; i = LIDENT -> mkident i ] ]
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
  label:
    [ [ i = LIDENT -> mkident i ] ]
  ;
  class_type:
    [ [ "["; t = ctyp; "]"; "->"; ct = SELF ->
          <:class_type< [ $t$ ] -> $ct$ >>
      | id = V clty_longident "list"; "["; tl = V (LIST1 ctyp SEP ","); "]" ->
          <:class_type< $_list:id$ [ $_list:tl$ ] >>
      | id = V clty_longident "list" -> <:class_type< $_list:id$ >>
      | "object"; cst = V (OPT class_self_type);
        csf = V (LIST0 [ csf = class_sig_item; ";" -> csf ]); "end" ->
          <:class_type< object $_opt:cst$ $_list:csf$ end >> ] ]
  ;
  class_self_type:
    [ [ "("; t = ctyp; ")" -> t ] ]
  ;
  class_sig_item:
    [ [ "declare"; st = V (LIST0 [ s = class_sig_item; ";" -> s ]); "end" ->
          <:class_sig_item< declare $_list:st$ end >>
      | "inherit"; cs = class_type -> <:class_sig_item< inherit $cs$ >>
      | "value"; mf = V (FLAG "mutable"); l = V label "lid" ""; ":";
        t = ctyp ->
          <:class_sig_item< value $_flag:mf$ $_lid:l$ : $t$ >>
      | "method"; "virtual"; pf = V (FLAG "private"); l = V label "lid" "";
        ":"; t = ctyp ->
          <:class_sig_item< method virtual $_flag:pf$ $_lid:l$ : $t$ >>
      | "method"; pf = V (FLAG "private"); l = V label "lid" ""; ":";
        t = ctyp ->
          <:class_sig_item< method $_flag:pf$ $_lid:l$ : $t$ >>
      | "type"; t1 = ctyp; "="; t2 = ctyp ->
          <:class_sig_item< type $t1$ = $t2$ >> ] ]
  ;
  class_description:
    [ [ vf = V (FLAG "virtual"); n = V LIDENT; ctp = class_type_parameters;
        ":"; ct = class_type ->
          {MLast.ciLoc = loc; MLast.ciVir = vf; MLast.ciPrm = ctp;
           MLast.ciNam = n; MLast.ciExp = ct} ] ]
  ;
  class_type_declaration:
    [ [ vf = V (FLAG "virtual"); n = V LIDENT; ctp = class_type_parameters;
        "="; cs = class_type ->
          {MLast.ciLoc = loc; MLast.ciVir = vf; MLast.ciPrm = ctp;
           MLast.ciNam = n; MLast.ciExp = cs} ] ]
  ;
  expr: LEVEL "apply"
    [ LEFTA
      [ "new"; i = V class_longident "list" -> <:expr< new $_list:i$ >>
      | "object"; cspo = V (OPT class_self_patt); cf = class_structure;
        "end" ->
          <:expr< object $_opt:cspo$ $_list:cf$ end >> ] ]
  ;
  expr: LEVEL "."
    [ [ e = SELF; "#"; lab = V label "lid" "" ->
          <:expr< $e$ # $_lid:lab$ >> ] ]
  ;
  expr: LEVEL "simple"
    [ [ "("; e = SELF; ":"; t = ctyp; ":>"; t2 = ctyp; ")" ->
          <:expr< ($e$ : $t$ :> $t2$ ) >>
      | "("; e = SELF; ":>"; t = ctyp; ")" -> <:expr< ($e$ :> $t$) >>
      | "{<"; fel = V (LIST0 field_expr SEP ";"); ">}" ->
          <:expr< {< $_list:fel$ >} >> ] ]
  ;
  field_expr:
    [ [ l = label; "="; e = expr -> (l, e) ] ]
  ;
  ctyp: LEVEL "simple"
    [ [ "#"; id = V class_longident "list" -> <:ctyp< # $_list:id$ >>
      | "<"; ml = V (LIST0 field SEP ";"); v = V (FLAG ".."); ">" ->
          <:ctyp< < $_list:ml$ $_flag:v$ > >> ] ]
  ;
  field:
    [ [ lab = LIDENT; ":"; t = ctyp -> (mkident lab, t) ] ]
  ;
  typevar:
    [ [ "'"; i = ident -> i ] ]
  ;
  clty_longident:
    [ [ m = UIDENT; "."; l = SELF -> [mkident m :: l]
      | i = LIDENT -> [mkident i] ] ]
  ;
  class_longident:
    [ [ m = UIDENT; "."; l = SELF -> [mkident m :: l]
      | i = LIDENT -> [mkident i] ] ]
  ;
  (* Labels *)
  ctyp: AFTER "arrow"
    [ NONA
      [ i = V TILDEIDENTCOLON; t = SELF -> <:ctyp< ~$_:i$: $t$ >>
      | i = V QUESTIONIDENTCOLON; t = SELF -> <:ctyp< ?$_:i$: $t$ >> ] ]
  ;
  ctyp: LEVEL "simple"
    [ [ "["; "="; rfl = poly_variant_list; "]" ->
          <:ctyp< [ = $_list:rfl$ ] >>
      | "["; ">"; rfl = poly_variant_list; "]" ->
          <:ctyp< [ > $_list:rfl$ ] >>
      | "["; "<"; rfl = poly_variant_list; "]" ->
          <:ctyp< [ < $_list:rfl$ ] >>
      | "["; "<"; rfl = poly_variant_list; ">"; ntl = V (LIST1 name_tag);
        "]" ->
          <:ctyp< [ < $_list:rfl$ > $_list:ntl$ ] >> ] ]
  ;
  poly_variant_list:
    [ [ rfl = V (LIST0 poly_variant SEP "|") -> rfl ] ]
  ;
  poly_variant:
    [ [ "`"; i = V ident "" -> <:poly_variant< ` $_:i$ >>
      | "`"; i = V ident ""; "of"; ao = V (FLAG "&");
        l = V (LIST1 ctyp SEP "&") ->
          <:poly_variant< ` $_:i$ of $_flag:ao$ $_list:l$ >>
      | t = ctyp -> <:poly_variant< $t$ >> ] ]
  ;
  name_tag:
    [ [ "`"; i = ident -> i ] ]
  ;
  patt: LEVEL "simple"
    [ [ "`"; s = V ident "" -> <:patt< ` $_:s$ >>
      | "#"; sl = V mod_ident "list" "" -> <:patt< # $_:sl$ >>
      | i = V TILDEIDENTCOLON; p = SELF -> <:patt< ~$_:i$: $p$ >>
      | i = V TILDEIDENT -> <:patt< ~$_:i$ >>
      | i = V QUESTIONIDENTCOLON; "("; p = patt_tcon; eo = V (OPT eq_expr);
        ")" ->
          <:patt< ?$_:i$: ($p$ $_opt:eo$) >>
      | i = V QUESTIONIDENT ->
          <:patt< ?$_:i$ >>
      | "?"; "("; p = patt_tcon; eo = V (OPT eq_expr); ")" ->
          <:patt< ? ($p$ $_opt:eo$) >> ] ]
  ;
  patt_tcon:
    [ [ p = patt; ":"; t = ctyp -> <:patt< ($p$ : $t$) >>
      | p = patt -> p ] ]
  ;
  ipatt:
    [ [ i = V TILDEIDENTCOLON; p = SELF -> <:patt< ~$_:i$: $p$ >>
      | i = V TILDEIDENT -> <:patt< ~$_:i$ >>
      | i = V QUESTIONIDENTCOLON; "("; p = ipatt_tcon;
        eo = V (OPT eq_expr); ")" ->
          <:patt< ?$_:i$: ($p$ $_opt:eo$) >>
      | i = V QUESTIONIDENT ->
          <:patt< ?$_:i$ >>
      | "?"; "("; p = ipatt_tcon; eo = V (OPT eq_expr); ")" ->
          <:patt< ? ($p$ $_opt:eo$) >> ] ]
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
      [ i = V TILDEIDENTCOLON; e = SELF -> <:expr< ~$_:i$: $e$ >>
      | i = V TILDEIDENT -> <:expr< ~$_:i$ >>
      | i = V QUESTIONIDENTCOLON; e = SELF -> <:expr< ?$_:i$: $e$ >>
      | i = V QUESTIONIDENT -> <:expr< ?$_:i$ >> ] ]
  ;
  expr: LEVEL "simple"
    [ [ "`"; s = V ident "" -> <:expr< ` $_:s$ >> ] ]
  ;
  direction_flag:
    [ [ "to" -> True
      | "downto" -> False ] ]
  ;
END;

value quotation_content s = do {
  loop 0 where rec loop i =
    if i = String.length s then ("", s)
    else if s.[i] = ':' || s.[i] = '@' then
      let i = i + 1 in
      (String.sub s 0 i, String.sub s i (String.length s - i))
    else loop (i + 1)
};

EXTEND
  GLOBAL: interf implem use_file top_phrase expr patt;
  interf:
    [ [ "#"; n = V LIDENT; dp = OPT expr; ";" ->
          ([(<:sig_item< # $_lid:n$ $opt:dp$ >>, loc)], True)
      | si = sig_item_semi; (sil, stopped) = SELF -> ([si :: sil], stopped)
      | EOI -> ([], False) ] ]
  ;
  sig_item_semi:
    [ [ si = sig_item; ";" -> (si, loc) ] ]
  ;
  implem:
    [ [ "#"; n = V LIDENT; dp = OPT expr; ";" ->
          ([(<:str_item< # $_lid:n$ $opt:dp$ >>, loc)], True)
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
          let con = quotation_content x in
          Pcaml.handle_expr_quotation loc con ] ]
  ;
  patt: LEVEL "simple"
    [ [ x = QUOTATION ->
          let con = quotation_content x in
          Pcaml.handle_patt_quotation loc con ] ]
  ;
END;
