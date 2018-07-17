(* camlp5r *)
(* q_MLast.ml,v *)
(* Copyright (c) INRIA 2007-2017 *)

#load "pa_extend.cmo";
#load "pa_extend_m.cmo";
#load "q_MLast.cmo";
#load "pa_macro.cmo";

IFDEF OCAML_VERSION <= OCAML_3_00 AND NOT COMPATIBLE_WITH_OLD_OCAML THEN
  #option "-split_ext";
END;

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
      if m = "" then <:expr< $uid:n$ >> else <:expr< $uid:m$ . $uid:n$ >>
    ;
    value patt_node m n =
      if m = "" then <:patt< $uid:n$ >> else <:patt< $uid:m$ . $uid:n$ >>
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

value module_type = Grammar.Entry.create gram "module_type";
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
value match_case = Grammar.Entry.create gram "match_case";
value constructor_declaration =
  Grammar.Entry.create gram "constructor_declaration";
value label_declaration =
  Grammar.Entry.create gram "label_declaration";

value with_constr = Grammar.Entry.create gram "with_constr";
value poly_variant = Grammar.Entry.create gram "poly_variant";

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
            Qast.Node "ExUid" [Qast.Loc; Qast.VaVal (Qast.Str "[]")]
        | a -> a ]
    | [e1 :: el] ->
        Qast.Node "ExApp"
          [Qast.Loc;
           Qast.Node "ExApp"
             [Qast.Loc;
              Qast.Node "ExUid" [Qast.Loc; Qast.VaVal (Qast.Str "::")]; e1];
           loop False el] ]
;

value mklistpat _ last =
  loop True where rec loop top =
    fun
    [ [] ->
        match last with
        [ Qast.Option (Some p) -> p
        | Qast.Option None ->
            Qast.Node "PaUid" [Qast.Loc; Qast.VaVal (Qast.Str "[]")]
        | a -> a ]
    | [p1 :: pl] ->
        Qast.Node "PaApp"
          [Qast.Loc;
           Qast.Node "PaApp"
             [Qast.Loc;
              Qast.Node "PaUid" [Qast.Loc; Qast.VaVal (Qast.Str "::")]; p1];
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

value mklabdecl _ i mf t = Qast.Tuple [Qast.Loc; Qast.Str i; Qast.Bool mf; t];
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

(* -- begin copy from pa_r to q_MLast -- *)

EXTEND
  GLOBAL: sig_item str_item ctyp patt expr module_type module_expr signature
    structure class_type class_expr class_sig_item class_str_item let_binding
    type_decl constructor_declaration label_declaration match_case ipatt
    with_constr poly_variant;
  module_expr:
    [ [ "functor"; "("; i = SV UIDENT; ":"; t = module_type; ")"; "->";
        me = SELF →
          Qast.Node "MeFun" [Qast.Loc; i; t; me]
      | "struct"; st = structure; /; "end" →
          Qast.Node "MeStr" [Qast.Loc; st] ]
    | [ me1 = SELF; me2 = SELF → Qast.Node "MeApp" [Qast.Loc; me1; me2] ]
    | [ me1 = SELF; "."; me2 = SELF → Qast.Node "MeAcc" [Qast.Loc; me1; me2] ]
    | "simple"
      [ i = SV UIDENT → Qast.Node "MeUid" [Qast.Loc; i]
      | "("; "value"; e = expr; ":"; mt = module_type; ")" →
          Qast.Node "MeUnp" [Qast.Loc; e; Qast.Option (Some mt)]
      | "("; "value"; e = expr; ")" →
          Qast.Node "MeUnp" [Qast.Loc; e; Qast.Option None]
      | "("; me = SELF; ":"; mt = module_type; ")" →
          Qast.Node "MeTyc" [Qast.Loc; me; mt]
      | "("; me = SELF; ")" → me ] ]
  ;
  structure:
    [ [ st = SV (LIST0 [ s = str_item; ";" → s ]) → st ] ]
  ;
  str_item:
    [ "top"
      [ "declare"; st = SV (LIST0 [ s = str_item; ";" → s ]); "end" →
          Qast.Node "StDcl" [Qast.Loc; st]
      | "exception"; ctl = constructor_declaration; b = rebind_exn →
          let (_, c, tl, _) =
            match ctl with
            [ Qast.Tuple [xx1; xx2; xx3; xx4] → (xx1, xx2, xx3, xx4)
            | _ → match () with [] ]
          in
          Qast.Node "StExc" [Qast.Loc; c; tl; b]
      | "external"; i = SV LIDENT; ":"; t = ctyp; "=";
        pd = SV (LIST1 STRING) →
          Qast.Node "StExt" [Qast.Loc; i; t; pd]
      | "include"; me = module_expr → Qast.Node "StInc" [Qast.Loc; me]
      | "module"; r = SV (FLAG "rec"); l = SV (LIST1 mod_binding SEP "and") →
          Qast.Node "StMod" [Qast.Loc; r; l]
      | "module"; "type"; i = SV ident ""; mt = mod_type_fun_binding →
          Qast.Node "StMty" [Qast.Loc; i; mt]
      | "open"; i = SV mod_ident "list" "" → Qast.Node "StOpn" [Qast.Loc; i]
      | "type"; nrfl = SV (FLAG "nonrec");
        tdl = SV (LIST1 type_decl SEP "and") →
          Qast.Node "StTyp" [Qast.Loc; nrfl; tdl]
      | "value"; r = SV (FLAG "rec"); l = SV (LIST1 let_binding SEP "and") →
          Qast.Node "StVal" [Qast.Loc; r; l]
      | "#"; n = SV LIDENT; dp = SV (OPT expr) →
          Qast.Node "StDir" [Qast.Loc; n; dp]
      | "#"; s = SV STRING;
        sil = SV (LIST0 [ si = str_item → Qast.Tuple [si; Qast.Loc] ]) →
          Qast.Node "StUse" [Qast.Loc; s; sil]
      | e = expr → Qast.Node "StExp" [Qast.Loc; e] ] ]
  ;
  rebind_exn:
    [ [ "="; a = SV mod_ident "list" "" → a
      | → Qast.VaVal (Qast.List []) ] ]
  ;
  mod_binding:
    [ [ i = SV UIDENT; me = mod_fun_binding → Qast.Tuple [i; me] ] ]
  ;
  mod_fun_binding:
    [ RIGHTA
      [ "("; m = SV UIDENT; ":"; mt = module_type; ")"; mb = SELF →
          Qast.Node "MeFun" [Qast.Loc; m; mt; mb]
      | ":"; mt = module_type; "="; me = module_expr →
          Qast.Node "MeTyc" [Qast.Loc; me; mt]
      | "="; me = module_expr → me ] ]
  ;
  mod_type_fun_binding:
    [ [ "("; m = SV UIDENT; ":"; mt1 = module_type; ")"; mt2 = SELF →
          Qast.Node "MtFun" [Qast.Loc; m; mt1; mt2]
      | "="; mt = module_type → mt ] ]
  ;
  module_type:
    [ [ "functor"; "("; i = SV UIDENT; ":"; t = SELF; ")"; "->"; mt = SELF →
          Qast.Node "MtFun" [Qast.Loc; i; t; mt] ]
    | [ mt = SELF; "with"; wcl = SV (LIST1 with_constr SEP "and") →
          Qast.Node "MtWit" [Qast.Loc; mt; wcl] ]
    | [ "sig"; sg = signature; /; "end" → Qast.Node "MtSig" [Qast.Loc; sg]
      | "module"; "type"; "of"; me = module_expr →
          Qast.Node "MtTyo" [Qast.Loc; me] ]
    | [ m1 = SELF; m2 = SELF → Qast.Node "MtApp" [Qast.Loc; m1; m2] ]
    | [ m1 = SELF; "."; m2 = SELF → Qast.Node "MtAcc" [Qast.Loc; m1; m2] ]
    | "simple"
      [ i = SV UIDENT → Qast.Node "MtUid" [Qast.Loc; i]
      | i = SV LIDENT → Qast.Node "MtLid" [Qast.Loc; i]
      | "'"; i = SV ident "" → Qast.Node "MtQuo" [Qast.Loc; i]
      | "("; mt = SELF; ")" → mt ] ]
  ;
  signature:
    [ [ st = SV (LIST0 [ s = sig_item; ";" → s ]) → st ] ]
  ;
  sig_item:
    [ "top"
      [ "declare"; st = SV (LIST0 [ s = sig_item; ";" → s ]); "end" →
          Qast.Node "SgDcl" [Qast.Loc; st]
      | "exception"; ctl = constructor_declaration →
          let (_, c, tl, _) =
            match ctl with
            [ Qast.Tuple [xx1; xx2; xx3; xx4] → (xx1, xx2, xx3, xx4)
            | _ → match () with [] ]
          in
          Qast.Node "SgExc" [Qast.Loc; c; tl]
      | "external"; i = SV LIDENT; ":"; t = ctyp; "=";
        pd = SV (LIST1 STRING) →
          Qast.Node "SgExt" [Qast.Loc; i; t; pd]
      | "include"; mt = module_type → Qast.Node "SgInc" [Qast.Loc; mt]
      | "module"; rf = SV (FLAG "rec");
        l = SV (LIST1 mod_decl_binding SEP "and") →
          Qast.Node "SgMod" [Qast.Loc; rf; l]
      | "module"; "type"; i = SV ident ""; "="; mt = module_type →
          Qast.Node "SgMty" [Qast.Loc; i; mt]
      | "open"; i = SV mod_ident "list" "" → Qast.Node "SgOpn" [Qast.Loc; i]
      | "type"; tdl = SV (LIST1 type_decl SEP "and") →
          Qast.Node "SgTyp" [Qast.Loc; tdl]
      | "value"; i = SV LIDENT; ":"; t = ctyp →
          Qast.Node "SgVal" [Qast.Loc; i; t]
      | "#"; n = SV LIDENT; dp = SV (OPT expr) →
          Qast.Node "SgDir" [Qast.Loc; n; dp]
      | "#"; s = SV STRING;
        sil = SV (LIST0 [ si = sig_item → Qast.Tuple [si; Qast.Loc] ]) →
          Qast.Node "SgUse" [Qast.Loc; s; sil] ] ]
  ;
  mod_decl_binding:
    [ [ i = SV UIDENT; mt = module_declaration → Qast.Tuple [i; mt] ] ]
  ;
  module_declaration:
    [ RIGHTA
      [ ":"; mt = module_type → mt
      | "("; i = SV UIDENT; ":"; t = module_type; ")"; mt = SELF →
          Qast.Node "MtFun" [Qast.Loc; i; t; mt] ] ]
  ;
  with_constr:
    [ [ "type"; i = SV mod_ident "list" ""; tpl = SV (LIST0 type_parameter);
        "="; pf = SV (FLAG "private"); t = ctyp →
          Qast.Node "WcTyp" [Qast.Loc; i; tpl; pf; t]
      | "type"; i = SV mod_ident "list" ""; tpl = SV (LIST0 type_parameter);
        ":="; t = ctyp →
          Qast.Node "WcTys" [Qast.Loc; i; tpl; t]
      | "module"; i = SV mod_ident "list" ""; "="; me = module_expr →
          Qast.Node "WcMod" [Qast.Loc; i; me]
      | "module"; i = SV mod_ident "list" ""; ":="; me = module_expr →
          Qast.Node "WcMos" [Qast.Loc; i; me] ] ]
  ;
  expr:
    [ "top" RIGHTA
      [ "let"; r = SV (FLAG "rec"); l = SV (LIST1 let_binding SEP "and");
        "in"; x = SELF →
          Qast.Node "ExLet" [Qast.Loc; r; l; x]
      | "let"; "module"; m = SV UIDENT; mb = mod_fun_binding; "in"; e = SELF →
          Qast.Node "ExLmd" [Qast.Loc; m; mb; e]
      | "let"; "open"; m = module_expr; "in"; e = SELF →
          Qast.Node "ExLop" [Qast.Loc; m; e]
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
      | "for"; i = SV LIDENT; "="; e1 = SELF; df = SV direction_flag "to";
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
      [ e1 = SELF; "."; "("; e2 = SELF; ")" →
          Qast.Node "ExAre" [Qast.Loc; e1; e2]
      | e1 = SELF; "."; "["; e2 = SELF; "]" →
          Qast.Node "ExSte" [Qast.Loc; e1; e2]
      | e = SELF; "."; "{"; el = SV (LIST1 expr SEP ","); "}" →
          Qast.Node "ExBae" [Qast.Loc; e; el]
      | e1 = SELF; "."; e2 = SELF → Qast.Node "ExAcc" [Qast.Loc; e1; e2] ]
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
      | i = SV LIDENT → Qast.Node "ExLid" [Qast.Loc; i]
      | i = SV GIDENT → Qast.Node "ExLid" [Qast.Loc; i]
      | i = SV UIDENT → Qast.Node "ExUid" [Qast.Loc; i]
      | "["; "]" → Qast.Node "ExUid" [Qast.Loc; Qast.VaVal (Qast.Str "[]")]
      | "["; el = LIST1 expr SEP ";"; last = cons_expr_opt; "]" →
          mklistexp Qast.Loc last el
      | "[|"; el = SV (LIST0 expr SEP ";"); "|]" →
          Qast.Node "ExArr" [Qast.Loc; el]
      | "{"; lel = SV (LIST1 label_expr SEP ";"); "}" →
          Qast.Node "ExRec" [Qast.Loc; lel; Qast.Option None]
      | "{"; "("; e = SELF; ")"; "with"; lel = SV (LIST1 label_expr SEP ";");
        "}" →
          Qast.Node "ExRec" [Qast.Loc; lel; Qast.Option (Some e)]
      | "("; ")" → Qast.Node "ExUid" [Qast.Loc; Qast.VaVal (Qast.Str "()")]
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
      | "let"; "module"; m = SV UIDENT; mb = mod_fun_binding; "in";
        el = SELF →
          Qast.List
            [Qast.Node "ExLmd" [Qast.Loc; m; mb; mksequence Qast.Loc el]]
      | "let"; "open"; m = module_expr; "in"; el = SELF →
          Qast.List [Qast.Node "ExLop" [Qast.Loc; m; mksequence Qast.Loc el]]
      | e = expr; ";"; el = SELF → Qast.Cons e el
      | e = expr; ";" → Qast.List [e]
      | e = expr → Qast.List [e] ] ]
  ;
  let_binding:
    [ [ p = ipatt; e = fun_binding → Qast.Tuple [p; e] ] ]
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
          mkmatchcase Qast.Loc p aso w e ] ]
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
  patt:
    [ LEFTA
      [ p1 = SELF; "|"; p2 = SELF → Qast.Node "PaOrp" [Qast.Loc; p1; p2] ]
    | NONA
      [ p1 = SELF; ".."; p2 = SELF → Qast.Node "PaRng" [Qast.Loc; p1; p2] ]
    | LEFTA
      [ p1 = SELF; p2 = SELF → Qast.Node "PaApp" [Qast.Loc; p1; p2]
      | "lazy"; p = SELF → Qast.Node "PaLaz" [Qast.Loc; p] ]
    | LEFTA
      [ p1 = SELF; "."; p2 = SELF → Qast.Node "PaAcc" [Qast.Loc; p1; p2] ]
    | "simple"
      [ s = SV LIDENT → Qast.Node "PaLid" [Qast.Loc; s]
      | s = SV GIDENT → Qast.Node "PaLid" [Qast.Loc; s]
      | s = SV UIDENT → Qast.Node "PaUid" [Qast.Loc; s]
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
      | "["; "]" → Qast.Node "PaUid" [Qast.Loc; Qast.VaVal (Qast.Str "[]")]
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
      | "module"; s = SV UIDENT; ":"; mt = module_type →
          Qast.Node "PaUnp" [Qast.Loc; s; Qast.Option (Some mt)]
      | "module"; s = SV UIDENT →
          Qast.Node "PaUnp" [Qast.Loc; s; Qast.Option None]
      | → Qast.Node "PaUid" [Qast.Loc; Qast.VaVal (Qast.Str "()")] ] ]
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
      [ p1 = SELF; "."; p2 = SELF → Qast.Node "PaAcc" [Qast.Loc; p1; p2] ]
    | "simple" RIGHTA
      [ i = SV UIDENT → Qast.Node "PaUid" [Qast.Loc; i]
      | i = SV LIDENT → Qast.Node "PaLid" [Qast.Loc; i]
      | "_" → Qast.Node "PaAny" [Qast.Loc] ] ]
  ;
  ipatt:
    [ [ "{"; lpl = SV (LIST1 label_ipatt SEP ";"); "}" →
          Qast.Node "PaRec" [Qast.Loc; lpl]
      | "("; p = paren_ipatt; ")" → p
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
      | "module"; s = SV UIDENT; ":"; mt = module_type →
          Qast.Node "PaUnp" [Qast.Loc; s; Qast.Option (Some mt)]
      | "module"; s = SV UIDENT →
          Qast.Node "PaUnp" [Qast.Loc; s; Qast.Option None]
      | → Qast.Node "PaUid" [Qast.Loc; Qast.VaVal (Qast.Str "()")] ] ]
  ;
  label_ipatt:
    [ [ i = patt_label_ident; "="; p = ipatt → Qast.Tuple [i; p] ] ]
  ;
  type_decl:
    [ [ n = SV type_patt "tp"; tpl = SV (LIST0 type_parameter); "=";
        pf = SV (FLAG "private") "priv"; tk = ctyp;
        cl = SV (LIST0 constrain) →
          Qast.Record
            [("tdNam", n); ("tdPrm", tpl); ("tdPrv", pf); ("tdDef", tk);
             ("tdCon", cl)] ] ]
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
  ctyp:
    [ "top" LEFTA
      [ t1 = SELF; "=="; pf = SV (FLAG "private") "priv"; t2 = SELF →
          Qast.Node "TyMan" [Qast.Loc; t1; pf; t2] ]
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
      [ t1 = SELF; "."; t2 = SELF → Qast.Node "TyAcc" [Qast.Loc; t1; t2] ]
    | "simple"
      [ "'"; i = SV ident "" → Qast.Node "TyQuo" [Qast.Loc; i]
      | i = GIDENT →
          Qast.Node "TyQuo" [Qast.Loc; Qast.VaVal (greek_ascii_equiv i)]
      | "_" → Qast.Node "TyAny" [Qast.Loc]
      | i = SV LIDENT → Qast.Node "TyLid" [Qast.Loc; i]
      | i = SV UIDENT → Qast.Node "TyUid" [Qast.Loc; i]
      | "module"; mt = module_type → Qast.Node "TyPck" [Qast.Loc; mt]
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
  constructor_declaration:
    [ [ ci = SV UIDENT; "of"; cal = SV (LIST1 ctyp SEP "and") →
          Qast.Tuple [Qast.Loc; ci; cal; Qast.Option None]
      | ci = SV UIDENT; ":"; t = ctyp →
          let (tl, rt) = generalized_type_of_type t in
          Qast.Tuple [Qast.Loc; ci; Qast.VaVal tl; Qast.Option (Some rt)]
      | ci = SV UIDENT →
          Qast.Tuple
            [Qast.Loc; ci; Qast.VaVal (Qast.List []); Qast.Option None] ] ]
  ;
  label_declaration:
    [ [ i = LIDENT; ":"; mf = FLAG "mutable"; t = ctyp →
          mklabdecl Qast.Loc i mf t ] ]
  ;
  ident:
    [ [ i = LIDENT → mkident i
      | i = UIDENT → mkident i ] ]
  ;
  mod_ident:
    [ RIGHTA
      [ i = UIDENT → Qast.List [mkident i]
      | i = LIDENT → Qast.List [mkident i]
      | i = UIDENT; "."; j = SELF → Qast.Cons (mkident i) j ] ]
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
        cfb = class_fun_binding →
          Qast.Record
            [("ciLoc", Qast.Loc); ("ciVir", vf); ("ciPrm", ctp); ("ciNam", i);
             ("ciExp", cfb)] ] ]
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
          Qast.Node "CeLet" [Qast.Loc; rf; lb; ce] ]
    | "apply" LEFTA
      [ ce = SELF; e = expr LEVEL "label" →
          Qast.Node "CeApp" [Qast.Loc; ce; e] ]
    | "simple"
      [ ci = SV class_longident "list" →
          Qast.Node "CeCon" [Qast.Loc; ci; Qast.VaVal (Qast.List [])]
      | "object"; cspo = SV (OPT class_self_patt); cf = class_structure;
        "end" →
          Qast.Node "CeStr" [Qast.Loc; cspo; cf]
      | "["; ctcl = SV (LIST1 ctyp SEP ","); "]";
        ci = SV class_longident "list" →
          Qast.Node "CeCon" [Qast.Loc; ci; ctcl]
      | "("; ce = SELF; ":"; ct = class_type; ")" →
          Qast.Node "CeTyc" [Qast.Loc; ce; ct]
      | "("; ce = SELF; ")" → ce ] ]
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
      | "inherit"; ce = class_expr; pb = SV (OPT as_lident) →
          Qast.Node "CrInh" [Qast.Loc; ce; pb]
      | "value"; ovf = SV (FLAG "!") "!"; mf = SV (FLAG "mutable");
        lab = SV lident "lid" ""; e = cvalue_binding →
          Qast.Node "CrVal" [Qast.Loc; ovf; mf; lab; e]
      | "value"; "virtual"; mf = SV (FLAG "mutable");
        lab = SV lident "lid" ""; ":"; t = ctyp →
          Qast.Node "CrVav" [Qast.Loc; mf; lab; t]
      | "method"; "virtual"; pf = SV (FLAG "private"); l = SV lident "lid" "";
        ":"; t = ctyp →
          Qast.Node "CrVir" [Qast.Loc; pf; l; t]
      | "method"; ovf = SV (FLAG "!") "!"; pf = SV (FLAG "private") "priv";
        l = SV lident "lid" ""; topt = SV (OPT polyt); e = fun_binding →
          Qast.Node "CrMth" [Qast.Loc; ovf; pf; l; topt; e]
      | "type"; t1 = ctyp; "="; t2 = ctyp →
          Qast.Node "CrCtr" [Qast.Loc; t1; t2]
      | "initializer"; se = expr → Qast.Node "CrIni" [Qast.Loc; se] ] ]
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
      | "object"; cst = SV (OPT class_self_type);
        csf = SV (LIST0 [ csf = class_sig_item; ";" → csf ]); "end" →
          Qast.Node "CtSig" [Qast.Loc; cst; csf]
      | ct = SELF; "["; tl = SV (LIST1 ctyp SEP ","); "]" →
          Qast.Node "CtCon" [Qast.Loc; ct; tl] ]
    | "apply"
      [ ct1 = SELF; ct2 = SELF → Qast.Node "CtApp" [Qast.Loc; ct1; ct2] ]
    | "dot"
      [ ct1 = SELF; "."; ct2 = SELF → Qast.Node "CtAcc" [Qast.Loc; ct1; ct2] ]
    | "simple"
      [ i = SV LIDENT "id" → Qast.Node "CtIde" [Qast.Loc; i]
      | i = SV UIDENT "id" → Qast.Node "CtIde" [Qast.Loc; i]
      | "("; ct = SELF; ")" → ct ] ]
  ;
  class_self_type:
    [ [ "("; t = ctyp; ")" → t ] ]
  ;
  class_sig_item:
    [ [ "declare"; st = SV (LIST0 [ s = class_sig_item; ";" → s ]); "end" →
          Qast.Node "CgDcl" [Qast.Loc; st]
      | "inherit"; cs = class_type → Qast.Node "CgInh" [Qast.Loc; cs]
      | "value"; mf = SV (FLAG "mutable"); l = SV lident "lid" ""; ":";
        t = ctyp →
          Qast.Node "CgVal" [Qast.Loc; mf; l; t]
      | "method"; "virtual"; pf = SV (FLAG "private"); l = SV lident "lid" "";
        ":"; t = ctyp →
          Qast.Node "CgVir" [Qast.Loc; pf; l; t]
      | "method"; pf = SV (FLAG "private"); l = SV lident "lid" ""; ":";
        t = ctyp →
          Qast.Node "CgMth" [Qast.Loc; pf; l; t]
      | "type"; t1 = ctyp; "="; t2 = ctyp →
          Qast.Node "CgCtr" [Qast.Loc; t1; t2] ] ]
  ;
  class_description:
    [ [ vf = SV (FLAG "virtual"); n = SV LIDENT; ctp = class_type_parameters;
        ":"; ct = class_type →
          Qast.Record
            [("ciLoc", Qast.Loc); ("ciVir", vf); ("ciPrm", ctp); ("ciNam", n);
             ("ciExp", ct)] ] ]
  ;
  class_type_declaration:
    [ [ vf = SV (FLAG "virtual"); n = SV LIDENT; ctp = class_type_parameters;
        "="; cs = class_type →
          Qast.Record
            [("ciLoc", Qast.Loc); ("ciVir", vf); ("ciPrm", ctp); ("ciNam", n);
             ("ciExp", cs)] ] ]
  ;
  expr: LEVEL "apply"
    [ LEFTA
      [ "new"; i = SV class_longident "list" → Qast.Node "ExNew" [Qast.Loc; i]
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
    [ [ "#"; id = SV class_longident "list" → Qast.Node "TyCls" [Qast.Loc; id]
      | "<"; ml = SV (LIST0 field SEP ";"); v = SV (FLAG ".."); ">" →
          Qast.Node "TyObj" [Qast.Loc; ml; v] ] ]
  ;
  field:
    [ [ lab = LIDENT; ":"; t = ctyp → Qast.Tuple [mkident lab; t] ] ]
  ;
  class_longident:
    [ [ m = UIDENT; "."; l = SELF → Qast.Cons (mkident m) l
      | i = LIDENT → Qast.List [mkident i] ] ]
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
    [ [ "`"; i = SV ident "" →
          Qast.Node "PvTag"
            [Qast.Loc; i; Qast.VaVal (Qast.Bool True);
             Qast.VaVal (Qast.List [])]
      | "`"; i = SV ident ""; "of"; ao = SV (FLAG "&");
        l = SV (LIST1 ctyp SEP "&") →
          Qast.Node "PvTag" [Qast.Loc; i; ao; l]
      | t = ctyp → Qast.Node "PvInh" [Qast.Loc; t] ] ]
  ;
  name_tag:
    [ [ "`"; i = ident → i ] ]
  ;
  patt: LEVEL "simple"
    [ [ "`"; s = SV ident "" → Qast.Node "PaVrn" [Qast.Loc; s]
      | "#"; sl = SV mod_ident "list" "" → Qast.Node "PaTyp" [Qast.Loc; sl]
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
  str_item:
    [ [ "def"; jal = SV (LIST1 joinautomaton SEP "and") →
          Qast.Node "StDef" [Qast.Loc; jal] ] ]
  ;
  expr: LEVEL "top"
    [ [ "def"; jal = SV (LIST1 joinautomaton SEP "and"); "in";
        e = expr LEVEL "top" →
          Qast.Node "ExJdf" [Qast.Loc; jal; e] ] ]
  ;
  expr: LEVEL "apply"
    [ [ "reply"; eo = SV (OPT expr); "to"; ji = SV joinident "jid" →
          Qast.Node "ExRpl" [Qast.Loc; eo; ji] ] ]
  ;
  expr: BEFORE ":="
    [ [ "spawn"; e = SELF → Qast.Node "ExSpw" [Qast.Loc; e] ] ]
  ;
  expr: LEVEL "&&"
    [ [ e1 = SELF; "&"; e2 = SELF → Qast.Node "ExPar" [Qast.Loc; e1; e2] ] ]
  ;
  joinautomaton:
    [ [ jcl = SV (LIST1 joinclause SEP "or") →
          Qast.Record [("jcLoc", Qast.Loc); ("jcVal", jcl)] ] ]
  ;
  joinclause:
    [ [ jpl = SV (LIST1 joinpattern SEP "&"); "="; e = expr →
          Qast.Tuple [Qast.Loc; jpl; e] ] ]
  ;
  joinpattern:
    [ [ ji = joinident; "("; op = SV (OPT patt); ")" →
          Qast.Tuple [Qast.Loc; ji; op] ] ]
  ;
  joinident:
    [ [ i = SV LIDENT → Qast.Tuple [Qast.Loc; i] ] ]
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
      | a = ANTIQUOT -> Qast.VaAnt "" loc a ] ]
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
        | x -> x ]
      else qast
    in
    Qast.to_patt (m ()) qast
  in
  Quotation.ExAst (expr, patt)
;

let sig_item_eoi = Grammar.Entry.create gram "sig_item_eoi" in
let str_item_eoi = Grammar.Entry.create gram "str_item_eoi" in
let ctyp_eoi = Grammar.Entry.create gram "ctyp_eoi" in
let patt_eoi = Grammar.Entry.create gram "patt_eoi" in
let expr_eoi = Grammar.Entry.create gram "expr_eoi" in
let module_type_eoi = Grammar.Entry.create gram "module_type_eoi" in
let module_expr_eoi = Grammar.Entry.create gram "module_expr_eoi" in
let class_type_eoi = Grammar.Entry.create gram "class_type_eoi" in
let class_expr_eoi = Grammar.Entry.create gram "class_expr_eoi" in
let class_sig_item_eoi = Grammar.Entry.create gram "class_sig_item_eoi" in
let class_str_item_eoi = Grammar.Entry.create gram "class_str_item_eoi" in
let with_constr_eoi = Grammar.Entry.create gram "with_constr_eoi" in
let poly_variant_eoi = Grammar.Entry.create gram "poly_variant_eoi" in
let type_decl_eoi = Grammar.Entry.create gram "type_decl_eoi" in
do {
  EXTEND
    sig_item_eoi: [ [ x = sig_item; EOI -> x ] ];
    str_item_eoi: [ [ x = str_item; EOI -> x ] ];
    ctyp_eoi: [ [ x = ctyp; EOI -> x ] ];
    patt_eoi: [ [ x = patt; EOI -> x ] ];
    expr_eoi: [ [ x = expr; EOI -> x ] ];
    module_type_eoi: [ [ x = module_type; EOI -> x ] ];
    module_expr_eoi: [ [ x = module_expr; EOI -> x ] ];
    class_type_eoi: [ [ x = class_type; EOI -> x ] ];
    class_expr_eoi: [ [ x = class_expr; EOI -> x ] ];
    class_sig_item_eoi: [ [ x = class_sig_item; EOI -> x ] ];
    class_str_item_eoi: [ [ x = class_str_item; EOI -> x ] ];
    with_constr_eoi: [ [ x = with_constr; EOI -> x ] ];
    poly_variant_eoi: [ [ x = poly_variant; EOI -> x ] ];
    type_decl_eoi: [ [ x = type_decl; EOI -> x ] ];
  END;
  List.iter (fun (q, f) -> Quotation.add q (f q))
    [("sig_item", apply_entry sig_item_eoi);
     ("str_item", apply_entry str_item_eoi);
     ("ctyp", apply_entry ctyp_eoi);
     ("patt", apply_entry patt_eoi);
     ("expr", apply_entry expr_eoi);
     ("module_type", apply_entry module_type_eoi);
     ("module_expr", apply_entry module_expr_eoi);
     ("class_type", apply_entry class_type_eoi);
     ("class_expr", apply_entry class_expr_eoi);
     ("class_sig_item", apply_entry class_sig_item_eoi);
     ("class_str_item", apply_entry class_str_item_eoi);
     ("with_constr", apply_entry with_constr_eoi);
     ("poly_variant", apply_entry poly_variant_eoi);
     ("type_decl", apply_entry type_decl_eoi)];
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
