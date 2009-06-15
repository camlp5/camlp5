(* camlp5r pa_extend.cmo pa_fstream.cmo q_MLast.cmo *)
(* $Id: pa_extprint.ml,v 1.44 2007/12/24 16:45:03 deraugla Exp $ *)
(* Copyright (c) INRIA 2007 *)

open Pcaml;

(** Types and Functions for [EXTEND_PRINTER] statement *)

type entry 'e 'p = { name : 'e; pos : option 'e; levels : list (level 'e 'p) }
and level 'e 'p = { label : option string; rules : list (rule 'e 'p) }
and rule 'e 'p = ('p * option 'e * 'e);

value not_impl name x = do {
  let desc =
    if Obj.is_block (Obj.repr x) then
      "tag = " ^ string_of_int (Obj.tag (Obj.repr x))
    else "int_val = " ^ string_of_int (Obj.magic x)
  in
  print_newline ();
  failwith ("pa_extprint: not impl " ^ name ^ " " ^ desc)
};

value rec mexpr p =
  let loc = MLast.loc_of_patt p in
  match p with
  [ <:patt< $p1$ $p2$ >> ->
      loop <:expr< [$mexpr p2$] >> p1 where rec loop el =
        fun
        [ <:patt< $p1$ $p2$ >> -> loop <:expr< [$mexpr p2$ :: $el$] >> p1
        | p -> <:expr< Extfun.Eapp [$mexpr p$ :: $el$] >> ]
  | <:patt< $p1$ . $p2$ >> ->
      loop <:expr< [$mexpr p2$] >> p1 where rec loop el =
        fun
        [ <:patt< $p1$ . $p2$ >> -> loop <:expr< [$mexpr p2$ :: $el$] >> p1
        | p -> <:expr< Extfun.Eacc [$mexpr p$ :: $el$] >> ]
  | <:patt< ($list:pl$) >> -> <:expr< Extfun.Etup $mexpr_list loc pl$ >>
  | <:patt< $uid:id$ >> -> <:expr< Extfun.Econ $str:id$ >>
  | <:patt< ` $id$ >> -> <:expr< Extfun.Econ $str:id$ >>
  | <:patt< $int:s$ >> -> <:expr< Extfun.Eint $str:s$ >>
  | <:patt< $str:s$ >> -> <:expr< Extfun.Estr $str:s$ >>
  | <:patt< ($p1$ as $_$) >> -> mexpr p1
  | <:patt< $lid:_$ >> -> <:expr< Extfun.Evar () >>
  | <:patt< _ >> -> <:expr< Extfun.Evar () >>
  | <:patt< $p1$ | $p2$ >> ->
      Ploc.raise loc (Failure "or patterns not allowed in extfun")
  | p -> not_impl "mexpr" p ]
and mexpr_list loc =
  fun
  [ [] -> <:expr< [] >>
  | [e :: el] -> <:expr< [$mexpr e$ :: $mexpr_list loc el$] >> ]
;

value rec split_or =
  fun
  [ [(<:patt< $p1$ | $p2$ >>, wo, e) :: pel] ->
      split_or [(p1, wo, e); (p2, wo, e) :: pel]
  | [(<:patt< ($p1$ | $p2$ as $p$) >>, wo, e) :: pel] ->
      let p1 =
        let loc = MLast.loc_of_patt p1 in
        <:patt< ($p1$ as $p$) >>
      in
      let p2 =
        let loc = MLast.loc_of_patt p2 in
        <:patt< ($p2$ as $p$) >>
      in
      split_or [(p1, wo, e); (p2, wo, e) :: pel]
  | [pe :: pel] -> [pe :: split_or pel]
  | [] -> [] ]
;

value rec catch_any =
  fun
  [ <:patt< $uid:id$ >> -> False
  | <:patt< ` $_$ >> -> False
  | <:patt< $lid:_$ >> -> True
  | <:patt< _ >> -> True
  | <:patt< ($list:pl$) >> -> List.for_all catch_any pl
  | <:patt< $p1$ $p2$ >> -> False
  | <:patt< $p1$ | $p2$ >> -> False
  | <:patt< $int:_$ >> -> False
  | <:patt< $str:_$ >> -> False
  | <:patt< ($p1$ as $_$) >> -> catch_any p1
  | p -> not_impl "catch_any" p ]
;

value conv loc (p, wo, e) =
  let tst = mexpr p in
  let e = <:expr< fun curr next pc -> $e$ >> in
  let e =
    if wo = None && catch_any p then <:expr< fun $p$ -> Some $e$ >>
    else <:expr< fun [ $p$ $opt:wo$ -> Some $e$ | _ -> None ] >>
  in
  <:expr< ($tst$, False, $e$) >>
;

value text_of_extprint loc el =
  let el =
    List.map
      (fun e ->
         let pos =
           match e.pos with
           [ Some e -> <:expr< Some $e$ >>
           | None -> <:expr< None >> ]
         in
         let levs =
           List.fold_right
             (fun lev levs ->
                let lab =
                  match lev.label with
                  [ Some s -> <:expr< Some $str:s$ >>
                  | None -> <:expr< None >> ]
                in
                let rules = split_or lev.rules in
                let rules =
                  match List.rev rules with
                  [ [(p, wo, _) :: _] ->
                      if wo = None && catch_any p then rules
                      else
                        let r = (<:patt< z >>, None, <:expr< next pc z >>) in
                        List.rev [r :: rules]
                  | [] ->
                      let r = (<:patt< z >>, None, <:expr< next pc z >>) in
                      [r] ]
                in
                let rules =
                  List.fold_right
                    (fun pe rules ->
                       let rule = conv loc pe in
                       <:expr< [$rule$ :: $rules$] >>)
                    rules <:expr< [] >>
                in
                let rules = <:expr< fun e__ -> Extfun.extend e__ $rules$ >> in
                <:expr< [($lab$, $rules$) :: $levs$] >>)
             e.levels <:expr< [] >>
         in
         <:expr< Eprinter.extend $e.name$ $pos$ $levs$ >>)
      el
  in
  match el with
  [ [e] -> e
  | _ -> <:expr< do { $list:el$ } >> ]
;

(** Types and Functions for [pprintf] statement *)

type break = [ PPbreak of int and int | PPspace ];
type paren_param = [ PPoffset of int | PPall of bool | PPnone ];

type tree =
  [ Tempty
  | Tlist of tree and tree and list tree
  | Tnode of break and tree and tree
  | Tparen of paren_param and tree
  | Tstring of string and list (bool * string) ]
;

value implode l =
  let s = String.create (List.length l) in
  loop 0 l where rec loop i =
    fun
    [ [c :: l] -> do { String.set s i c; loop (i + 1) l }
    | [] -> s ]
;

value rec parse_int_loop n =
  fparser
  [ [: `('0'..'9' as c);
       n = parse_int_loop (10 * n + Char.code c - Char.code '0') :] -> n
  | [: :] -> n ]
;

value parse_int =
  fparser
    [: `('0'..'9' as c);
       n = parse_int_loop (Char.code c - Char.code '0') :] ->
      n
;

value rec parse_pformat =
  fparser
  [ [: `'%'; `'p'; (cl, sl) = parse_pformat :] ->
      ([], [(False, implode cl) :: sl])
  | [: `'%'; `'q'; (cl, sl) = parse_pformat :] ->
      ([], [(True, implode cl) :: sl])
  | [: `c; (cl, sl) = parse_pformat :] ->
      ([c :: cl], sl)
  | [: :] ->
      ([], []) ]
;

value pformat_of_char_list cl =
  match parse_pformat (Fstream.of_list cl) with
  [ Some ((cl, sl), _) -> Tstring (implode cl) sl
  | None -> assert False ]
;

value parse_break =
  fparser
  [ [: `'@'; `';'; `'<'; sp = parse_int; `' '; off = parse_int; `'>' :] ->
      PPbreak sp off
  | [: `'@'; `';' :] ->
      PPbreak 1 2
  | [: `'@'; `' ' :] ->
      PPspace ]
;

value parse_paren_param =
  fparser
  [ [: `'<'; off = parse_int; `'>' :] -> PPoffset off
  | [: `'<'; `('a' | 'b' as c); `'>' :] -> PPall (c = 'b')
  | [: :] -> PPnone ]
;

value rec parse_string strm =
  match Fstream.next strm with
  [ Some ('@', strm1) ->
      match Fstream.next strm1 with
      [ Some ('[' | ']' | ';' | ' ', _) -> None
      | Some (c, strm) ->
          let (cl, strm) =
            match parse_string strm with
            [ Some (cl, strm) -> (cl, strm)
            | None -> ([], strm) ]
          in
          let cl =
            let cl = [c :: cl] in
            if c = '@' then cl else ['@' :: cl]
          in
          Some (cl, strm)
      | None ->
          Some (['@'], strm1) ]
  | Some (c, strm) ->
      let (cl, strm) =
        match parse_string strm with
        [ Some (cl, strm) -> (cl, strm)
        | None -> ([], strm) ]
      in
      Some ([c :: cl], strm)
  | None ->
      None ]
;

value rec parse_format =
  fparser
  [ [: t = parse_simple_format; t = parse_format_kont t :] -> t ]
and parse_format_kont t1 =
  fparser
  [ [: b = parse_break; t2 = parse_simple_format;
       t = parse_format_kont (Tnode b t1 t2) :] -> t
  | [: :] -> t1 ]
and parse_simple_format =
  fparser
  [ [: tl = parse_atom_list :] ->
      match tl with
      [ [] -> Tempty
      | [t] -> t
      | [t1; t2 :: tl] -> Tlist t1 t2 tl ] ]
and parse_atom_list =
  fparser
  [ [: t = parse_atom; tl = parse_atom_list :] -> [t :: tl]
  | [: :] -> [] ]
and parse_atom =
  fparser
  [ [: `'@'; `'['; pp = parse_paren_param; t = parse_format;
       _ = end_paren :] ->
      Tparen pp t
  | [: cl = parse_string :] ->
      pformat_of_char_list cl ]
and end_paren =
  fparser
  [ [: `'@'; `']' :] -> ()
  | [: :] -> () ]
;

value make_pc loc erase_bef erase_aft is_empty_bef is_empty_aft pc bef bef_al
    aft aft_al a_dang =
  let lbl =
    if not erase_bef && bef = "" then []
    else
      let e =
        if erase_bef || is_empty_bef then
          match bef_al with
          [ [] -> <:expr< $str:bef$ >>
          | [a] when bef = "%s" -> a
          | _ ->
              let e = <:expr< Pretty.sprintf $str:bef$ >> in
              List.fold_left (fun f e -> <:expr< $f$ $e$ >>) e bef_al ]
        else
          let bef = "%s" ^ bef in
          let e = <:expr< Pretty.sprintf $str:bef$ >> in
          let e = <:expr< $e$ $pc$.bef >> in
          List.fold_left (fun f e -> <:expr< $f$ $e$ >>) e bef_al
      in
      [(<:patt< bef >>, e)]
  in
  let lbl =
    if not erase_aft && aft = "" then lbl
    else
      let e =
        if erase_aft || is_empty_aft then
          match aft_al with
          [ [] -> <:expr< $str:aft$ >>
          | [a] when aft = "%s" -> a
          | _ ->
              let e = <:expr< Pretty.sprintf $str:aft$ >> in
              List.fold_left (fun f e -> <:expr< $f$ $e$ >>) e aft_al ]
        else
          let aft = aft ^ "%s" in
          let e = <:expr< Pretty.sprintf $str:aft$ >> in
          let e = List.fold_left (fun f e -> <:expr< $f$ $e$ >>) e aft_al in
          <:expr< $e$ $pc$.aft >>
      in
      [(<:patt< aft >>, e) :: lbl]
  in
  let lbl =
    match a_dang with
    [ Some a -> [(<:patt< dang >>, a) :: lbl]
    | None -> lbl ]
  in
  if lbl = [] then pc
  else <:expr< {($pc$) with $list:List.rev lbl$} >>
;

value get_assoc_args loc str al =
  loop [] al 0 where rec loop rev_str_al al i =
    if i + 1 < String.length str then
      let (rev_str_al, al, i) =
        if str.[i] = '%' then
          let (rev_str_al, al) =
            match str.[i+1] with
            [ 'c' | 's' ->
                match al with
                [ [a :: al] -> ([a :: rev_str_al], al)
                | [] ->
                    Ploc.raise loc (Stream.Error "Not enough parameters") ]
            | _ ->
                (rev_str_al, al) ]
          in
          (rev_str_al, al, i + 2)
        else (rev_str_al, al, i + 1)
      in
      loop rev_str_al al i
    else if i < String.length str && str.[i] = '%' then
      Ploc.raise loc
        (Stream.Error
           (Printf.sprintf "Premature end of format string ``\"%s\"''" str))
    else (List.rev rev_str_al, al)
;

value expr_of_pformat loc fmt is_empty_bef is_empty_aft pc al fmt1 =
  fun
  [ [] ->
      let (bef_al, al) = get_assoc_args loc fmt1 al in
      let e =
        if is_empty_bef && is_empty_aft then
          match bef_al with
          [ [] -> <:expr< $str:fmt1$ >>
          | [a] when fmt1 = "%s" -> a
          | _ ->
              let e = <:expr< Pretty.sprintf $str:fmt1$ >> in
              List.fold_left (fun f a -> <:expr< $f$ $a$ >>) e bef_al ]
        else
          let fmt1 = if is_empty_bef then fmt1 else "%s" ^ fmt1 in
          let fmt1 = if is_empty_aft then fmt1 else fmt1 ^ "%s" in
          let e = <:expr< Pretty.sprintf $str:fmt1$ >> in
          let e = if is_empty_bef then e else <:expr< $e$ $pc$.bef >> in
          let e = List.fold_left (fun f a -> <:expr< $f$ $a$ >>) e bef_al in
          if is_empty_aft then e else <:expr< $e$ $pc$.aft >>
      in
      (e, al)
  | [(with_dang, fmt2) :: fmtl] ->
      let (e, al) =
        let (bef_al, al) = get_assoc_args loc fmt1 al in
        let (f, a, al) =
          match al with
          [ [f; a :: al] -> (f, a, al)
          | _ -> Ploc.raise loc (Stream.Error "Not enough parameters") ]
        in
        let (a_dang, al) =
          if with_dang then
            match al with
            [ [a :: al] -> (Some a, al)
            | _ -> Ploc.raise loc (Stream.Error "Not enough parameters") ]
          else (None, al)
        in
        let (aft_al, al) = get_assoc_args loc fmt2 al in
        let pc =
          make_pc loc False (fmtl <> []) is_empty_bef is_empty_aft pc fmt1
            bef_al fmt2 aft_al a_dang
        in
        let e = <:expr< $f$ $pc$ $a$ >> in
        (e, al)
      in
      if fmtl = [] then (e, al)
      else
        let (sfmt, el, al) =
          loop "%s" [e] al fmtl where rec loop sfmt rev_el al =
            fun
            [ [] -> (sfmt, List.rev rev_el, al)
            | [(with_dang, fmt) :: fmtl] ->
                let (f, a, al) =
                  match al with
                  [ [f; a :: al] -> (f, a, al)
                  | _ ->
                      Ploc.raise loc (Stream.Error "Not enough parameters") ]
                in
                let (a_dang, al) =
                  if with_dang then
                    match al with
                    [ [a :: al] -> (Some a, al)
                    | _ ->
                        Ploc.raise loc
                          (Stream.Error "Not enough parameters") ]
                  else (None, al)
                in
                let (aft_al, al) = get_assoc_args loc fmt al in
                let pc =
                  make_pc loc True (fmtl <> []) is_empty_bef is_empty_aft
                    pc "" [] fmt aft_al a_dang
                in
                let e = <:expr< $f$ $pc$ $a$ >> in
                loop ("%s" ^ sfmt) [e :: rev_el] al fmtl ]
        in
        let e =
          List.fold_left (fun f e -> <:expr< $f$ $e$ >>)
            <:expr< Pretty.sprintf $str:sfmt$ >> el
        in
        (e, al) ]
;

value rec expr_of_tree_aux loc fmt is_empty_bef is_empty_aft pc al t =
  match t with
  [ Tempty -> (<:expr< Pretty.sprintf "%s%s" $pc$.bef $pc$.aft >>, al)
  | Tlist t1 (Tparen _ _ as t2) [] ->
      let (e1, al) =
        expr_of_tree_aux loc fmt is_empty_bef False <:expr< pc >> al t1
      in
      let (e2, al) =
        expr_of_tree_aux loc fmt True is_empty_aft pc al t2
      in
      let e = <:expr< let pc = {($pc$) with aft = $e2$} in $e1$ >> in
      (e, al)
  | Tlist (Tparen _ _ as t1) t2 [] ->
      let (e1, al) =
        expr_of_tree_aux loc fmt is_empty_bef True pc al t1
      in
      let (e2, al) =
        expr_of_tree_aux loc fmt False is_empty_aft <:expr< pc >> al t2
      in
      let e = <:expr< let pc = {($pc$) with bef = $e1$} in $e2$ >> in
      (e, al)
  | Tlist t1 t2 tl -> not_impl "expr_of_tree_aux" 1
  | Tnode br t1 t2 ->
      let (e1, al) =
        expr_of_tree_aux loc fmt is_empty_bef True <:expr< pc >> al t1
      in
      let (e2, al) =
        expr_of_tree_aux loc fmt is_empty_bef is_empty_aft <:expr< pc >> al t2
      in
      let e =
        let (off, sp) =
          let (off, sp) =
            match br with
            [ PPbreak off sp -> (off, sp)
            | PPspace -> (1, 0) ]
          in
          (string_of_int off, string_of_int sp)
        in
        <:expr<
          Eprinter.sprint_break $int:off$ $int:sp$ $pc$
            (fun pc -> $e1$) (fun pc -> $e2$)
        >>
      in
      (e, al)
  | Tparen (PPoffset off) t ->
      let pc =
        let soff = string_of_int off in
        <:expr< {($pc$) with ind = $pc$.ind + $int:soff$} >>
      in
      let (e, al) =
        expr_of_tree_aux loc fmt is_empty_bef is_empty_aft <:expr< pc >> al t
      in
      (<:expr< let pc = $pc$ in $e$ >>, al)
  | Tparen (PPall b) t ->
      let (t1, tl) =
        loop [] t where rec loop tl =
          fun
          [ Tnode br t1 t2 -> loop [(br, t2) :: tl] t1
          | t -> (t, tl) ]
      in
      let (e1, al) =
        expr_of_tree_aux loc fmt is_empty_bef (is_empty_aft || tl <> [])
          <:expr< pc >> al t1
      in
      let (el, al) =
        loop al tl where rec loop al =
          fun
          [ [(br, t) :: tl] ->
              let (off, sp) =
                match br with
                [ PPbreak off sp -> (off, sp)
                | PPspace -> (1, 0) ]
              in
              let (e, al) = 
                expr_of_tree_aux loc fmt is_empty_bef
                  (is_empty_aft || tl <> []) <:expr< pc >> al t
              in
              let (el, al) = loop al tl in
              ([(off, sp, e) :: el], al)
          | [] ->
              ([], al) ]
      in
      let e =
        let el =
          List.fold_left
            (fun e (off, sp, e1) ->
               let (off, sp) = (string_of_int off, string_of_int sp) in
               <:expr< [($int:off$, $int:sp$, fun pc -> $e1$) :: $e$] >>)
            <:expr< [] >> (List.rev el)
        in
        let b = if b then <:expr< True >> else <:expr< False >> in
        <:expr< Eprinter.sprint_break_all $b$ $pc$ (fun pc -> $e1$) $el$ >>
      in
      (e, al)
  | Tparen PPnone t ->
      expr_of_tree_aux loc fmt is_empty_bef is_empty_aft pc al t
  | Tstring s sl ->
      expr_of_pformat loc fmt is_empty_bef is_empty_aft pc al s sl ]
;

value expr_of_tree loc fmt pc al t =
  let (e, al) = expr_of_tree_aux loc fmt False False pc al t in
  match al with
  [ [] -> e
  | [a :: _] ->
      let loc = MLast.loc_of_expr a in
      Ploc.raise loc (Stream.Error "Too many parameters") ]
;

value expand_pprintf loc pc fmt al =
  match parse_format (Fstream.of_string fmt) with
  [ Some (t, _) -> expr_of_tree loc fmt pc al t
  | None -> assert False ]
;

(** Syntax extensions *)

EXTEND
  GLOBAL: expr;
  expr: AFTER "top"
    [ [ "EXTEND_PRINTER"; e = extprint_body; "END" -> e ] ]
  ;
  expr: LEVEL "apply"
    [ [ "pprintf"; pc = qualid; fmt = STRING; al = LIST0 NEXT ->
          expand_pprintf loc pc fmt al ] ]
  ;
  extprint_body:
    [ [ el = LIST1 [ e = entry; ";" -> e ] -> text_of_extprint loc el ] ]
  ;
  entry:
    [ [ n = name; ":"; pos = OPT position; ll = level_list ->
          {name = n; pos = pos; levels = ll} ] ]
  ;
  level_list:
    [ [ "["; ll = LIST0 level SEP "|"; "]" -> ll ] ]
  ;
  level:
    [ [ lab = OPT STRING; rules = rule_list ->
          {label = lab; rules = rules} ] ]
  ;
  rule_list:
    [ [ "["; "]" -> []
      | "["; rules = LIST1 rule SEP "|"; "]" -> rules ] ]
  ;
  rule:
    [ [ p = patt_as; wo = OPT [ "when"; e = expr -> e ]; "->"; e = expr ->
          (p, wo, e) ] ]
  ;
  patt_as:
    [ [ p = patt -> p
      | p1 = patt; "as"; p2 = patt -> <:patt< ($p1$ as $p2$) >> ] ]
  ;
  position:
    [ [ UIDENT "FIRST" -> <:expr< Eprinter.First >>
      | UIDENT "LAST" -> <:expr< Eprinter.Last >>
      | UIDENT "BEFORE"; n = STRING -> <:expr< Eprinter.Before $str:n$ >>
      | UIDENT "AFTER"; n = STRING -> <:expr< Eprinter.After $str:n$ >>
      | UIDENT "LEVEL"; n = STRING -> <:expr< Eprinter.Level $str:n$ >> ] ]
  ;
  name:
    [ [ e = qualid -> e ] ]
  ;
  qualid:
    [ [ e1 = SELF; "."; e2 = SELF -> <:expr< $e1$ . $e2$ >> ]
    | [ i = UIDENT -> <:expr< $uid:i$ >>
      | i = LIDENT -> <:expr< $lid:i$ >> ] ]
  ;
END;
