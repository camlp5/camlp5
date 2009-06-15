(* camlp5r pa_extend.cmo pa_fstream.cmo q_MLast.cmo *)
(* $Id: pa_extprint.ml,v 1.25 2007/12/17 20:32:03 deraugla Exp $ *)
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

value expand_item loc pc fmt al =
  let (str, str_list) =
    loop [] (String.length fmt) (String.length fmt - 2)
    where rec loop str_list i_end i =
      if i >= 0 then
        if fmt.[i] = '%' && fmt.[i+1] = 'p' then
          let str = String.sub fmt (i + 2) (i_end - i - 2) in
          loop [str :: str_list] i (i - 2)
        else
          loop str_list i_end (i - 1)
      else
        (String.sub fmt 0 i_end, str_list)
  in
  let (pcl, al) =
    loop [] str al str_list
    where rec loop rev_pcl bef al =
      fun
      [ [aft :: str_list] ->
          let (bef_al, al) = get_assoc_args loc bef al in
          let (f, f_a, al) =
            match al with
            [ [f; f_a :: al] -> (f, f_a, al)
            | _ -> Ploc.raise loc (Stream.Error "Not enough parameters") ]
          in
          let (aft_al, al) = get_assoc_args loc aft al in
          let pc = (bef, bef_al, aft, aft_al, Some (f, f_a)) in
          loop [pc :: rev_pcl] "" al str_list
      | [] ->
          if bef = "" then (List.rev rev_pcl, al)
          else
            let (bef_al, al) = get_assoc_args loc bef al in
            let pc = (bef, bef_al, "", [], None) in
            ([pc], al) ]
  in
  (pcl, al)
;

type pp = [ PPbreak of int and int | PPspace ];

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

value parse_pp_param =
  fparser [: `'<'; nsp = parse_int; `' '; off = parse_int; `'>' :] ->
    (nsp, off)
;

value parse_paren_param =
  fparser [: `'<'; off = parse_int; `'>' :] -> off
;

value parse_all_param =
  fparser [: `'<'; `('a' | 'b' as c); `'>' :] -> c
;

value next_item loc pc fmt al i_beg =
  loop al i_beg where rec loop al i =
    if i + 1 < String.length fmt then
      if fmt.[i] = '@' then
        match fmt.[i+1] with
        [ ';' | ' ' | '[' | ']' ->
            let pcl_al_opt =
              if i = i_beg then None
              else
                let fmt1 = String.sub fmt i_beg (i - i_beg) in
                Some (expand_item loc pc fmt1 al)
            in
            (pcl_al_opt, i)
        | _ ->
            loop al (i + 1) ]
      else loop al (i + 1)
    else
      let pcl_al_opt =
        if fmt = "" then None
        else
          let fmt1 = String.sub fmt i_beg (String.length fmt - i_beg) in
          Some (expand_item loc pc fmt1 al)
      in
      (pcl_al_opt, String.length fmt)

;

type tree 'a 'b =
  [ Node of tree 'a 'b and 'a and tree 'a 'b
  | Leaf of 'b
  | Offset of int and tree 'a 'b
  | BreakAll of bool and tree 'a 'b ]
;

value rec concat_tree t1 t2 =
  match (t1, t2) with
  [ (Node t11 op1 t12, _) -> Node t11 op1 (concat_tree t12 t2)
  | (_, Node t21 op2 t22) -> Node (concat_tree t1 t21) op2 t22
  | (Leaf l1, Leaf l2) -> Leaf (l1 @ l2)
  | (Offset _ t1, _) -> concat_tree t1 t2
  | (_, Offset _ t2) -> concat_tree t1 t2
  | (BreakAll _ t1, _) -> concat_tree t1 t2
  | (_, BreakAll _ t2) -> concat_tree t1 t2 ]
;

value rec read_tree loc pc fmt al i =
  let (tree, al, i) = read_simple_tree loc pc fmt al i in
  kont tree al i where rec kont tree al i =
    if i = String.length fmt then (tree, al, i)
    else if i + 1 < String.length fmt && fmt.[i] = '@' then
      match fmt.[i+1] with
      [ ';' ->
          let (pp, i) =
            let (nspaces, offset, i) =
              let s =
                String.sub fmt (i + 2) (String.length fmt - i - 2)
              in
              match parse_pp_param (Fstream.of_string s) with
              [ Some ((nspaces, noffset), strm) ->
                  (nspaces, noffset, i + 2 + Fstream.count strm)
              | None -> (1, 2, i + 2) ]
            in
            (PPbreak nspaces offset, i)
          in
          let (tree2, al, i) = read_simple_tree loc pc fmt al i in
          let tree = Node tree pp tree2 in
          kont tree al i
      | ' ' ->
          let (tree2, al, i) = read_simple_tree loc pc fmt al (i + 2) in
          let tree = Node tree PPspace tree2 in
          kont tree al i
      | ']' ->
          (tree, al, i + 2)
      | '[' ->
          let (tree2, al, i) = read_simple_tree loc pc fmt al i in
          let tree = concat_tree tree tree2 in
          kont tree al i
      | c ->
          failwith ("not impl '" ^ String.make 1 c ^ "'") ]
    else
      let (tree2, al, i) = read_simple_tree loc pc fmt al i in
      let tree = concat_tree tree tree2 in
      kont tree al i

and read_simple_tree loc pc fmt al i =
  if i + 1 < String.length fmt && fmt.[i] = '@' && fmt.[i+1] = '[' then
    let i = i + 2 in
    let s = String.sub fmt i (String.length fmt - i) in
    let strm = Fstream.of_string s in
    match parse_paren_param strm with
    [ Some (offset, strm) ->
        let i = i + Fstream.count strm in
        let (tree, al, i) = read_tree loc pc fmt al i in
        (Offset offset tree, al, i)
    | None ->
        match parse_all_param strm with
        [ Some (c, strm) ->
            let i = i + Fstream.count strm in
            let (tree, al, i) = read_tree loc pc fmt al i in
            (BreakAll (c = 'b') tree, al, i)
        | None ->
            let (tree, al, i) = read_tree loc pc fmt al i in
            (tree, al, i) ] ]
  else
    let (pcl_al_opt, i) = next_item loc pc fmt al i in
    let (pcl, al) =
      match pcl_al_opt with
      [ Some (pcl, al) -> (Leaf pcl, al)
      | None -> (Leaf [], al) ]
    in
    (pcl, al, i)
;

value make_call loc aft_is_empty pc pcl =
  let el =
    loop [] True pcl where rec loop rev_el is_first =
      fun
      [ [(bef, bef_al, aft, aft_al, f_f_a_opt) :: pcl] ->
          let is_last = pcl = [] in
          let add_pc_bef = is_first in
          let add_pc_aft = not aft_is_empty && is_last in
          let e =
            match f_f_a_opt with
            [ Some (f, f_a) ->
                let lbl = [] in
                let lbl =
                  if is_first && bef = "" then lbl
                  else              
                    let e =
                      if not add_pc_bef && bef_al = [] then
                        <:expr< $str:bef$ >>
                      else
                        let bef = if add_pc_bef then "%s" ^ bef else bef in
                        let e = <:expr< Pretty.sprintf $str:bef$ >> in
                        let e =
                          if add_pc_bef then <:expr< $e$ $pc$.bef >> else e
                        in
                        List.fold_left (fun f e -> <:expr< $f$ $e$ >>) e
                          bef_al
                    in
                    [(<:patt< bef >>, e) :: lbl]
                in
                let lbl =
                  if is_last && aft = "" then lbl
                  else
                    let e =
                      if not add_pc_aft && aft_al = [] then
                        <:expr< $str:aft$ >>
                      else if not add_pc_aft && aft = "%s" then
                        match aft_al with
                        [ [a] -> a
                        | _ -> assert False ]
                      else
                        let aft = if add_pc_aft then aft ^ "%s" else aft in
                        let e = <:expr< Pretty.sprintf $str:aft$ >> in
                        let e =
                          List.fold_left (fun f e -> <:expr< $f$ $e$ >>) e
                            aft_al
                        in
                        if add_pc_aft then <:expr< $e$ $pc$.aft >> else e
                    in
                    [(<:patt< aft >>, e) :: lbl]
                in
                let pc =
                  if lbl = [] then pc
                  else <:expr< {($pc$) with $list:List.rev lbl$} >>
                in
                <:expr< $f$ $pc$ $f_a$ >>
            | None ->
                if not add_pc_bef && bef_al = [] then <:expr< $str:bef$ >>
                else
                  let fmt = if add_pc_bef then "%s" ^ bef else bef in
                  let fmt = if add_pc_aft then fmt ^ "%s" else fmt in
                  let e = <:expr< Pretty.sprintf $str:fmt$ >> in
                  let e =
                    if add_pc_bef then <:expr< $e$ $pc$.bef >> else e
                  in
                  let e =
                    List.fold_left (fun f e -> <:expr< $f$ $e$ >>) e bef_al
                  in
                  if add_pc_aft then <:expr< $e$ $pc$.aft >> else e ]
          in
          loop [e :: rev_el] False pcl
      | [] ->
          List.rev rev_el ]
  in
  match el with
  [ [] ->
      let fmt = "%s" in
      let fmt = if not aft_is_empty then fmt ^ "%s" else fmt in
      let e = <:expr< Pretty.sprintf $str:fmt$ >> in
      let e = <:expr< $e$ $pc$.bef >> in
      if not aft_is_empty then <:expr< $e$ $pc$.aft >> else e
  | [e] -> e
  | _ ->
      let fmt = String.concat "" (List.map (fun _ -> "%s") el) in
      List.fold_left (fun f e -> <:expr< $f$ $e$ >>)
        <:expr< Pretty.sprintf $str:fmt$ >> el ]
;

value let_offset_in_e loc pc offset e =
  let soff = string_of_int offset in
  <:expr< let pc = {($pc$) with ind = $pc$.ind + $int:soff$} in $e$ >>
;

value expand_pprintf loc pc fmt al =
  let (tree, al, _) = read_tree loc pc fmt al 0 in
  match al with
  [ [a :: _] ->
      let last_a = List.hd (List.rev al) in
      let loc = Ploc.encl (MLast.loc_of_expr a) (MLast.loc_of_expr last_a) in
      Ploc.raise loc (Stream.Error "too many parameters")
  | [] ->
      loop pc False tree where rec loop pc aft_is_empty =
        fun
        [ Leaf pcl -> make_call loc aft_is_empty pc pcl
        | Node tree1 pp tree2 ->
            let (s, o) =
              match pp with
              [ PPbreak sp off -> (string_of_int sp, string_of_int off)
              | PPspace -> ("1", "0") ]
            in
            let e1 = loop <:expr< pc >> True tree1 in
            let e2 = loop <:expr< pc >> aft_is_empty tree2 in
            <:expr<
              Eprinter.sprint_break $int:s$ $int:o$ $pc$ (fun pc -> $e1$)
                (fun pc -> $e2$)
            >>
        | Offset offset t ->
            let e = loop <:expr< pc >> aft_is_empty t in
            let_offset_in_e loc pc offset e
        | BreakAll force_newlines t ->
            let (e, oel) =
              loop_1 pc aft_is_empty t where rec loop_1 pc aft_is_empty =
                fun
                [ Node t1 pp t2 ->
                    let (e1, oel1) = loop_1 pc True t1 in
                    let (e2, oel2) = loop_1 pc aft_is_empty t2 in
                    let (s, o) =
                      match pp with
                      [ PPbreak s o -> (s, o)
                      | PPspace -> (1, 0) ]
                    in
                    (e1, oel1 @ [(s, o, e2) :: oel2])
                | Offset offset t ->
                    let (e, oel) = loop_1 <:expr< pc >> aft_is_empty t in
                    let e = let_offset_in_e loc pc offset e in
                    let oel =
                      List.map
                        (fun (s, o, e) ->
                           let o = if o = 0 then offset else o in
                           (s, o, e))
                        oel
                    in
                    (e, oel)
                | t ->
                    (loop pc aft_is_empty t, []) ]
            in
            let fl =
              List.fold_right
                (fun (s, o, e) el ->
                   let s = string_of_int s in
                   let o = string_of_int o in
                   <:expr< [($int:s$, $int:o$, fun pc -> $e$) :: $el$] >>)
                oel <:expr< [] >>
            in
            let fn =
              if force_newlines then <:expr< True >> else <:expr< False >>
            in
            <:expr<
              Eprinter.sprint_break_all $fn$ $pc$ (fun pc -> $e$) $fl$
            >> ] ]
;

(** Types and Functions for [pprintf] statement; version 2 *)

type break = [ PPbreak of int and int | PPspace ];
type paren_param = [ PPoffset of int | PPall of bool | PPnone ];

type pformat = [ Pf of list string ];

type tree2 =
  [ Tbreak of break
  | Tsub of paren_param and (pformat * list (tree2 * pformat)) ]
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
  [ [: `'%'; `'p'; (cl, sl) = parse_pformat :] -> ([], [implode cl :: sl])
  | [: `c; (cl, sl) = parse_pformat :] -> ([c :: cl], sl)
  | [: :] -> ([], []) ]
;

value pformat_of_char_list cl =
  match parse_pformat (Fstream.of_list cl) with
  [ Some ((cl, sl), _) -> Pf [implode cl :: sl]
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

value rec parse_paren_format =
  fparser
  [ [: b = parse_break; (cl, tl) = parse_paren_format :] ->
      ([], [(Tbreak b, pformat_of_char_list cl) :: tl])
  | [: `'@'; `'['; pp = parse_paren_param; (cl, tl) = parse_paren_format;
       (cl2, tl2) = parse_paren_format :] ->
      let pf1 = pformat_of_char_list cl in
      let pf2 = pformat_of_char_list cl2 in
      ([], [(Tsub pp (pf1, tl), pf2) :: tl2])
  | [: `'@'; `']' :] ->
      ([], [])
  | [: `c; (cl, tl) = parse_paren_format :] ->
      ([c :: cl], tl)
  | [: :] ->
      ([], []) ]
;

value rec parse_format_aux =
  fparser
  [ [: b = parse_break; (cl, tl) = parse_format_aux :] ->
      ([], [(Tbreak b, pformat_of_char_list cl) :: tl])
  | [: `'@'; `'['; pp = parse_paren_param; (cl, tl) = parse_paren_format;
       (cl2, tl2) = parse_format_aux :] ->
      let pf1 = pformat_of_char_list cl in
      let pf2 = pformat_of_char_list cl2 in
      ([], [(Tsub pp (pf1, tl), pf2) :: tl2])
  | [: `c; (cl, tl) = parse_format_aux :] ->
      ([c :: cl], tl)
  | [: :] ->
      ([], []) ]
;

value parse_format =
  fparser
  [ [: (cl, t) = parse_format_aux :] -> (pformat_of_char_list cl, t) ]
;

value expr_of_string_list loc sl =
  List.fold_right (fun s e -> <:expr< [$str:s$ :: $e$] >>) sl <:expr< [] >>
;

value rec meta_tree_for_trace loc (s, tl) =
  let tl =
    List.fold_right
      (fun t e ->
         let t =
           match t with
           [ (Tbreak br, Pf sl) ->
               let br =
                 match br with
                 [ PPbreak sp off ->
                     let ssp = string_of_int sp in
                     let soff = string_of_int off in
                     <:expr< PPbreak $int:ssp$ $int:soff$ >>
                 | PPspace -> <:expr< PPspace >> ]
               in
               let sl = expr_of_string_list loc sl in
               <:expr< (Tbreak $br$, Pf $sl$) >>
           | (Tsub pp s_tl, Pf sl) ->
               let s_tl = meta_tree_for_trace loc s_tl in
               <:expr< Tsub $s_tl$ >> ]
         in
         <:expr< [$t$ :: $e$] >>)
      tl <:expr< [] >>
  in
  let s =
    match s with
    [ Pf sl -> expr_of_string_list loc sl ]
  in
  <:expr< ($s$, $tl$) >>
;

value get_format_args fmt al = ([], al);

value make_pc loc erase_bef erase_aft is_empty_bef is_empty_aft pc bef bef_al
    aft aft_al =
  let lbl =
    if not erase_bef && bef = "" then []
    else
      let e =
        if (erase_bef || is_empty_bef) && bef_al = [] then
          <:expr< $str:bef$ >>
        else
          let bef = if erase_bef || is_empty_bef then bef else "%s" ^ bef in
          let e = <:expr< Pretty.sprintf $str:bef$ >> in
          let e =
            if erase_bef || is_empty_bef then e else <:expr< $e$ $pc$.bef >>
          in
          List.fold_left (fun f e -> <:expr< $f$ $e$ >>) e bef_al
      in
      [(<:patt< bef >>, e)]
  in
  let lbl =
    if not erase_aft && aft = "" then lbl
    else
      let e =
        if (erase_aft || is_empty_aft) && aft_al = [] then
          <:expr< $str:aft$ >>
        else
          let aft = if erase_aft || is_empty_aft then aft else aft ^ "%s" in
          let e = <:expr< Pretty.sprintf $str:aft$ >> in
          let e = List.fold_left (fun f e -> <:expr< $f$ $e$ >>) e aft_al in
          if erase_aft || is_empty_aft then e else <:expr< $e$ $pc$.aft >>
      in
      [(<:patt< aft >>, e) :: lbl]
  in
  if lbl = [] then pc
  else <:expr< {($pc$) with $list:List.rev lbl$} >>
;

value expr_of_pformat loc fmt empty_bef empty_aft pc al =
  fun
  [ [fmt] ->
      let (al, al_rest) = get_assoc_args loc fmt al in
      let e =
        if empty_bef && empty_aft && al = [] then <:expr< $str:fmt$ >>
        else
          let fmt = if empty_bef then fmt else "%s" ^ fmt in
          let fmt = if empty_aft then fmt else fmt ^ "%s" in
          let e = <:expr< Pretty.sprintf $str:fmt$ >> in
          let e = if empty_bef then e else <:expr< $e$ $pc$.bef >> in
          let e = List.fold_left (fun f a -> <:expr< $f$ $a$ >>) e al in
          if empty_aft then e else <:expr< $e$ $pc$.aft >>
      in
      (e, al_rest)
  | [fmt1; fmt2] ->
      let (bef_al, al) = get_assoc_args loc fmt1 al in
      let (f, a, al) =
        match al with
        [ [f; a :: al] -> (f, a, al)
        | _ -> Ploc.raise loc (Stream.Error "Not enough parameters") ]
      in
      let (aft_al, al) = get_assoc_args loc fmt2 al in
      let pc =
        make_pc loc False False empty_bef empty_aft pc fmt1 bef_al fmt2 aft_al
      in
      let e = <:expr< $f$ $pc$ $a$ >> in
      (e, al)
  | [fmt1; fmt2; fmt3] ->
      let (bef_al, al) = get_assoc_args loc fmt1 al in
      let (f1, a1, al) =
        match al with
        [ [f; a :: al] -> (f, a, al)
        | _ -> Ploc.raise loc (Stream.Error "Not enough parameters") ]
      in
      let (aft_al, al) = get_assoc_args loc fmt2 al in
      let pc1 =
        make_pc loc False True False False pc fmt1 bef_al fmt2 aft_al
      in
      let e1 = <:expr< $f1$ $pc1$ $a1$ >> in
      let (f2, a2, al) =
        match al with
        [ [f; a :: al] -> (f, a, al)
        | _ -> Ploc.raise loc (Stream.Error "Not enough parameters") ]
      in
      let (aft2_al, al) = get_assoc_args loc fmt3 al in
      let pc2 = make_pc loc True False False False pc "" [] fmt3 aft2_al in
      let e2 = <:expr< $f2$ $pc2$ $a2$ >> in
      (<:expr< Pretty.sprintf "%s%s" $e1$ $e2$ >>, al)
  | _ ->
      (<:expr< ccc $str:fmt$ >>, al) ]
;

value rec expr_of_tree_aux loc fmt empty_bef empty_aft pc t al =
  match t with
  [ (Pf sl, []) -> expr_of_pformat loc fmt empty_bef empty_aft pc al sl
  | (Pf sl1, [(Tbreak br, Pf sl2) :: t]) ->
      let (t1, br, t2) =
        (* left associate *)
        let r =
          loop t where rec loop =
            fun
            [ [] -> None
            | [x] ->
                match x with
                [ (Tbreak br, Pf sl) -> Some ([], br, (Pf sl, []))
                | (Tsub _ _, _) -> None ]
            | [x :: t] ->
                match loop t with
                [ Some (t1, br, t2) -> Some ([x :: t1], br, t2)
                | None ->
                    match x with
                    [ (Tbreak br, Pf sl) -> Some ([], br, (Pf sl, t))
                    | _ -> None ] ] ]
        in
        match r with
        [ Some (t1, br1, t2) ->
           ((Pf sl1, [(Tbreak br, Pf sl2) :: t1]), br1, t2)
        | None ->
           ((Pf sl1, []), br, (Pf sl2, t)) ]
      in
      let (e1, al) =
        expr_of_tree_aux loc fmt empty_bef True <:expr< pc >> t1 al
      in
      let (e2, al) =
        expr_of_tree_aux loc fmt True empty_aft <:expr< pc >> t2 al
      in
      let (soff, ssp) =
        let (off, sp) =
          match br with
          [ PPbreak off sp -> (off, sp)
          | PPspace -> (1, 0) ]
        in
        (string_of_int off, string_of_int sp)
      in
      let e =
        <:expr<
          Eprinter.sprint_break $int:soff$ $int:ssp$ $pc$
            (fun pc -> $e1$) (fun pc -> $e2$)
        >>
      in
      (e, al)
  | (Pf [""], [(Tsub (PPoffset off) t, Pf [""])]) ->
      let pc =
        let soff = string_of_int off in
        <:expr< {($pc$) with ind = $pc$.ind + $int:soff$} >>
      in
      let (e, al) = expr_of_tree_aux loc fmt False False <:expr< pc >> t al in
      (<:expr< let pc = $pc$ in $e$ >>, al)
  | (Pf [""], [(Tsub (PPall b) (Pf sl, tl), Pf [""])]) ->
      let (e1, al) =
        expr_of_pformat loc fmt empty_bef True <:expr< pc >> al sl
      in
      let (rev_el, al) =
        List.fold_left
          (fun (rev_el, al) (br, pf) ->
             let sl = match pf with [ Pf sl -> sl ] in
             let (e, al) =
               expr_of_pformat loc fmt False False <:expr< pc >> al sl
             in
             let (off, sp) =
               match br with
               [ Tbreak (PPbreak off sp) -> (off, sp)
               | Tbreak PPspace -> (1, 0)
               | Tsub _ _ -> failwith "not impl Tsub" ]
             in
             ([(e, off, sp) :: rev_el], al))
          ([], al) tl
      in
      let e =
        let el =
          List.fold_left
            (fun e (e1, off, sp) ->
               let (off, sp) = (string_of_int off, string_of_int sp) in
               <:expr< [($int:off$, $int:sp$, fun pc -> $e1$) :: $e$] >>)
            <:expr< [] >> rev_el
        in
        let b = if b then <:expr< True >> else <:expr< False >> in
        <:expr< Eprinter.sprint_break_all $b$ $pc$ (fun pc -> $e1$) $el$ >>
      in
      (e, al)
  | (Pf [""], [(Tsub PPnone t, Pf [""])]) ->
      expr_of_tree_aux loc fmt empty_bef empty_aft pc t al
  | (Pf sl1, [(Tsub pp t1, Pf sl2) :: t]) ->
      let (e1, al) = expr_of_pformat loc fmt empty_bef True pc al sl1 in
      let (e, al) = expr_of_tree_aux loc fmt True True pc t1 al in
      let (e2, al) =
        expr_of_pformat loc fmt True (t <> [] || empty_aft) pc al sl2
      in
      (<:expr< eee $str:fmt$ $e1$ $e$ $e2$ >>, al) ]
;

value expr_of_tree loc fmt pc t al =
  let (e, al) = expr_of_tree_aux loc fmt False False pc t al in
  e
;

value expand_pprintf_2 loc pc fmt al =
  match parse_format (Fstream.of_string fmt) with
  [ Some (t, _) -> expr_of_tree loc fmt pc t al
  | None -> assert False ]
;

(** Types and Functions for [pprintf] statement; version choice *)

value pprintf_expander_2 = ref False;
Pcaml.add_option "-v2" (Arg.Set pprintf_expander_2)
  " pprintf expander 2 (debugging)";

value expand_pprintf loc pc fmt al =
  if pprintf_expander_2.val then expand_pprintf_2 loc pc fmt al
  else expand_pprintf loc pc fmt al
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
