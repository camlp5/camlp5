(* camlp5r *)
(* pa_pprintf.ml,v *)
(* Copyright (c) INRIA 2007-2017 *)

#load "pa_extend.cmo";
#load "pa_fstream.cmo";
#load "q_MLast.cmo";

open Pcaml;
open Versdep;

(** Types and Functions for the [pprintf] statement *)

value not_impl name x = do {
  let desc =
    if Obj.is_block (Obj.repr x) then
      "tag = " ^ string_of_int (Obj.tag (Obj.repr x))
    else "int_val = " ^ string_of_int (Obj.magic x)
  in
  print_newline ();
  failwith ("pa_pprintf: not impl " ^ name ^ " " ^ desc)
};

type break = [ PPbreak of int and int | PPspace ];
type all = [ A_all_or_nothing | A_all | A_all_if ];
type paren_param = [ PPoffset of int | PPall of all | PPnone ];

type tree =
  [ Tempty
  | Tlist of tree and tree and list tree
  | Tnode of break and tree and tree
  | Tparen of paren_param and tree
  | Tstring of string and list (bool * string) ]
;

value implode l =
  let s = string_create (List.length l) in
  bytes_to_string (loop 0 l) where rec loop i =
    fun
    [ [c :: l] -> do { string_unsafe_set s i c; loop (i + 1) l }
    | [] -> s ]
;

value rec parse_int_aux n =
  fparser
  [ [: `('0'..'9' as c);
       n = parse_int_aux (10 * n + Char.code c - Char.code '0') :] -> n
  | [: :] -> n ]
;

value parse_int =
  fparser
    [: `('0'..'9' as c);
       n = parse_int_aux (Char.code c - Char.code '0') :] ->
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

value all =
  fun
  [ 'a' -> A_all_or_nothing
  | 'b' -> A_all
  | 'i' -> A_all_if
  | _ -> invalid_arg "all" ]
;

value parse_paren_param =
  fparser
  [ [: `'<'; off = parse_int; `'>' :] -> PPoffset off
  | [: `'<'; `('a' | 'b' | 'i' as c); `'>' :] -> PPall (all c)
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

value rec parse_epformat =
  fparser
  [ [: t = parse_simple_format; t = parse_epformat_kont t :] -> t ]
and parse_epformat_kont t1 =
  fparser
  [ [: b = parse_break; t2 = parse_simple_format;
       t = parse_epformat_kont (Tnode b t1 t2) :] -> t
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
  [ [: `'@'; `'['; pp = parse_paren_param; t = parse_epformat;
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
          let e = <:expr< $e$ $pc$.Pprintf.bef >> in
          List.fold_left (fun f e -> <:expr< $f$ $e$ >>) e bef_al
      in
      [(<:patt< Pprintf.bef >>, e)]
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
          <:expr< $e$ $pc$.Pprintf.aft >>
      in
      [(<:patt< Pprintf.aft >>, e) :: lbl]
  in
  let lbl =
    match a_dang with
    [ Some a -> [(<:patt< Pprintf.dang >>, a) :: lbl]
    | None -> lbl ]
  in
  if lbl = [] then pc
  else <:expr< {($pc$) with $list:List.rev lbl$} >>
;

value parse_flags =
  fparser
  [ [: `'-' | '0' | '+' | ' ' | '#' :] -> ()
  | [: :] -> () ]
;

value parse_width =
  fparser
  [ [: _ = parse_int :] -> ()
  | [: :] -> () ]
;

value parse_precision =
  fparser
  [ [: `'.'; _ = parse_int :] -> ()
  | [: :] -> () ]
;

value parse_format_type loc rev_str_al al =
  fparser
  [ [: `'a' :] ->
      match al with
      [ [a1; a2 :: al] -> ([a2; a1 :: rev_str_al], al)
      | [_] | [] -> Ploc.raise loc (Stream.Error "Not enough parameters") ]
  | [: `'A'..'Z' | 'a'..'z' :] ->
      match al with
      [ [a :: al] -> ([a :: rev_str_al], al)
      | [] -> Ploc.raise loc (Stream.Error "Not enough parameters") ]
  | [: `'!' | '%' :] ->
      (rev_str_al, al)
  | [: `c :] ->
      Ploc.raise loc
        (Stream.Error ("Invalid format type: %" ^ String.make 1 c))
  | [: :] ->
      (rev_str_al, al) ]
;

value rec parse_format loc rev_str_al al =
  fparser
  [ [: `'%'; _ = parse_flags; _ = parse_width; _ = parse_precision;
       (rev_str_al, al) = parse_format_type loc rev_str_al al;
       a = parse_format loc rev_str_al al :] -> a
  | [: `_; a = parse_format loc rev_str_al al :] -> a
  | [: :] -> (List.rev rev_str_al, al) ]
;

value get_assoc_args loc str al =
  match parse_format loc [] al (Fstream.of_string str) with
  [ Some (r, _) -> r
  | None -> assert False ]
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
          let e =
            if is_empty_bef then e else <:expr< $e$ $pc$.Pprintf.bef >>
          in
          let e = List.fold_left (fun f a -> <:expr< $f$ $a$ >>) e bef_al in
          if is_empty_aft then e else <:expr< $e$ $pc$.Pprintf.aft >>
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
  [ Tempty ->
      (<:expr< Pretty.sprintf "%s%s" $pc$.Pprintf.bef $pc$.Pprintf.aft >>, al)
  | Tlist t1 (Tparen _ _ as t2) [] ->
      let (e1, al) =
        expr_of_tree_aux loc fmt is_empty_bef False <:expr< pc >> al t1
      in
      let (e2, al) =
        let pc = if is_empty_bef then pc else <:expr< pc >> in
        let (e2, al) =
          expr_of_tree_aux loc fmt True is_empty_aft pc al t2
        in
        let e2 =
          if is_empty_bef then e2
          else <:expr< let pc = {($pc$) with Pprintf.bef = ""} in $e2$ >>
        in
        (e2, al)
      in
      let e = <:expr< let pc = {($pc$) with Pprintf.aft = $e2$} in $e1$ >> in
      (e, al)
  | Tlist (Tparen _ _ as t1) t2 [] ->
      let (e1, al) =
        expr_of_tree_aux loc fmt is_empty_bef True pc al t1
      in
      let (e2, al) =
        expr_of_tree_aux loc fmt False is_empty_aft <:expr< pc >> al t2
      in
      let e = <:expr< let pc = {($pc$) with Pprintf.bef = $e1$} in $e2$ >> in
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
          Pprintf.sprint_break $int:off$ $int:sp$ $pc$
            (fun pc -> $e1$) (fun pc -> $e2$)
        >>
      in
      (e, al)
  | Tparen (PPoffset off) t ->
      let pc =
        let soff = string_of_int off in
        <:expr< {($pc$) with Pprintf.ind = $pc$.Pprintf.ind + $int:soff$} >>
      in
      let (e, al) =
        expr_of_tree_aux loc fmt is_empty_bef is_empty_aft <:expr< pc >> al t
      in
      (<:expr< let pc = $pc$ in $e$ >>, al)
  | Tparen (PPall all) t ->
      let (t1, tl) =
        loop [] t where rec loop tl =
          fun
          [ Tnode br t1 t2 -> loop [(br, t2) :: tl] t1
          | t -> (t, tl) ]
      in
      let (b, al) =
        match all with
        [ A_all -> (<:expr< True >>, al)
        | A_all_or_nothing -> (<:expr< False >>, al)
        | A_all_if ->
            match al with
            [ [a :: al] -> (a, al)
            | [] -> (<:expr< error >>, al) ] ]
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
        <:expr< Pprintf.sprint_break_all $b$ $pc$ (fun pc -> $e1$) $el$ >>
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
  match parse_epformat (Fstream.of_string fmt) with
  [ Some (t, _) -> expr_of_tree loc fmt pc al t
  | None -> assert False ]
;

(** Syntax extensions *)

EXTEND
  GLOBAL: expr;
  expr: LEVEL "apply"
    [ [ "pprintf"; pc = variable; fmt = STRING; al = LIST0 NEXT ->
          expand_pprintf loc pc fmt al
      | "lprintf"; pc = variable; fmt = STRING; al = LIST0 NEXT ->
          let e = expand_pprintf loc pc fmt al in
          <:expr< expand_lprintf $pc$ loc (fun pc -> $e$) >>
   ] ]
  ;
  variable:
    [ [ e1 = SELF; "."; e2 = SELF -> <:expr< $e1$ . $e2$ >> ]
    | [ i = UIDENT -> <:expr< $uid:i$ >>
      | i = LIDENT -> <:expr< $lid:i$ >> ] ]
  ;
END;
