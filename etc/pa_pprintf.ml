(* camlp5r pa_extend.cmo pa_fstream.cmo q_MLast.cmo *)
(* $Id: pa_pprintf.ml,v 1.11 2007/12/05 13:35:50 deraugla Exp $ *)
(* Copyright (c) INRIA 2007 *)

(* pprintf statement *)

open Pcaml;

value get_assoc_args loc str al =
  loop [] al 0 where rec loop rev_str_al al i =
    if i + 1 < String.length str then
      let (rev_str_al, al, i) =
        if str.[i] = '%' then
          let (rev_str_al, al) =
            match str.[i+1] with
            [ 's' ->
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
            (pcl_al_opt, i + 1)
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
  | Offset of int and tree 'a 'b ]
;

value rec read_tree loc pc fmt al i =
  let (tree, al, i) = read_simple_tree loc pc fmt al i in
  kont tree al i where rec kont tree al i =
    if i = String.length fmt then (tree, al, i)
    else
      match fmt.[i] with
      [ ';' ->
          let (pp, i) =
            let (nspaces, offset, i) =
              let s =
                String.sub fmt (i + 1) (String.length fmt - i - 1)
              in
              match parse_pp_param (Fstream.of_string s) with
              [ Some ((nspaces, noffset), strm) ->
                  (nspaces, noffset, i + 1 + Fstream.count strm)
              | None -> (1, 2, i + 1) ]
            in
            (PPbreak nspaces offset, i)
          in
          let (tree2, al, i) = read_simple_tree loc pc fmt al i in
          let tree = Node tree pp tree2 in
          kont tree al i
      | ' ' ->
          let (tree2, al, i) = read_simple_tree loc pc fmt al (i + 1) in
          let tree = Node tree PPspace tree2 in
          kont tree al i
      | ']' ->
          (tree, al, i + 1)
      | c -> failwith ("not impl '" ^ String.make 1 c ^ "'") ]

and read_simple_tree loc pc fmt al i =
  if i + 1 < String.length fmt && fmt.[i] = '@' && fmt.[i+1] = '[' then
    let (offset, i) =
      let s = String.sub fmt (i + 2) (String.length fmt - i - 2) in
      match parse_paren_param (Fstream.of_string s) with
      [ Some (offset, strm) -> (offset, i + 2 + Fstream.count strm)
      | None -> (0, i + 2) ]
    in
    let (tree, al, i) = read_tree loc pc fmt al i in
    let tree = if offset > 0 then Offset offset tree else tree in
    if i + 1 < String.length fmt && fmt.[i] = '@' && fmt.[i+1] = ']' then
      (tree, al, i + 2)
    else if i = String.length fmt then
      (tree, al, i)
    else
       assert False
  else
    let (pcl_al_opt, i) = next_item loc pc fmt al i in
    let (pcl, al) =
      match pcl_al_opt with
      [ Some (pcl, al) -> (Leaf pcl, al)
      | None -> (Leaf [], al) ]
    in
    (pcl, al, i)
;

value make_call loc (bef_is_empty, aft_is_empty) pc offset pcl =
  let el =
    loop [] True pcl where rec loop rev_el is_first =
      fun
      [ [(bef, bef_al, aft, aft_al, f_f_a_opt) :: pcl] ->
          let is_last = pcl = [] in
          let add_pc_aft = not aft_is_empty && is_last in
          let e =
            match f_f_a_opt with
            [ Some (f, f_a) ->
                let lbl = [] in
                let lbl =
                  if offset > 0 then
                    let e =
                      let soff = string_of_int offset in
                      <:expr< $pc$.ind + $int:soff$ >>
                    in
                    [(<:patt< ind >>, e) :: lbl]
                  else lbl
                in
                let lbl =
                  if is_first && bef = "" then lbl
                  else              
                    let e =
                      if not is_first && bef_al = [] then <:expr< $str:bef$ >>
                      else
                        let bef = if is_first then "%s" ^ bef else bef in
                        let e = <:expr< sprintf $str:bef$ >> in
                        let e =
                          if is_first then <:expr< $e$ $pc$.bef >> else e
                        in
                        List.fold_left (fun f e -> <:expr< $f$ $e$ >>) e bef_al
                    in
                    [(<:patt< bef >>, e) :: lbl]
                in
                let lbl =
                  if is_last && aft = "" then lbl
                  else
                    let e =
                      if not add_pc_aft && aft_al = [] then <:expr< $str:aft$ >>
                      else if not add_pc_aft && aft = "%s" then
                        match aft_al with
                        [ [a] -> a
                        | _ -> assert False ]
                      else
                        let aft = if add_pc_aft then aft ^ "%s" else aft in
                        let e = <:expr< sprintf $str:aft$ >> in
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
                if not is_first && bef_al = [] then <:expr< $str:bef$ >>
                else
                  let fmt = if is_first then "%s" ^ bef else bef in
                  let fmt = if add_pc_aft then fmt ^ "%s" else fmt in
                  let e = <:expr< sprintf $str:fmt$ >> in
                  let e =
                    if is_first then <:expr< $e$ $pc$.bef >> else e
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
      let fmt = if not bef_is_empty then "%s" else "" in
      let fmt = if not aft_is_empty then fmt ^ "%s" else "" in
      let e = <:expr< sprintf $str:fmt$ >> in
      let e = if not bef_is_empty then <:expr< $e$ $pc$.bef >> else e in
      if not aft_is_empty then <:expr< $e$ $pc$.aft >> else e
  | [e] -> e
  | _ ->
      let fmt = String.concat "" (List.map (fun _ -> "%s") el) in
      List.fold_left (fun f e -> <:expr< $f$ $e$ >>)
        <:expr< sprintf $str:fmt$ >> el ]
;

value expand_pprintf loc pc fmt al =
  let (tree, al, _) = read_tree loc pc fmt al 0 in
  match al with
  [ [a :: _] ->
      let last_a = List.hd (List.rev al) in
      let loc = Ploc.encl (MLast.loc_of_expr a) (MLast.loc_of_expr last_a) in
      Ploc.raise loc (Stream.Error "too many parameters")
  | [] ->
      loop pc 0 (False, False) tree
      where rec loop pc offset (bef_is_empty, aft_is_empty) =
        fun
        [ Leaf pcl -> make_call loc (bef_is_empty, aft_is_empty) pc offset pcl
        | Node tree1 pp tree2 ->
            let (s, o) =
              match pp with
              [ PPbreak sp off -> (string_of_int sp, string_of_int off)
              | PPspace -> ("1", "0") ]
            in
            let e1 = loop <:expr< pc >> 0 (bef_is_empty, True) tree1 in
            let e2 = loop <:expr< pc >> 0 (True, aft_is_empty) tree2 in
            let pc =
              if offset > 0 then
                let soff = string_of_int offset in
                <:expr< {($pc$) with ind = $pc$.ind + $int:soff$} >>
              else pc
            in
            <:expr<
              sprint_break $int:s$ $int:o$ $pc$ (fun pc -> $e1$)
                (fun pc -> $e2$)
            >>
        | Offset offset t ->
            loop pc offset (bef_is_empty, aft_is_empty) t ] ]
;

EXTEND
  GLOBAL: expr;
  expr: LEVEL "apply"
    [ [ "pprintf"; pc = lident; fmt = STRING; al = LIST0 NEXT ->
          expand_pprintf loc pc fmt al ] ]
  ;
  lident:
    [ [ i = LIDENT -> <:expr< $lid:i$ >> ] ]
  ;
END;
