(* camlp5r pa_extend.cmo q_MLast.cmo *)
(* $Id: pa_pprintf.ml,v 1.1 2007/12/03 09:57:52 deraugla Exp $ *)
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
          let pc = (bef, bef_al, aft, aft_al, f, f_a) in
          loop [pc :: rev_pcl] "" al str_list
      | [] ->
          (List.rev rev_pcl, al) ]
  in
  (pcl, al)
;

value make_call loc pc pcl =
  let el =
    loop [] True pcl where rec loop rev_el is_first =
      fun
      [ [(bef, bef_al, aft, aft_al, f, f_a) :: pcl] ->
          let is_last = pcl = [] in
          let lbl = [] in
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
                if not is_last && aft_al = [] then <:expr< $str:aft$ >>
                else
                  let aft = if is_last then aft ^ "%s" else aft in
                  let e = <:expr< sprintf $str:aft$ >> in
                  let e =
                    List.fold_left (fun f e -> <:expr< $f$ $e$ >>) e aft_al
                  in
                  if is_last then <:expr< $e$ $pc$.aft >> else e
              in
              [(<:patt< aft >>, e) :: lbl]
          in
          let pc =
            if lbl = [] then pc
            else <:expr< {($pc$) with $list:List.rev lbl$} >>
          in
          let e = <:expr< $f$ $pc$ $f_a$ >> in
          loop [e :: rev_el] False pcl
      | [] ->
          List.rev rev_el ]
  in
  match el with
  [ [e] -> e
  | _ ->
      let fmt = String.concat "" (List.map (fun _ -> "%s") el) in
      List.fold_left (fun f e -> <:expr< $f$ $e$ >>)
        <:expr< sprintf $str:fmt$ >> el ]
;

value expand_pprintf loc pc fmt al =
  let (pclcl, pcl, al) =
    loop [] al 0 0 where rec loop rev_pclcl al i_beg i =
      if i + 1 < String.length fmt then
        if fmt.[i] = '@' && List.mem fmt.[i+1] [' '; ','] then
          let fmt1 = String.sub fmt i_beg (i - i_beg) in
          let (pcl, al) = expand_item loc pc fmt1 al in
          loop [(pcl, fmt.[i+1]) :: rev_pclcl] al (i + 2) (i + 2)
        else loop rev_pclcl al i_beg (i + 1)
      else
        let (pcl, al) =
          let fmt1 = String.sub fmt i_beg (String.length fmt - i_beg) in
          expand_item loc pc fmt1 al
        in
        (List.rev rev_pclcl, pcl, al)
  in
  (* [(x1, c1); (x2, c2) ... (xn, cn)], x ->
     x1, [(c1, x2); (c2, x3) ... (cn, x)] *)
  let (pcl, pclcl) =
    match pclcl with
    [ [(pcl1, c1) :: pclcl] ->
        let pclcl =
          loop c1 pclcl where rec loop c =
            fun
            [ [(pcl2, c1) :: pclcl] -> [(c, pcl2) :: loop c1 pclcl]
            | [] -> [(c, pcl)] ]
        in
        (pcl1, pclcl)
    | [] ->
        (pcl, []) ]
  in
  match al with
  [ [a :: _] ->
      let last_a = List.hd (List.rev al) in
      let loc = Ploc. encl (MLast.loc_of_expr a) (MLast.loc_of_expr last_a) in
      Ploc.raise loc (Stream.Error "too many parameters")
  | [] ->
      if pclcl = [] then make_call loc pc pcl
      else
        List.fold_left
          (fun e (c, pcl1) ->
             let (s, o) =
               match c with
               [ ' ' -> ("1", "2")
               | ',' -> ("1", "0")
               | _ -> ("0", "0") ]
             in
             let e1 = make_call loc <:expr< pc >> pcl1 in
             <:expr<
               break $int:s$ $int:o$ $pc$ (fun pc -> $e$) (fun pc -> $e1$)
             >>)
          (make_call loc <:expr< pc >> pcl) pclcl ]
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
