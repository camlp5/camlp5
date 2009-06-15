(* camlp5r *)
(***********************************************************************)
(*                                                                     *)
(*                             Camlp5                                  *)
(*                                                                     *)
(*                Daniel de Rauglaudre, INRIA Rocquencourt             *)
(*                                                                     *)
(*  Copyright 2007 Institut National de Recherche en Informatique et   *)
(*  Automatique.  Distributed only by permission.                      *)
(*                                                                     *)
(***********************************************************************)

(* $Id: grammar.ml,v 1.23 2007/07/27 22:32:27 deraugla Exp $ *)

open Stdpp;
open Gramext;
open Format;

value rec flatten_tree =
  fun
  [ DeadEnd -> []
  | LocAct _ _ -> [[]]
  | Node {node = n; brother = b; son = s} ->
      List.map (fun l -> [n :: l]) (flatten_tree s) @ flatten_tree b ]
;

value print_str ppf s = fprintf ppf "\"%s\"" (String.escaped s);

value rec print_symbol ppf =
  fun
  [ Smeta n sl _ -> print_meta ppf n sl
  | Slist0 s -> fprintf ppf "LIST0 %a" print_symbol1 s
  | Slist0sep s t ->
      fprintf ppf "LIST0 %a SEP %a" print_symbol1 s print_symbol1 t
  | Slist1 s -> fprintf ppf "LIST1 %a" print_symbol1 s
  | Slist1sep s t ->
      fprintf ppf "LIST1 %a SEP %a" print_symbol1 s print_symbol1 t
  | Sopt s -> fprintf ppf "OPT %a" print_symbol1 s
  | Stoken (con, prm) when con <> "" && prm <> "" ->
      fprintf ppf "%s@ %a" con print_str prm
  | Snterml e l ->
      fprintf ppf "%s%s@ LEVEL@ %a" e.ename (if e.elocal then "*" else "")
        print_str l
  | Snterm _ | Snext | Sself | Stoken _ | Stree _ as s ->
      print_symbol1 ppf s ]
and print_meta ppf n sl =
  loop 0 sl where rec loop i =
    fun
    [ [] -> ()
    | [s :: sl] -> do {
        let j =
          try String.index_from n i ' ' with [ Not_found -> String.length n ]
        in
        fprintf ppf "%s %a" (String.sub n i (j - i)) print_symbol1 s;
        if sl = [] then ()
        else do { fprintf ppf " "; loop (min (j + 1) (String.length n)) sl }
      } ]
and print_symbol1 ppf =
  fun
  [ Snterm e -> fprintf ppf "%s%s" e.ename (if e.elocal then "*" else "")
  | Sself -> pp_print_string ppf "SELF"
  | Snext -> pp_print_string ppf "NEXT"
  | Stoken ("", s) -> print_str ppf s
  | Stoken (con, "") -> pp_print_string ppf con
  | Stree t -> print_level ppf pp_print_space (flatten_tree t)
  | Smeta _ _ _ | Snterml _ _ | Slist0 _ | Slist0sep _ _ | Slist1 _ |
    Slist1sep _ _ | Sopt _ | Stoken _ as s ->
      fprintf ppf "(%a)" print_symbol s ]
and print_rule ppf symbols = do {
  fprintf ppf "@[<hov 0>";
  let _ =
    List.fold_left
      (fun sep symbol -> do {
         fprintf ppf "%t%a" sep print_symbol symbol;
         fun ppf -> fprintf ppf ";@ "
       })
      (fun ppf -> ()) symbols
  in
  fprintf ppf "@]"
}
and print_level ppf pp_print_space rules = do {
  fprintf ppf "@[<hov 0>[ ";
  let _ =
    List.fold_left
      (fun sep rule -> do {
         fprintf ppf "%t%a" sep print_rule rule;
         fun ppf -> fprintf ppf "%a| " pp_print_space ()
       })
      (fun ppf -> ()) rules
  in
  fprintf ppf " ]@]"
};

value print_levels ppf elev =
  let _ =
    List.fold_left
      (fun sep lev -> do {
         let rules =
           List.map (fun t -> [Sself :: t]) (flatten_tree lev.lsuffix) @
           flatten_tree lev.lprefix
         in
         fprintf ppf "%t@[<hov 2>" sep;
         match lev.lname with
         [ Some n -> fprintf ppf "%a@;<1 2>" print_str n
         | None -> () ];
         match lev.assoc with
         [ LeftA -> fprintf ppf "LEFTA"
         | RightA -> fprintf ppf "RIGHTA"
         | NonA -> fprintf ppf "NONA" ];
         fprintf ppf "@]@;<1 2>";
         print_level ppf pp_force_newline rules;
         fun ppf -> fprintf ppf "@,| "
       })
      (fun ppf -> ()) elev
  in
  ()
;

value print_entry ppf e = do {
  fprintf ppf "@[<v 0>[ ";
  match e.edesc with
  [ Dlevels elev -> print_levels ppf elev
  | Dparser _ -> fprintf ppf "<parser>" ];
  fprintf ppf " ]@]"
};

value iter_entry f e =
  let treated = ref [] in
  let rec do_entry e =
    if List.memq e treated.val then ()
    else do {
      treated.val := [e :: treated.val];
      f e;
      match e.edesc with
      [ Dlevels ll -> List.iter do_level ll
      | Dparser _ -> () ]
    }
  and do_level lev = do { do_tree lev.lsuffix; do_tree lev.lprefix }
  and do_tree =
    fun
    [ Node n -> do_node n
    | LocAct _ _ | DeadEnd -> () ]
  and do_node n = do { do_symbol n.node; do_tree n.son; do_tree n.brother }
  and do_symbol =
    fun
    [ Smeta _ sl _ -> List.iter do_symbol sl
    | Snterm e | Snterml e _ -> do_entry e
    | Slist0 s | Slist1 s | Sopt s -> do_symbol s
    | Slist0sep s1 s2 | Slist1sep s1 s2 -> do { do_symbol s1; do_symbol s2 }
    | Stree t -> do_tree t
    | Sself | Snext | Stoken _ -> () ]
  in
  do_entry e
;

value fold_entry f e init =
  let treated = ref [] in
  let rec do_entry accu e =
    if List.memq e treated.val then accu
    else do {
      treated.val := [e :: treated.val];
      let accu = f e accu in
      match e.edesc with
      [ Dlevels ll -> List.fold_left do_level accu ll
      | Dparser _ -> accu ]
    }
  and do_level accu lev =
    let accu = do_tree accu lev.lsuffix in
    do_tree accu lev.lprefix
  and do_tree accu =
    fun
    [ Node n -> do_node accu n
    | LocAct _ _ | DeadEnd -> accu ]
  and do_node accu n =
    let accu = do_symbol accu n.node in
    let accu = do_tree accu n.son in
    do_tree accu n.brother
  and do_symbol accu =
    fun
    [ Smeta _ sl _ -> List.fold_left do_symbol accu sl
    | Snterm e | Snterml e _ -> do_entry accu e
    | Slist0 s | Slist1 s | Sopt s -> do_symbol accu s
    | Slist0sep s1 s2 | Slist1sep s1 s2 ->
        let accu = do_symbol accu s1 in
        do_symbol accu s2
    | Stree t -> do_tree accu t
    | Sself | Snext | Stoken _ -> accu ]
  in
  do_entry init e
;

value floc = ref (fun _ -> failwith "internal error when computing location");

value loc_of_token_interval bp ep =
  if bp == ep then
    if bp == 0 then Stdpp.dummy_loc
    else Stdpp.after_loc (floc.val (bp - 1)) 0 1
  else
    let loc1 = floc.val bp in
    let loc2 = floc.val (pred ep) in
    Stdpp.encl_loc loc1 loc2
;

value rec name_of_symbol entry =
  fun
  [ Snterm e -> "[" ^ e.ename ^ "]"
  | Snterml e l -> "[" ^ e.ename ^ " level " ^ l ^ "]"
  | Sself | Snext -> "[" ^ entry.ename ^ "]"
  | Stoken tok -> entry.egram.glexer.Token.tok_text tok
  | _ -> "???" ]
;

value rec get_token_list entry tokl last_tok tree =
  match tree with
  [ Node {node = Stoken tok; son = son; brother = DeadEnd} ->
      get_token_list entry [last_tok :: tokl] tok son
  | _ ->
      if tokl = [] then None
      else Some (List.rev [last_tok :: tokl], last_tok, tree) ]
;

value rec name_of_symbol_failed entry =
  fun
  [ Slist0 s -> name_of_symbol_failed entry s
  | Slist0sep s _ -> name_of_symbol_failed entry s
  | Slist1 s -> name_of_symbol_failed entry s
  | Slist1sep s _ -> name_of_symbol_failed entry s
  | Sopt s -> name_of_symbol_failed entry s
  | Stree t -> name_of_tree_failed entry t
  | Smeta _ [s :: _] _ -> name_of_symbol_failed entry s
  | s -> name_of_symbol entry s ]
and name_of_tree_failed entry =
  fun
  [ Node {node = s; brother = bro; son = son} ->
      let tokl =
        match s with
        [ Stoken tok -> get_token_list entry [] tok son
        | _ -> None ]
      in
      match tokl with
      [ None ->
          let txt = name_of_symbol_failed entry s in
          let txt =
            match (s, son) with
            [ (Sopt _, Node _) -> txt ^ " or " ^ name_of_tree_failed entry son
            | _ -> txt ]
          in
          let txt =
            match bro with
            [ DeadEnd | LocAct _ _ -> txt
            | Node _ -> txt ^ " or " ^ name_of_tree_failed entry bro ]
          in
          txt
      | Some (tokl, last_tok, son) ->
          List.fold_left
            (fun s tok ->
               (if s = "" then "" else s ^ " ") ^
               entry.egram.glexer.Token.tok_text tok)
            "" tokl ]
  | DeadEnd | LocAct _ _ -> "???" ]
;

value search_tree_in_entry prev_symb tree =
  fun
  [ Dlevels levels ->
      let rec search_levels =
        fun
        [ [] -> tree
        | [level :: levels] ->
            match search_level level with
            [ Some tree -> tree
            | None -> search_levels levels ] ]
      and search_level level =
        match search_tree level.lsuffix with
        [ Some t -> Some (Node {node = Sself; son = t; brother = DeadEnd})
        | None -> search_tree level.lprefix ]
      and search_tree t =
        if tree <> DeadEnd && t == tree then Some t
        else
          match t with
          [ Node n ->
              match search_symbol n.node with
              [ Some symb ->
                  Some (Node {node = symb; son = n.son; brother = DeadEnd})
              | None ->
                  match search_tree n.son with
                  [ Some t ->
                      Some (Node {node = n.node; son = t; brother = DeadEnd})
                  | None -> search_tree n.brother ] ]
          | LocAct _ _ | DeadEnd -> None ]
      and search_symbol symb =
        match symb with
        [ Snterm _ | Snterml _ _ | Slist0 _ | Slist0sep _ _ | Slist1 _ |
          Slist1sep _ _ | Sopt _ | Stoken _ | Stree _
          when symb == prev_symb ->
            Some symb
        | Slist0 symb ->
            match search_symbol symb with
            [ Some symb -> Some (Slist0 symb)
            | None -> None ]
        | Slist0sep symb sep ->
            match search_symbol symb with
            [ Some symb -> Some (Slist0sep symb sep)
            | None ->
                match search_symbol sep with
                [ Some sep -> Some (Slist0sep symb sep)
                | None -> None ] ]
        | Slist1 symb ->
            match search_symbol symb with
            [ Some symb -> Some (Slist1 symb)
            | None -> None ]
        | Slist1sep symb sep ->
            match search_symbol symb with
            [ Some symb -> Some (Slist1sep symb sep)
            | None ->
                match search_symbol sep with
                [ Some sep -> Some (Slist1sep symb sep)
                | None -> None ] ]
        | Sopt symb ->
            match search_symbol symb with
            [ Some symb -> Some (Sopt symb)
            | None -> None ]
        | Stree t ->
            match search_tree t with
            [ Some t -> Some (Stree t)
            | None -> None ]
        | _ -> None ]
      in
      search_levels levels
  | Dparser _ -> tree ]
;

value error_verbose = ref False;

value tree_failed entry prev_symb_result prev_symb tree = do {
  let txt = name_of_tree_failed entry tree in
  let txt =
    match prev_symb with
    [ Slist0 s ->
        let txt1 = name_of_symbol_failed entry s in
        txt1 ^ " or " ^ txt ^ " expected"
    | Slist1 s ->
        let txt1 = name_of_symbol_failed entry s in
        txt1 ^ " or " ^ txt ^ " expected"
    | Slist0sep s sep ->
        match Obj.magic prev_symb_result with
        [ [] ->
            let txt1 = name_of_symbol_failed entry s in
            txt1 ^ " or " ^ txt ^ " expected"
        | _ ->
            let txt1 = name_of_symbol_failed entry sep in
            txt1 ^ " or " ^ txt ^ " expected" ]
    | Slist1sep s sep ->
        match Obj.magic prev_symb_result with
        [ [] ->
            let txt1 = name_of_symbol_failed entry s in
            txt1 ^ " or " ^ txt ^ " expected"
        | _ ->
            let txt1 = name_of_symbol_failed entry sep in
            txt1 ^ " or " ^ txt ^ " expected" ]
    | Sopt _ | Stree _ -> txt ^ " expected"
    | _ -> txt ^ " expected after " ^ name_of_symbol entry prev_symb ]
  in
  if error_verbose.val then do {
    let tree = search_tree_in_entry prev_symb tree entry.edesc in
    let ppf = err_formatter in
    fprintf ppf "@[<v 0>@,";
    fprintf ppf "----------------------------------@,";
    fprintf ppf "Parse error in entry [%s], rule:@;<0 2>" entry.ename;
    fprintf ppf "@[";
    print_level ppf pp_force_newline (flatten_tree tree);
    fprintf ppf "@]@,";
    fprintf ppf "----------------------------------@,";
    fprintf ppf "@]@."
  }
  else ();
  txt ^ " (in [" ^ entry.ename ^ "])"
};

value symb_failed entry prev_symb_result prev_symb symb =
  let tree = Node {node = symb; brother = DeadEnd; son = DeadEnd} in
  tree_failed entry prev_symb_result prev_symb tree
;

external app : Obj.t -> 'a = "%identity";

value is_level_labelled n lev =
  match lev.lname with
  [ Some n1 -> n = n1
  | None -> False ]
;

value level_number entry lab =
  let rec lookup levn =
    fun
    [ [] -> failwith ("unknown level " ^ lab)
    | [lev :: levs] ->
        if is_level_labelled lab lev then levn else lookup (succ levn) levs ]
  in
  match entry.edesc with
  [ Dlevels elev -> lookup 0 elev
  | Dparser _ -> raise Not_found ]
;

value rec top_symb entry =
  fun
  [ Sself | Snext -> Snterm entry
  | Snterml e _ -> Snterm e
  | Slist1sep s sep -> Slist1sep (top_symb entry s) sep
  | _ -> raise Stream.Failure ]
;

value entry_of_symb entry =
  fun
  [ Sself | Snext -> entry
  | Snterm e -> e
  | Snterml e _ -> e
  | _ -> raise Stream.Failure ]
;

value top_tree entry =
  fun
  [ Node {node = s; brother = bro; son = son} ->
      Node {node = top_symb entry s; brother = bro; son = son}
  | LocAct _ _ | DeadEnd -> raise Stream.Failure ]
;

value skip_if_empty bp p strm =
  if Stream.count strm == bp then Gramext.action (fun a -> p strm)
  else raise Stream.Failure
;

value continue entry bp a s son p1 =
  parser
    [: a = (entry_of_symb entry s).econtinue 0 bp a;
       act = p1 ? tree_failed entry a s son :] ->
      Gramext.action (fun _ -> app act a)
;

value do_recover parser_of_tree entry nlevn alevn bp a s son =
  parser
  [ [: a = parser_of_tree entry nlevn alevn (top_tree entry son) :] -> a
  | [: a = skip_if_empty bp (parser []) :] -> a
  | [: a =
         continue entry bp a s son
           (parser_of_tree entry nlevn alevn son) :] ->
      a ]
;

value strict_parsing = ref False;

value recover parser_of_tree entry nlevn alevn bp a s son strm =
  if strict_parsing.val then raise (Stream.Error (tree_failed entry a s son))
  else do_recover parser_of_tree entry nlevn alevn bp a s son strm
;

value token_count = ref 0;

value peek_nth n strm = do {
  let list = Stream.npeek n strm in
  token_count.val := Stream.count strm + n;
  let rec loop list n =
    match (list, n) with
    [ ([x :: _], 1) -> Some x
    | ([_ :: l], n) -> loop l (n - 1)
    | ([], _) -> None ]
  in
  loop list n
};

value rec parser_of_tree entry nlevn alevn =
  fun
  [ DeadEnd -> parser []
  | LocAct act _ -> parser [: :] -> act
  | Node {node = Sself; son = LocAct act _; brother = DeadEnd} ->
      parser [: a = entry.estart alevn :] -> app act a
  | Node {node = Sself; son = LocAct act _; brother = bro} ->
      let p2 = parser_of_tree entry nlevn alevn bro in
      parser
      [ [: a = entry.estart alevn :] -> app act a
      | [: a = p2 :] -> a ]
  | Node {node = s; son = son; brother = DeadEnd} ->
      let tokl =
        match s with
        [ Stoken tok -> get_token_list entry [] tok son
        | _ -> None ]
      in
      match tokl with
      [ None ->
          let ps = parser_of_symbol entry nlevn s in
          let p1 = parser_of_tree entry nlevn alevn son in
          let p1 = parser_cont p1 entry nlevn alevn s son in
          parser bp [: a = ps; act = p1 bp a :] -> app act a
      | Some (tokl, last_tok, son) ->
          let p1 = parser_of_tree entry nlevn alevn son in
          let p1 = parser_cont p1 entry nlevn alevn (Stoken last_tok) son in
          parser_of_token_list entry.egram p1 tokl ]
  | Node {node = s; son = son; brother = bro} ->
      let tokl =
        match s with
        [ Stoken tok -> get_token_list entry [] tok son
        | _ -> None ]
      in
      match tokl with
      [ None ->
          let ps = parser_of_symbol entry nlevn s in
          let p1 = parser_of_tree entry nlevn alevn son in
          let p1 = parser_cont p1 entry nlevn alevn s son in
          let p2 = parser_of_tree entry nlevn alevn bro in
          parser bp
          [ [: a = ps; act = p1 bp a :] -> app act a
          | [: a = p2 :] -> a ]
      | Some (tokl, last_tok, son) ->
          let p1 = parser_of_tree entry nlevn alevn son in
          let p1 = parser_cont p1 entry nlevn alevn (Stoken last_tok) son in
          let p1 = parser_of_token_list entry.egram p1 tokl in
          let p2 = parser_of_tree entry nlevn alevn bro in
          parser
          [ [: a = p1 :] -> a
          | [: a = p2 :] -> a ] ] ]
and parser_cont p1 entry nlevn alevn s son bp a =
  parser
  [ [: a = p1 :] -> a
  | [: a = recover parser_of_tree entry nlevn alevn bp a s son :] -> a
  | [: :] -> raise (Stream.Error (tree_failed entry a s son)) ]
and parser_of_token_list gram p1 tokl =
  loop 1 tokl where rec loop n =
    fun
    [ [tok :: tokl] ->
        let tematch = gram.glexer.Token.tok_match tok in
        match tokl with
        [ [] ->
            let ps strm =
              match peek_nth n strm with
              [ Some tok -> do {
                  let r = tematch tok in
                  for i = 1 to n do { Stream.junk strm };
                  Obj.repr r
                }
              | None -> raise Stream.Failure ]
            in
            parser bp [: a = ps; act = p1 bp a :] -> app act a
        | _ ->
            let ps strm =
              match peek_nth n strm with
              [ Some tok -> tematch tok
              | None -> raise Stream.Failure ]
            in
            let p1 = loop (n + 1) tokl in
            parser [: a = ps; act = p1 ! :] -> app act a ]
    | [] -> invalid_arg "parser_of_token_list" ]
and parser_of_symbol entry nlevn =
  fun
  [ Smeta _ symbl act ->
      let act = Obj.magic act entry symbl in
      Obj.magic
        (List.fold_left
           (fun act symb -> Obj.magic act (parser_of_symbol entry nlevn symb))
           act symbl)
  | Slist0 s ->
      let ps = parser_of_symbol entry nlevn s in
      let rec loop al =
        parser
        [ [: a = ps; a = loop [a :: al] ! :] -> a
        | [: :] -> al ]
      in
      parser [: a = loop [] :] -> Obj.repr (List.rev a)
  | Slist0sep symb sep ->
      let ps = parser_of_symbol entry nlevn symb in
      let pt = parser_of_symbol entry nlevn sep in
      let rec kont al =
        parser
        [ [: v = pt; a = ps ? symb_failed entry v sep symb;
             a = kont [a :: al] ! :] ->
            a
        | [: :] -> al ]
      in
      parser
      [ [: a = ps; a = kont [a] ! :] -> Obj.repr (List.rev a)
      | [: :] -> Obj.repr [] ]
  | Slist1 s ->
      let ps = parser_of_symbol entry nlevn s in
      let rec loop al =
        parser
        [ [: a = ps; a = loop [a :: al] ! :] -> a
        | [: :] -> al ]
      in
      parser [: a = ps; a = loop [a] ! :] -> Obj.repr (List.rev a)
  | Slist1sep symb sep ->
      let ps = parser_of_symbol entry nlevn symb in
      let pt = parser_of_symbol entry nlevn sep in
      let rec kont al =
        parser
        [ [: v = pt;
             a =
               parser
               [ [: a = ps :] -> a
               | [: a = parse_top_symb entry symb :] -> a
               | [: :] ->
                   raise (Stream.Error (symb_failed entry v sep symb)) ];
             a = kont [a :: al] ! :] ->
            a
        | [: :] -> al ]
      in
      parser [: a = ps; a = kont [a] ! :] -> Obj.repr (List.rev a)
  | Sopt s ->
      let ps = parser_of_symbol entry nlevn s in
      parser
      [ [: a = ps :] -> Obj.repr (Some a)
      | [: :] -> Obj.repr None ]
  | Stree t ->
      let pt = parser_of_tree entry 1 0 t in
      parser bp
        [: a = pt :] ep ->
          let loc = loc_of_token_interval bp ep in
          app a loc
  | Snterm e -> parser [: a = e.estart 0 :] -> a
  | Snterml e l -> parser [: a = e.estart (level_number e l) :] -> a
  | Sself -> parser [: a = entry.estart 0 :] -> a
  | Snext -> parser [: a = entry.estart nlevn :] -> a
  | Stoken tok ->
      let f = entry.egram.glexer.Token.tok_match tok in
      fun strm ->
        match Stream.peek strm with
        [ Some tok -> do {
            let r = f tok in
            Stream.junk strm;
            Obj.repr r
          }
        | None -> raise Stream.Failure ] ]
and parse_top_symb entry symb =
  parser_of_symbol entry 0 (top_symb entry symb)
;

value symb_failed_txt e s1 s2 = symb_failed e 0 s1 s2;

value rec continue_parser_of_levels entry clevn =
  fun
  [ [] -> fun levn bp a -> parser []
  | [lev :: levs] ->
      let p1 = continue_parser_of_levels entry (succ clevn) levs in
      match lev.lsuffix with
      [ DeadEnd -> p1
      | tree ->
          let alevn =
            match lev.assoc with
            [ LeftA | NonA -> succ clevn
            | RightA -> clevn ]
          in
          let p2 = parser_of_tree entry (succ clevn) alevn tree in
          fun levn bp a strm ->
            if levn > clevn then p1 levn bp a strm
            else
              match strm with parser
              [ [: a = p1 levn bp a :] -> a
              | [: act = p2 :] ep ->
                  let a = app act a (loc_of_token_interval bp ep) in
                  entry.econtinue levn bp a strm ] ] ]
;

value rec start_parser_of_levels entry clevn =
  fun
  [ [] -> fun levn -> parser []
  | [lev :: levs] ->
      let p1 = start_parser_of_levels entry (succ clevn) levs in
      match lev.lprefix with
      [ DeadEnd -> p1
      | tree ->
          let alevn =
            match lev.assoc with
            [ LeftA | NonA -> succ clevn
            | RightA -> clevn ]
          in
          let p2 = parser_of_tree entry (succ clevn) alevn tree in
          match levs with
          [ [] ->
              fun levn strm ->
                match strm with parser bp
                  [: act = p2 :] ep ->
                    let a = app act (loc_of_token_interval bp ep) in
                    entry.econtinue levn bp a strm
          | _ ->
              fun levn strm ->
                if levn > clevn then p1 levn strm
                else
                  match strm with parser bp
                  [ [: act = p2 :] ep ->
                      let a = app act (loc_of_token_interval bp ep) in
                      entry.econtinue levn bp a strm
                  | [: a = p1 levn :] -> a ] ] ] ]
;

value continue_parser_of_entry entry =
  match entry.edesc with
  [ Dlevels elev ->
      let p = continue_parser_of_levels entry 0 elev in
      fun levn bp a ->
        parser
        [ [: a = p levn bp a :] -> a
        | [: :] -> a ]
  | Dparser p -> fun levn bp a -> parser [] ]
;

value empty_entry ename levn strm =
  raise (Stream.Error ("entry [" ^ ename ^ "] is empty"))
;

value start_parser_of_entry entry =
  match entry.edesc with
  [ Dlevels [] -> empty_entry entry.ename
  | Dlevels elev -> start_parser_of_levels entry 0 elev
  | Dparser p -> fun levn strm -> p strm ]
;

(* Extend syntax *)

value extend_entry entry position rules =
  try do {
    let elev = Gramext.levels_of_rules entry position rules in
    entry.edesc := Dlevels elev;
    entry.estart :=
      fun lev strm -> do {
        let f = start_parser_of_entry entry in
        entry.estart := f;
        f lev strm
      };
    entry.econtinue :=
      fun lev bp a strm -> do {
        let f = continue_parser_of_entry entry in
        entry.econtinue := f;
        f lev bp a strm
      }
  }
  with
  [ Token.Error s -> do {
      Printf.eprintf "Lexer initialization error:\n- %s\n" s;
      flush stderr;
      failwith "Grammar.extend"
    } ]
;

value extend entry_rules_list =
  let gram = ref None in
  List.iter
    (fun (entry, position, rules) -> do {
       match gram.val with
       [ Some g ->
           if g != entry.egram then do {
             Printf.eprintf "Error: entries with different grammars\n";
             flush stderr;
             failwith "Grammar.extend"
           }
           else ()
       | None -> gram.val := Some entry.egram ];
       extend_entry entry position rules
     })
    entry_rules_list
;

(* Deleting a rule *)

value delete_rule entry sl =
  match entry.edesc with
  [ Dlevels levs -> do {
      let levs = Gramext.delete_rule_in_level_list entry sl levs in
      entry.edesc := Dlevels levs;
      entry.estart :=
        fun lev strm -> do {
          let f = start_parser_of_entry entry in
          entry.estart := f;
          f lev strm
        };
      entry.econtinue :=
        fun lev bp a strm -> do {
          let f = continue_parser_of_entry entry in
          entry.econtinue := f;
          f lev bp a strm
        }
    }
  | Dparser _ -> () ]
;

value warning_verbose = Gramext.warning_verbose;

(* Normal interface *)

type token = (string * string);
type g = Gramext.grammar token;

value create_toktab () = Hashtbl.create 301;
value gcreate glexer = {gtokens = create_toktab (); glexer = glexer};

value tokens g con = do {
  let list = ref [] in
  Hashtbl.iter
    (fun (p_con, p_prm) c ->
       if p_con = con then list.val := [(p_prm, c.val) :: list.val] else ())
    g.gtokens;
  list.val
};

value glexer g = g.glexer;

type gen_parsable 'te =
  { pa_chr_strm : Stream.t char;
    pa_tok_strm : Stream.t 'te;
    pa_loc_func : Token.location_function }
;

type parsable = gen_parsable token;

value parsable g cs =
  let (ts, lf) = g.glexer.Token.tok_func cs in
  {pa_chr_strm = cs; pa_tok_strm = ts; pa_loc_func = lf}
;

value parse_parsable entry p = do {
  let efun = entry.estart 0 in
  let ts = p.pa_tok_strm in
  let cs = p.pa_chr_strm in
  let fun_loc = p.pa_loc_func in
  let restore =
    let old_floc = floc.val in
    let old_tc = token_count.val in
    fun () -> do { floc.val := old_floc; token_count.val := old_tc }
  in
  let get_loc () =
    try
      let cnt = Stream.count ts in
      let loc = fun_loc cnt in
      if token_count.val - 1 <= cnt then loc
      else Stdpp.encl_loc loc (fun_loc (token_count.val - 1))
    with _ ->
      Stdpp.make_loc (Stream.count cs, Stream.count cs + 1)
  in
  floc.val := fun_loc;
  token_count.val := 0;
  try do {
    let r = efun ts in
    restore ();
    r
  }
  with
  [ Stream.Failure -> do {
      let loc = get_loc () in
      restore ();
      Stdpp.raise_with_loc loc
        (Stream.Error ("illegal begin of " ^ entry.ename))
    }
  | Stream.Error _ as exc -> do {
      let loc = get_loc () in
      restore ();
      Stdpp.raise_with_loc loc exc
    }
  | exc -> do {
      let loc = (Stream.count cs, Stream.count cs + 1) in
      restore ();
      raise_with_loc (make_loc loc) exc
    } ]
};

value find_entry e s =
  let rec find_levels =
    fun
    [ [] -> None
    | [lev :: levs] ->
        match find_tree lev.lsuffix with
        [ None ->
            match find_tree lev.lprefix with
            [ None -> find_levels levs
            | x -> x ]
        | x -> x ] ]
  and find_symbol =
    fun
    [ Snterm e -> if e.ename = s then Some e else None
    | Snterml e _ -> if e.ename = s then Some e else None
    | Smeta _ sl _ -> find_symbol_list sl
    | Slist0 s -> find_symbol s
    | Slist0sep s _ -> find_symbol s
    | Slist1 s -> find_symbol s
    | Slist1sep s _ -> find_symbol s
    | Sopt s -> find_symbol s
    | Stree t -> find_tree t
    | Sself | Snext | Stoken _ -> None ]
  and find_symbol_list =
    fun
    [ [s :: sl] ->
        match find_symbol s with
        [ None -> find_symbol_list sl
        | x -> x ]
    | [] -> None ]
  and find_tree =
    fun
    [ Node {node = s; brother = bro; son = son} ->
        match find_symbol s with
        [ None ->
            match find_tree bro with
            [ None -> find_tree son
            | x -> x ]
        | x -> x ]
    | LocAct _ _ | DeadEnd -> None ]
  in
  match e.edesc with
  [ Dlevels levs ->
      match find_levels levs with
      [ Some e -> e
      | None -> raise Not_found ]
  | Dparser _ -> raise Not_found ]
;

module Entry =
  struct
    type te = token;
    type e 'a = g_entry te;
    value create g n =
      {egram = g; ename = n; estart = empty_entry n; elocal = False;
       econtinue _ _ _ = parser []; edesc = Dlevels []}
    ;
    value parse_parsable (entry : e 'a) p : 'a =
      Obj.magic (parse_parsable entry p : Obj.t)
    ;
    value parse (entry : e 'a) cs : 'a =
      let parsable = parsable entry.egram cs in
      parse_parsable entry parsable
    ;
    value parse_token (entry : e 'a) ts : 'a =
      Obj.magic (entry.estart 0 ts : Obj.t)
    ;
    value name e = e.ename;
    value of_parser g n (p : Stream.t te -> 'a) : e 'a =
      {egram = g; ename = n; elocal = False;
       estart _ = (Obj.magic p : Stream.t te -> Obj.t);
       econtinue _ _ _ = parser [];
       edesc = Dparser (Obj.magic p : Stream.t te -> Obj.t)}
    ;
    external obj : e 'a -> Gramext.g_entry te = "%identity";
    value print e = printf "%a@." print_entry (obj e);
    value find e s = find_entry (obj e) s;
  end
;

value of_entry e = e.egram;

value create_local_entry g n =
  {egram = g; ename = n; elocal = True; estart = empty_entry n;
   econtinue _ _ _ = parser []; edesc = Dlevels []}
;

(* Unsafe *)

value clear_entry e = do {
  e.estart := fun _ -> parser [];
  e.econtinue := fun _ _ _ -> parser [];
  match e.edesc with
  [ Dlevels _ -> e.edesc := Dlevels []
  | Dparser _ -> () ]
};

value gram_reinit g glexer = do {
  Hashtbl.clear g.gtokens;
  g.glexer := glexer
};

module Unsafe =
  struct
    value gram_reinit = gram_reinit;
    value clear_entry = clear_entry;
  end
;

(* Functorial interface *)

module type GLexerType = sig type te = 'x; value lexer : Token.glexer te; end;

module type S =
  sig
    type te = 'x;
    type parsable = 'x;
    value parsable : Stream.t char -> parsable;
    value tokens : string -> list (string * int);
    value glexer : Token.glexer te;
    module Entry :
      sig
        type e 'a = 'x;
        value create : string -> e 'a;
        value parse : e 'a -> parsable -> 'a;
        value parse_token : e 'a -> Stream.t te -> 'a;
        value name : e 'a -> string;
        value of_parser : string -> (Stream.t te -> 'a) -> e 'a;
        value print : e 'a -> unit;
        external obj : e 'a -> Gramext.g_entry te = "%identity";
      end
    ;
    module Unsafe :
      sig
        value gram_reinit : Token.glexer te -> unit;
        value clear_entry : Entry.e 'a -> unit;
      end
    ;
    value extend :
      Entry.e 'a -> option Gramext.position ->
        list
          (option string * option Gramext.g_assoc *
           list (list (Gramext.g_symbol te) * Gramext.g_action)) ->
        unit;
    value delete_rule : Entry.e 'a -> list (Gramext.g_symbol te) -> unit;
  end
;

module GMake (L : GLexerType) =
  struct
    type te = L.te;
    type parsable = gen_parsable te;
    value gram = gcreate L.lexer;
    value parsable cs =
      let (ts, lf) = L.lexer.Token.tok_func cs in
      {pa_chr_strm = cs; pa_tok_strm = ts; pa_loc_func = lf}
    ;
    value tokens = tokens gram;
    value glexer = glexer gram;
    module Entry =
      struct
        type e 'a = g_entry te;
        value create n =
          {egram = gram; ename = n; elocal = False; estart = empty_entry n;
           econtinue _ _ _ = parser []; edesc = Dlevels []}
        ;
        external obj : e 'a -> Gramext.g_entry te = "%identity";
        value parse (e : e 'a) p : 'a =
          Obj.magic (parse_parsable e p : Obj.t)
        ;
        value parse_token (e : e 'a) ts : 'a =
          Obj.magic (e.estart 0 ts : Obj.t)
        ;
        value name e = e.ename;
        value of_parser n (p : Stream.t te -> 'a) : e 'a =
          {egram = gram; ename = n; elocal = False;
           estart _ = (Obj.magic p : Stream.t te -> Obj.t);
           econtinue _ _ _ = parser [];
           edesc = Dparser (Obj.magic p : Stream.t te -> Obj.t)}
        ;
        value print e = printf "%a@." print_entry (obj e);
      end
    ;
    module Unsafe =
      struct
        value gram_reinit = gram_reinit gram;
        value clear_entry = clear_entry;
      end
    ;
    value extend = extend_entry;
    value delete_rule e r = delete_rule (Entry.obj e) r;
  end
;
