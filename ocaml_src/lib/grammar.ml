(* camlp5r *)
(* grammar.ml,v *)
(* Copyright (c) INRIA 2007-2016 *)

(* #load "pa_fstream.cmo" *)

open Gramext;;
open Format;;

let stderr = Pervasives.stderr;;

let rec flatten_tree =
  function
    DeadEnd -> []
  | LocAct (_, _) -> [[]]
  | Node {node = n; brother = b; son = s} ->
      List.map (fun l -> n :: l) (flatten_tree s) @ flatten_tree b
;;

let utf8_print = ref true;;

let utf8_string_escaped s =
  let b = Buffer.create (String.length s) in
  let rec loop i =
    if i = String.length s then Buffer.contents b
    else
      begin
        begin match s.[i] with
          '"' -> Buffer.add_string b "\\\""
        | '\\' -> Buffer.add_string b "\\\\"
        | '\n' -> Buffer.add_string b "\\n"
        | '\t' -> Buffer.add_string b "\\t"
        | '\r' -> Buffer.add_string b "\\r"
        | '\b' -> Buffer.add_string b "\\b"
        | c -> Buffer.add_char b c
        end;
        loop (i + 1)
      end
  in
  loop 0
;;

let string_escaped s =
  if !utf8_print then utf8_string_escaped s else String.escaped s
;;

let print_str ppf s = fprintf ppf "\"%s\"" (string_escaped s);;

let rec print_symbol ppf =
  function
    Sfacto s -> print_symbol ppf s
  | Smeta (n, sl, _) -> print_meta ppf n sl
  | Slist0 s -> fprintf ppf "LIST0 %a" print_symbol1 s
  | Slist0sep (s, t, osep) ->
      fprintf ppf "LIST0 %a SEP %a%s" print_symbol1 s print_symbol1 t
        (if osep then " OPT_SEP" else "")
  | Slist1 s -> fprintf ppf "LIST1 %a" print_symbol1 s
  | Slist1sep (s, t, osep) ->
      fprintf ppf "LIST1 %a SEP %a%s" print_symbol1 s print_symbol1 t
        (if osep then " OPT_SEP" else "")
  | Sopt s -> fprintf ppf "OPT %a" print_symbol1 s
  | Sflag s -> fprintf ppf "FLAG %a" print_symbol1 s
  | Stoken (con, prm) when con <> "" && prm <> "" ->
      fprintf ppf "%s@ %a" con print_str prm
  | Svala (_, s) -> fprintf ppf "V %a" print_symbol s
  | Snterml (e, l) ->
      fprintf ppf "%s%s@ LEVEL@ %a" e.ename (if e.elocal then "*" else "")
        print_str l
  | Snterm _ | Snext | Sself | Stoken _ | Stree _ as s -> print_symbol1 ppf s
and print_meta ppf n sl =
  let rec loop i =
    function
      [] -> ()
    | s :: sl ->
        let j =
          try String.index_from n i ' ' with Not_found -> String.length n
        in
        fprintf ppf "%s %a" (String.sub n i (j - i)) print_symbol1 s;
        if sl = [] then ()
        else
          begin fprintf ppf " "; loop (min (j + 1) (String.length n)) sl end
  in
  loop 0 sl
and print_symbol1 ppf =
  function
    Sfacto s -> print_symbol1 ppf s
  | Snterm e -> fprintf ppf "%s%s" e.ename (if e.elocal then "*" else "")
  | Sself -> pp_print_string ppf "SELF"
  | Snext -> pp_print_string ppf "NEXT"
  | Stoken ("", s) -> print_str ppf s
  | Stoken (con, "") -> pp_print_string ppf con
  | Stree t -> print_level ppf pp_print_space (flatten_tree t)
  | Smeta (_, _, _) | Snterml (_, _) | Slist0 _ | Slist0sep (_, _, _) |
    Slist1 _ | Slist1sep (_, _, _) | Sopt _ | Sflag _ | Stoken _ |
    Svala (_, _) as s ->
      fprintf ppf "(%a)" print_symbol s
and print_rule ppf symbols =
  fprintf ppf "@[<hov 0>";
  let _ =
    List.fold_left
      (fun sep symbol ->
         fprintf ppf "%t%a" sep print_symbol symbol;
         fun ppf -> fprintf ppf ";@ ")
      (fun ppf -> ()) symbols
  in
  fprintf ppf "@]"
and print_level ppf pp_print_space rules =
  fprintf ppf "@[<hov 0>[ ";
  let _ =
    List.fold_left
      (fun sep rule ->
         fprintf ppf "%t%a" sep print_rule rule;
         fun ppf -> fprintf ppf "%a| " pp_print_space ())
      (fun ppf -> ()) rules
  in
  fprintf ppf " ]@]"
;;

let print_levels ppf elev =
  let _ =
    List.fold_left
      (fun sep lev ->
         let rules =
           List.map (fun t -> Sself :: t) (flatten_tree lev.lsuffix) @
           flatten_tree lev.lprefix
         in
         fprintf ppf "%t@[<hov 2>" sep;
         begin match lev.lname with
           Some n -> fprintf ppf "%a@;<1 2>" print_str n
         | None -> ()
         end;
         begin match lev.assoc with
           LeftA -> fprintf ppf "LEFTA"
         | RightA -> fprintf ppf "RIGHTA"
         | NonA -> fprintf ppf "NONA"
         end;
         fprintf ppf "@]@;<1 2>";
         print_level ppf pp_force_newline rules;
         fun ppf -> fprintf ppf "@,| ")
      (fun ppf -> ()) elev
  in
  ()
;;

let print_entry ppf e =
  fprintf ppf "@[<v 0>[ ";
  begin match e.edesc with
    Dlevels elev -> print_levels ppf elev
  | Dparser _ -> fprintf ppf "<parser>"
  end;
  fprintf ppf " ]@]"
;;

let iter_entry f e =
  let treated = ref [] in
  let rec do_entry e =
    if List.memq e !treated then ()
    else
      begin
        treated := e :: !treated;
        f e;
        match e.edesc with
          Dlevels ll -> List.iter do_level ll
        | Dparser _ -> ()
      end
  and do_level lev = do_tree lev.lsuffix; do_tree lev.lprefix
  and do_tree =
    function
      Node n -> do_node n
    | LocAct (_, _) | DeadEnd -> ()
  and do_node n = do_symbol n.node; do_tree n.son; do_tree n.brother
  and do_symbol =
    function
      Sfacto s -> do_symbol s
    | Smeta (_, sl, _) -> List.iter do_symbol sl
    | Snterm e -> do_entry e
    | Snterml (e, _) -> do_entry e
    | Slist0 s -> do_symbol s
    | Slist1 s -> do_symbol s
    | Sopt s -> do_symbol s
    | Sflag s -> do_symbol s
    | Slist0sep (s1, s2, _) -> do_symbol s1; do_symbol s2
    | Slist1sep (s1, s2, _) -> do_symbol s1; do_symbol s2
    | Stree t -> do_tree t
    | Svala (_, s) -> do_symbol s
    | Sself | Snext | Stoken _ -> ()
  in
  do_entry e
;;

let fold_entry f e init =
  let treated = ref [] in
  let rec do_entry accu e =
    if List.memq e !treated then accu
    else
      begin
        treated := e :: !treated;
        let accu = f e accu in
        match e.edesc with
          Dlevels ll -> List.fold_left do_level accu ll
        | Dparser _ -> accu
      end
  and do_level accu lev =
    let accu = do_tree accu lev.lsuffix in do_tree accu lev.lprefix
  and do_tree accu =
    function
      Node n -> do_node accu n
    | LocAct (_, _) | DeadEnd -> accu
  and do_node accu n =
    let accu = do_symbol accu n.node in
    let accu = do_tree accu n.son in do_tree accu n.brother
  and do_symbol accu =
    function
      Sfacto s -> do_symbol accu s
    | Smeta (_, sl, _) -> List.fold_left do_symbol accu sl
    | Snterm e -> do_entry accu e
    | Snterml (e, _) -> do_entry accu e
    | Slist0 s -> do_symbol accu s
    | Slist1 s -> do_symbol accu s
    | Sopt s -> do_symbol accu s
    | Sflag s -> do_symbol accu s
    | Slist0sep (s1, s2, _) -> do_symbol (do_symbol accu s1) s2
    | Slist1sep (s1, s2, _) -> do_symbol (do_symbol accu s1) s2
    | Stree t -> do_tree accu t
    | Svala (_, s) -> do_symbol accu s
    | Sself | Snext | Stoken _ -> accu
  in
  do_entry init e
;;

let floc = ref (fun _ -> failwith "internal error when computing location");;

let loc_of_token_interval bp ep =
  if bp == ep then
    if bp == 0 then Ploc.dummy else Ploc.after (!floc (bp - 1)) 0 1
  else
    let loc1 = !floc bp in let loc2 = !floc (pred ep) in Ploc.encl loc1 loc2
;;

let rec name_of_symbol entry =
  function
    Snterm e -> "[" ^ e.ename ^ "]"
  | Snterml (e, l) -> "[" ^ e.ename ^ " level " ^ l ^ "]"
  | Sself | Snext -> "[" ^ entry.ename ^ "]"
  | Stoken tok -> entry.egram.glexer.Plexing.tok_text tok
  | _ -> "???"
;;

let rec get_token_list entry tokl last_tok tree =
  match tree with
    Node {node = Stoken tok; son = son; brother = DeadEnd} ->
      get_token_list entry (last_tok :: tokl) (tok, None) son
  | Node {node = Svala (ls, Stoken tok); son = son; brother = DeadEnd} ->
      get_token_list entry (last_tok :: tokl) (tok, Some ls) son
  | _ ->
      if tokl = [] then None
      else Some (List.rev (last_tok :: tokl), last_tok, tree)
;;

let rec name_of_symbol_failed entry =
  function
    Sfacto s -> name_of_symbol_failed entry s
  | Slist0 s -> name_of_symbol_failed entry s
  | Slist0sep (s, _, _) -> name_of_symbol_failed entry s
  | Slist1 s -> name_of_symbol_failed entry s
  | Slist1sep (s, _, _) -> name_of_symbol_failed entry s
  | Sopt s -> name_of_symbol_failed entry s
  | Sflag s -> name_of_symbol_failed entry s
  | Stree t -> name_of_tree_failed entry t
  | Svala (_, s) -> name_of_symbol_failed entry s
  | Smeta (_, s :: _, _) -> name_of_symbol_failed entry s
  | s -> name_of_symbol entry s
and name_of_tree_failed entry =
  function
    Node {node = s; brother = bro; son = son} ->
      let tokl =
        match s with
          Stoken tok -> get_token_list entry [] (tok, None) son
        | Svala (ls, Stoken tok) -> get_token_list entry [] (tok, Some ls) son
        | _ -> None
      in
      begin match tokl with
        None ->
          let txt = name_of_symbol_failed entry s in
          let txt =
            match s, son with
              Sopt _, Node _ -> txt ^ " or " ^ name_of_tree_failed entry son
            | _ -> txt
          in
          let txt =
            match bro with
              DeadEnd | LocAct (_, _) -> txt
            | Node _ -> txt ^ " or " ^ name_of_tree_failed entry bro
          in
          txt
      | Some (tokl, last_tok, son) ->
          List.fold_left
            (fun s (tok, _) ->
               (if s = "" then "" else s ^ " ") ^
               entry.egram.glexer.Plexing.tok_text tok)
            "" tokl
      end
  | DeadEnd | LocAct (_, _) -> "???"
;;

let search_tree_in_entry prev_symb tree =
  function
    Dlevels levels ->
      let rec search_levels =
        function
          [] -> tree
        | level :: levels ->
            match search_level level with
              Some tree -> tree
            | None -> search_levels levels
      and search_level level =
        match search_tree level.lsuffix with
          Some t -> Some (Node {node = Sself; son = t; brother = DeadEnd})
        | None -> search_tree level.lprefix
      and search_tree t =
        if tree <> DeadEnd && t == tree then Some t
        else
          match t with
            Node n ->
              begin match search_symbol n.node with
                Some symb ->
                  Some (Node {node = symb; son = n.son; brother = DeadEnd})
              | None ->
                  match search_tree n.son with
                    Some t ->
                      Some (Node {node = n.node; son = t; brother = DeadEnd})
                  | None -> search_tree n.brother
              end
          | LocAct (_, _) | DeadEnd -> None
      and search_symbol symb =
        match symb with
          Snterm _ | Snterml (_, _) | Slist0 _ | Slist0sep (_, _, _) |
          Slist1 _ | Slist1sep (_, _, _) | Sopt _ | Stoken _ | Stree _
          when symb == prev_symb ->
            Some symb
        | Slist0 symb ->
            begin match search_symbol symb with
              Some symb -> Some (Slist0 symb)
            | None -> None
            end
        | Slist0sep (symb, sep, b) ->
            begin match search_symbol symb with
              Some symb -> Some (Slist0sep (symb, sep, b))
            | None ->
                match search_symbol sep with
                  Some sep -> Some (Slist0sep (symb, sep, b))
                | None -> None
            end
        | Slist1 symb ->
            begin match search_symbol symb with
              Some symb -> Some (Slist1 symb)
            | None -> None
            end
        | Slist1sep (symb, sep, b) ->
            begin match search_symbol symb with
              Some symb -> Some (Slist1sep (symb, sep, b))
            | None ->
                match search_symbol sep with
                  Some sep -> Some (Slist1sep (symb, sep, b))
                | None -> None
            end
        | Sopt symb ->
            begin match search_symbol symb with
              Some symb -> Some (Sopt symb)
            | None -> None
            end
        | Stree t ->
            begin match search_tree t with
              Some t -> Some (Stree t)
            | None -> None
            end
        | _ -> None
      in
      search_levels levels
  | Dparser _ -> tree
;;

let error_verbose = ref false;;

let tree_failed entry prev_symb_result prev_symb tree =
  let txt = name_of_tree_failed entry tree in
  let txt =
    match prev_symb with
      Slist0 s ->
        let txt1 = name_of_symbol_failed entry s in
        txt1 ^ " or " ^ txt ^ " expected"
    | Slist1 s ->
        let txt1 = name_of_symbol_failed entry s in
        txt1 ^ " or " ^ txt ^ " expected"
    | Slist0sep (s, sep, _) ->
        begin match Obj.magic prev_symb_result with
          [] ->
            let txt1 = name_of_symbol_failed entry s in
            txt1 ^ " or " ^ txt ^ " expected"
        | _ ->
            let txt1 = name_of_symbol_failed entry sep in
            txt1 ^ " or " ^ txt ^ " expected"
        end
    | Slist1sep (s, sep, _) ->
        begin match Obj.magic prev_symb_result with
          [] ->
            let txt1 = name_of_symbol_failed entry s in
            txt1 ^ " or " ^ txt ^ " expected"
        | _ ->
            let txt1 = name_of_symbol_failed entry sep in
            txt1 ^ " or " ^ txt ^ " expected"
        end
    | Sopt _ | Sflag _ | Stree _ | Svala (_, _) -> txt ^ " expected"
    | _ -> txt ^ " expected after " ^ name_of_symbol_failed entry prev_symb
  in
  if !error_verbose then
    begin let tree = search_tree_in_entry prev_symb tree entry.edesc in
      let ppf = err_formatter in
      fprintf ppf "@[<v 0>@,";
      fprintf ppf "----------------------------------@,";
      fprintf ppf "Parse error in entry [%s], rule:@;<0 2>" entry.ename;
      fprintf ppf "@[";
      print_level ppf pp_force_newline (flatten_tree tree);
      fprintf ppf "@]@,";
      fprintf ppf "----------------------------------@,";
      fprintf ppf "@]@."
    end;
  txt ^ " (in [" ^ entry.ename ^ "])"
;;

let symb_failed entry prev_symb_result prev_symb symb =
  let tree = Node {node = symb; brother = DeadEnd; son = DeadEnd} in
  tree_failed entry prev_symb_result prev_symb tree
;;

external app : Obj.t -> 'a = "%identity";;

let is_level_labelled n lev =
  match lev.lname with
    Some n1 -> n = n1
  | None -> false
;;

let level_number entry lab =
  let rec lookup levn =
    function
      [] -> failwith ("unknown level " ^ lab)
    | lev :: levs ->
        if is_level_labelled lab lev then levn else lookup (succ levn) levs
  in
  match entry.edesc with
    Dlevels elev -> lookup 0 elev
  | Dparser _ -> raise Not_found
;;

let rec top_symb entry =
  function
    Sself | Snext -> Snterm entry
  | Snterml (e, _) -> Snterm e
  | Slist1sep (s, sep, b) -> Slist1sep (top_symb entry s, sep, b)
  | _ -> raise Stream.Failure
;;

let entry_of_symb entry =
  function
    Sself | Snext -> entry
  | Snterm e -> e
  | Snterml (e, _) -> e
  | _ -> raise Stream.Failure
;;

let top_tree entry =
  function
    Node {node = s; brother = bro; son = son} ->
      Node {node = top_symb entry s; brother = bro; son = son}
  | LocAct (_, _) | DeadEnd -> raise Stream.Failure
;;

let skip_if_empty bp p strm =
  if Stream.count strm == bp then Gramext.action (fun a -> p strm)
  else raise Stream.Failure
;;

let continue entry bp a s son p1 (strm__ : _ Stream.t) =
  let a = (entry_of_symb entry s).econtinue 0 bp a strm__ in
  let act =
    try p1 strm__ with
      Stream.Failure -> raise (Stream.Error (tree_failed entry a s son))
  in
  Gramext.action (fun _ -> app act a)
;;

let do_recover parser_of_tree entry nlevn alevn bp a s son
    (strm__ : _ Stream.t) =
  try parser_of_tree entry nlevn alevn (top_tree entry son) strm__ with
    Stream.Failure ->
      try
        skip_if_empty bp (fun (strm__ : _ Stream.t) -> raise Stream.Failure)
          strm__
      with Stream.Failure ->
        continue entry bp a s son (parser_of_tree entry nlevn alevn son)
          strm__
;;

let strict_parsing = ref false;;

let recover parser_of_tree entry nlevn alevn bp a s son strm =
  if !strict_parsing then raise (Stream.Error (tree_failed entry a s son))
  else do_recover parser_of_tree entry nlevn alevn bp a s son strm
;;

let token_count = ref 0;;

let peek_nth n strm =
  let list = Stream.npeek n strm in
  token_count := Stream.count strm + n;
  let rec loop list n =
    match list, n with
      x :: _, 1 -> Some x
    | _ :: l, n -> loop l (n - 1)
    | [], _ -> None
  in
  loop list n
;;

let item_skipped = ref false;;
let skip_item a = item_skipped := true; a;;

let call_and_push ps al strm =
  item_skipped := false;
  let a = ps strm in
  let al = if !item_skipped then al else a :: al in item_skipped := false; al
;;

let bcall_and_push ps al strm =
  item_skipped := false;
  match ps strm with
    Some (a, strm, Fstream.K kont) ->
      let rec kont2 kont () =
        item_skipped := false;
        match kont () with
          Some (a, strm, Fstream.K kont) ->
            let al = if !item_skipped then al else a :: al in
            item_skipped := false; Some (al, strm, Fstream.K (kont2 kont))
        | None -> None
      in
      let al = if !item_skipped then al else a :: al in
      item_skipped := false; Some (al, strm, Fstream.K (kont2 kont))
  | None -> None
;;

let rec parser_of_tree entry nlevn alevn =
  function
    DeadEnd -> (fun (strm__ : _ Stream.t) -> raise Stream.Failure)
  | LocAct (act, _) -> (fun (strm__ : _ Stream.t) -> act)
  | Node {node = Sself; son = LocAct (act, _); brother = DeadEnd} ->
      (fun (strm__ : _ Stream.t) ->
         let a = entry.estart alevn strm__ in app act a)
  | Node {node = Sself; son = LocAct (act, _); brother = bro} ->
      let p2 = parser_of_tree entry nlevn alevn bro in
      (fun (strm__ : _ Stream.t) ->
         match
           try Some (entry.estart alevn strm__) with Stream.Failure -> None
         with
           Some a -> app act a
         | _ -> p2 strm__)
  | Node {node = s; son = son; brother = DeadEnd} ->
      let tokl =
        match s with
          Stoken tok -> get_token_list entry [] (tok, None) son
        | Svala (ls, Stoken tok) -> get_token_list entry [] (tok, Some ls) son
        | _ -> None
      in
      begin match tokl with
        None ->
          let ps = parser_of_symbol entry nlevn s in
          let p1 = parser_of_tree entry nlevn alevn son in
          let p1 = parser_cont p1 entry nlevn alevn s son in
          (fun (strm__ : _ Stream.t) ->
             let bp = Stream.count strm__ in
             let a = ps strm__ in
             let act =
               try p1 bp a strm__ with
                 Stream.Failure -> raise (Stream.Error "")
             in
             app act a)
      | Some (tokl, (last_tok, svala), son) ->
          let lt =
            let t = Stoken last_tok in
            match svala with
              Some l -> Svala (l, t)
            | None -> t
          in
          let p1 = parser_of_tree entry nlevn alevn son in
          let p1 = parser_cont p1 entry nlevn alevn lt son in
          parser_of_token_list entry.egram p1 tokl
      end
  | Node {node = s; son = son; brother = bro} ->
      let tokl =
        match s with
          Stoken tok -> get_token_list entry [] (tok, None) son
        | Svala (ls, Stoken tok) -> get_token_list entry [] (tok, Some ls) son
        | _ -> None
      in
      match tokl with
        None ->
          let ps = parser_of_symbol entry nlevn s in
          let p1 = parser_of_tree entry nlevn alevn son in
          let p1 = parser_cont p1 entry nlevn alevn s son in
          let p2 = parser_of_tree entry nlevn alevn bro in
          (fun (strm__ : _ Stream.t) ->
             let bp = Stream.count strm__ in
             match try Some (ps strm__) with Stream.Failure -> None with
               Some a ->
                 let act =
                   try p1 bp a strm__ with
                     Stream.Failure -> raise (Stream.Error "")
                 in
                 app act a
             | _ -> p2 strm__)
      | Some (tokl, (last_tok, vala), son) ->
          let lt =
            let t = Stoken last_tok in
            match vala with
              Some ls -> Svala (ls, t)
            | None -> t
          in
          let p1 = parser_of_tree entry nlevn alevn son in
          let p1 = parser_cont p1 entry nlevn alevn lt son in
          let p1 = parser_of_token_list entry.egram p1 tokl in
          let p2 = parser_of_tree entry nlevn alevn bro in
          fun (strm__ : _ Stream.t) ->
            try p1 strm__ with Stream.Failure -> p2 strm__
and parser_cont p1 entry nlevn alevn s son bp a (strm__ : _ Stream.t) =
  try p1 strm__ with
    Stream.Failure ->
      try recover parser_of_tree entry nlevn alevn bp a s son strm__ with
        Stream.Failure -> raise (Stream.Error (tree_failed entry a s son))
and parser_of_token_list gram p1 tokl =
  let rec loop n =
    function
      (tok, vala) :: tokl ->
        let tematch =
          let tematch = gram.glexer.Plexing.tok_match tok in
          match vala with
            Some al ->
              let pa =
                match al with
                  [] ->
                    let t = "V " ^ fst tok in
                    gram.glexer.Plexing.tok_match (t, "")
                | al ->
                    let rec loop =
                      function
                        a :: al ->
                          let pa = gram.glexer.Plexing.tok_match ("V", a) in
                          let pal = loop al in
                          (fun tok ->
                             try pa tok with Stream.Failure -> pal tok)
                      | [] -> fun tok -> raise Stream.Failure
                    in
                    loop al
              in
              (fun tok ->
                 try Obj.repr (Ploc.VaAnt (Obj.magic (pa tok : string))) with
                   Stream.Failure -> Obj.repr (Ploc.VaVal (tematch tok)))
          | None -> fun tok -> Obj.repr (tematch tok : string)
        in
        begin match tokl with
          [] ->
            let ps strm =
              match peek_nth n strm with
                Some tok ->
                  let r = tematch tok in
                  for i = 1 to n do Stream.junk strm done; Obj.repr r
              | None -> raise Stream.Failure
            in
            (fun (strm__ : _ Stream.t) ->
               let bp = Stream.count strm__ in
               let a = ps strm__ in
               let act =
                 try p1 bp a strm__ with
                   Stream.Failure -> raise (Stream.Error "")
               in
               app act a)
        | _ ->
            let ps strm =
              match peek_nth n strm with
                Some tok -> tematch tok
              | None -> raise Stream.Failure
            in
            let p1 = loop (n + 1) tokl in
            fun (strm__ : _ Stream.t) ->
              let a = ps strm__ in let act = p1 strm__ in app act a
        end
    | [] -> invalid_arg "parser_of_token_list"
  in
  loop 1 tokl
and parser_of_symbol entry nlevn =
  function
    Sfacto s -> parser_of_symbol entry nlevn s
  | Smeta (_, symbl, act) ->
      let act = Obj.magic act entry symbl in
      Obj.magic
        (List.fold_left
           (fun act symb -> Obj.magic act (parser_of_symbol entry nlevn symb))
           act symbl)
  | Slist0 s ->
      let ps = call_and_push (parser_of_symbol entry nlevn s) in
      let rec loop al (strm__ : _ Stream.t) =
        match try Some (ps al strm__) with Stream.Failure -> None with
          Some al -> loop al strm__
        | _ -> al
      in
      (fun (strm__ : _ Stream.t) ->
         let a = loop [] strm__ in Obj.repr (List.rev a))
  | Slist0sep (symb, sep, false) ->
      let ps = call_and_push (parser_of_symbol entry nlevn symb) in
      let pt = parser_of_symbol entry nlevn sep in
      let rec kont al (strm__ : _ Stream.t) =
        match try Some (pt strm__) with Stream.Failure -> None with
          Some v ->
            let al =
              try ps al strm__ with
                Stream.Failure ->
                  raise (Stream.Error (symb_failed entry v sep symb))
            in
            kont al strm__
        | _ -> al
      in
      (fun (strm__ : _ Stream.t) ->
         match try Some (ps [] strm__) with Stream.Failure -> None with
           Some al -> let a = kont al strm__ in Obj.repr (List.rev a)
         | _ -> Obj.repr [])
  | Slist0sep (symb, sep, true) ->
      let ps = call_and_push (parser_of_symbol entry nlevn symb) in
      let pt = parser_of_symbol entry nlevn sep in
      let rec kont al (strm__ : _ Stream.t) =
        match try Some (pt strm__) with Stream.Failure -> None with
          Some v ->
            begin match
              (try Some (ps al strm__) with Stream.Failure -> None)
            with
              Some al -> kont al strm__
            | _ -> al
            end
        | _ -> al
      in
      (fun (strm__ : _ Stream.t) ->
         match try Some (ps [] strm__) with Stream.Failure -> None with
           Some al -> let a = kont al strm__ in Obj.repr (List.rev a)
         | _ -> Obj.repr [])
  | Slist1 s ->
      let ps = call_and_push (parser_of_symbol entry nlevn s) in
      let rec loop al (strm__ : _ Stream.t) =
        match try Some (ps al strm__) with Stream.Failure -> None with
          Some al -> loop al strm__
        | _ -> al
      in
      (fun (strm__ : _ Stream.t) ->
         let al = ps [] strm__ in
         let a = loop al strm__ in Obj.repr (List.rev a))
  | Slist1sep (symb, sep, false) ->
      let ps = call_and_push (parser_of_symbol entry nlevn symb) in
      let pt = parser_of_symbol entry nlevn sep in
      let rec kont al (strm__ : _ Stream.t) =
        match try Some (pt strm__) with Stream.Failure -> None with
          Some v ->
            let al =
              try ps al strm__ with
                Stream.Failure ->
                  let a =
                    try parse_top_symb entry symb strm__ with
                      Stream.Failure ->
                        raise (Stream.Error (symb_failed entry v sep symb))
                  in
                  a :: al
            in
            kont al strm__
        | _ -> al
      in
      (fun (strm__ : _ Stream.t) ->
         let al = ps [] strm__ in
         let a = kont al strm__ in Obj.repr (List.rev a))
  | Slist1sep (symb, sep, true) ->
      let ps = call_and_push (parser_of_symbol entry nlevn symb) in
      let pt = parser_of_symbol entry nlevn sep in
      let rec kont al (strm__ : _ Stream.t) =
        match try Some (pt strm__) with Stream.Failure -> None with
          Some v ->
            begin match
              (try Some (ps al strm__) with Stream.Failure -> None)
            with
              Some al -> kont al strm__
            | _ ->
                match
                  try Some (parse_top_symb entry symb strm__) with
                    Stream.Failure -> None
                with
                  Some a -> kont (a :: al) strm__
                | _ -> al
            end
        | _ -> al
      in
      (fun (strm__ : _ Stream.t) ->
         let al = ps [] strm__ in
         let a = kont al strm__ in Obj.repr (List.rev a))
  | Sopt s ->
      let ps = parser_of_symbol entry nlevn s in
      (fun (strm__ : _ Stream.t) ->
         match try Some (ps strm__) with Stream.Failure -> None with
           Some a -> Obj.repr (Some a)
         | _ -> Obj.repr None)
  | Sflag s ->
      let ps = parser_of_symbol entry nlevn s in
      (fun (strm__ : _ Stream.t) ->
         match try Some (ps strm__) with Stream.Failure -> None with
           Some _ -> Obj.repr true
         | _ -> Obj.repr false)
  | Stree t ->
      let pt = parser_of_tree entry 1 0 t in
      (fun (strm__ : _ Stream.t) ->
         let bp = Stream.count strm__ in
         let a = pt strm__ in
         let ep = Stream.count strm__ in
         let loc = loc_of_token_interval bp ep in app a loc)
  | Svala (al, s) ->
      let pa =
        match al with
          [] ->
            let t =
              match s with
                Sflag _ -> Some "V FLAG"
              | Sopt _ -> Some "V OPT"
              | Slist0 _ | Slist0sep (_, _, _) -> Some "V LIST"
              | Slist1 _ | Slist1sep (_, _, _) -> Some "V LIST"
              | Stoken (con, "") -> Some ("V " ^ con)
              | _ -> None
            in
            begin match t with
              Some t -> parser_of_token entry (t, "")
            | None -> fun (strm__ : _ Stream.t) -> raise Stream.Failure
            end
        | al ->
            let rec loop =
              function
                a :: al ->
                  let pa = parser_of_token entry ("V", a) in
                  let pal = loop al in
                  (fun (strm__ : _ Stream.t) ->
                     try pa strm__ with Stream.Failure -> pal strm__)
              | [] -> fun (strm__ : _ Stream.t) -> raise Stream.Failure
            in
            loop al
      in
      let ps = parser_of_symbol entry nlevn s in
      (fun (strm__ : _ Stream.t) ->
         match try Some (pa strm__) with Stream.Failure -> None with
           Some a -> Obj.repr (Ploc.VaAnt (Obj.magic a : string))
         | _ -> let a = ps strm__ in Obj.repr (Ploc.VaVal a))
  | Snterm e -> (fun (strm__ : _ Stream.t) -> e.estart 0 strm__)
  | Snterml (e, l) ->
      (fun (strm__ : _ Stream.t) -> e.estart (level_number e l) strm__)
  | Sself -> (fun (strm__ : _ Stream.t) -> entry.estart 0 strm__)
  | Snext -> (fun (strm__ : _ Stream.t) -> entry.estart nlevn strm__)
  | Stoken tok -> parser_of_token entry tok
and parser_of_token entry tok =
  let f = entry.egram.glexer.Plexing.tok_match tok in
  fun strm ->
    match Stream.peek strm with
      Some tok -> let r = f tok in Stream.junk strm; Obj.repr r
    | None -> raise Stream.Failure
and parse_top_symb entry symb =
  parser_of_symbol entry 0 (top_symb entry symb)
;;

let symb_failed_txt e s1 s2 = symb_failed e 0 s1 s2;;

let rec continue_parser_of_levels entry clevn =
  function
    [] -> (fun levn bp a (strm__ : _ Stream.t) -> raise Stream.Failure)
  | lev :: levs ->
      let p1 = continue_parser_of_levels entry (succ clevn) levs in
      match lev.lsuffix with
        DeadEnd -> p1
      | tree ->
          let alevn =
            match lev.assoc with
              LeftA | NonA -> succ clevn
            | RightA -> clevn
          in
          let p2 = parser_of_tree entry (succ clevn) alevn tree in
          fun levn bp a strm ->
            if levn > clevn then p1 levn bp a strm
            else
              let (strm__ : _ Stream.t) = strm in
              try p1 levn bp a strm__ with
                Stream.Failure ->
                  let act = p2 strm__ in
                  let ep = Stream.count strm__ in
                  let a = app act a (loc_of_token_interval bp ep) in
                  entry.econtinue levn bp a strm
;;

let rec start_parser_of_levels entry clevn =
  function
    [] -> (fun levn (strm__ : _ Stream.t) -> raise Stream.Failure)
  | lev :: levs ->
      let p1 = start_parser_of_levels entry (succ clevn) levs in
      match lev.lprefix with
        DeadEnd -> p1
      | tree ->
          let alevn =
            match lev.assoc with
              LeftA | NonA -> succ clevn
            | RightA -> clevn
          in
          let p2 = parser_of_tree entry (succ clevn) alevn tree in
          match levs with
            [] ->
              (fun levn strm ->
                 (* this code should be there but is commented to preserve
                    compatibility with previous versions... with this code,
                    the grammar entry e: [[ "x"; a = e | "y" ]] should fail
                    because it should be: e: [RIGHTA[ "x"; a = e | "y" ]]...
                 if levn > clevn then match strm with parser []
                 else
                 *)
                 let (strm__ : _ Stream.t) = strm in
                 let bp = Stream.count strm__ in
                 let act = p2 strm__ in
                 let ep = Stream.count strm__ in
                 let a = app act (loc_of_token_interval bp ep) in
                 entry.econtinue levn bp a strm)
          | _ ->
              fun levn strm ->
                if levn > clevn then p1 levn strm
                else
                  let (strm__ : _ Stream.t) = strm in
                  let bp = Stream.count strm__ in
                  match try Some (p2 strm__) with Stream.Failure -> None with
                    Some act ->
                      let ep = Stream.count strm__ in
                      let a = app act (loc_of_token_interval bp ep) in
                      entry.econtinue levn bp a strm
                  | _ -> p1 levn strm__
;;

let continue_parser_of_entry entry =
  match entry.edesc with
    Dlevels elev ->
      let p = continue_parser_of_levels entry 0 elev in
      (fun levn bp a (strm__ : _ Stream.t) ->
         try p levn bp a strm__ with Stream.Failure -> a)
  | Dparser p -> fun levn bp a (strm__ : _ Stream.t) -> raise Stream.Failure
;;

let empty_entry ename levn strm =
  raise (Stream.Error ("entry [" ^ ename ^ "] is empty"))
;;

let start_parser_of_entry entry =
  match entry.edesc with
    Dlevels [] -> empty_entry entry.ename
  | Dlevels elev -> start_parser_of_levels entry 0 elev
  | Dparser p -> fun levn strm -> p strm
;;

(* version for backtracking parsers *)

let backtrack_stalling_limit = ref 10000;;
let backtrack_parse = ref false;;
let backtrack_trace = ref false;;
let backtrack_trace_try = ref false;;

let s = try Sys.getenv "CAMLP5PARAM" with Not_found -> "" in
let rec loop i =
  if i = String.length s then ()
  else if s.[i] = 'b' then begin backtrack_parse := true; loop (i + 1) end
  else if s.[i] = 'l' && i + 1 < String.length s && s.[i+1] = '=' then
    let (n, i) =
      let rec loop n i =
        if i = String.length s then n, i
        else if s.[i] >= '0' && s.[i] <= '9' then
          loop (10 * n + Char.code s.[i] - Char.code '0') (i + 1)
        else n, i
      in
      loop 0 (i + 2)
    in
    backtrack_stalling_limit := n; loop i
  else if s.[i] = 't' then begin backtrack_trace := true; loop (i + 1) end
  else if s.[i] = 'y' then begin backtrack_trace_try := true; loop (i + 1) end
  else loop (i + 1)
in
loop 0;;

let tind = ref "";;
let max_fcount = ref 0;;
let nb_ftry = ref 0;;

let rec btop_symb entry =
  function
    Sself | Snext -> Some (Snterm entry)
  | Snterml (e, _) -> Some (Snterm e)
  | Slist1sep (s, sep, b) ->
      begin match btop_symb entry s with
        Some s -> Some (Slist1sep (s, sep, b))
      | None -> None
      end
  | _ -> None
;;

let btop_tree entry son strm =
  match son with
    Node {node = s; brother = bro; son = son} ->
      begin match btop_symb entry s with
        Some sy ->
          let r = Node {node = sy; brother = bro; son = son} in
          let _ =
            if !backtrack_trace then
              begin
                Printf.eprintf "recovering pos %d\n" (Fstream.count strm);
                flush stderr
              end
          in
          Fstream.b_act r strm
      | None -> None
      end
  | LocAct (_, _) | DeadEnd -> None
;;

let brecover bparser_of_tree entry next_levn assoc_levn bp a s son
    (strm__ : _ Fstream.t) =
  Fstream.b_seq (fun strm__ -> btop_tree entry son strm__)
    (fun t strm__ ->
       Fstream.b_seq
         (fun strm__ -> bparser_of_tree entry next_levn assoc_levn t strm__)
         Fstream.b_act strm__)
    strm__
;;

let rec bparser_of_tree entry next_levn assoc_levn =
  function
    DeadEnd -> (fun (strm__ : _ Fstream.t) -> None)
  | LocAct (act, _) ->
      (fun (strm__ : _ Fstream.t) -> Fstream.b_act act strm__)
  | Node {node = Sself; son = LocAct (act, _); brother = DeadEnd} ->
      (fun (strm__ : _ Fstream.t) ->
         Fstream.b_seq (fun strm__ -> entry.bstart assoc_levn strm__)
           (fun a strm__ -> Fstream.b_act (app act a) strm__) strm__)
  | Node {node = Sself; son = LocAct (act, _); brother = bro} ->
      let p2 = bparser_of_tree entry next_levn assoc_levn bro in
      (fun (strm__ : _ Fstream.t) ->
         Fstream.b_or
           (fun strm__ ->
              Fstream.b_seq (fun strm__ -> entry.bstart assoc_levn strm__)
                (fun a strm__ -> Fstream.b_act (app act a) strm__) strm__)
           (fun strm__ -> Fstream.b_seq p2 Fstream.b_act strm__) strm__)
  | Node {node = s; son = son; brother = DeadEnd} ->
      let ps = bparser_of_symbol entry next_levn s in
      let p1 = bparser_of_tree entry next_levn assoc_levn son in
      let p1 = bparser_cont p1 entry next_levn assoc_levn s son in
      (fun (strm__ : _ Fstream.t) ->
         let bp = Fstream.count strm__ in
         Fstream.b_seq ps
           (fun a strm__ ->
              Fstream.b_seq (fun strm__ -> p1 bp a strm__)
                (fun act strm__ -> Fstream.b_act (app act a) strm__) strm__)
           strm__)
  | Node {node = s; son = son; brother = bro} ->
      let ps = bparser_of_symbol entry next_levn s in
      let p1 = bparser_of_tree entry next_levn assoc_levn son in
      let p1 = bparser_cont p1 entry next_levn assoc_levn s son in
      let p2 = bparser_of_tree entry next_levn assoc_levn bro in
      fun (strm__ : _ Fstream.t) ->
        let bp = Fstream.count strm__ in
        Fstream.b_or
          (fun strm__ ->
             Fstream.b_seq ps
               (fun a strm__ ->
                  Fstream.b_seq (fun strm__ -> p1 bp a strm__)
                    (fun act strm__ -> Fstream.b_act (app act a) strm__)
                    strm__)
               strm__)
          (fun strm__ -> Fstream.b_seq p2 Fstream.b_act strm__) strm__
and bparser_cont p1 entry next_levn assoc_levn s son bp a
    (strm__ : _ Fstream.t) =
  Fstream.b_or (fun strm__ -> Fstream.b_seq p1 Fstream.b_act strm__)
    (fun strm__ ->
       Fstream.b_seq
         (fun strm__ ->
            brecover bparser_of_tree entry next_levn assoc_levn bp a s son
              strm__)
         Fstream.b_act strm__)
    strm__
and bparser_of_symbol entry next_levn =
  function
    Sfacto s -> bparser_of_symbol entry next_levn s
  | Smeta (_, symbl, act) ->
      let act = Obj.magic act entry symbl in
      Obj.magic
        (List.fold_left
           (fun act symb ->
              Obj.magic act (bparser_of_symbol entry next_levn symb))
           act symbl)
  | Slist0 s ->
      let ps = bcall_and_push (bparser_of_symbol entry next_levn s) in
      let rec loop al (strm__ : _ Fstream.t) =
        Fstream.b_or
          (fun strm__ ->
             Fstream.b_seq (fun strm__ -> ps al strm__)
               (fun al strm__ ->
                  Fstream.b_seq (fun strm__ -> loop al strm__) Fstream.b_act
                    strm__)
               strm__)
          (fun strm__ -> Fstream.b_act al strm__) strm__
      in
      (fun (strm__ : _ Fstream.t) ->
         Fstream.b_seq (fun strm__ -> loop [] strm__)
           (fun a strm__ -> Fstream.b_act (Obj.repr (List.rev a)) strm__)
           strm__)
  | Slist0sep (symb, sep, false) ->
      let ps = bcall_and_push (bparser_of_symbol entry next_levn symb) in
      let pt = bparser_of_symbol entry next_levn sep in
      let rec kont al (strm__ : _ Fstream.t) =
        Fstream.b_or
          (fun strm__ ->
             Fstream.b_seq pt
               (fun v strm__ ->
                  Fstream.b_seq (fun strm__ -> ps al strm__)
                    (fun al strm__ ->
                       Fstream.b_seq (fun strm__ -> kont al strm__)
                         Fstream.b_act strm__)
                    strm__)
               strm__)
          (fun strm__ -> Fstream.b_act al strm__) strm__
      in
      (fun (strm__ : _ Fstream.t) ->
         Fstream.b_or
           (fun strm__ ->
              Fstream.b_seq (fun strm__ -> ps [] strm__)
                (fun al strm__ ->
                   Fstream.b_seq (fun strm__ -> kont al strm__)
                     (fun a strm__ ->
                        Fstream.b_act (Obj.repr (List.rev a)) strm__)
                     strm__)
                strm__)
           (fun strm__ -> Fstream.b_act (Obj.repr []) strm__) strm__)
  | Slist0sep (symb, sep, true) ->
      failwith "LIST0 _ SEP _ OPT_SEP not implemented; please report"
  | Slist1 s ->
      let ps = bcall_and_push (bparser_of_symbol entry next_levn s) in
      let rec loop al (strm__ : _ Fstream.t) =
        Fstream.b_or
          (fun strm__ ->
             Fstream.b_seq (fun strm__ -> ps al strm__)
               (fun al strm__ ->
                  Fstream.b_seq (fun strm__ -> loop al strm__) Fstream.b_act
                    strm__)
               strm__)
          (fun strm__ -> Fstream.b_act al strm__) strm__
      in
      (fun (strm__ : _ Fstream.t) ->
         Fstream.b_seq (fun strm__ -> ps [] strm__)
           (fun al strm__ ->
              Fstream.b_seq (fun strm__ -> loop al strm__)
                (fun a strm__ -> Fstream.b_act (Obj.repr (List.rev a)) strm__)
                strm__)
           strm__)
  | Slist1sep (symb, sep, true) ->
      failwith "LIST1 _ SEP _ OPT_SEP not implemented; please report"
  | Slist1sep (symb, sep, false) ->
      let ps = bcall_and_push (bparser_of_symbol entry next_levn symb) in
      let pt = bparser_of_symbol entry next_levn sep in
      let rec kont al (strm__ : _ Fstream.t) =
        Fstream.b_or
          (fun strm__ ->
             Fstream.b_seq pt
               (fun v strm__ ->
                  Fstream.b_seq
                    (fun strm__ ->
                       (fun (strm__ : _ Fstream.t) ->
                          Fstream.b_or
                            (fun strm__ ->
                               Fstream.b_seq (fun strm__ -> ps al strm__)
                                 Fstream.b_act strm__)
                            (fun strm__ ->
                               Fstream.b_seq
                                 (fun strm__ ->
                                    bparse_top_symb entry symb strm__)
                                 (fun a strm__ ->
                                    Fstream.b_act (a :: al) strm__)
                                 strm__)
                            strm__)
                         strm__)
                    (fun al strm__ ->
                       Fstream.b_seq (fun strm__ -> kont al strm__)
                         Fstream.b_act strm__)
                    strm__)
               strm__)
          (fun strm__ -> Fstream.b_act al strm__) strm__
      in
      (fun (strm__ : _ Fstream.t) ->
         Fstream.b_seq (fun strm__ -> ps [] strm__)
           (fun al strm__ ->
              Fstream.b_seq (fun strm__ -> kont al strm__)
                (fun a strm__ -> Fstream.b_act (Obj.repr (List.rev a)) strm__)
                strm__)
           strm__)
  | Sopt s ->
      let ps = bparser_of_symbol entry next_levn s in
      (fun (strm__ : _ Fstream.t) ->
         Fstream.b_or
           (fun strm__ ->
              Fstream.b_seq ps
                (fun a strm__ -> Fstream.b_act (Obj.repr (Some a)) strm__)
                strm__)
           (fun strm__ -> Fstream.b_act (Obj.repr None) strm__) strm__)
  | Sflag s ->
      let ps = bparser_of_symbol entry next_levn s in
      (fun (strm__ : _ Fstream.t) ->
         Fstream.b_or
           (fun strm__ ->
              Fstream.b_seq ps
                (fun _ strm__ -> Fstream.b_act (Obj.repr true) strm__) strm__)
           (fun strm__ -> Fstream.b_act (Obj.repr false) strm__) strm__)
  | Stree t ->
      let pt = bparser_of_tree entry 1 0 t in
      (fun (strm__ : _ Fstream.t) ->
         let bp = Fstream.count strm__ in
         Fstream.b_seq pt
           (fun a strm__ ->
              let ep = Fstream.count strm__ in
              Fstream.b_act
                (let loc = loc_of_token_interval bp ep in app a loc) strm__)
           strm__)
  | Svala (al, s) ->
      let pa =
        match al with
          [] ->
            let t =
              match s with
                Sflag _ -> Some "V FLAG"
              | Sopt _ -> Some "V OPT"
              | Slist0 _ | Slist0sep (_, _, _) -> Some "V LIST"
              | Slist1 _ | Slist1sep (_, _, _) -> Some "V LIST"
              | Stoken (con, "") -> Some ("V " ^ con)
              | _ -> None
            in
            begin match t with
              Some t -> bparser_of_token entry (t, "")
            | None -> fun (strm__ : _ Fstream.t) -> None
            end
        | al ->
            let rec loop =
              function
                a :: al ->
                  let pa = bparser_of_token entry ("V", a) in
                  let pal = loop al in
                  (fun (strm__ : _ Fstream.t) ->
                     Fstream.b_or
                       (fun strm__ -> Fstream.b_seq pa Fstream.b_act strm__)
                       (fun strm__ -> Fstream.b_seq pal Fstream.b_act strm__)
                       strm__)
              | [] -> fun (strm__ : _ Fstream.t) -> None
            in
            loop al
      in
      let ps = bparser_of_symbol entry next_levn s in
      (fun (strm__ : _ Fstream.t) ->
         Fstream.b_or
           (fun strm__ ->
              Fstream.b_seq pa
                (fun a strm__ ->
                   Fstream.b_act
                     (Obj.repr (Ploc.VaAnt (Obj.magic a : string))) strm__)
                strm__)
           (fun strm__ ->
              Fstream.b_seq ps
                (fun a strm__ ->
                   Fstream.b_act (Obj.repr (Ploc.VaVal a)) strm__)
                strm__)
           strm__)
  | Snterm e ->
      (fun (strm__ : _ Fstream.t) ->
         Fstream.b_seq (fun strm__ -> e.bstart 0 strm__) Fstream.b_act strm__)
  | Snterml (e, l) ->
      (fun (strm__ : _ Fstream.t) ->
         Fstream.b_seq (fun strm__ -> e.bstart (level_number e l) strm__)
           Fstream.b_act strm__)
  | Sself ->
      (fun (strm__ : _ Fstream.t) ->
         Fstream.b_seq (fun strm__ -> entry.bstart 0 strm__) Fstream.b_act
           strm__)
  | Snext ->
      (fun (strm__ : _ Fstream.t) ->
         Fstream.b_seq (fun strm__ -> entry.bstart next_levn strm__)
           Fstream.b_act strm__)
  | Stoken tok -> bparser_of_token entry tok
and bparser_of_token entry tok =
  let f = entry.egram.glexer.Plexing.tok_match tok in
  fun strm ->
    let _ =
      if !backtrack_trace then
        begin
          Printf.eprintf "%stesting (\"%s\", \"%s\") ..." !tind (fst tok)
            (snd tok);
          flush stderr
        end
    in
    let _ =
      if !backtrack_stalling_limit > 0 || !backtrack_trace_try then
        if Fstream.count strm > !max_fcount then
          begin max_fcount := Fstream.count strm; nb_ftry := 0 end
        else
          begin
            incr nb_ftry;
            if !backtrack_trace_try then
              begin
                Printf.eprintf "\rtokens read: %d; tokens tests: %d "
                  !max_fcount !nb_ftry;
                flush stderr
              end;
            if !backtrack_stalling_limit > 0 &&
               !nb_ftry >= !backtrack_stalling_limit
            then
              begin
                if !backtrack_trace_try then
                  begin Printf.eprintf "\n"; flush stderr end;
                raise Stream.Failure
              end
          end
    in
    match Fstream.next strm with
      Some (tok, strm) ->
        begin try
          let r = f tok in
          let _ =
            if !backtrack_trace then
              begin
                Printf.eprintf " yes!!! \"%s\"\n" (snd (Obj.magic tok));
                flush stderr
              end
          in
          Fstream.b_act (Obj.repr r) strm
        with Stream.Failure ->
          let _ =
            if !backtrack_trace then
              begin
                Printf.eprintf " found (\"%s\", \"%s\")\n"
                  (fst (Obj.magic tok)) (snd (Obj.magic tok));
                flush stderr
              end
          in
          None
        end
    | None ->
        let _ =
          if !backtrack_trace then
            begin Printf.eprintf " eos\n"; flush stderr end
        in
        None
and bparse_top_symb entry symb =
  match btop_symb entry symb with
    Some sy -> bparser_of_symbol entry 0 sy
  | None -> fun (strm__ : _ Fstream.t) -> None
;;

let bcount strm = Fstream.b_act (Fstream.count strm) strm;;

let rec bstart_parser_of_levels entry clevn =
  function
    [] -> (fun levn (strm__ : _ Fstream.t) -> None)
  | lev :: levs ->
      let p1 = bstart_parser_of_levels entry (succ clevn) levs in
      match lev.lprefix with
        DeadEnd -> p1
      | tree ->
          let alevn =
            match lev.assoc with
              LeftA | NonA -> succ clevn
            | RightA -> clevn
          in
          let p2 = bparser_of_tree entry (succ clevn) alevn tree in
          match levs with
            [] ->
              (fun levn strm ->
                 if levn > clevn then let (_ : _ Fstream.t) = strm in None
                 else
                   let (strm__ : _ Fstream.t) = strm in
                   let bp = Fstream.count strm__ in
                   Fstream.b_seq p2
                     (fun act strm__ ->
                        Fstream.b_seq bcount
                          (fun ep strm__ ->
                             Fstream.b_seq
                               (fun strm__ ->
                                  entry.bcontinue levn bp
                                    (app act (loc_of_token_interval bp ep))
                                    strm__)
                               Fstream.b_act strm__)
                          strm__)
                     strm__)
          | _ ->
              fun levn strm ->
                if levn > clevn then p1 levn strm
                else
                  let (strm__ : _ Fstream.t) = strm in
                  let bp = Fstream.count strm__ in
                  Fstream.b_or
                    (fun strm__ ->
                       Fstream.b_seq p2
                         (fun act strm__ ->
                            Fstream.b_seq bcount
                              (fun ep strm__ ->
                                 Fstream.b_seq
                                   (fun strm__ ->
                                      entry.bcontinue levn bp
                                        (app act
                                           (loc_of_token_interval bp ep))
                                        strm__)
                                   Fstream.b_act strm__)
                              strm__)
                         strm__)
                    (fun strm__ ->
                       Fstream.b_seq (fun strm__ -> p1 levn strm__)
                         Fstream.b_act strm__)
                    strm__
;;

let rec bcontinue_parser_of_levels entry clevn =
  function
    [] -> (fun levn bp a (strm__ : _ Fstream.t) -> None)
  | lev :: levs ->
      let p1 = bcontinue_parser_of_levels entry (succ clevn) levs in
      match lev.lsuffix with
        DeadEnd -> p1
      | tree ->
          let alevn =
            match lev.assoc with
              LeftA | NonA -> succ clevn
            | RightA -> clevn
          in
          let p2 = bparser_of_tree entry (succ clevn) alevn tree in
          fun levn bp a strm ->
            if levn > clevn then p1 levn bp a strm
            else
              let (strm__ : _ Fstream.t) = strm in
              Fstream.b_or
                (fun strm__ ->
                   Fstream.b_seq (fun strm__ -> p1 levn bp a strm__)
                     Fstream.b_act strm__)
                (fun strm__ ->
                   Fstream.b_seq p2
                     (fun act strm__ ->
                        Fstream.b_seq bcount
                          (fun ep strm__ ->
                             Fstream.b_seq
                               (fun strm__ ->
                                  entry.bcontinue levn bp
                                    (app act a (loc_of_token_interval bp ep))
                                    strm__)
                               Fstream.b_act strm__)
                          strm__)
                     strm__)
                strm__
;;

let bstart_parser_of_entry entry =
  match entry.edesc with
    Dlevels [] -> (fun _ (strm__ : _ Fstream.t) -> None)
  | Dlevels elev -> bstart_parser_of_levels entry 0 elev
  | Dparser p -> fun levn strm -> failwith "Dparser for Fstream"
;;

let bcontinue_parser_of_entry entry =
  match entry.edesc with
    Dlevels elev ->
      let p = bcontinue_parser_of_levels entry 0 elev in
      (fun levn bp a (strm__ : _ Fstream.t) ->
         Fstream.b_or
           (fun strm__ ->
              Fstream.b_seq (fun strm__ -> p levn bp a strm__) Fstream.b_act
                strm__)
           (fun strm__ -> Fstream.b_act a strm__) strm__)
  | Dparser p -> fun levn bp a (strm__ : _ Fstream.t) -> None
;;

(* Extend syntax *)

let init_entry_functions entry =
  entry.estart <-
    (fun lev strm ->
       let f = start_parser_of_entry entry in entry.estart <- f; f lev strm);
  entry.econtinue <-
    (fun lev bp a strm ->
       let f = continue_parser_of_entry entry in
       entry.econtinue <- f; f lev bp a strm);
  entry.bstart <-
    (fun lev strm ->
       let f = bstart_parser_of_entry entry in
       let f =
         if !backtrack_trace then
           fun lev strm ->
             let t = !tind in
             Printf.eprintf "%s>> start %s lev %d\n" !tind entry.ename lev;
             flush stderr;
             tind := !tind ^ " ";
             try
               let r = f lev strm in
               tind := t;
               Printf.eprintf "%s<< start %s lev %d\n" !tind entry.ename lev;
               flush stderr;
               r
             with e ->
               tind := t;
               Printf.eprintf "%sexception \"%s\"\n" !tind
                 (Printexc.to_string e);
               flush stderr;
               raise e
         else f
       in
       entry.bstart <- f; f lev strm);
  entry.bcontinue <-
    fun lev bp a strm ->
      let f = bcontinue_parser_of_entry entry in
      let f =
        if !backtrack_trace then
          fun lev bp a strm ->
            let t = !tind in
            Printf.eprintf "%s>> continue %s lev %d bp %d pos %d\n" !tind
              entry.ename lev bp (Fstream.count strm);
            flush stderr;
            tind := !tind ^ " ";
            try
              let r = f lev bp a strm in
              tind := t;
              Printf.eprintf "%s<< continue %s lev %d %d\n" !tind entry.ename
                lev bp;
              flush stderr;
              r
            with e ->
              tind := t;
              Printf.eprintf "%sexception \"%s\"\n" !tind
                (Printexc.to_string e);
              flush stderr;
              raise e
        else f
      in
      entry.bcontinue <- f; f lev bp a strm
;;

let reinit_entry_functions entry =
  match entry.edesc with
    Dlevels elev -> init_entry_functions entry
  | _ -> ()
;;

let extend_entry entry position rules =
  try
    let elev = Gramext.levels_of_rules entry position rules in
    entry.edesc <- Dlevels elev; init_entry_functions entry
  with Plexing.Error s ->
    Printf.eprintf "Lexer initialization error:\n- %s\n" s;
    flush stderr;
    failwith "Grammar.extend"
;;

let extend entry_rules_list =
  let gram = ref None in
  List.iter
    (fun (entry, position, rules) ->
       begin match !gram with
         Some g ->
           if g != entry.egram then
             begin
               Printf.eprintf "Error: entries with different grammars\n";
               flush stderr;
               failwith "Grammar.extend"
             end
       | None -> gram := Some entry.egram
       end;
       extend_entry entry position rules)
    entry_rules_list
;;

(* Deleting a rule *)

let delete_rule entry sl =
  match entry.edesc with
    Dlevels levs ->
      let levs = Gramext.delete_rule_in_level_list entry sl levs in
      entry.edesc <- Dlevels levs;
      entry.estart <-
        (fun lev strm ->
           let f = start_parser_of_entry entry in
           entry.estart <- f; f lev strm);
      entry.econtinue <-
        (fun lev bp a strm ->
           let f = continue_parser_of_entry entry in
           entry.econtinue <- f; f lev bp a strm);
      entry.bstart <-
        (fun lev strm ->
           let f = bstart_parser_of_entry entry in
           entry.bstart <- f; f lev strm);
      entry.bcontinue <-
        (fun lev bp a strm ->
           let f = bcontinue_parser_of_entry entry in
           entry.bcontinue <- f; f lev bp a strm)
  | Dparser _ -> ()
;;

type parse_algorithm =
  Gramext.parse_algorithm = Predictive | Backtracking | DefaultAlgorithm
;;

let warning_verbose = Gramext.warning_verbose;;

(* Normal interface *)

type token = string * string;;
type g = token Gramext.grammar;;

let create_toktab () = Hashtbl.create 301;;
let gcreate glexer =
  {gtokens = create_toktab (); glexer = glexer; galgo = DefaultAlgorithm}
;;

let set_algorithm g algo = g.galgo <- algo;;

let tokens g con =
  let list = ref [] in
  Hashtbl.iter
    (fun (p_con, p_prm) c -> if p_con = con then list := (p_prm, !c) :: !list)
    g.gtokens;
  !list
;;

let glexer g = g.glexer;;

type 'te gen_parsable =
  { pa_chr_strm : char Stream.t;
    pa_tok_strm : 'te Stream.t;
    mutable pa_tok_fstrm : 'te Fstream.t;
    pa_loc_func : Plexing.location_function }
;;

type parsable = token gen_parsable;;

let parsable g cs =
  let (ts, lf) = g.glexer.Plexing.tok_func cs in
  let fts =
    Fstream.from
      (fun _ ->
         match Stream.peek ts with
           None -> None
         | x -> Stream.junk ts; x)
  in
  {pa_chr_strm = cs; pa_tok_strm = ts; pa_tok_fstrm = fts; pa_loc_func = lf}
;;

let parse_parsable entry p =
  let efun = entry.estart 0 in
  let ts = p.pa_tok_strm in
  let cs = p.pa_chr_strm in
  let fun_loc = p.pa_loc_func in
  let restore =
    let old_floc = !floc in
    let old_tc = !token_count in
    fun () -> floc := old_floc; token_count := old_tc
  in
  let get_loc () =
    try
      let cnt = Stream.count ts in
      let loc = fun_loc cnt in
      if !token_count - 1 <= cnt then loc
      else Ploc.encl loc (fun_loc (!token_count - 1))
    with Failure _ -> Ploc.make_unlined (Stream.count cs, Stream.count cs + 1)
  in
  floc := fun_loc;
  token_count := 0;
  try let r = efun ts in restore (); r with
    Stream.Failure ->
      let loc = get_loc () in
      restore ();
      Ploc.raise loc (Stream.Error ("illegal begin of " ^ entry.ename))
  | Stream.Error _ as exc ->
      let loc = get_loc () in restore (); Ploc.raise loc exc
  | exc ->
      let loc = Stream.count cs, Stream.count cs + 1 in
      restore (); Ploc.raise (Ploc.make_unlined loc) exc
;;

let bparse_parsable entry p =
  let efun = entry.bstart 0 in
  let fts = p.pa_tok_fstrm in
  let cs = p.pa_chr_strm in
  let fun_loc = p.pa_loc_func in
  let restore =
    let old_floc = !floc in
    let old_tc = !token_count in
    let old_max_fcount = !max_fcount in
    let old_nb_ftry = !nb_ftry in
    fun () ->
      floc := old_floc;
      token_count := old_tc;
      max_fcount := old_max_fcount;
      nb_ftry := old_nb_ftry
  in
  let get_loc () =
    try
      let cnt = Fstream.count_unfrozen fts - 1 in
      let loc = fun_loc cnt in
      if !token_count - 1 <= cnt then loc
      else Ploc.encl loc (fun_loc (!token_count - 1))
    with Failure _ -> Ploc.make_unlined (Stream.count cs, Stream.count cs + 1)
  in
  floc := fun_loc;
  token_count := 0;
  max_fcount := 0;
  nb_ftry := 0;
  if !backtrack_trace_try then begin Printf.eprintf "\n"; flush stderr end;
  try
    let r = efun fts in
    restore ();
    match r with
      Some (r, strm, _) -> p.pa_tok_fstrm <- strm; r
    | None -> raise Stream.Failure
  with
    Stream.Failure ->
      let loc = get_loc () in restore (); Ploc.raise loc (Stream.Error "")
  | exc ->
      let loc = Stream.count cs, Stream.count cs + 1 in
      restore (); Ploc.raise (Ploc.make_unlined loc) exc
;;

let bparse_parsable_all entry p =
  let efun = entry.bstart 0 in
  let fts = p.pa_tok_fstrm in
  let cs = p.pa_chr_strm in
  let fun_loc = p.pa_loc_func in
  let restore =
    let old_floc = !floc in
    let old_tc = !token_count in
    let old_max_fcount = !max_fcount in
    let old_nb_ftry = !nb_ftry in
    fun () ->
      floc := old_floc;
      token_count := old_tc;
      max_fcount := old_max_fcount;
      nb_ftry := old_nb_ftry
  in
  floc := fun_loc;
  token_count := 0;
  max_fcount := 0;
  nb_ftry := 0;
  if !backtrack_trace_try then begin Printf.eprintf "\n"; flush stderr end;
  try
    let rl =
      let rec loop rev_rl =
        function
          Some (r, strm, k) ->
            let _ =
              if !backtrack_trace then
                begin Printf.eprintf "result found !\n\n"; flush stderr end
            in
            loop (r :: rev_rl) (Fstream.bcontinue k)
        | None -> List.rev rev_rl
      in
      loop [] (efun fts)
    in
    restore (); rl
  with exc ->
    let loc = Stream.count cs, Stream.count cs + 1 in
    restore (); Ploc.raise (Ploc.make_unlined loc) exc
;;

let find_entry e s =
  let rec find_levels =
    function
      [] -> None
    | lev :: levs ->
        match find_tree lev.lsuffix with
          None ->
            begin match find_tree lev.lprefix with
              None -> find_levels levs
            | x -> x
            end
        | x -> x
  and find_symbol =
    function
      Sfacto s -> find_symbol s
    | Snterm e -> if e.ename = s then Some e else None
    | Snterml (e, _) -> if e.ename = s then Some e else None
    | Smeta (_, sl, _) -> find_symbol_list sl
    | Slist0 s -> find_symbol s
    | Slist0sep (s, _, _) -> find_symbol s
    | Slist1 s -> find_symbol s
    | Slist1sep (s, _, _) -> find_symbol s
    | Sopt s -> find_symbol s
    | Sflag s -> find_symbol s
    | Stree t -> find_tree t
    | Svala (_, s) -> find_symbol s
    | Sself | Snext | Stoken _ -> None
  and find_symbol_list =
    function
      s :: sl ->
        begin match find_symbol s with
          None -> find_symbol_list sl
        | x -> x
        end
    | [] -> None
  and find_tree =
    function
      Node {node = s; brother = bro; son = son} ->
        begin match find_symbol s with
          None ->
            begin match find_tree bro with
              None -> find_tree son
            | x -> x
            end
        | x -> x
        end
    | LocAct (_, _) | DeadEnd -> None
  in
  match e.edesc with
    Dlevels levs ->
      begin match find_levels levs with
        Some e -> e
      | None -> raise Not_found
      end
  | Dparser _ -> raise Not_found
;;

module Entry =
  struct
    type te = token;;
    type 'a e = te g_entry;;
    let create g n =
      {egram = g; ename = n; elocal = false; estart = empty_entry n;
       econtinue = (fun _ _ _ (strm__ : _ Stream.t) -> raise Stream.Failure);
       bstart = (fun _ (strm__ : _ Fstream.t) -> None);
       bcontinue = (fun _ _ _ (strm__ : _ Fstream.t) -> None);
       edesc = Dlevels []}
    ;;
    let parse_parsable (entry : 'a e) p : 'a =
      match entry.egram.galgo with
        DefaultAlgorithm ->
          if !backtrack_parse then Obj.magic (bparse_parsable entry p : Obj.t)
          else Obj.magic (parse_parsable entry p : Obj.t)
      | Predictive -> Obj.magic (parse_parsable entry p : Obj.t)
      | Backtracking -> Obj.magic (bparse_parsable entry p : Obj.t)
    ;;
    let parse (entry : 'a e) cs : 'a =
      let parsable = parsable entry.egram cs in parse_parsable entry parsable
    ;;
    let parse_parsable_all (entry : 'a e) p : 'a =
      match entry.egram.galgo with
        DefaultAlgorithm ->
          if !backtrack_parse then
            Obj.magic (bparse_parsable_all entry p : Obj.t list)
          else
            begin try Obj.magic [(parse_parsable entry p : Obj.t)] with
              Stream.Failure | Stream.Error _ -> []
            end
      | Predictive ->
          begin try Obj.magic [(parse_parsable entry p : Obj.t)] with
            Stream.Failure | Stream.Error _ -> []
          end
      | Backtracking -> Obj.magic (bparse_parsable_all entry p : Obj.t list)
    ;;
    let parse_all (entry : 'a e) cs : 'a =
      let parsable = parsable entry.egram cs in
      parse_parsable_all entry parsable
    ;;
    let parse_token (entry : 'a e) ts : 'a =
      Obj.magic (entry.estart 0 ts : Obj.t)
    ;;
    let name e = e.ename;;
    let of_parser g n (p : te Stream.t -> 'a) : 'a e =
      {egram = g; ename = n; elocal = false;
       estart = (fun _ -> (Obj.magic p : te Stream.t -> Obj.t));
       econtinue = (fun _ _ _ (strm__ : _ Stream.t) -> raise Stream.Failure);
       bstart =
         (fun _ fstrm ->
            let ts =
              let fts = ref fstrm in
              Stream.from
                (fun _ ->
                   match Fstream.next !fts with
                     Some (v, fstrm) -> fts := fstrm; Some v
                   | None -> None)
            in
            try
              let r : Obj.t = Obj.magic p ts in
              let fstrm =
                let rec loop fstrm i =
                  if i = 0 then fstrm
                  else
                    match Fstream.next fstrm with
                      Some (_, fstrm) -> loop fstrm (i - 1)
                    | None -> failwith "internal error in Entry.of_parser"
                in
                loop fstrm (Stream.count ts)
              in
              Fstream.b_act r fstrm
            with Stream.Failure -> None);
       bcontinue = (fun _ _ _ (strm__ : _ Fstream.t) -> None);
       edesc = Dparser (Obj.magic p : te Stream.t -> Obj.t)}
    ;;
    external obj : 'a e -> te Gramext.g_entry = "%identity";;
    let print ppf e = fprintf ppf "%a@." print_entry (obj e);;
    let find e s = find_entry (obj e) s;;
  end
;;

let of_entry e = e.egram;;

let create_local_entry g n =
  {egram = g; ename = n; elocal = true; estart = empty_entry n;
   econtinue = (fun _ _ _ (strm__ : _ Stream.t) -> raise Stream.Failure);
   bstart = (fun _ (strm__ : _ Fstream.t) -> None);
   bcontinue = (fun _ _ _ (strm__ : _ Fstream.t) -> None); edesc = Dlevels []}
;;

(* Unsafe *)

let clear_entry e =
  e.estart <- (fun _ (strm__ : _ Stream.t) -> raise Stream.Failure);
  e.econtinue <- (fun _ _ _ (strm__ : _ Stream.t) -> raise Stream.Failure);
  e.bstart <- (fun _ (strm__ : _ Fstream.t) -> None);
  e.bcontinue <- (fun _ _ _ (strm__ : _ Fstream.t) -> None);
  match e.edesc with
    Dlevels _ -> e.edesc <- Dlevels []
  | Dparser _ -> ()
;;

let gram_reinit g glexer = Hashtbl.clear g.gtokens; g.glexer <- glexer;;

module Unsafe =
  struct
    let gram_reinit = gram_reinit;;
    let clear_entry = clear_entry;;
  end
;;

(* Functorial interface *)

module type GLexerType = sig type te;; val lexer : te Plexing.lexer;; end;;

module type S =
  sig
    type te;;
    type parsable;;
    val parsable : char Stream.t -> parsable;;
    val tokens : string -> (string * int) list;;
    val glexer : te Plexing.lexer;;
    val set_algorithm : parse_algorithm -> unit;;
    module Entry :
      sig
        type 'a e;;
        val create : string -> 'a e;;
        val parse : 'a e -> parsable -> 'a;;
        val parse_token : 'a e -> te Stream.t -> 'a;;
        val name : 'a e -> string;;
        val of_parser : string -> (te Stream.t -> 'a) -> 'a e;;
        val print : Format.formatter -> 'a e -> unit;;
        external obj : 'a e -> te Gramext.g_entry = "%identity";;
      end
    ;;
    module Unsafe :
      sig
        val gram_reinit : te Plexing.lexer -> unit;;
        val clear_entry : 'a Entry.e -> unit;;
      end
    ;;
    val extend :
      'a Entry.e -> Gramext.position option ->
        (string option * Gramext.g_assoc option *
           (te Gramext.g_symbol list * Gramext.g_action) list)
          list ->
        unit;;
    val delete_rule : 'a Entry.e -> te Gramext.g_symbol list -> unit;;
  end
;;

module GMake (L : GLexerType) =
  struct
    type te = L.te;;
    type parsable = te gen_parsable;;
    let gram = gcreate L.lexer;;
    let parsable cs =
      let (ts, lf) = L.lexer.Plexing.tok_func cs in
      let fts =
        Fstream.from
          (fun _ ->
             match Stream.peek ts with
               None -> None
             | x -> Stream.junk ts; x)
      in
      {pa_chr_strm = cs; pa_tok_strm = ts; pa_tok_fstrm = fts;
       pa_loc_func = lf}
    ;;
    let tokens = tokens gram;;
    let glexer = glexer gram;;
    let set_algorithm algo = gram.galgo <- algo;;
    module Entry =
      struct
        type 'a e = te g_entry;;
        let create n =
          {egram = gram; ename = n; elocal = false; estart = empty_entry n;
           econtinue =
             (fun _ _ _ (strm__ : _ Stream.t) -> raise Stream.Failure);
           bstart = (fun _ (strm__ : _ Fstream.t) -> None);
           bcontinue = (fun _ _ _ (strm__ : _ Fstream.t) -> None);
           edesc = Dlevels []}
        ;;
        external obj : 'a e -> te Gramext.g_entry = "%identity";;
        let parse (e : 'a e) p : 'a =
          match gram.galgo with
            DefaultAlgorithm ->
              if !backtrack_parse then Obj.magic (bparse_parsable e p : Obj.t)
              else Obj.magic (parse_parsable e p : Obj.t)
          | Predictive -> Obj.magic (parse_parsable e p : Obj.t)
          | Backtracking -> Obj.magic (bparse_parsable e p : Obj.t)
        ;;
        let parse_token (e : 'a e) ts : 'a =
          Obj.magic (e.estart 0 ts : Obj.t)
        ;;
        let name e = e.ename;;
        let of_parser n (p : te Stream.t -> 'a) : 'a e =
          {egram = gram; ename = n; elocal = false;
           estart = (fun _ -> (Obj.magic p : te Stream.t -> Obj.t));
           econtinue =
             (fun _ _ _ (strm__ : _ Stream.t) -> raise Stream.Failure);
           bstart = (fun _ (strm__ : _ Fstream.t) -> None);
           bcontinue = (fun _ _ _ (strm__ : _ Fstream.t) -> None);
           edesc = Dparser (Obj.magic p : te Stream.t -> Obj.t)}
        ;;
        let print ppf e = fprintf ppf "%a@." print_entry (obj e);;
      end
    ;;
    module Unsafe =
      struct
        let gram_reinit = gram_reinit gram;;
        let clear_entry = clear_entry;;
      end
    ;;
    let extend = extend_entry;;
    let delete_rule e r = delete_rule (Entry.obj e) r;;
  end
;;
