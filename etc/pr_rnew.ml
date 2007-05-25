(* camlp4r q_MLast.cmo ./pa_extfun.cmo *)
(* $Id$ *)
(* Copyright (c) INRIA 2007 *)

open Sformat;

module Buff =
  struct
    value buff = ref (String.create 80);
    value store len x = do {
      if len >= String.length buff.val then
        buff.val := buff.val ^ String.create (String.length buff.val)
      else ();
      buff.val.[len] := x;
      succ len
    };
    value mstore len s =
      add_rec len 0 where rec add_rec len i =
        if i == String.length s then len
        else add_rec (store len s.[i]) (succ i)
    ;
    value get len = String.sub buff.val 0 len;
  end
;
(*

(*
 * Getting comments inside phrases.
 *)

value rev_extract_comment strm =
  let rec find_comm len =
    parser
    [ [: `' '; a = find_comm (Buff.store len ' ') :] -> a
    | [: `'\t'; a = find_comm (Buff.mstore len (String.make 8 ' ')) :] -> a
    | [: `'\n'; a = find_comm (Buff.store len '\n') :] -> a
    | [: `')'; a = find_star_bef_rparen (Buff.store len ')') :] -> a
    | [: :] -> 0 ]
  and find_star_bef_rparen len =
    parser
    [ [: `'*'; a = insert (Buff.store len '*') :] -> a
    | [: :] -> 0 ]
  and insert len =
    parser
    [ [: `')'; a = find_star_bef_rparen_in_comm (Buff.store len ')') :] -> a
    | [: `'*'; a = find_lparen_aft_star (Buff.store len '*') :] -> a
    | [: `x; a = insert (Buff.store len x) :] -> a
    | [: :] -> len ]
  and find_star_bef_rparen_in_comm len =
    parser
    [ [: `'*'; len = insert (Buff.store len '*'); s :] -> insert len s
    | [: a = insert len :] -> a ]
  and find_lparen_aft_star len =
    parser
    [ [: `'('; a = while_space (Buff.store len '(') :] -> a
    | [: a = insert len :] -> a ]
  and while_space len =
    parser
    [ [: `' '; a = while_space (Buff.store len ' ') :] -> a
    | [: `'\t'; a = while_space (Buff.mstore len (String.make 8 ' ')) :] -> a
    | [: `'\n'; a = while_space (Buff.store len '\n') :] -> a
    | [: `')'; a = find_star_bef_rparen_again len :] -> a
    | [: :] -> len ]
  and find_star_bef_rparen_again len =
    parser
    [ [: `'*'; a = insert (Buff.mstore len ")*") :] -> a
    | [: :] -> len ]
  in
  let len = find_comm 0 strm in
  let s = Buff.get len in
  loop (len - 1) 0 0 where rec loop i nl_bef ind_bef =
    if i <= 0 then ("", 0, 0)
    else if s.[i] = '\n' then loop (i - 1) (nl_bef + 1) ind_bef
    else if s.[i] = ' ' then loop (i - 1) nl_bef (ind_bef + 1)
    else (
      let s = String.sub s 0 (i + 1) in
      for i = 0 to String.length s / 2 - 1 do
        let t = s.[i] in
        s.[i] := s.[String.length s - i - 1];
        s.[String.length s - i - 1] := t;
      done;
      (s, nl_bef, ind_bef)
    )
;
*)

value file = ref "";

(*
value rev_read_comment_in_file bp ep =
  let strm =
    Stream.from
      (fun i ->
         let j = bp - i - 1 in
         if j < 0 || j >= String.length file.val then None
         else Some file.val.[j])
  in
  rev_extract_comment strm
;

value adjust_comment_indentation ind s nl_bef ind_bef =
  if s = "" then ""
  else
    let (ind_aft, i_bef_ind) =
      loop 0 (String.length s - 1) where rec loop ind_aft i =
        if i >= 0 && s.[i] = ' ' then loop (ind_aft + 1) (i - 1)
        else (ind_aft, i)
    in
    let ind_bef = if nl_bef > 0 then ind_bef else ind in
    let len = i_bef_ind + 1 in
    let olen = Buff.mstore 0 (String.make ind ' ') in
    loop olen 0 where rec loop olen i =
      if i = len then Buff.get olen
      else
        let olen = Buff.store olen s.[i] in
        let (olen, i) =
          if s.[i] = '\n' && (i + 1 = len || s.[i + 1] <> '\n') then
            let delta_ind = if i = i_bef_ind then 0 else ind - ind_bef in
            if delta_ind >= 0 then
              (Buff.mstore olen (String.make delta_ind ' '), i + 1)
            else
              let i =
                loop delta_ind (i + 1) where rec loop cnt i =
                  if cnt = 0 then i
                  else if i = len then i
                  else if s.[i] = ' ' then loop (cnt + 1) (i + 1)
                  else i
              in
              (olen, i)
          else (olen, i + 1)
        in
        loop olen i
;

value comm_bef ind loc =
  let bp = Stdpp.first_pos loc in
  let ep = Stdpp.last_pos loc in
  let (s, nl_bef, ind_bef) = rev_read_comment_in_file bp ep in
  adjust_comment_indentation ind s nl_bef ind_bef
;

value add_nl s =
  if String.length s > 0 && s.[String.length s - 1] <> '\n' then s ^ "\n"
  else s
;

value add_sp s =
  if String.length s > 0 && s.[String.length s - 1] <> ' ' then s ^ " "
  else s
;

value remove_nl s =
  if String.length s > 0 && s.[String.length s - 1] = '\n' then
    String.sub s 0 (String.length s - 1) ^ " "
  else s
;

value indent ind s =
  if s = "" then ""
  else
    let t = String.make ind ' ' in
    loop True 0 0 where rec loop bol len i =
      if i = String.length s then Buff.get len
      else
        let len = if bol && s.[i] <> '\n' then Buff.mstore len t else len in
        loop (s.[i] = '\n') (Buff.store len s.[i]) (i + 1)
;

(*
 * Other functions.
 *)

type alt 'a 'b = [ Left of 'a | Right of 'b ];
*)

value is_infix = do {
  let infixes = Hashtbl.create 73 in
  List.iter (fun s -> Hashtbl.add infixes s True)
    ["!="; "&&"; "*"; "**"; "*."; "+"; "+."; "-"; "-."; "/"; "/."; "<"; "<.";
     "<="; "<=."; "<>"; "<>."; "="; "=."; "=="; ">"; ">."; ">="; ">=."; "@";
     "^"; "asr"; "land"; "lor"; "lsl"; "lsr"; "lxor"; "mod"; "or"; "||";
     "~-"; "~-."];
  fun s -> try Hashtbl.find infixes s with [ Not_found -> False ]
};

(*
value is_implemented_infix = (
  let infixes = Hashtbl.create 73 in
  List.iter (fun s -> Hashtbl.add infixes s True)
    ["!="; "&&"; "*"; "**"; "*."; "+"; "+."; "-"; "-."; "/"; "/."; "<"; "<=";
     "<>"; "="; "=="; ">"; ">="; "@"; "^"; "land"; "lor"; "lsl"; "lxor";
     "mod"; "||"];
  fun s -> try Hashtbl.find infixes s with [ Not_found -> False ]
);
*)

value is_keyword =
  let keywords = ["value"] in
  fun s -> List.mem s keywords
;

value has_special_chars s =
  if String.length s = 0 then False
  else
    match s.[0] with
    [ '0'..'9' | 'A'..'Z' | 'a'..'z' | '_' -> False
    | _ -> True ]
;

(*
value rec is_irrefut_patt =
  fun
  [ <:patt< $lid:_$ >> -> True
  | <:patt< () >> -> True
  | <:patt< _ >> -> True
  | <:patt< ($x$ as $y$) >> -> is_irrefut_patt x && is_irrefut_patt y
  | <:patt< { $list:fpl$ } >> ->
      List.for_all (fun (_, p) -> is_irrefut_patt p) fpl
  | <:patt< ($p$ : $_$) >> -> is_irrefut_patt p
  | <:patt< ($list:pl$) >> -> List.for_all is_irrefut_patt pl
  | <:patt< ? $_$ >> -> True
  | <:patt< ? ($_$ = $_$) >> -> True
  | <:patt< ~ $_$ >> -> True
  | _ -> False ]
;
*)

value not_impl name ind b x k =
  let desc =
    if Obj.tag (Obj.repr x) = Obj.tag (Obj.repr "") then
      sprintf "\"%s\"" (Obj.magic x)
    else if Obj.is_block (Obj.repr x) then
      "tag = " ^ string_of_int (Obj.tag (Obj.repr x))
    else "int_val = " ^ string_of_int (Obj.magic x)
  in
  sprintf "%s\"pr_r: not impl: %s; %s\"%s" b name (String.escaped desc) k
;

value tab ind = String.make ind ' ';

(*
value last_line_starts_with_space ind s =
  try
    let i = String.rindex s '\n' + ind + 1 in
    i < String.length s && s.[i] = ' '
  with
  [ Not_found -> False ]
;
*)

value ident ind b x k =
  horiz_vertic
    (fun nofit ->
       if String.contains x '\n' then nofit () else sprintf "%s%s%s" b x k)
    (fun () -> sprintf "%s%s%s" b x k)
;

value var_escaped ind b v k =
  let x =
    if is_infix v || has_special_chars v then "\\" ^ v
    else if is_keyword v then v ^ "__"
    else v
  in
  ident ind b x k
;

value rec mod_ident ind b sl k =
  match sl with
  [ [] -> sprintf "%s%s" b k
  | [s] -> var_escaped ind b s k
  | [s :: sl] -> mod_ident ind (sprintf "%s%s." b s) sl k ]
;

(*
value option ind elem b z k =
  match z with
  [ Some z -> elem ind b z k
  | None -> sprintf "%s%s" b k ]
;
*)

(* horizontal list *)
value rec hlist elem ind b xl k =
  match xl with
  [ [] -> sprintf "%s%s" b k
  | [x] -> elem ind b x k
  | [x :: xl] -> sprintf "%s %s" (elem ind b x "") (hlist elem ind "" xl k) ]
;

(* vertical list *)
value rec vlist elem ind b xl k =
  match xl with
  [ [] -> sprintf "%s%s" b k
  | [x] -> elem ind b x k
  | [x :: xl] ->
      sprintf "%s\n%s" (elem ind b x "") (vlist elem ind (tab ind) xl k) ]
;

(*
(* list with separator *)
value rec listws1 ind elem b nl xl k =
  match xl with
  [ [] -> sprintf "%s%s" b k
  | [(x, _)] -> elem ind b x k
  | [(x, sep) :: xl] ->
      if nl then
        let s1 = elem ind b x sep in
        let s1 = sprintf "%s\n" s1 in
        let s2 = listws1 ind elem (tab ind) nl xl k in
        sprintf "%s%s" s1 s2
      else listws1 ind elem (elem ind b x (sprintf "%s " sep)) nl xl k ]
;

value listws ind elem b sep nl xl k =
  listws1 ind elem b nl (List.map (fun x -> (x, sep)) xl) k
;

(* list with separator, cumulative *)
value listwscum ind sh elem (b, bsp) xl k =
  let ind_sh = ind + sh in
  let () =
    try
      let _ : int = String.index k '\n' in
      invalid_arg (sprintf "listwscum %s" k)
    with
    [ Not_found -> () ]
  in
  loop ind (b, bsp) xl where rec loop ind (b, bsp) =
    fun
    [ [] -> sprintf "%s%s" b k
    | [(x, _)] -> elem ind (sprintf "%s%s" b bsp) x k
    | [(x, sep1) :: xl] ->
        match
          horiz_vertic (fun _ -> Some (elem 0 (sprintf "%s%s" b bsp) x sep1))
            (fun () -> None)
        with
        [ Some s1 ->
            (* current holds on line; accumulating all next ones which hold
               on line also *)
            let (s, xl) =
              loop s1 xl where rec loop s1 =
                fun
                [ [] ->
                    assert False
                | [(x, sep)] ->
                    horiz_vertic
                      (fun _ -> (elem 0 (sprintf "%s " s1) x k, []))
                      (fun () -> (s1, [(x, sep)]))
                | [(x, sep) :: xl] ->
                    let r =
                      horiz_vertic
                        (fun _ -> Some (elem 0 (sprintf "%s " s1) x sep))
                        (fun () -> None)
                    in
                    match r with
                    [ Some s2 -> loop s2 xl
                    | None -> (s1, [(x, sep) :: xl]) ] ]
            in
            if xl = [] then s
            else if String.length s <= ind_sh then
              (* small left part, typically an apply of a function with
                 a short name *)
              let ind2 = String.length s + 1 in
              loop ind2 (s, " ") xl
            else
              let s1 = sprintf "%s\n" s in
              sprintf "%s%s" s1 (loop ind_sh (tab ind_sh, "") xl)
        | None ->
            (* current does not hold on line; printing it and restarting
               with a fresh line. *)
            let s = elem ind (sprintf "%s%s" b bsp) x sep1 in
            let s1 = sprintf "%s\n" s in
            sprintf "%s%s" s1 (loop ind_sh (tab ind_sh, "") xl) ] ]
;

(* list with separator; trying to print it horizontally; if failing,
   print elements accumulating them into as few lines as possible. *)
value listws_hv ind sh elem b xl k =
  horiz_vertic (fun _ -> listws1 0 elem b False xl k)
    (fun () -> listwscum ind sh elem (b, "") xl k)
;

(* other kind of list with separator... *)
value listws_be ind elem (b, bsp) xl k1 k2 =
  let xl = List.map (fun x -> (x, "")) xl in
  horiz_vertic
    (fun _ ->
       let s =
         listws1 0 elem (sprintf "%s%s" b bsp) False xl
           (sprintf "%s %s" k1 k2)
       in
       ("", s))
    (fun () ->
       let ind1 = String.length b + String.length bsp in
       let sh1 = ind + 2 - ind1 in
       let s = listwscum ind1 sh1 elem (b, bsp) xl k1 in
       let sp = sprintf "%s\n" s in
       (sp, sprintf "%s%s" (tab ind) k2))
;

value sprint_indent ind sh f1 f2 =
  horiz_vertic
    (fun _ ->
       let s = f1 0 False in
       sprintf "%s%s" s (f2 0 " " False))
    (fun () ->
       let s = sprintf "%s\n" (f1 ind True) in
       sprintf "%s%s" s (f2 (ind + sh) (tab (ind + sh)) True))
;

value sprint_indent_unindent ind sh f1 f2 f3 =
  horiz_vertic
    (fun _ ->
       let s = f1 0 in
       let s = sprintf "%s %s" s (f2 0 "" False) in
       sprintf "%s%s" s (f3 0 "" " "))
    (fun () ->
       let s = sprintf "%s\n" (f1 ind) in
       let s = sprintf "%s%s\n" s (f2 (ind + sh) (tab (ind + sh)) True) in
       sprintf "%s%s" s (f3 ind (tab ind) ""))
;
*)

value comma_after elem ind b x k = elem ind b x (sprintf ";%s" k);
value and_before elem ind b x k = elem ind (sprintf "%sand" b) x k;

(*

(* *)

value rec let_and_seq_list_loop letexprlr e =
  match e with
  [ <:expr< let $opt:rf$ $list:pel$ in $e1$ >> ->
      let_and_seq_list_loop [Left (e, rf, pel) :: letexprlr] e1
  | <:expr< do { $list:el$ } >> ->
      (let_and_seq_list_of_list letexprlr el, True)
  | e ->
      (List.rev [Right e :: letexprlr], False) ]
and let_and_seq_list_of_list letexprlr =
  fun
  [ [] -> List.rev letexprlr
  | [e] -> fst (let_and_seq_list_loop letexprlr e)
  | [e :: el] -> let_and_seq_list_of_list [Right e :: letexprlr] el ]
;

value let_and_seq_list = let_and_seq_list_loop [];

value operator ind left right sh b op x y k =
  let op = if op = "" then "" else " " ^ op in
  sprint_indent ind sh (fun ind _ -> left ind b x op)
    (fun ind b _ -> right ind b y k)
;

value left_operator ind sh unfold next b x k =
  let xl =
    loop [] x "" where rec loop xl x op =
      match unfold x with
      [ Some (x1, op1, x2) -> loop [(x2, op) :: xl] x1 op1
      | None -> [(x, op) :: xl] ]
  in
  match xl with
  [ [(x, _)] -> next ind b x k
  | _ -> listws_hv ind sh next b xl k ]
;

value right_operator ind sh unfold next b x k =
  let xl =
    loop [] x where rec loop xl x =
      match unfold x with
      [ Some (x1, op, x2) -> loop [(x1, op) :: xl] x2
      | None -> List.rev [(x, "") :: xl] ]
  in
  match xl with
  [ [(x, _)] -> next ind b x k
  | _ -> listws_hv ind sh next b xl k ]
;
*)

(*
 * Extensible printers
 *)

type printer_t 'a =
  { pr_fun : mutable string -> pr_fun 'a;
    pr_levels : mutable list (pr_level 'a) }
and pr_level 'a = { pr_label : string; pr_rules : mutable pr_rule 'a }
and pr_rule 'a =
  Extfun.t 'a (pr_fun 'a -> pr_fun 'a -> int -> string -> string -> string)
and pr_fun 'a = int -> string -> 'a -> string -> string;

(*
value rec find_pr_level lab =
  fun
  [ [] -> failwith ("level " ^ lab ^ " not found")
  | [lev :: levl] ->
      if lev.pr_label = lab then lev else find_pr_level lab levl ]
;
*)

value printer loc_of name = do {
  let pr_fun name pr lab =
    loop False pr.pr_levels where rec loop app =
      fun
      [ [] -> fun ind b z k ->
          failwith
            (Printf.sprintf "unable to print %s%s" name
               (if lab = "" then "" else " \"" ^ lab ^ "\""))
      | [lev :: levl] ->
          if app || lev.pr_label = lab then
            let next = loop True levl in
            curr where rec curr ind b z k =
              Extfun.apply lev.pr_rules z curr next ind b k
          else loop app levl ]
  in
  let pr = {pr_fun = fun []; pr_levels = []} in
  pr.pr_fun := pr_fun name pr;
  pr
};

value pr_expr = printer MLast.loc_of_expr "expr";
(*
value pr_patt = printer MLast.loc_of_patt "patt";
value pr_ctyp = printer MLast.loc_of_ctyp "type";
*)
value pr_str_item = printer MLast.loc_of_str_item "str_item";
value pr_sig_item = printer MLast.loc_of_sig_item "sig_item";
value pr_module_expr = printer MLast.loc_of_module_expr "module_expr";
(*
value pr_module_type = printer MLast.loc_of_module_type "module_type";
*)

value expr ind b z k = pr_expr.pr_fun "top" ind b z k;
(*
value patt ind b z k = pr_patt.pr_fun "top" ind b z k;
value ctyp ind b z k = pr_ctyp.pr_fun "top" ind b z k;
*)
value str_item ind b z k = pr_str_item.pr_fun "top" ind b z k;
value sig_item ind b z k = pr_sig_item.pr_fun "top" ind b z k;
value module_expr ind b z k = pr_module_expr.pr_fun "top" ind b z k;
(*
value module_type ind b z k = pr_module_type.pr_fun "top" ind b z k;
value expr_fun_args ge = Extfun.apply Pcaml.pr_expr_fun_args.val ge;

value patt_as ind b z k =
  match z with
  [ <:patt< ($x$ as $y$) >> -> patt ind b x (patt ind " as " y k)
  | z -> patt ind b z k ]
;

(* utilities specific to pr_r *)

Pcaml.pr_expr_fun_args.val :=
  extfun Extfun.empty with
  [ <:expr< fun $p$ -> $e$ >> as z ->
      if is_irrefut_patt p then
        let (pl, e) = expr_fun_args e in
        ([p :: pl], e)
      else ([], z)
  | z -> ([], z) ]
;
*)

value binding ind b pe k = not_impl "binding" ind b pe k;

(*
value rec binding_list ind (b, bsp) pel (ksp, k) =
  match pel with
  [ [] -> sprintf "%s%s%s" b ksp k
  | [pe] -> binding ind True (b, bsp) pe (ksp, k)
  | [pe :: pel] ->
      let s1 = binding ind False (b, bsp) pe ("", "") in
      let s1 = sprintf "%s\n" s1 in
      let s2 =
        binding_list ind (sprintf "%sand" (tab ind), " ") pel (ksp, k)
      in
      sprintf "%s%s" s1 s2 ]
and binding ind last (b, bsp) (p, e1) (ksp, k) =
  let (pl, e) = expr_fun_args e1 in
  let (sp, b, e) =
    let (e, k) =
      match e with
      [ <:expr< ($e$ : $t$) >> -> (e, ctyp ind " : " t "")
      | _ -> (e, "") ]
    in
    let (sp, b) = listws_be ind patt (b, bsp) [p :: pl] k "=" in
    (sp, b, e)
  in
  let se =
    horiz_vertic
      (fun nofit ->
         let ccc = comm_bef ind (MLast.loc_of_expr e) in
         if String.contains ccc '\n' then nofit ()
         else expr 0 (sprintf "%s%s " b ccc) e (sprintf "%s%s" ksp k))
      (fun () ->
         let (letexprl, has_seq) = let_and_seq_list e in
         let ind2 = ind + 2 in
         if has_seq then
           let b =
             sprint_indent ind 0 (fun _ _ -> b)
               (fun ind b _ -> sprintf "%s(" b)
           in
           let b = sprintf "%s\n" b in
           let se =
             let_in_and_sequence_combination ind2 (tab ind2) letexprl ""
           in
           sprintf "%s%s\n%s)%s%s" b se (tab ind)
             (if ksp = " " then "\n" ^ tab ind else "") k
         else
           let ccc = comm_bef ind2 (MLast.loc_of_expr e) in
           let sp = sprintf "%s\n%s" b ccc in
           if last then
             let se = expr ind2 (tab ind2) e "" in
             sprintf "%s%s\n%s%s" sp se (tab ind) k
           else
             let se = expr ind2 (tab ind2) e (ksp ^ k) in
             sprintf "%s%s" sp se)
  in
  sprintf "%s%s" sp se
and match_assoc_list ind b pwel k =
  let (nb_cut, _) =
    List.fold_right
      (fun pwe (cnt, k) ->
         (horiz_vertic
            (fun _ -> let _ : string = match_assoc 0 0 b False pwe k in cnt)
            (fun () -> cnt + 1),
          ""))
      pwel (0, k)
  in
  match_assoc_list_loop ind b (nb_cut > 1) pwel k
and match_assoc_list_loop ind b glob_cut pwel k =
  match pwel with
  [ [] -> sprintf "%s%s" b k
  | [pwe] -> match_assoc ind 2 b glob_cut pwe k
  | [pwe :: pwel] ->
      horiz_vertic (fun nofit -> nofit ())
        (fun () ->
           let s = match_assoc ind 2 b glob_cut pwe "" in
           let s1 = sprintf "%s\n" s in
           sprintf "%s%s" s1
             (match_assoc_list_loop ind (sprintf "%s| " (tab ind)) glob_cut
                pwel k)) ]
and match_assoc ind dind b glob_cut (p, w, e) k =
  let when_expr ind _ z k = expr 0 " when " z k in
  horiz_vertic
    (fun nofit ->
       if glob_cut then nofit ()
       else
         let ccc = comm_bef 0 (MLast.loc_of_expr e) in
         if String.contains ccc '\n' then nofit ()
         else
           patt_as 0 b p
             (option 0 when_expr "" w
                (sprintf " -> %s%s" (add_sp ccc) (expr 0 "" e k))))
    (fun () ->
       let (letexprl, has_seq) = let_and_seq_list e in
       let sp =
         let k = if has_seq then " (" else "" in
         let ind = ind + dind in
         match w with
         [ Some e ->
             horiz_vertic
               (fun _ ->
                  patt_as 0 b p (expr 0 " when " e (sprintf " ->%s" k)))
               (fun () ->
                  let sp = patt_as ind b p "" in
                  let sp = sprintf "%s\n" sp in
                  let k = sprintf " ->%s" k in
                  let se =
                    sprint_indent ind 4
                      (fun ind2 nl ->
                         let ind = if nl then ind2 + 2 else ind in
                         sprintf "%swhen" (tab ind))
                      (fun ind b nl -> expr ind b e k)
                  in
                  sprintf "%s%s" sp se)
         | None -> patt_as ind b p (sprintf " ->%s" k) ]
       in
       let sp = sprintf "%s\n" sp in
       if has_seq then
         let ind2 = ind + dind + 2 in
         let se =
           let_in_and_sequence_combination ind2 (tab ind2) letexprl ""
         in
         sprintf "%s%s\n%s)%s" sp se (tab (ind + dind)) k
       else
         let ccc = comm_bef (ind + dind + 2) (MLast.loc_of_expr e) in
         let sp = sprintf "%s%s" sp (add_nl ccc) in
         let se = expr (ind + dind + 2) (tab (ind + dind + 2)) e k in
         sprintf "%s%s" sp se)
and let_in_and_sequence_combination ind b letexprl k =
  loop "" b letexprl where rec loop s b =
    fun
    [ [] ->
        sprintf "%s%s" s b
    | [Right e] ->
        let ccc = comm_bef ind (MLast.loc_of_expr e) in
        let s = sprintf "%s%s" s ccc in
        sprintf "%s%s" s (expr ind b e k)
    | [Left (e, rf, pel) :: l] ->
        let ccc = comm_bef ind (MLast.loc_of_expr e) in
        let s = sprintf "%s%s" s ccc in
        let b = sprintf "%s%s" b (if rf then "let rec" else "let") in
        let sb = binding_list ind (b, " ") pel (" ", "in") in
        let s = sprintf "%s%s\n" s sb in
        loop s (tab ind) l
    | [Right e :: l] ->
        let ccc = comm_bef ind (MLast.loc_of_expr e) in
        let s = sprintf "%s%s" s ccc in
        let s = sprintf "%s%s\n" s (expr ind b e ";") in
        loop s (tab ind) l ]
;

value record_assoc elem ind b (lab, x) k =
  sprint_indent ind 2 (fun ind _ -> patt ind b lab " =")
    (fun ind b _ -> elem ind b x k)
;

value rec make_expr_list =
  fun
  [ <:expr< [$x$ :: $y$] >> ->
      let (xl, c) = make_expr_list y in
      ([x :: xl], c)
  | <:expr< [] >> -> ([], None)
  | x -> ([], Some x) ]
;

value rec make_patt_list =
  fun
  [ <:patt< [$x$ :: $y$] >> ->
      let (xl, c) = make_patt_list y in
      ([x :: xl], c)
  | <:patt< [] >> -> ([], None)
  | x -> ([], Some x) ]
;

value x_list ind elem b (xl, c) k =
  let ini =
    match c with
    [ None -> ("", [])
    | Some x -> (" ::", [(x, "")]) ]
  in
  let (_, xl) =
    List.fold_right (fun x (sep, xl) -> (";", [(x, sep) :: xl])) xl ini
  in
  listws_hv (ind + 1) 0 elem (sprintf "%s[" b) xl (sprintf "]%s" k)
;

value rec type_params ind b l k =
  match l with
  [ [(s, vari) :: l] ->
      let b =
        match vari with
        [ (True, False) -> sprintf "%s+" b
        | (False, True) -> sprintf "%s-" b
        | _ -> b ]
      in
      sprintf " %s'%s%s%s" b s "" (type_params ind "" l k)
  | [] -> sprintf "%s%s" b k ]
;

value type_decl ind last b ((_, tn), tp, te, cl) k =
  let tn = var_escaped ind "" tn "" in
  if last then
    sprint_indent_unindent ind 2
      (fun ind -> sprintf "%s %s%s =" b tn (type_params ind "" tp ""))
      (fun ind b _ ->
         ctyp ind b te
           (sprintf "%s%s" (if cl = [] then "" else " \"constraint\"") ""))
      (fun ind b _ -> sprintf "%s%s" b k)
  else
    sprint_indent ind 2
      (fun ind _ -> sprintf "%s %s%s =" b tn (type_params ind "" tp ""))
      (fun ind b _ ->
         ctyp ind b te
           (sprintf "%s%s" (if cl = [] then "" else " \"constraint\"") k))
;

value rec type_decl_list ind b tdl k =
  match tdl with
  [ [] -> sprintf "%s%s" b k
  | [td] -> type_decl ind True b td k
  | [td :: tdl] ->
      let () = horiz_vertic (fun nofit -> nofit ()) (fun () -> ()) in
      let s1 = type_decl ind False b td "" in
      let s1 = sprintf "%s\n" s1 in
      sprintf "%s%s" s1
        (type_decl_list ind (sprintf "%sand" (tab ind)) tdl k) ]
;

(* definitions of printers by decreasing level *)

value ctyp_top =
  extfun Extfun.empty with
  [ <:ctyp< $x$ == $y$ >> ->
      fun curr next ind b k -> operator ind next next 2 b "==" x y k
  | z -> fun curr next ind b k -> next ind b z k ]
;

value ctyp_arrow =
  extfun Extfun.empty with
  [ z ->
      fun curr next ind b k ->
        let unfold =
          fun
          [ <:ctyp< $x$ -> $y$ >> -> Some (x, " ->", y)
          | _ -> None ]
        in
        right_operator ind 2 unfold next b z k ]
;

value ctyp_apply =
  extfun Extfun.empty with
  [ z ->
      fun curr next ind b k ->
        let unfold =
          fun
          [ <:ctyp< $x$ $y$ >> -> Some (x, "", y)
          | _ -> None ]
        in
        left_operator ind 0 unfold next b z k ]
;

value ctyp_dot =
  extfun Extfun.empty with
  [ <:ctyp< $x$ . $y$ >> ->
      fun curr next ind b k -> curr ind (curr ind b x ".") y k
  | z -> fun curr next ind b k -> next ind b z k ]
;

value ctyp_simple =
  extfun Extfun.empty with
  [ <:ctyp< ($x$ as $y$) >> ->
      fun curr next ind b k ->
        sprint_indent (ind + 1) 2
          (fun ind _ -> ctyp 0 (sprintf "%s(" b) x " as")
          (fun ind b _ -> ctyp ind b y (sprintf ")%s" k))
  | <:ctyp< { $list:ltl$ } >> ->
      fun curr next ind b k ->
        horiz_vertic
          (fun _ ->
             listws 0
               (fun ind b (_, l, m, t) k ->
                  let sm = if m then "mutable " else "" in
                  ctyp ind (sprintf "%s%s : %s" b l sm) t k)
               (sprintf "%s{ " b) ";" False ltl (sprintf " }%s" k))
          (fun () ->
             listws (ind + 2)
               (fun ind b (_, l, m, t) k ->
                  let b = sprintf "%s%s :" b l in
                  let sm = if m then "mutable " else "" in
                  sprint_indent ind 2 (fun _ _ -> b)
                    (fun ind b _ -> ctyp ind (sprintf "%s%s" b sm) t k))
               (sprintf "%s{ " b) ";" True ltl (sprintf " }%s" k))
  | <:ctyp< [= $list:rfl$ ] >> as t ->
      fun curr next ind b k ->
        let vdl =
          List.map
            (fun rf ->
               match rf with
               [ <:row_field< `$s$ of $opt:_$ $list:tl$ >> ->
                   (MLast.loc_of_ctyp t, s, tl)
               | <:row_field< $t$ >> -> (MLast.loc_of_ctyp t, "Foo", []) ])
            rfl
        in
        let loc = MLast.loc_of_ctyp t in
        curr ind b <:ctyp< [ $list:vdl$ ] >> k
  | <:ctyp< [ $list:vdl$ ] >> ->
      fun curr next ind b k ->
        horiz_vertic
          (fun _ ->
             if vdl = [] then sprintf "%s[ ]%s" b k
             else
               listws 0
                 (fun ind b (_, c, tl) k ->
                    if tl = [] then sprintf "%s%s%s" b c k
                    else
                      listws ind ctyp (sprintf "%s%s of " b c) " and" False
                        tl k)
                 (sprintf "%s[ " b) " |" False vdl (" ]" ^ k))
          (fun () ->
             let sep = sprintf "%s| " (tab ind) in
             loop (sprintf "%s[ " b) vdl where rec loop b =
               fun
               [ [] -> sprintf "%s%s" b k
               | [(_, c, tl) :: vdl] ->
                   let k = if vdl = [] then sprintf " ]%s" k else "" in
                   let se =
                     if tl = [] then sprintf "%s%s%s" b c k
                     else
                       let tl = List.map (fun t -> (t, " and")) tl in
                       sprint_indent (ind + 4) 0
                         (fun _ _ -> sprintf "%s%s of" b c)
                         (fun ind b _ -> listws_hv (ind + 2) 0 ctyp b tl k)
                   in
                   if vdl = [] then se
                   else
                     let se = sprintf "%s\n" se in
                     sprintf "%s%s" se (loop sep vdl) ])
  | <:ctyp< ($list:tl$) >> ->
      fun curr next ind b k ->
        let tl = List.map (fun t -> (t, " *")) tl in
        listws_hv (ind + 1) 0 ctyp (sprintf "%s(" b) tl (sprintf ")%s" k)
  | <:ctyp< $lid:t$ >> ->
      fun curr next ind b k -> var_escaped ind b t k
  | <:ctyp< $uid:t$ >> ->
      fun curr next ind b k -> sprintf "%s%s%s" b t k
  | <:ctyp< ' $s$ >> ->
      fun curr next ind b k -> sprintf "%s'%s%s" b s k
  | <:ctyp< _ >> ->
      fun curr next ind b k -> sprintf "%s_%s" b k
  | <:ctyp< ? $_$ : $t$ >> | <:ctyp< ~ $_$ : $t$ >> ->
      fun curr next ind b k -> pr_ctyp.pr_fun "apply" ind b t k
  | <:ctyp< < $list:_$ $opt:_$ > >> ->
      fun curr next ind b k ->
        failwith "cannot convert objects in syntax 's'"
  | <:ctyp< $_$ $_$ >> | <:ctyp< $_$ -> $_$ >> as z ->
      fun curr next ind b k ->
        ctyp (ind + 1) (sprintf "%s(" b) z (sprintf ")%s" k)
  | z ->
      fun curr next ind b k -> not_impl "ctyp" ind b z k ]
;

(* used for 'else' parts of 'if' expressions to prevent comments to be
   added because the source can come from normal OCaml syntax where rec 'else'
   parts are optional, converted into 'else ()' with a location of the
   whole 'else' (actually bug of pa_o.ml) *)
value is_unit =
  fun
  [ <:expr< () >> -> True
  | _ -> False ]
;

(* [must_be_printed_identically]

   Heuristic to decide to print two items identically or not.

   Printing identically means:
     - either put a newline before *both*
     - or print *both* in one only line

   The two items are printed, and the resulting two strings are compared
   using the "diff" library module; if they are "almost" equal, (i.e. their
   difference is greater than [equality_threshold]), the decision is taken.

   Examples of printing which were improved thanks to this heuristic
   (borrowed to some real codes):

   1/
     displaying without heuristic:
        if String.length s > 0 && s.[0] = '-' then
          sprintf "%s(%s%s)%s" b s a k
        else sprintf "%s%s%s%s" b s a k
     displaying with heuristic:
        if String.length s > 0 && s.[0] = '-' then
          sprintf "%s(%s%s)%s" b s a k
        else
          sprintf "%s%s%s%s" b s a k

   2/
     displaying without heuristic:
        if ligne.cs_sel then (
          ligne.cs_sel := False;
          state.nbMarques := state.nbMarques - 1
        )
        else (ligne.cs_sel := True; state.nbMarques := state.nbMarques + 1)
     displaying with heuristic:
        if ligne.cs_sel then (
          ligne.cs_sel := False;
          state.nbMarques := state.nbMarques - 1
        )
        else (
          ligne.cs_sel := True;
          state.nbMarques := state.nbMarques + 1
        )

   3/
     displaying without heuristic:
        if define_class then
          fun ppf -> Printtyp.class_declaration id ppf clty
        else fun ppf -> Printtyp.cltype_declaration id ppf cltydef
     displaying with heuristic:
        if define_class then
          fun ppf -> Printtyp.class_declaration id ppf clty
        else
          fun ppf -> Printtyp.cltype_declaration id ppf cltydef

   4/
     displaying without heuristic:
        if closed then if tags = None then " " else "< "
        else if tags = None then "> "
        else "? "
     displaying with heuristic:
        if closed then if tags = None then " " else "< "
        else if tags = None then "> " else "? "

*)
value equality_threshold = 0.51;
value must_be_printed_identically f x1 x2 =
  let (s1, s2) = (
    (* the two strings; this code tries to prevents computing possible
       too long lines (which might slow down the program) *)
    let v = Sformat.line_length.val in
    Sformat.line_length.val := 2 * v;
    let s1 = horiz_vertic (fun _ -> Some (f 0 "" x1 "")) (fun () -> None) in
    let s2 = horiz_vertic (fun _ -> Some (f 0 "" x2 "")) (fun () -> None) in
    Sformat.line_length.val := v;
    (s1, s2)
  )
  in
  match (s1, s2) with
  [ (Some s1, Some s2) ->
      (* one string at least could hold in the line; comparing them; if
         they are "close" to each other, return True, meaning that they
         should be displayed *both* in one line or *both* in several lines *)
      let (d1, d2) =
        let a1 = Array.init (String.length s1) (fun i -> s1.[i]) in
        let a2 = Array.init (String.length s2) (fun i -> s2.[i]) in
        Diff.f a1 a2
      in
      let eq =
        loop 0 0 where rec loop i eq =
          if i = Array.length d1 then eq
          else loop (i + 1) (if d1.(i) then eq else eq + 1)
      in
      let r1 = float eq /. float (Array.length d1) in
      let r2 = float eq /. float (Array.length d2) in
      r1 >= equality_threshold && r2 >= equality_threshold
  | _ -> False ]
;

value must_be_printed_identically f x1 x2 =
  call_with Sformat.output Ostring (must_be_printed_identically f x1) x2
;
*)

value expr_top =
  extfun Extfun.empty with
  [
(*
    <:expr< if $e1$ then $e2$ else $e3$ >> ->
      fun curr next ind b k ->
        horiz_vertic
          (fun _ ->
             sprintf "%sif %s then %s%s else %s%s" b (curr ind "" e1 "")
               (comm_bef ind (MLast.loc_of_expr e2)) (curr ind "" e2 "")
               (if is_unit e3 then ""
                else comm_bef ind (MLast.loc_of_expr e3))
               (curr ind "" e3 k))
          (fun () ->
             let mbpi = must_be_printed_identically curr e2 e3 in
             let (eel, e3) =
               if mbpi then ([], e3)
               else
                 let b1 = sprintf "%selse " (tab ind) in
                 elseif [] e3 where rec elseif reel e =
                   match e with
                   [ <:expr< if $e1$ then $e2$ else $e3$ >> ->
                       elseif [(False, b1, e1, e2) :: reel] e3
                   | _ -> (List.rev reel, e) ]
             in
             let eel = [(True, b, e1, e2) :: eel] in
             let e2_holds_in_line = ref False in
             let s1 =
               List.fold_left
                 (fun s1 (is_first, b1, e1, e2) ->
                    let nl = if is_first then "" else "\n" in
                    let s1 = sprintf "%s%s" s1 nl in
                    let s2 =
                      horiz_vertic
                        (fun nofit -> (
                           let r =
                             sprintf "%sif %s then %s%s" b1 (curr ind "" e1 "")
                               (comm_bef ind (MLast.loc_of_expr e2))
                               (curr ind "" e2 "")
                           in
                           e2_holds_in_line.val := True;
                           r
                         ))
                        (fun () ->
                           let (letexprl, has_seq) = let_and_seq_list e2 in
                           let k = if has_seq then " (" else "" in
                           let se1 =
                             if is_first then
                               sprint_indent ind 0
                                 (fun ind _ ->
                                    let ind3 = ind + 3 in
                                    curr ind3 (sprintf "%sif " b1) e1 "")
                                 (fun ind b _ -> sprintf "%sthen%s" b k)
                             else
                               sprint_indent_unindent ind 2
                                 (fun ind -> sprintf "%sif" b1)
                                 (fun ind b _ -> curr ind b e1 "")
                                 (fun ind b c -> sprintf "%s%sthen%s" b c k)
                           in
                           let se1 = sprintf "%s\n" se1 in
                           let ind2 = ind + 2 in
                           let se1 =
                             if has_seq then se1
                             else
                               let ccc2 =
                                 comm_bef ind2 (MLast.loc_of_expr e2)
                               in
                               sprintf "%s%s" se1 ccc2
                           in
                           let se2 =
                             if has_seq then
                               sprintf "%s\n%s)"
                                 (let_in_and_sequence_combination ind2
                                    (tab ind2) letexprl "")
                                 (tab ind)
                             else curr ind2 (tab ind2) e2 ""
                           in
                           sprintf "%s%s" se1 se2)
                    in
                    sprintf "%s%s" s1 s2)
                 "" eel
             in
             let s1 = sprintf "%s\n" s1 in
             let s2 =
               horiz_vertic
                 (fun nofit ->
                    if mbpi && not e2_holds_in_line.val then nofit ()
                    else
                      let ccc3 =
                        if is_unit e3 then ""
                        else remove_nl (comm_bef 0 (MLast.loc_of_expr e3))
                      in
                      if String.contains ccc3 '\n' then nofit ()
                      else
                        curr ind (sprintf "%selse %s" (tab ind) ccc3) e3 k)
                 (fun () ->
                    let (letexprl, has_seq) = let_and_seq_list e3 in
                    let ind2 = ind + 2 in
                    if has_seq then
                      let s1 = sprintf "%selse (\n" (tab ind) in
                      let s2 =
                        let_in_and_sequence_combination ind2 (tab ind2)
                          letexprl ""
                      in
                      sprintf "%s%s\n%s)%s" s1 s2 (tab ind) k
                    else
                      let ccc3 = comm_bef ind2 (MLast.loc_of_expr e3) in
                      let s = sprintf "%selse\n%s" (tab ind) ccc3 in
                      let se3 = curr ind2 (tab ind2) e3 k in
                      sprintf "%s%s" s se3)
             in
             sprintf "%s%s" s1 s2)
  | <:expr< fun [ $list:pwel$ ] >> ->
      fun curr next ind b k ->
        match pwel with
        [ [(p1, None, e1)] when is_irrefut_patt p1 ->
            let (pl, e) =
              let (pl, e) = expr_fun_args e1 in
              ([p1 :: pl], e)
            in
            let ind2 = ind + 2 in
            horiz_vertic
              (fun _ ->
                 sprintf "%s%s%s"
                   (listws 0 patt (sprintf "%sfun " b) "" False pl " -> ")
                   (comm_bef 0 (MLast.loc_of_expr e)) (curr 0 "" e k))
              (fun () ->
                 let (letexprl, has_seq) = let_and_seq_list e in
                 let sp =
                   let b = sprintf "%sfun" b in
                   let k = if has_seq then " (" else "" in
                   let (sp, b) =
                     listws_be ind patt (b, " ") pl "" (sprintf "->%s" k)
                   in
                   sprintf "%s%s" sp b
                 in
                 let sp = sprintf "%s\n" sp in
                 if has_seq then
                   let se =
                     let_in_and_sequence_combination ind2 (tab ind2) letexprl
                       ""
                   in
                   sprintf "%s%s\n%s)%s" sp se (tab ind) k
                 else
                   let ccc = comm_bef ind2 (MLast.loc_of_expr e) in
                   let sp = sprintf "%s%s" sp ccc in
                   let se = curr ind2 (tab ind2) e k in
                   sprintf "%s%s" sp se)
        | [] ->
            sprintf "%sfun []%s" b k
        | _ ->
            sprint_indent ind 0 (fun _ _ -> sprintf "%sfun" b)
              (fun ind b _ ->
                 match_assoc_list ind (sprintf "%s[ " b) pwel
                   (sprintf " ]%s" k)) ]
  | <:expr< try $e1$ with [ $list:pwel$ ] >> |
    <:expr< match $e1$ with [ $list:pwel$ ] >> as e ->
      fun curr next ind b k ->
        let op =
          match e with
          [ <:expr< try $_$ with [ $list:_$ ] >> -> "try"
          | _ -> "match" ]
        in
        let ind2 = ind + 2 in
        match pwel with
        [ [(p2, None, e2)] when is_irrefut_patt p2 ->
            horiz_vertic
              (fun _ ->
                 curr 0 (sprintf "%s%s " b op) e1
                   (patt 0 " with " p2 (expr 0 " -> " e2 k)))
              (fun () ->
                 let (letexprl, has_seq) = let_and_seq_list e2 in
                 let s1 =
                   let k = if has_seq then " (" else "" in
                   horiz_vertic
                     (fun _ ->
                        curr ind (sprintf "%s%s " b op) e1
                          (patt ind " with " p2 (sprintf " ->%s" k)))
                     (fun () ->
                        let (letexprl, has_seq) = let_and_seq_list e1 in
                        let b1 = if has_seq then " (" else "" in
                        let s1 = sprintf "%s%s%s\n" b op b1 in
                        let s2 =
                          let_in_and_sequence_combination ind2 (tab ind2)
                            letexprl ""
                        in
                        let s1 = sprintf "%s%s" s1 s2 in
                        let s1 =
                          if has_seq then sprintf "%s\n%s)" s1 (tab ind)
                          else s1
                        in
                        let s1 = sprintf "%s\n" s1 in
                        let s2 =
                          patt ind (sprintf "%swith " (tab ind)) p2
                            (sprintf " ->%s" k)
                        in
                        sprintf "%s%s" s1 s2)
                 in
                 let s1 = sprintf "%s\n" s1 in
                 let s2 =
                   if has_seq then
                     let s =
                       let_in_and_sequence_combination ind2 (tab ind2)
                         letexprl ""
                     in
                     sprintf "%s\n%s)%s" s (tab ind) k
                   else curr ind2 (tab ind2) e2 k
                 in
                 sprintf "%s%s" s1 s2)
        | [] ->
            curr 0 (sprintf "%s%s " b op) e1 (sprintf " with []%s" k)
        | _ ->
            horiz_vertic
              (fun nofit ->
                 match pwel with
                 [ [pwe] ->
                     curr 0 (sprintf "%s%s " b op) e1
                       (match_assoc 0 0 " with [ " False pwe
                          (sprintf " ]%s" k))
                 | _ -> nofit () ])
              (fun () ->
                 let s1 =
                   horiz_vertic
                     (fun _ -> curr ind (sprintf "%s%s " b op) e1 " with")
                     (fun () ->
                        let (letexprl, has_seq) = let_and_seq_list e1 in
                        let b1 = if has_seq then " (" else "" in
                        let s1 = sprintf "%s%s%s\n" b op b1 in
                        let s2 =
                          if has_seq then
                            let_in_and_sequence_combination ind2 (tab ind2)
                              letexprl ""
                          else curr ind2 (tab ind2) e1 ""
                        in
                        let s3 = sprintf "%s%s" s1 s2 in
                        let s =
                          if has_seq then sprintf "%s\n%s)" s3 (tab ind)
                          else s3
                        in
                        sprintf "%s\n%swith" s (tab ind))
                 in
                 let s1 = sprintf "%s\n" s1 in
                 let s2 =
                   match_assoc_list ind (sprintf "%s[ " (tab ind)) pwel
                     (sprintf " ]%s" k)
                 in
                 sprintf "%s%s" s1 s2) ]
  | <:expr< let $opt:rf1$ $list:pel1$ in $e1$ >> as e ->
      fun curr next ind b k ->
        match
          match e with
          [ <:expr< let rec $p$ = $body$ in $e$ >> ->
              let e1 =
                loop e where rec loop =
                  fun
                  [ <:expr< $e$ $_$ >> -> loop e
                  | e -> e ]
              in
              match (p, e1, body) with
              [ (<:patt< $lid:f$ >>, <:expr< $lid:g$ >>,
                 <:expr< fun [ $list:_$ ] >>) ->
                  if f = g then Some (p, e, body) else None
              | _ -> None ]
          | _ -> None ]
        with
        [ Some (p, e, body) ->
            horiz_vertic
              (fun _ ->
                 let b = sprintf "%s where rec" (curr ind b e "") in
                 binding ind False (b, " ") (p, body) ("", k))
              (fun () ->
                 match
                   horiz_vertic (fun _ -> Some (curr 0 b e ""))
                     (fun () -> None)
                 with
                 [ Some s1 ->
                     binding ind False (sprintf "%s where rec" s1, " ") (p, body)
                       ("", k)
                 | None ->
                     let s1 = curr ind b e "" in
                     let s1 = sprintf "%s\n" s1 in
                     let s2 =
                       binding ind False (sprintf "%swhere rec" (tab ind), " ")
                         (p, body) ("", k)
                     in
                     sprintf "%s%s" s1 s2 ])
        | None ->
            horiz_vertic (fun nofit -> nofit ())
              (fun () ->
                 let (letexprl, has_seq) = let_and_seq_list e in
                 let (ind, k) =
                   if has_seq then (ind + 1, ")" ^ k) else (ind, k)
                 in
                 if has_seq then
                   let_in_and_sequence_combination ind (sprintf "%s(" b)
                     letexprl k
                 else
                   let b =
                     sprintf "%s%s" b (if rf1 then "let rec" else "let")
                   in
                   let sb = binding_list ind (b, " ") pel1 (" ", "in") in
                   let ccc = comm_bef ind (MLast.loc_of_expr e1) in
                   let sb = sprintf "%s\n%s" sb ccc in
                   sprintf "%s%s" sb (curr ind (tab ind) e1 k)) ]
  | <:expr< while $e1$ do { $list:el$ } >> ->
      fun curr next ind b k ->
        sprint_indent_unindent ind 2
          (fun ind ->
             sprint_indent_unindent ind 2 (fun _ -> sprintf "%swhile" b)
               (fun ind b _ -> curr ind b e1 "")
               (fun ind b1 b2 -> sprintf "%s%sdo" b1 b2))
          (fun ind b nl ->
             if nl then
               let letexprl = let_and_seq_list_of_list [] el in
               let_in_and_sequence_combination ind b letexprl ";"
             else listws ind curr "" ";" False el ";")
          (fun ind b1 b2 -> sprintf "%s%sdone%s" b1 b2 k)
  | <:expr< for $v$ = $e1$ $to:d$ $e2$ do { $list:el$ } >> ->
      fun curr next ind b k ->
        sprint_indent_unindent ind 2
          (fun ind ->
             sprintf "%sfor %s = %s %s %s do" b v (curr ind "" e1 "")
               (if d then "to" else "downto") (curr ind "" e2 ""))
          (fun ind b nl ->
             if nl then
               let letexprl = let_and_seq_list_of_list [] el in
               let_in_and_sequence_combination ind b letexprl ";"
             else listws ind curr "" ";" False el ";")
          (fun ind b1 b2 -> sprintf "%s%sdone%s" b1 b2 k)
  |
*)
    z ->
      fun curr next ind b k -> next ind b z k ]
;

(*
value expr_assign =
  extfun Extfun.empty with
  [ <:expr< $x$ := $y$ >> ->
      fun curr next ind b k -> operator ind next expr 2 b ":=" x y k
  | z -> fun curr next ind b k -> next ind b z k ]
;

value expr_or =
  extfun Extfun.empty with
  [ z ->
      fun curr next ind b k ->
        let unfold =
          fun
          [ <:expr< $lid:op$ $x$ $y$ >> ->
              if List.mem op ["||"] then Some (x, " " ^ op, y) else None
          | _ -> None ]
        in
        right_operator ind 0 unfold next b z k ]
;

value expr_and =
  extfun Extfun.empty with
  [ z ->
      fun curr next ind b k ->
        let unfold =
          fun
          [ <:expr< $lid:op$ $x$ $y$ >> ->
              if List.mem op ["&&"] then Some (x, " " ^ op, y) else None
          | _ -> None ]
        in
        right_operator ind 0 unfold next b z k ]
;

value expr_less =
  extfun Extfun.empty with
  [ <:expr< $lid:op$ $x$ $y$ >> as z ->
      fun curr next ind b k ->
        match op with
        [ "!=" | "<" | "<=" | "<>" | "=" | "==" | ">" | ">=" ->
            operator ind next next 0 b op x y k
        | _ -> next ind b z k ]
  | z -> fun curr next ind b k -> next ind b z k ]
;

value expr_concat =
  extfun Extfun.empty with
  [ z ->
      fun curr next ind b k ->
        let unfold =
          fun
          [ <:expr< $lid:op$ $x$ $y$ >> ->
              if List.mem op ["^"; "@"] then Some (x, " " ^ op, y) else None
          | _ -> None ]
        in
        right_operator ind 0 unfold next b z k ]
;

value expr_add =
  let ops = ["+"; "+."; "-"; "-."] in
  extfun Extfun.empty with
  [ z ->
      fun curr next ind b k ->
        let unfold =
          fun
          [ <:expr< $lid:op$ $x$ $y$ >> ->
              if List.mem op ops then Some (x, " " ^ op, y) else None
          | _ -> None ]
        in
        left_operator ind 0 unfold next b z k ]
;

value expr_mul =
  let ops = ["*"; "*."; "/"; "/."; "land"; "lor"; "lxor"; "mod"] in
  extfun Extfun.empty with
  [ z ->
      fun curr next ind b k ->
        let unfold =
          fun
          [ <:expr< $lid:op$ $x$ $y$ >> ->
              if List.mem op ops then Some (x, " " ^ op, y) else None
          | _ -> None ]
        in
        left_operator ind 0 unfold next b z k ]
;

value expr_pow =
  extfun Extfun.empty with
  [ z ->
      fun curr next ind b k ->
        let unfold =
          fun
          [ <:expr< $lid:op$ $x$ $y$ >> ->
              if List.mem op ["**"; "lsl"] then Some (x, " " ^ op, y)
              else None
          | _ -> None ]
        in
        right_operator ind 0 unfold next b z k ]
;

value expr_unary_minus =
  extfun Extfun.empty with
  [ <:expr< ~- $x$ >> ->
      fun curr next ind b k -> curr ind (sprintf "%s- " b) x k
  | <:expr< ~-. $x$ >> ->
      fun curr next ind b k -> curr ind (sprintf "%s-. " b) x k
  | z ->
      fun curr next ind b k -> next ind b z k ]
;

value expr_apply =
  extfun Extfun.empty with
  [ <:expr< assert False >> ->
      fun curr next ind b k -> sprintf "%sassert False%s" b k
  | <:expr< assert $e$ >> ->
      fun curr next ind b k ->
        sprint_indent ind 2 (fun _ _ -> sprintf "%sassert" b)
          (fun ind b _ -> next ind b e k)
  | <:expr< lazy $e$ >> ->
      fun curr next ind b k ->
        sprint_indent ind 2 (fun _ _ -> sprintf "%slazy" b)
          (fun ind b _ -> next ind b e k)
  | <:expr< $int:s$ >> as e ->
      fun curr next ind b k ->
        if String.length s > 0 && s.[0] = '-' then sprintf "%s%s%s" b s k
        else next ind b e k
  | <:expr< $_$ $_$ >> as z ->
      fun curr next ind b k ->
        let inf =
          match z with
          [ <:expr< $lid:n$ $_$ $_$ >> -> is_infix n
          | <:expr< [$_$ :: $_$] >> -> True
          | _ -> False ]
        in
        if inf then next ind b z k
        else
          let unfold =
            fun
            [ <:expr< $x$ $y$ >> -> Some (x, "", y)
            | e -> None ]
          in
          left_operator ind 2 unfold next b z k
  | z ->
      fun curr next ind b k -> next ind b z k ]
;

value expr_dot =
  extfun Extfun.empty with
  [ <:expr< $x$ . $y$ >> ->
      fun curr next ind b k ->
        horiz_vertic (fun _ -> curr 0 (curr 0 b x ".") y k)
          (fun () ->
             let s1 = curr ind b x "" in
             let s2 = curr ind (sprintf "%s." (tab ind)) y k in
             sprintf "%s\n%s" s1 s2)
  | <:expr< $x$ .( $y$ ) >> ->
      fun curr next ind b k ->
        expr ind (curr ind b x ".(") y (sprintf ")%s" k)
  | <:expr< $x$ .[ $y$ ] >> ->
      fun curr next ind b k ->
        expr ind (curr ind b x ".[") y (sprintf "]%s" k)
  | z ->
      fun curr next ind b k -> next ind b z k ]
;
*)

value expr_simple =
  extfun Extfun.empty with
  [ (*
    <:expr< do { $list:el$ } >> as z ->
      fun curr next ind b k ->
        horiz_vertic
          (fun nofit ->
             let ind = ind + 1 in
             let has_comm =
               List.exists (fun e -> comm_bef 0 (MLast.loc_of_expr e) <> "")
                 el
             in
             if has_comm then nofit ()
             else
               listws ind expr (sprintf "%s(" b) ";" False el
                 (sprintf ")%s" k))
          (fun () ->
             let (letexprl, has_seq) = let_and_seq_list z in
             let (ind, k) =
               if has_seq then (ind + 1, ")" ^ k) else (ind, k)
             in
             let b = if has_seq then sprintf "%s(" b else b in
             let_in_and_sequence_combination ind b letexprl k)
  | <:expr< ($list:el$) >> ->
      fun curr next ind b k ->
        let el = List.map (fun e -> (e, ",")) el in
        listws_hv (ind + 1) 0 expr (sprintf "%s(" b) el (sprintf ")%s" k)
  | <:expr< {$list:lel$} >> ->
      fun curr next ind b k ->
        let lxl = List.map (fun lx -> (lx, ";")) lel in
        listws_hv (ind + 1) 0
          (fun ind b pe k -> binding ind False (b, "") pe ("", k))
          (sprintf "%s{" b) lxl (sprintf "}%s" k)
  | <:expr< {($e$) with $list:lel$} >> ->
      fun curr next ind b k ->
        let b1 = expr ind "(" e ") with " in
        let lxl = List.map (fun lx -> (lx, ";")) lel in
        listws_hv (ind + 1) 0
          (fun ind b pe k -> binding ind False (b, "") pe ("", k))
          (sprintf "%s{%s" b b1) lxl (sprintf "}%s" k)
  | <:expr< [| $list:el$ |] >> ->
      fun curr next ind b k ->
        if el = [] then sprintf "%s[| |]%s" b k
        else
          let el = List.map (fun e -> (e, ";")) el in
          listws_hv (ind + 3) 0 expr (sprintf "%s[| " b) el
            (sprintf " |]%s" k)
  | <:expr< [$_$ :: $_$] >> as z ->
      fun curr next ind b k -> x_list ind expr b (make_expr_list z) k
  | <:expr< ($e$ : $t$) >> ->
      fun curr next ind b k ->
        let expr =
          (* beuh... *)
          match e with
          [ <:expr< let $opt:_$ $list:_$ in $_$ >> -> curr
          | _ -> expr ]
        in
        sprint_indent (ind + 1) 0
          (fun ind _ -> expr ind (sprintf "%s(" b) e " :")
          (fun ind b _ -> ctyp ind b t (sprintf ")%s" k))
  | <:expr< $int:s$ >> | <:expr< $flo:s$ >> ->
      fun curr next ind b k ->
        if String.length s > 0 && s.[0] = '-' then sprintf "%s(%s)%s" b s k
        else sprintf "%s%s%s" b s k
  | <:expr< $int32:s$ >> ->
      fun curr next ind b k ->
        let s = s ^ "l" in
        if String.length s > 0 && s.[0] = '-' then sprintf "%s(%s)%s" b s k
        else sprintf "%s%s%s" b s k
  | <:expr< $int64:s$ >> ->
      fun curr next ind b k ->
        let s = s ^ "L" in
        if String.length s > 0 && s.[0] = '-' then sprintf "%s(%s)%s" b s k
        else sprintf "%s%s%s" b s k
  | <:expr< $nativeint:s$ >> ->
      fun curr next ind b k ->
        let s = s ^ "n" in
        if String.length s > 0 && s.[0] = '-' then sprintf "%s(%s)%s" b s k
        else sprintf "%s%s%s" b s k
  | <:expr< $lid:s$ >> ->
      fun curr next ind b k -> var_escaped ind b s k
  | <:expr< $uid:s$ >> | <:expr< `$uid:s$ >> ->
      fun curr next ind b k -> ident ind b s k
  |
*)
    <:expr< $str:s$ >> ->
      fun curr next ind b k -> ident ind b ("\"" ^ s ^ "\"") k
(*
  | <:expr< $chr:s$ >> ->
      fun curr next ind b k -> sprintf "%s'%s'%s" b s k
  | <:expr< ? $s$ >> ->
      fun curr next ind b k -> var_escaped ind b s k
  | <:expr< ~ $_$ : $z$ >> ->
      fun curr next ind b k -> curr ind b z k
  | <:expr< let $opt:_$ $list:_$ in $e$ >> as z
    when snd (let_and_seq_list e) ->
      fun curr next ind b k -> expr ind b z k
  | <:expr< $_$ $_$ >> | <:expr< $_$ := $_$ >> |
    <:expr< fun [ $list:_$ ] >> | <:expr< if $_$ then $_$ else $_$ >> |
    <:expr< let $opt:_$ $list:_$ in $_$ >> |
    <:expr< match $_$ with [ $list:_$ ] >> |
    <:expr< try $_$ with [ $list:_$ ] >> as z ->
      fun curr next ind b k ->
        let (inf, n) =
          match z with
          [ <:expr< $lid:n$ $_$ $_$ >> ->
              (not (is_implemented_infix n) && is_infix n, n)
          | _ -> (False, "") ]
        in
        if inf then not_impl "op" ind b n k
        else expr (ind + 1) (sprintf "%s(" b) z (sprintf ")%s" k)
*)
  | z ->
      fun curr next ind b k -> not_impl "expr" ind b z k ]
;

(*
value patt_top =
  extfun Extfun.empty with
  [ z ->
      fun curr next ind b k ->
        let unfold =
          fun
          [ <:patt< $x$ | $y$ >> -> Some (x, " |", y)
          | _ -> None ]
        in
        left_operator ind 0 unfold next b z k ]
;

value patt_range =
  extfun Extfun.empty with
  [ <:patt< $x$ .. $y$ >> ->
      fun curr next ind b k ->
        sprintf "%s..%s" (next ind b x "") (next ind "" y k)
  | z -> fun curr next ind b k -> next ind b z k ]
;

value rec patt_apply =
  extfun Extfun.empty with
  [ z ->
      fun curr next ind b k ->
        let unfold =
          fun
          [ <:patt< [ $_$ :: $_$ ] >> -> None
          | <:patt< $x$ $y$ >> -> Some (x, "", y)
          | p -> None ]
        in
        left_operator ind 2 unfold next b z k ]
;

value patt_dot =
  extfun Extfun.empty with
  [ <:patt< $x$ . $y$ >> ->
      fun curr next ind b k -> curr ind (curr ind b x ".") y k
  | z -> fun curr next ind b k -> next ind b z k ]
;

value patt_simple =
  extfun Extfun.empty with
  [ <:patt< ($x$ as $y$) >> ->
      fun curr next ind b k ->
        sprint_indent (ind + 1) 2
          (fun ind _ -> patt ind (sprintf "%s(" b) x " as")
          (fun ind b _ -> patt ind b y (sprintf ")%s" k))
  | <:patt< ($list:pl$) >> ->
      fun curr next ind b k ->
        let pl = List.map (fun p -> (p, ",")) pl in
        listws_hv (ind + 1) 0 patt (sprintf "%s(" b) pl (sprintf ")%s" k)
  | <:patt< {$list:lpl$} >> ->
      fun curr next ind b k ->
        let lxl = List.map (fun lx -> (lx, ";")) lpl in
        listws_hv (ind + 1) 0 (record_assoc patt) (sprintf "%s{" b) lxl
          (sprintf "}%s" k)
  | <:patt< [$_$ :: $_$] >> as z ->
      fun curr next ind b k -> x_list ind patt b (make_patt_list z) k
  | <:patt< ($p$ : $t$) >> ->
      fun curr next ind b k ->
        sprint_indent (ind + 1) 0
          (fun ind _ -> patt ind (sprintf "%s(" b) p " :")
          (fun ind b _ -> ctyp ind b t (sprintf ")%s" k))
  | <:patt< $int:s$ >> ->
      fun curr next ind b k -> sprintf "%s%s%s" b s k
  | <:patt< $lid:s$ >> | <:patt< ~ $s$ >> ->
      fun curr next ind b k -> var_escaped ind b s k
  | <:patt< $uid:s$ >> | <:patt< `$uid:s$ >> ->
      fun curr next ind b k -> ident ind b s k
  | <:patt< $chr:s$ >> ->
      fun curr next ind b k -> sprintf "%s'%s'%s" b s k
  | <:patt< $str:s$ >> ->
      fun curr next ind b k -> sprintf "%s\"%s\"%s" b s k
  | <:patt< _ >> ->
      fun curr next ind b k -> sprintf "%s_%s" b k
  | <:patt< ? $s$ >> | <:patt< ? ($lid:s$ = $_$) >> ->
      fun curr next ind b k -> var_escaped ind b s k
  | <:patt< $_$ $_$ >> | <:patt< $_$ | $_$ >> | <:patt< $_$ .. $_$ >> as z ->
      fun curr next ind b k ->
        patt (ind + 1) (sprintf "%s(" b) z (sprintf ")%s" k)
  | z ->
      fun curr next ind b k -> not_impl "patt" ind b z k ]
;

value external_item ind b n t sl k =
  horiz_vertic
    (fun _ ->
       var_escaped ind (sprintf "%sexternal " b) n
         (ctyp ind " : " t
            (listws ind (fun ind b z k -> sprintf "%s\"%s\"%s" b z k) " = "
               "" False sl k)))
    (fun () ->
       match
         horiz_vertic
           (fun _ -> Some (ctyp ind (sprintf "%sexternal %s : " b n) t " ="))
           (fun () -> None)
       with
       [ Some s1 ->
           let s2 =
             let ind2 = ind + 2 in
             listws ind2 (fun ind b z k -> sprintf "%s\"%s\"%s" b z k)
               (tab ind2) "" False sl k
           in
           sprintf "%s\n%s" s1 s2
       | None ->
           let ind2 = ind + 2 in
           let s1 = sprintf "%sexternal %s :" b n in
           let s1 = sprintf "%s\n" s1 in
           let s2 =
             sprint_indent ind2 2 (fun ind _ -> ctyp ind (tab ind2) t " =")
               (fun ind b _ ->
                  listws ind (fun ind b z k -> sprintf "%s\"%s\"%s" b z k) b
                    "" False sl k)
           in
           sprintf "%s%s" s1 s2 ])
;

value exception_item ind b e tl c k =
  sprint_indent ind 2
    (fun ind _ ->
       sprintf "%sexception %s%s" b e (if tl = [] then "" else " of"))
    (fun ind b _ ->
       sprintf "%s%s%s"
         (if tl = [] then "" else listws ind ctyp b " and" False tl "")
         (if c = [] then "" else sprintf " = chaispasquoi") k)
;
*)

value str_item_top =
  extfun Extfun.empty with
  [ <:str_item< # $s$ $e$ >> ->
      fun curr next ind b k -> expr ind (sprintf "%s#%s " b s) e k
(*
  | <:str_item< declare $list:sil$ end >> ->
      fun curr next ind b k ->
        if sil = [] then sprintf "%sdeclare end%s" b k
        else
          horiz_vertic
            (fun _ ->
               sprintf "%sdeclare %s end%s" b
                 (listws ind str_item "" ";" False sil ";") k)
            (fun () ->
               let ind2 = ind + 2 in
               sprintf "%sdeclare\n%s\n%send%s" b
                 (listws ind2 str_item (tab ind2) ";" True sil ";") (tab ind)
                 k)
  | <:str_item< exception $e$ of $list:tl$ = $c$ >> ->
      fun curr next ind b k -> exception_item ind b e tl c k
  | <:str_item< external $n$ : $t$ = $list:sl$ >> ->
      fun curr next ind b k -> external_item ind b n t sl k
*)
  | <:str_item< module $m$ = $me$ >> ->
      fun curr next ind b k ->
        horiz_vertic
          (fun _ ->
             sprintf "%smodule %s = %s%s" b m (module_expr 0 "" me "") k)
          (fun () ->
             sprintf "%smodule %s =\n%s\n%s" b m
               (module_expr (ind + 2) (tab (ind + 2)) me "") k)
(*
  | <:str_item< module type $m$ = $mt$ >> ->
      fun curr next ind b k ->
        sprint_indent_unindent ind 2
          (fun ind -> sprintf "%smodule type %s =" b m)
          (fun ind b _ -> module_type ind b mt "")
          (fun ind b _ -> sprintf "%s%s" b k)
*)
  | <:str_item< open $i$ >> ->
      fun curr next ind b k -> mod_ident ind (sprintf "%sopen " b) i k
(*
  | <:str_item< type $list:tdl$ >> ->
      fun curr next ind b k ->
        type_decl_list ind (sprintf "%s%s" b "type") tdl k
*)
  | <:str_item< value $opt:rf$ $list:[pe :: pel]$ >> ->
      fun curr next ind b k ->
        horiz_vertic
          (fun _ ->
             sprintf "%svalue %s%s%s%s%s" b (if rf then "rec " else "")
               (binding 0 "" pe "") (if pel = [] then "" else " ")
               (hlist (and_before binding) 0 "" pel "") k)
          (fun () -> not_impl "value vertic" ind b [pe :: pel] k)
(*
  | <:str_item< $exp:e$ >> ->
      fun curr next ind b k ->
        horiz_vertic (fun _ -> expr ind b e k)
(*
          (fun () -> sprintf "%s\n%s%s" (expr ind b e "") (tab ind) k)
*)
          (fun () ->
             call_with Sformat.output Ostring
               (fun () ->
                  let se = expr ind b e "" in
                  if last_line_starts_with_space ind se then
                    sprintf "%s\n%s%s" se (tab ind) k
                  else
                    sprintf "%s%s" se k)
               ())
(**)
  | MLast.StUse _ _ _ ->
      fun curr next ind b k ->
        (* extra ast generated by camlp4 *)
        ""
*)
  | z ->
      fun curr next ind b k -> not_impl "str_item" ind b z k ]
;

(*
value sig_item_top =
  extfun Extfun.empty with
  [ <:sig_item< exception $e$ of $list:tl$ >> ->
      fun curr next ind b k -> exception_item ind b e tl [] k
  | <:sig_item< external $n$ : $t$ = $list:sl$ >> ->
      fun curr next ind b k -> external_item ind b n t sl k
  | <:sig_item< module $m$ : $mt$ >> ->
      fun curr next ind b k ->
        sprint_indent_unindent ind 2 (fun ind -> sprintf "%smodule %s :" b m)
          (fun ind b _ -> module_type ind b mt "")
          (fun ind b _ -> sprintf "%s%s" b k)
  | <:sig_item< module type $m$ = $mt$ >> ->
      fun curr next ind b k ->
        sprint_indent_unindent ind 2
          (fun ind -> sprintf "%smodule type %s =" b m)
          (fun ind b _ -> module_type ind b mt "")
          (fun ind b _ -> sprintf "%s%s" b k)
  | <:sig_item< open $i$ >> ->
      fun curr next ind b k -> mod_ident ind (sprintf "%sopen " b) i k
  | <:sig_item< type $list:tdl$ >> ->
      fun curr next ind b k ->
        type_decl_list ind (sprintf "%s%s" b "type") tdl k
  | <:sig_item< value $s$ : $t$ >> ->
      fun curr next ind b k ->
        sprint_indent ind 2
          (fun ind _ -> var_escaped ind (sprintf "%svalue " b) s " :")
          (fun ind b _ -> ctyp ind b t k)
  | z ->
      fun curr next ind b k -> not_impl "sig_item" ind b z k ]
;
*)

value module_expr_top =
  extfun Extfun.empty with
  [ <:module_expr< functor ($s$ : $mt$) -> $me$ >> ->
      fun curr next ind b k ->
        horiz_vertic (fun _ -> not_impl "functor horiz" ind b 0 k)
          (fun () -> not_impl "functor vertic" ind b 0 k)
  | <:module_expr< struct $list:sil$ end >> ->
      fun curr next ind b k ->
        horiz_vertic
          (fun _ ->
             sprintf "%sstruct %s end%s" b
               (hlist (comma_after str_item) ind "" sil "") k)
          (fun () ->
             sprintf "%sstruct\n%s\n%send%s" b
               (vlist (comma_after str_item) (ind + 2) (tab (ind + 2)) sil "")
               (tab ind) k)
  | z ->
      fun curr next ind b k -> next ind b z k ]
;

(*
value module_expr_apply =
  extfun Extfun.empty with
  [ z ->
      fun curr next ind b k ->
        let unfold =
          fun
          [ <:module_expr< $x$ $y$ >> -> Some (x, "", y)
          | e -> None ]
        in
        left_operator ind 2 unfold next b z k ]
;

value module_expr_dot =
  extfun Extfun.empty with
  [ <:module_expr< $x$ . $y$ >> ->
      fun curr next ind b k -> curr ind (curr ind b x ".") y k
  | z -> fun curr next ind b k -> next ind b z k ]
;

value module_expr_simple =
  extfun Extfun.empty with
  [ <:module_expr< $uid:s$ >> ->
      fun curr next ind b k -> sprintf "%s%s%s" b s k
  | <:module_expr< ($me$ : $mt$) >> ->
      fun curr next ind b k ->
        sprint_indent (ind + 1) 2
          (fun ind _ -> module_expr ind (sprintf "%s(" b) me " :")
          (fun ind b _ -> module_type ind b mt (sprintf ")%s" k))
  | <:module_expr< struct $list:_$ end >> as z ->
      fun curr next ind b k ->
        module_expr (ind + 1) (sprintf "%s(" b) z (sprintf ")%s" k)
  | z ->
      fun curr next ind b k -> not_impl "module_expr" ind b z k ]
;

value with_constraint ind b wc k =
  match wc with
  [ <:with_constr< type $sl$ $list:tpl$ = $t$ >> ->
      let b =
        let k = type_params ind "" tpl " = " in
        mod_ident ind (sprintf "%swith type " b) sl k
      in
      ctyp ind b t k
  | <:with_constr< module $sl$ = $me$ >> ->
      module_expr ind (mod_ident ind (sprintf "%swith module " b) sl " = ")
        me k ]
;

value module_type_top =
  extfun Extfun.empty with
  [ <:module_type< functor ($s$ : $mt1$) -> $mt2$ >> ->
      fun curr next ind b k ->
        sprint_indent (ind + 2) 0
          (fun ind _ ->
             module_type ind (sprintf "%sfunctor (%s : " b s) mt1 ") ->")
          (fun ind b _ -> module_type ind b mt2 k)
  | <:module_type< sig $list:sil$ end >> ->
      fun curr next ind b k ->
        sprint_indent_unindent ind 2 (fun _ -> sprintf "%ssig" b)
          (fun ind b nl -> listws ind sig_item b ";" nl sil ";")
          (fun ind b1 b2 -> sprintf "%s%send%s" b1 b2 k)
  | <:module_type< $mt$ with $list:wcl$ >> ->
      fun curr next ind b k ->
        sprint_indent ind 2 (fun ind _ -> module_type ind b mt "")
          (fun ind b nl -> listws ind with_constraint b b nl wcl k)
  | z ->
      fun curr next ind b k -> next ind b z k ]
;

value module_type_dot =
  extfun Extfun.empty with
  [ <:module_type< $x$ . $y$ >> ->
      fun curr next ind b k -> curr ind (curr ind b x ".") y k
  | z -> fun curr next ind b k -> next ind b z k ]
;

value module_type_simple =
  extfun Extfun.empty with
  [ <:module_type< $uid:s$ >> ->
      fun curr next ind b k -> sprintf "%s%s%s" b s k
  | z -> fun curr next ind b k -> not_impl "module_type" ind b z k ]
;
*)

(* initialization or re-initialization of predefined printers *)

pr_expr.pr_levels :=
  [{pr_label = "top"; pr_rules = expr_top};
(*
   {pr_label = "ass"; pr_rules = expr_assign};
   {pr_label = "bar"; pr_rules = expr_or};
   {pr_label = "amp"; pr_rules = expr_and};
   {pr_label = "less"; pr_rules = expr_less};
   {pr_label = "concat"; pr_rules = expr_concat};
   {pr_label = "add"; pr_rules = expr_add};
   {pr_label = "mul"; pr_rules = expr_mul};
   {pr_label = "pow"; pr_rules = expr_pow};
   {pr_label = "unary"; pr_rules = expr_unary_minus};
   {pr_label = "apply"; pr_rules = expr_apply};
   {pr_label = "dot"; pr_rules = expr_dot};
*)
   {pr_label = "simple"; pr_rules = expr_simple}]
;

(*
pr_patt.pr_levels :=
  [{pr_label = "top"; pr_rules = patt_top};
   {pr_label = "range"; pr_rules = patt_range};
   {pr_label = "apply"; pr_rules = patt_apply};
   {pr_label = "dot"; pr_rules = patt_dot};
   {pr_label = "simple"; pr_rules = patt_simple}]
;

pr_ctyp.pr_levels :=
  [{pr_label = "top"; pr_rules = ctyp_top};
   {pr_label = "arrow"; pr_rules = ctyp_arrow};
   {pr_label = "apply"; pr_rules = ctyp_apply};
   {pr_label = "dot"; pr_rules = ctyp_dot};
   {pr_label = "simple"; pr_rules = ctyp_simple}]
;
*)

pr_str_item.pr_levels := [{pr_label = "top"; pr_rules = str_item_top}];

(*
pr_sig_item.pr_levels := [{pr_label = "top"; pr_rules = sig_item_top}];
*)

pr_module_expr.pr_levels :=
  [{pr_label = "top"; pr_rules = module_expr_top}(*;
   {pr_label = "apply"; pr_rules = module_expr_apply};
   {pr_label = "dot"; pr_rules = module_expr_dot};
   {pr_label = "simple"; pr_rules = module_expr_simple}*)]
;

(*
pr_module_type.pr_levels :=
  [{pr_label = "top"; pr_rules = module_type_top};
   {pr_label = "dot"; pr_rules = module_type_dot};
   {pr_label = "simple"; pr_rules = module_type_simple}]
;
*)

(* main part *)

value sep = ref None;

value output_string_eval oc s =
  loop 0 where rec loop i =
    if i == String.length s then ()
    else if i == String.length s - 1 then output_char oc s.[i]
    else
      match (s.[i], s.[i + 1]) with
      [ ('\\', 'n') -> do { output_char oc '\n'; loop (i + 2) }
      | (c, _) -> do { output_char oc c; loop (i + 1) } ]
;

value input_source src bp len =
  let len = min (max 0 len) (String.length src) in
  String.sub src bp len
;

value copy_source src oc first bp ep =
  match sep.val with
  [ Some str ->
      if first then ()
      else if ep == String.length src then output_string oc "\n"
      else output_string_eval oc str
  | None ->
      let s = input_source src bp (ep - bp) in
      let s =
        if first then s
        else
          (* generally, what is before the first newline belongs to the
             previous phrase and should have been treated (included, perhaps)
             previously *)
          try
            let i = String.index s '\n' in
            String.sub s i (String.length s - i)
          with
          [ Not_found -> s ]
      in
      output_string oc s ]
;

value copy_to_end src oc first bp =
  let ilen = String.length src in
  if bp < ilen then copy_source src oc first bp ilen
  else output_string oc "\n"
;

value apply_printer f ast = do {
  if Pcaml.input_file.val = "-" then sep.val := Some "\n"
  else do {
    let ic = open_in_bin Pcaml.input_file.val in
    let src =
      loop 0 where rec loop len =
        match try Some (input_char ic) with [ End_of_file -> None ] with
        [ Some c -> loop (Buff.store len c)
        | None -> Buff.get len ]
    in
    file.val := src;
    close_in ic
  };
  let oc = stdout in
  let (first, last_pos) =
    List.fold_left
      (fun (first, last_pos) (si, loc) -> do {
         let bp = Stdpp.first_pos loc in
         let ep = Stdpp.last_pos loc in
         copy_source file.val oc first last_pos bp;
         flush oc;
         output_string oc (f 0 "" si ";");
         (False, ep)
       })
      (True, 0) ast
  in
  copy_to_end file.val oc first last_pos;
  flush oc
};

Pcaml.print_interf.val := apply_printer sig_item;
Pcaml.print_implem.val := apply_printer str_item;
