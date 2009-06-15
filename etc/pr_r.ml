(* camlp4r q_MLast.cmo ./pa_extfun.cmo *)
(* $Id: pr_r.ml,v 1.33 2007/07/04 17:43:09 deraugla Exp $ *)
(* Copyright (c) INRIA 2007 *)

open Pretty;
open Pcaml.Printers;
open Prtools;

value flag_expand_declare = ref False;
value flag_horiz_let_in = ref False;
value flag_sequ_begin_at_eol = ref True;

value flag_where_after_in = ref True;
value flag_where_after_let_eq = ref True;
value flag_where_after_match = ref True;
value flag_where_after_lparen = ref True;
value flag_where_after_field_eq = ref False;
value flag_where_in_sequences = ref False;
value flag_where_after_then = ref True;
value flag_where_after_value_eq = ref True;
value flag_where_after_arrow = ref True;

(* general functions *)

value is_infix = do {
  let infixes = Hashtbl.create 73 in
  List.iter (fun s -> Hashtbl.add infixes s True)
    ["!="; "&&"; "*"; "**"; "*."; "+"; "+."; "-"; "-."; "/"; "/."; "<"; "<=";
     "<>"; "="; "=="; ">"; ">="; "@"; "^"; "asr"; "land"; "lor"; "lsl"; "lsr";
     "lxor"; "mod"; "or"; "||"; "~-"; "~-."];
  fun s -> try Hashtbl.find infixes s with [ Not_found -> False ]
};

value is_keyword =
  let keywords = ["value"; "where"] in
  fun s -> List.mem s keywords
;

value has_special_chars s =
  if String.length s = 0 then False
  else
    match s.[0] with
    [ '0'..'9' | 'A'..'Z' | 'a'..'z' | '_' -> False
    | _ -> True ]
;

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
  | <:patt< ? $_$ : ($_$ = $_$) >> -> True
  | <:patt< ? $_$ >> -> True
  | <:patt< ~ $_$ >> -> True
  | <:patt< ~ $_$ : $_$ >> -> True
  | _ -> False ]
;

value rec get_defined_ident =
  fun
  [ <:patt< $_$ . $_$ >> -> []
  | <:patt< _ >> -> []
  | <:patt< $lid:x$ >> -> [x]
  | <:patt< ($p1$ as $p2$) >> -> get_defined_ident p1 @ get_defined_ident p2
  | <:patt< $int:_$ >> -> []
  | <:patt< $flo:_$ >> -> []
  | <:patt< $str:_$ >> -> []
  | <:patt< $chr:_$ >> -> []
  | <:patt< [| $list:pl$ |] >> -> List.flatten (List.map get_defined_ident pl)
  | <:patt< ($list:pl$) >> -> List.flatten (List.map get_defined_ident pl)
  | <:patt< $uid:_$ >> -> []
  | <:patt< ` $_$ >> -> []
  | <:patt< # $list:_$ >> -> []
  | <:patt< $p1$ $p2$ >> -> get_defined_ident p1 @ get_defined_ident p2
  | <:patt< { $list:lpl$ } >> ->
      List.flatten (List.map (fun (lab, p) -> get_defined_ident p) lpl)
  | <:patt< $p1$ | $p2$ >> -> get_defined_ident p1 @ get_defined_ident p2
  | <:patt< $p1$ .. $p2$ >> -> get_defined_ident p1 @ get_defined_ident p2
  | <:patt< ($p$ : $_$) >> -> get_defined_ident p
  | <:patt< ~ $_$ >> -> []
  | <:patt< ~ $_$ : $p$ >> -> get_defined_ident p
  | <:patt< ? $_$ >> -> []
  | <:patt< ? $_$ : ($p$) >> -> get_defined_ident p
  | <:patt< ? $_$ : ($p$ = $e$) >> -> get_defined_ident p
  | <:patt< $anti:p$ >> -> get_defined_ident p
  | _ -> [] ]
;

value un_irrefut_patt p =
  let loc = MLast.loc_of_patt p in
  match get_defined_ident p with
  [ [] -> (<:patt< _ >>, <:expr< () >>)
  | [i] -> (<:patt< $lid:i$ >>, <:expr< $lid:i$ >>)
  | il ->
      let (upl, uel) =
        List.fold_right
          (fun i (upl, uel) ->
             ([<:patt< $lid:i$ >> :: upl], [<:expr< $lid:i$ >> :: uel]))
          il ([], [])
      in
      (<:patt< ($list:upl$) >>, <:expr< ($list:uel$) >>) ]
;            

value not_impl name pc x =
  let desc =
    if Obj.tag (Obj.repr x) = Obj.tag (Obj.repr "") then
      sprintf "\"%s\"" (Obj.magic x)
    else if Obj.is_block (Obj.repr x) then
      "tag = " ^ string_of_int (Obj.tag (Obj.repr x))
    else "int_val = " ^ string_of_int (Obj.magic x)
  in
  sprintf "%s\"pr_r, not impl: %s; %s\"%s" pc.bef name (String.escaped desc)
    pc.aft
;

value var_escaped pc v =
  let x =
    if is_infix v || has_special_chars v then "\\" ^ v
    else if is_keyword v then v ^ "__"
    else v
  in
  sprintf "%s%s%s" pc.bef x pc.aft
;

value cons_escaped pc v =
  let x =
    match v with
    [ " True" -> "True_"
    | " False" -> "False_"
    | _ -> v ]
  in
  sprintf "%s%s%s" pc.bef x pc.aft
;

value rec mod_ident pc sl =
  match sl with
  [ [] -> sprintf "%s%s" pc.bef pc.aft
  | [s] -> var_escaped pc s
  | [s :: sl] -> mod_ident {(pc) with bef = sprintf "%s%s." pc.bef s} sl ]
;

value semi_after elem pc x = elem {(pc) with aft = sprintf ";%s" pc.aft} x;
value star_after elem pc x = elem {(pc) with aft = sprintf " *%s" pc.aft} x;
value op_after elem pc (x, op) =
  elem {(pc) with aft = sprintf "%s%s" op pc.aft} x
;

value and_before elem pc x = elem {(pc) with bef = sprintf "%sand " pc.bef} x;
value bar_before elem pc x = elem {(pc) with bef = sprintf "%s| " pc.bef} x;

value operator pc left right sh op x y =
  let op = if op = "" then "" else " " ^ op in
  horiz_vertic
    (fun () ->
       sprintf "%s%s%s %s%s" pc.bef (left {(pc) with bef = ""; aft = ""} x)
         op (right {(pc) with bef = ""; aft = ""} y) pc.aft)
    (fun () ->
       let s1 = left {(pc) with aft = op} x in
       let s2 =
         right {(pc) with ind = pc.ind + 2; bef = (tab (pc.ind + 2))} y
       in
       sprintf "%s\n%s" s1 s2)
;

value left_operator pc sh unfold next x =
  let xl =
    loop [] x "" where rec loop xl x op =
      match unfold x with
      [ Some (x1, op1, x2) -> loop [(x2, op) :: xl] x1 op1
      | None -> [(x, op) :: xl] ]
  in
  match xl with
  [ [(x, _)] -> next pc x
  | _ ->
      horiz_vertic (fun () -> hlist (op_after next) pc xl)
        (fun () -> plist next sh pc xl) ]
;

value right_operator pc sh unfold next x =
  let xl =
    loop [] x where rec loop xl x =
      match unfold x with
      [ Some (x1, op, x2) -> loop [(x1, op) :: xl] x2
      | None -> List.rev [(x, "") :: xl] ]
  in
  match xl with
  [ [(x, _)] -> next pc x
  | _ ->
      horiz_vertic (fun () -> hlist (op_after next) pc xl)
        (fun () -> plist next sh pc xl) ]
;

(*
 * Extensible printers
 *)

value expr pc z = pr_expr.pr_fun "top" pc z;
value patt pc z = pr_patt.pr_fun "top" pc z;
value ctyp pc z = pr_ctyp.pr_fun "top" pc z;
value str_item pc z = pr_str_item.pr_fun "top" pc z;
value sig_item pc z = pr_sig_item.pr_fun "top" pc z;
value module_expr pc z = pr_module_expr.pr_fun "top" pc z;
value module_type pc z = pr_module_type.pr_fun "top" pc z;
value expr_fun_args ge = Extfun.apply pr_expr_fun_args.val ge;

(* expression with adding the possible comment before *)
value comm_expr expr pc z =
  let ccc = comm_bef pc (MLast.loc_of_expr z) in
  sprintf "%s%s" ccc (expr pc z)
;

(* couple pattern/anytype with adding the possible comment before *)
value comm_patt_any f pc z =
  let ccc = comm_bef pc (MLast.loc_of_patt (fst z)) in
  sprintf "%s%s" ccc (f pc z)
;

value patt_as pc z =
  match z with
  [ <:patt< ($x$ as $y$) >> ->
      let p1 = patt {(pc) with aft = ""} x in
      let p2 = patt {(pc) with bef = ""} y in
      sprintf "%s as %s" p1 p2
  | z -> patt pc z ]
;

(* utilities specific to pr_r *)

(* Basic displaying of a 'binding' (let, value, expr or patt record field).
   The pretty printing is done correctly, but there are no syntax shortcuts
   (e.g. "let f = fun x -> y" is *not* shortened as "let f x = y"), nor
   pretty printing shortcuts (e.g.
       let f =
         do {
           ...
         }
   is not shortened as
       let f = do {
         ...
       }

   Some functions follow (some of them with '_binding' in their name) which
   use syntax or pretty printing shortcuts.
*)
value binding elem pc (p, e) =
  horiz_vertic
    (fun () ->
       sprintf "%s%s = %s%s" pc.bef (patt {(pc) with bef = ""; aft = ""} p)
         (elem {(pc) with bef = ""; aft = ""} e) pc.aft)
    (fun () ->
       sprintf "%s\n%s" (patt {(pc) with aft = " ="} p)
         (elem {(pc) with ind = pc.ind + 2; bef = (tab (pc.ind + 2))} e))
;

pr_expr_fun_args.val :=
  extfun Extfun.empty with
  [ <:expr< fun $p$ -> $e$ >> as z ->
      if is_irrefut_patt p then
        let (pl, e) = expr_fun_args e in
        ([p :: pl], e)
      else ([], z)
  | z -> ([], z) ]
;

value sequencify e =
  if not flag_sequ_begin_at_eol.val then None else flatten_sequence e
;

(* Pretty printing improvement (optional):
   - print the sequence beginner at end of previous lines,
     therefore printing the sequence with one tabulation less
   - example:
          value f x =
            do {
              ...
            }
     is printed :
          value f x = do {
            ...
          }
 *)
value sequence_box pc expr el =
  let s1 = pc.bef " do {" in
  let s2 =
    vlistl (semi_after (comm_expr expr))
      (comm_expr expr)
      {(pc) with ind = pc.ind + 2; bef = tab (pc.ind + 2); aft = ""} el
  in
  let s3 = sprintf "%s%s%s" (tab pc.ind) "}" pc.aft in
  sprintf "%s\n%s\n%s" s1 s2 s3
;

(* Pretty printing improvement (optional):
   - test a "let" binding can be displayed as "where"
 *)
value can_be_displayed_as_where e =
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
;

(* Pretty printing improvement (optional):
   - display a "let" binding with the "where" construct
*)
value rec where_binding pc (p, e, body) =
  let (pl, body) = expr_fun_args body in
  let pl = [p :: pl] in
  horiz_vertic
    (fun () ->
       sprintf "%s%s where rec %s = %s%s" pc.bef
         (expr {(pc) with bef = ""; aft = ""} e)
         (hlist patt {(pc) with bef = ""; aft = ""} pl)
         (expr {(pc) with bef = ""; aft = ""} body) pc.aft)
    (fun () ->
       let horiz_where k =
         sprintf "%s%s where rec %s =%s" pc.bef
           (expr {(pc) with bef = ""; aft = ""} e)
           (hlist patt {(pc) with bef = ""; aft = ""} pl) k
       in
       let vertic_where k =
         let s1 = expr {(pc) with aft = ""} e in
         let s2 =
           hlist patt
             {(pc) with bef = (sprintf "%swhere rec " (tab pc.ind));
              aft = (sprintf " =%s" k)} pl
         in
         sprintf "%s\n%s" s1 s2
       in
       match sequencify body with
       [ Some el ->
           let expr_wh =
             if flag_where_in_sequences.val then expr_wh else expr
           in
           sequence_box
             {(pc) with
              bef k =
                horiz_vertic (fun () -> horiz_where k)
                  (fun () -> vertic_where k)}
             expr_wh el
       | None ->
           let s1 =
             horiz_vertic (fun () -> horiz_where "")
               (fun () -> vertic_where "")
           in
           let s2 =
             comm_expr expr
               {(pc) with ind = pc.ind + 2; bef = (tab (pc.ind + 2))} body
           in
           sprintf "%s\n%s" s1 s2 ])

and expr_wh pc e =
  match can_be_displayed_as_where e with
  [ Some (p, e, body) -> where_binding pc (p, e, body)
  | None -> expr pc e ]
;

value sequence_box2 pc el =
  let expr_wh = if flag_where_in_sequences.val then expr_wh else expr in
  sequence_box pc expr_wh el
;

(* Pretty printing improvements (optional):
   - prints "field x = e" instead of "field = fun x -> e" in a record
   - if vertical and "e" is a sequence, put the "do {" at after the "="
   Cancellation of all these improvements could be done by changing calls
   to this function to a call to "binding expr" above.
*)
value record_binding pc (p, e) =
  let (pl, e) = expr_fun_args e in
  let pl = [p :: pl] in
  let expr_wh = if flag_where_after_field_eq.val then expr_wh else expr in
  horiz_vertic
    (fun () ->
       sprintf "%s%s = %s%s" pc.bef
         (hlist patt {(pc) with bef = ""; aft = ""} pl)
         (expr_wh {(pc) with bef = ""; aft = ""} e) pc.aft)
    (fun () ->
       match sequencify e with
       [ Some el ->
           sequence_box2
             {(pc) with
              bef k = hlist patt {(pc) with aft = sprintf " =%s" k} pl}
             el
       | None ->
           sprintf "%s\n%s" (hlist patt {(pc) with aft = " ="} pl)
             (expr_wh {(pc) with ind = pc.ind + 2; bef = tab (pc.ind + 2)}
                e) ])
;

(* Pretty printing improvements (optional):
   - prints "value x = e" instead of "value = fun x -> e"
   - if vertical and "e" is a sequence, put the "do {" at after the "="
   - the continuation after the expression is optionally on next line if
     it not a sequence
   - the expression after '=' is displayed with the 'where' statement if
     possible (expr_wh)
   - if "e" is a type constraint, put the constraint after the params. E.g.
        value f x y = (e : t)
     is displayed:
        value f x y : t = e
   Cancellation of all these improvements could be done by changing calls
   to this function to a call to "binding expr" above.
*)
value value_binding pc (p, e) =
  let expr_wh = if flag_where_after_value_eq.val then expr_wh else expr in
  let (p, e) =
    if is_irrefut_patt p then (p, e)
    else
      let loc = MLast.loc_of_expr e in
      let (p, e) =
        loop p e where rec loop p =
          fun
          [ <:expr< fun $p1$ -> $e$ >> -> loop <:patt< $p$ $p1$ >> e
          | e -> (p, e) ]
      in
      let (up, ue) = un_irrefut_patt p in
      (up, <:expr< match $e$ with [ $p$ -> $ue$ ] >>)
  in
  let (pl, e) = expr_fun_args e in
  let pl = [p :: pl] in
  let (e, tyo) =
    match e with
    [ <:expr< ($e$ : $t$) >>  -> (e, Some t)
    | _ -> (e, None) ]
  in
  horiz_vertic
    (fun () ->
       sprintf "%s%s%s = %s%s" pc.bef
         (hlist patt {(pc) with bef = ""; aft = ""} pl)
         (match tyo with
          [ Some t -> sprintf " : %s" (ctyp {(pc) with bef = ""; aft = ""} t)
          | None -> "" ])
         (expr_wh {(pc) with bef = ""; aft = ""} e)
         pc.aft)
    (fun () ->
       let patt_eq k =
         horiz_vertic
           (fun () ->
              sprintf "%s%s%s =%s" pc.bef
                (hlist patt {(pc) with bef = ""; aft = ""} pl)
                (match tyo with
                 [ Some t ->
                     sprintf " : %s" (ctyp {(pc) with bef = ""; aft = ""} t)
                 | None -> "" ])
                k)
           (fun () ->
              let patt_tycon tyo pc p =
                match tyo with
                [ Some t ->
                    patt {(pc) with aft = ctyp {(pc) with bef = " : "} t} p
                | None -> patt pc p ]
              in
              let pl = List.map (fun p -> (p, "")) pl in
              plistl patt (patt_tycon tyo) 4
                {(pc) with aft = sprintf " =%s" k} pl)
       in
       match sequencify e with
       [ Some el -> sequence_box2 {(pc) with bef = patt_eq} el
       | None ->
           let s1 = patt_eq "" in
           let s2 =
             comm_expr expr_wh
               {(pc) with ind = pc.ind + 2; bef = tab (pc.ind + 2); aft = ""}
               e
           in
           let s3 =
             if pc.aft = "" then "" else sprintf "\n%s%s" (tab pc.ind) pc.aft
           in
           sprintf "%s\n%s%s" s1 s2 s3 ])
;

(* Pretty printing improvements (optional):
   - prints "let f x = e" instead of "let f = fun x -> e"
   - prints a newline before the "in" if last element not horizontal
   - the expression after '=' is displayed as 'where' if possible (expr_wh)
   Cancellation of all these improvements could be done by changing calls
   to this function to a call to "binding expr" above.
*)
value let_binding pc (p, e) =
  let expr_wh = if flag_where_after_let_eq.val then expr_wh else expr in
  let (p, e) =
    if is_irrefut_patt p then (p, e)
    else
      let loc = MLast.loc_of_expr e in
      let (p, e) =
        loop p e where rec loop p =
          fun
          [ <:expr< fun $p1$ -> $e$ >> -> loop <:patt< $p$ $p1$ >> e
          | e -> (p, e) ]
      in
      let (up, ue) = un_irrefut_patt p in
      (up, <:expr< match $e$ with [ $p$ -> $ue$ ] >>)
  in
  let (pl, e) = expr_fun_args e in
  let pl = [p :: pl] in
  let (e, tyo) =
    match e with
    [ <:expr< ($e$ : $t$) >>  -> (e, Some t)
    | _ -> (e, None) ]
  in
  horiz_vertic
    (fun () ->
       sprintf "%s%s%s = %s%s" pc.bef
         (hlist patt {(pc) with bef = ""; aft = ""} pl)
         (match tyo with
          [ Some t -> sprintf " : %s" (ctyp {(pc) with bef = ""; aft = ""} t)
          | None -> "" ])
         (expr_wh {(pc) with bef = ""; aft = ""} e)
         (if pc.aft = "in" then " in" else ""))
    (fun () ->
       let patt_eq k =
         horiz_vertic
           (fun () ->
              sprintf "%s%s%s =%s" pc.bef
                (hlist patt {(pc) with bef = ""; aft = ""} pl)
                (match tyo with
                 [ Some t ->
                     sprintf " : %s" (ctyp {(pc) with bef = ""; aft = ""} t)
                 | None -> "" ])
                k)
           (fun () ->
              let patt_tycon tyo pc p =
                match tyo with
                [ Some t ->
                    patt {(pc) with aft = ctyp {(pc) with bef = " : "} t} p
                | None -> patt pc p ]
              in
              let pl = List.map (fun p -> (p, "")) pl in
              plistl patt (patt_tycon tyo) 4
                {(pc) with aft = sprintf " =%s" k} pl)
       in
       let s =
         match sequencify e with
         [ Some el -> sequence_box2 {(pc) with bef = patt_eq; aft = ""} el
         | None ->
             let s1 = patt_eq "" in
             let s2 =
               comm_expr expr_wh
                 {(pc) with ind = pc.ind + 2; bef = tab (pc.ind + 2);
                  aft = ""}
                 e
              in
             sprintf "%s\n%s" s1 s2 ]
       in
       if pc.aft = "in" then sprintf "%s\n%sin" s (tab pc.ind) else s)
;

value match_assoc pc (p, w, e) =
  let expr_wh = if flag_where_after_arrow.val then expr_wh else expr in
  horiz_vertic
    (fun () ->
       sprintf "%s%s%s -> %s%s" pc.bef
         (patt_as {(pc) with bef = ""; aft = ""} p)
         (match w with
          [ Some e ->
              sprintf " when %s" (expr {(pc) with bef = ""; aft = ""} e)
          | None -> "" ])
         (comm_expr expr {(pc) with bef = ""; aft = ""} e) pc.aft)
    (fun () ->
       let patt_arrow k =
         match w with
         [ Some e ->
             horiz_vertic
               (fun () ->
                  sprintf "%s%s when %s ->%s" pc.bef
                    (patt_as {(pc) with bef = ""; aft = ""} p)
                    (expr {(pc) with bef = ""; aft = ""} e) k)
               (fun () ->
                  let s1 = patt_as {(pc) with aft = ""} p in
                  let s2 =
                    horiz_vertic
                      (fun () ->
                         sprintf "%swhen %s ->%s" (tab pc.ind)
                           (expr {(pc) with bef = ""; aft = ""} e) k)
                      (fun () ->
                         let s1 = sprintf "%swhen" (tab pc.ind) in
                         let s2 =
                           expr
                             {(pc) with ind = pc.ind + 2;
                              bef = tab (pc.ind + 2); aft = sprintf " ->%s" k}
                             e
                         in
                         sprintf "%s\n%s" s1 s2)
                  in
                  sprintf "%s\n%s" s1 s2)
         | None -> patt_as {(pc) with aft = sprintf " ->%s" k} p ]
       in
       match sequencify e with
       [ Some el ->
           sequence_box2
             {(pc) with
              bef k =
                horiz_vertic (fun _ -> sprintf "\n") (fun () -> patt_arrow k)}
             el
       | None ->
           let s1 = patt_arrow "" in
           let s2 =
             comm_expr expr_wh
               {(pc) with ind = pc.ind + 2; bef = tab (pc.ind + 2)} e
           in
           sprintf "%s\n%s" s1 s2 ])
;

value match_assoc_sh pc pwe = match_assoc {(pc) with ind = pc.ind + 2} pwe;

value match_assoc_list pc pwel =
  if pwel = [] then sprintf "%s[]%s" pc.bef pc.aft
  else
    vlist2 match_assoc_sh (bar_before match_assoc_sh)
      {(pc) with bef = sprintf "%s[ " pc.bef;
       aft = ("", sprintf " ]%s" pc.aft)}
      pwel
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

value type_var pc (tv, (p, m)) =
  sprintf "%s%s'%s%s" pc.bef (if p then "+" else if m then "-" else "") tv
    pc.aft
;

value type_constraint pc (t1, t2) =
  horiz_vertic
    (fun () ->
       sprintf "%sconstraint %s = %s%s" pc.bef
         (ctyp {(pc) with bef = ""; aft = ""} t1)
         (ctyp {(pc) with bef = ""; aft = ""} t2) pc.aft)
    (fun () -> not_impl "type_constraint vertic" pc t1)
;

value type_decl pc td =
  let ((_, tn), tp, pf, te, cl) =
    (td.MLast.tdNam, td.MLast.tdPrm, td.MLast.tdPrv, td.MLast.tdDef,
     td.MLast.tdCon)
  in
  horiz_vertic
    (fun () ->
       sprintf "%s%s%s = %s%s%s" pc.bef
         (var_escaped {(pc) with bef = ""; aft = ""} tn)
         (if tp = [] then ""
          else
            sprintf " %s" (hlist type_var {(pc) with bef = ""; aft = ""} tp))
         (ctyp {(pc) with bef = ""; aft = ""} te)
         (if cl = [] then ""
          else hlist type_constraint {(pc) with bef = " "; aft = ""} cl)
         pc.aft)
    (fun () ->
       let s1 =
         horiz_vertic
           (fun () ->
              sprintf "%s%s%s =" pc.bef
                (var_escaped {(pc) with bef = ""; aft = ""} tn)
                (if tp = [] then ""
                 else
                   sprintf " %s"
                     (hlist type_var {(pc) with bef = ""; aft = ""} tp)))
           (fun () -> not_impl "type_decl vertic 1" {(pc) with aft = ""} tn)
       in
       let s2 =
         if cl = [] then
           ctyp {(pc) with ind = pc.ind + 2; bef = tab (pc.ind + 2); aft = ""}
             te
         else
           horiz_vertic
             (fun () ->
                sprintf "%s%s%s%s" (tab (pc.ind + 2))
                  (ctyp {(pc) with bef = ""; aft = ""} te)
                  (not_impl "type_decl cl 2" {(pc) with bef = ""; aft = ""}
                     cl)
                  "")
             (fun () ->
                not_impl "type_decl vertic 2" {(pc) with bef = ""; aft = ""}
                  tn)
       in
       let s3 =
         if pc.aft = "" then "" else sprintf "\n%s%s" (tab pc.ind) pc.aft
       in
       sprintf "%s\n%s%s" s1 s2 s3)
;

value label_decl pc (_, l, m, t) =
  horiz_vertic
    (fun () ->
       sprintf "%s%s : %s%s%s" pc.bef l (if m then "mutable " else "")
         (ctyp {(pc) with bef = ""; aft = ""} t) pc.aft)
    (fun () ->
       let s1 = sprintf "%s%s :%s" pc.bef l (if m then " mutable" else "") in
       let s2 = ctyp {(pc) with ind = pc.ind + 2; bef = tab (pc.ind + 2)} t in
       sprintf "%s\n%s" s1 s2)
;

value cons_decl pc (_, c, tl) =
  if tl = [] then cons_escaped pc c
  else
    horiz_vertic
      (fun () ->
         sprintf "%s%s of %s%s" pc.bef c
           (hlist2 ctyp (and_before ctyp)
              {(pc) with bef = ""; aft = ("", "")} tl) pc.aft)
      (fun () ->
         let s1 = sprintf "%s%s of" pc.bef c in
         let s2 =
           horiz_vertic
             (fun () ->
                sprintf "%s%s%s" (tab (pc.ind + 4))
                  (hlist2 ctyp (and_before ctyp)
                     {(pc) with bef = ""; aft = ("", "")} tl) pc.aft)
             (fun () ->
                let tl = List.map (fun t -> (t, " and")) tl in
                plist ctyp 2
                  {(pc) with ind = pc.ind + 4; bef = tab (pc.ind + 4)} tl)
         in
         sprintf "%s\n%s" s1 s2)
;

value has_cons_with_params vdl = List.exists (fun (_, _, tl) -> tl <> []) vdl;

value rec get_else_if =
  fun
  [ <:expr< if $e1$ then $e2$ else $e3$ >> ->
      let (eel, e3) = get_else_if e3 in
      ([(e1, e2) :: eel], e3)
  | e -> ([], e) ]
;

value alone_in_line pc =
  (pc.aft = "" || pc.aft = ";") && pc.bef <> "" &&
  loop 0 where rec loop i =
    if i >= String.length pc.bef then True
    else if pc.bef.[i] = ' ' then loop (i + 1)
    else False
;

(* Expressions displayed without spaces separating elements; special
   for expressions as strings or arrays indexes (x.[...] or x.(...)).
   Applied only if only containing +, -, *, /, integers and variables. *)
value expr_short pc x =
  let rec expr1 pc z =
    match z with
    [ <:expr< $lid:op$ $x$ $y$ >> ->
        if op = "+" || op = "-" then
          sprintf "%s%s%s%s%s" pc.bef
            (expr1 {(pc) with bef = ""; aft = ""} x) op
            (expr2 {(pc) with bef = ""; aft = ""} y) pc.aft
        else expr2 pc z
    | _ -> expr2 pc z ]
  and expr2 pc z =
    match z with
    [ <:expr< $lid:op$ $x$ $y$ >> ->
        if op = "*" || op = "/" then
          sprintf "%s%s%s%s%s" pc.bef
            (expr2 {(pc) with bef = ""; aft = ""} x) op
            (expr3 {(pc) with bef = ""; aft = ""} y) pc.aft
        else expr3 pc z
    | _ -> expr3 pc z ]
  and expr3 pc z =
    match z with
    [ <:expr< $lid:v$ >> ->
        if is_infix v || has_special_chars v then raise Exit
        else var_escaped pc v
    | <:expr< $int:s$ >> -> sprintf "%s%s%s" pc.bef s pc.aft
    | <:expr< $lid:op$ $_$ $_$ >> ->
        if List.mem op ["+"; "-"; "*"; "/"] then
          sprintf "%s(%s)%s" pc.bef (expr1 {(pc) with bef = ""; aft = ""} z)
            pc.aft
        else raise Exit
    | _ -> raise Exit ]
  in
  try horiz_vertic (fun () -> expr1 pc x) (fun () -> raise Exit) with
  [ Exit -> expr pc x ]
;

(* definitions of printers by decreasing level *)

value ctyp_top =
  extfun Extfun.empty with
  [ <:ctyp< $x$ == $y$ >> ->
      fun curr next pc -> operator pc next next 2 "==" x y
  | z -> fun curr next pc -> next pc z ]
;

value ctyp_arrow =
  extfun Extfun.empty with
  [ <:ctyp< $_$ -> $_$ >> as z ->
      fun curr next pc ->
        let unfold =
          fun
          [ <:ctyp< $x$ -> $y$ >> -> Some (x, " ->", y)
          | _ -> None ]
        in
        right_operator pc 2 unfold next z
  | z -> fun curr next pc -> next pc z ]
;

value ctyp_apply =
  extfun Extfun.empty with
  [ <:ctyp< $_$ $_$ >> as z ->
      fun curr next pc ->
        let unfold =
          fun
          [ <:ctyp< $x$ $y$ >> -> Some (x, "", y)
          | _ -> None ]
        in
        left_operator pc 2 unfold next z
  | z -> fun curr next pc -> next pc z ]
;

value ctyp_dot =
  extfun Extfun.empty with
  [ <:ctyp< $x$ . $y$ >> ->
      fun curr next pc ->
        curr {(pc) with bef = curr {(pc) with aft = "."} x} y
  | z -> fun curr next pc -> next pc z ]
;

value ctyp_simple =
  extfun Extfun.empty with
  [ <:ctyp< { $list:ltl$ } >> ->
      fun curr next pc ->
        horiz_vertic
          (fun () ->
             hlistl (semi_after label_decl) label_decl
               {(pc) with bef = sprintf "%s{ " pc.bef;
                aft = sprintf " }%s" pc.aft}
               ltl)
          (fun () ->
             vlistl (semi_after label_decl) label_decl
               {(pc) with ind = pc.ind + 2; bef = sprintf "%s{ " pc.bef;
                aft = sprintf " }%s" pc.aft}
               ltl)
  | <:ctyp< [ $list:vdl$ ] >> ->
      fun curr next pc ->
        horiz_vertic
          (fun () ->
             if has_cons_with_params vdl then sprintf "\n"
             else
               hlist2 cons_decl (bar_before cons_decl)
                 {(pc) with bef = sprintf "%s[ " pc.bef;
                  aft = ("", sprintf " ]%s" pc.aft)}
                 vdl)
          (fun () ->
             vlist2 cons_decl (bar_before cons_decl)
               {(pc) with bef = sprintf "%s[ " pc.bef;
                aft = ("", sprintf " ]%s" pc.aft)}
               vdl)
  | <:ctyp< ($list:tl$) >> ->
      fun curr next pc ->
        horiz_vertic
          (fun () ->
             sprintf "%s(%s)%s" pc.bef
               (hlistl (star_after ctyp) ctyp {(pc) with bef = ""; aft = ""}
                  tl)
               pc.aft)
          (fun () ->
             let tl = List.map (fun t -> (t, " *")) tl in
             plist ctyp 1
               {(pc) with bef = sprintf "%s(" pc.bef;
                aft = sprintf ")%s" pc.aft} tl)
  | <:ctyp< $lid:t$ >> ->
      fun curr next pc -> var_escaped pc t
  | <:ctyp< $uid:t$ >> ->
      fun curr next pc -> sprintf "%s%s%s" pc.bef t pc.aft
  | <:ctyp< ' $s$ >> ->
      fun curr next pc -> var_escaped {(pc) with bef = sprintf "%s'" pc.bef} s
  | <:ctyp< _ >> ->
      fun curr next pc -> sprintf "%s_%s" pc.bef pc.aft
  | <:ctyp< ? $i$ : $t$ >> | <:ctyp< ~ $_$ : $t$ >> ->
      fun curr next pc ->
        failwith "labels not pretty printed (in type); add pr_ro.cmo"
  | <:ctyp< [ = $list:_$ ] >> | <:ctyp< [ > $list:_$ ] >> |
    <:ctyp< [ < $list:_$ ] >> | <:ctyp< [ < $list:_$ > $list:_$ ] >> ->
      fun curr next pc ->
        failwith "variants not pretty printed (in type); add pr_ro.cmo"
  | <:ctyp< $_$ $_$ >> | <:ctyp< $_$ -> $_$ >> as z ->
      fun curr next pc ->
        ctyp
          {(pc) with ind = pc.ind + 1; bef = sprintf "%s(" pc.bef;
           aft = sprintf ")%s" pc.aft}
          z
  | z ->
      fun curr next pc -> not_impl "ctyp" pc z ]
;

value expr_top =
  extfun Extfun.empty with
  [ <:expr< if $e1$ then $e2$ else $e3$ >> ->
      fun curr next pc ->
        let expr_wh = if flag_where_after_then.val then expr_wh else expr in
        horiz_vertic
         (fun () ->
            sprintf "%sif %s then %s else %s%s" pc.bef
              (curr {(pc) with bef = ""; aft = ""} e1)
              (curr {(pc) with bef = ""; aft = ""} e2)
              (curr {(pc) with bef = ""; aft = ""} e3) pc.aft)
         (fun () ->
            let if_then pc else_b e1 e2 =
              horiz_vertic
                (fun () ->
                   sprintf "%s%sif %s then %s%s" pc.bef else_b
                     (curr {(pc) with bef = ""; aft = ""} e1)
                     (curr {(pc) with bef = ""; aft = ""} e2) pc.aft)
                (fun () ->
                   let horiz_if_then k =
                     sprintf "%s%sif %s then%s" pc.bef else_b
                       (curr {(pc) with bef = ""; aft = ""} e1) k
                   in
                   let vertic_if_then k =
                     let s1 =
                       if else_b = "" then
                         curr
                           {(pc) with ind = pc.ind + 3;
                            bef = sprintf "%s%sif " pc.bef else_b; aft = ""}
                           e1
                       else
                         let s1 = sprintf "%s%sif" pc.bef else_b in
                         let s2 =
                           curr
                             {(pc) with ind = pc.ind + 2;
                              bef = tab (pc.ind + 2); aft = ""}
                             e1
                         in
                         sprintf "%s\n%s" s1 s2
                     in
                     let s2 = sprintf "%sthen%s" (tab pc.ind) k in
                     sprintf "%s\n%s" s1 s2
                   in
                   match sequencify e2 with
                   [ Some el ->
                       sequence_box2
                         {(pc) with
                          bef k =
                            horiz_vertic (fun () -> horiz_if_then k)
                              (fun () -> vertic_if_then k);
                          aft = ""}
                         el
                   | None ->
                       let s1 =
                         horiz_vertic (fun () -> horiz_if_then "")
                           (fun () -> vertic_if_then "")
                       in
                       let s2 =
                         comm_expr expr_wh
                           {(pc) with ind = pc.ind + 2;
                            bef = tab (pc.ind + 2); aft = ""}
                           e2
                       in
                       sprintf "%s\n%s" s1 s2 ])
            in
            let s1 = if_then {(pc) with aft = ""} "" e1 e2 in
            let (eel, e3) = get_else_if e3 in
            let s2 =
              loop eel where rec loop =
                fun
                [ [(e1, e2) :: eel] ->
                    sprintf "\n%s%s"
                      (if_then {(pc) with aft = ""} "else " e1 e2)
                      (loop eel)
                | [] -> "" ]
            in
            let s3 =
              horiz_vertic
                (fun () ->
                   sprintf "%selse %s%s" (tab pc.ind)
                     (comm_expr curr {(pc) with bef = ""; aft = ""} e3)
                        pc.aft)
                (fun () ->
                   match sequencify e3 with
                   [ Some el ->
                       sequence_box2
                         {(pc) with
                          bef k =
                            horiz_vertic (fun () -> sprintf "\n")
                              (fun () -> sprintf "%selse%s" (tab pc.ind) k)}
                         el
                   | None ->
                       let s =
                         comm_expr expr_wh
                           {(pc) with ind = pc.ind + 2;
                            bef = tab (pc.ind + 2)}
                           e3
                       in
                       sprintf "%selse\n%s" (tab pc.ind) s ])
            in
            sprintf "%s%s\n%s" s1 s2 s3)
  | <:expr< fun [ $list:pwel$ ] >> ->
      fun curr next pc ->
        match pwel with
        [ [(p1, None, e1)] when is_irrefut_patt p1 ->
            let (pl, e1) = expr_fun_args e1 in
            let pl = [p1 :: pl] in
            horiz_vertic
              (fun () ->
                 sprintf "%sfun %s -> %s%s" pc.bef
                   (hlist patt {(pc) with bef = ""; aft = ""} pl)
                   (curr {(pc) with bef = ""; aft = ""} e1) pc.aft)
              (fun () ->
                 let fun_arrow k =
                   let pl = List.map (fun p -> (p, "")) pl in
                   plist patt 4
                     {(pc) with bef = sprintf "%sfun " pc.bef;
                      aft = sprintf " ->%s" k}
                     pl
                 in
                 match sequencify e1 with
                 [ Some el ->
                     sequence_box2
                       {(pc) with
                        bef k =
                          horiz_vertic (fun _ -> sprintf "\n")
                            (fun () -> fun_arrow k)}
                       el
                 | None ->
                     let s1 = fun_arrow "" in
                     let s2 =
                       curr
                         {(pc) with ind = pc.ind + 2; bef = tab (pc.ind + 2)}
                         e1
                     in
                     sprintf "%s\n%s" s1 s2 ])
        | [] -> sprintf "%sfun []%s" pc.bef pc.aft
        | pwel ->
            let s = match_assoc_list {(pc) with bef = tab pc.ind} pwel in
            sprintf "%sfun\n%s" pc.bef s ]
  | <:expr< try $e1$ with [ $list:pwel$ ] >> |
    <:expr< match $e1$ with [ $list:pwel$ ] >> as e ->
      fun curr next pc ->
        let expr_wh = if flag_where_after_match.val then expr_wh else curr in
        let op =
          match e with
          [ <:expr< try $_$ with [ $list:_$ ] >> -> "try"
          | _ -> "match" ]
        in
        match pwel with
        [ [(p, wo, e)] when is_irrefut_patt p ->
            horiz_vertic
              (fun () ->
                 sprintf "%s%s %s with %s%s" pc.bef op
                   (expr_wh {(pc) with bef = ""; aft = ""} e1)
                   (match_assoc {(pc) with bef = ""; aft = ""} (p, wo, e))
                   pc.aft)
              (fun () ->
                 match
                   horiz_vertic
                     (fun () ->
                        Some
                          (sprintf "%s%s %s with %s%s ->" pc.bef op
                             (expr_wh {(pc) with bef = ""; aft = ""} e1)
                             (patt {(pc) with bef = ""; aft = ""} p)
                             (match wo with
                              [ Some e ->
                                  curr {(pc) with bef = " when"; aft = ""} e
                              | None -> "" ])))
                      (fun () -> None)
                 with
                 [ Some s1 ->
                     let s2 =
                       curr
                         {(pc) with ind = pc.ind + 2; bef = tab (pc.ind + 2)}
                         e
                     in
                     sprintf "%s\n%s" s1 s2
                 | None ->
                     let s1 =
                       match sequencify e1 with
                       [ Some el ->
                           sequence_box2
                             {(pc) with bef k = sprintf "%s%s%s" pc.bef op k;
                              aft = ""}
                             el
                       | None ->
                           let s =
                             expr_wh
                               {(pc) with ind = pc.ind + 2;
                                bef = tab (pc.ind + 2); aft = ""}
                               e1
                           in
                           sprintf "%s%s\n%s" pc.bef op s ]
                     in
                     let s2 =
                       match_assoc
                         {(pc) with bef = sprintf "%swith " (tab pc.ind)}
                         (p, wo, e)
                     in
                     sprintf "%s\n%s" s1 s2 ])
        | _ ->
            horiz_vertic
              (fun () ->
                 sprintf "%s%s %s with %s%s" pc.bef op
                   (expr_wh {(pc) with bef = ""; aft = ""} e1)
                   (match_assoc_list {(pc) with bef = ""; aft = ""} pwel)
                   pc.aft)
              (fun () ->
                 let s1 =
                   horiz_vertic
                     (fun () ->
                        sprintf "%s%s %s with" pc.bef op
                          (expr_wh {(pc) with bef = ""; aft = ""} e1))
                     (fun () ->
                        let s =
                          match sequencify e1 with
                          [ Some el ->
                              sequence_box2
                                {(pc) with
                                 bef k =
                                   horiz_vertic (fun _ -> sprintf "\n")
                                     (fun () -> sprintf "%s%s%s" pc.bef op k);
                                 aft = ""}
                                el
                          | None ->
                              let s =
                                expr_wh
                                  {(pc) with ind = pc.ind + 2;
                                   bef = tab (pc.ind + 2); aft = ""}
                                  e1
                              in
                              sprintf "%s%s\n%s" pc.bef op s ]
                        in
                        sprintf "%s\n%swith" s (tab pc.ind))
                 in
                 let s2 =
                   match_assoc_list {(pc) with bef = tab pc.ind} pwel
                 in
                 sprintf "%s\n%s" s1 s2) ]
  | <:expr< let $opt:rf$ $list:pel$ in $e$ >> as ge ->
      fun curr next pc ->
        let expr_wh = if flag_where_after_in.val then expr_wh else curr in
        horiz_vertic
          (fun () ->
             if not flag_horiz_let_in.val then sprintf "\n"
             else
               sprintf "%slet %s%s %s%s" pc.bef (if rf then "rec " else "")
                 (hlist2 let_binding (and_before let_binding)
                    {(pc) with bef = ""; aft = ("", "in")} pel)
                 (curr {(pc) with bef = ""; aft = ""} e) pc.aft)
          (fun () ->
             match flatten_sequence ge with
             [ Some el ->
                 let loc = MLast.loc_of_expr ge in
                 curr pc <:expr< do { $list:el$ } >>
             | None ->
                 let s1 =
                   vlist2 let_binding (and_before let_binding)
                     {(pc) with
                      bef =
                        sprintf "%slet %s" pc.bef (if rf then "rec " else "");
                      aft = ("", "in")}
                     pel
                 in
                 let s2 = comm_expr expr_wh {(pc) with bef = tab pc.ind} e in
                 sprintf "%s\n%s" s1 s2 ])
  | <:expr< let module $s$ = $me$ in $e$ >> ->
      fun curr next pc ->
        horiz_vertic
          (fun () ->
             sprintf "%slet module %s = %s in %s%s" pc.bef s
               (module_expr {(pc) with bef = ""; aft = ""} me)
               (curr {(pc) with bef = ""; aft = ""} e) pc.aft)
          (fun () ->
             let s1 =
               horiz_vertic
                 (fun () ->
                    sprintf "%slet module %s = %s in" pc.bef s
                      (module_expr {(pc) with bef = ""; aft = ""} me))
                 (fun () ->
                    let s1 = sprintf "%slet module %s =" pc.bef s in
                    let s2 =
                      module_expr
                        {(pc) with ind = pc.ind + 2; bef = tab (pc.ind + 2);
                         aft = ""}
                        me
                    in
                    let s3 = sprintf "%sin" (tab pc.ind) in
                    sprintf "%s\n%s\n%s" s1 s2 s3)
             in
             let s2 = curr {(pc) with bef = tab pc.ind} e in
             sprintf "%s\n%s" s1 s2)
  | <:expr< do { $list:el$ } >> as ge ->
      fun curr next pc ->
        let el =
          match flatten_sequence ge with
          [ Some el -> el
          | None -> el ]
        in
        horiz_vertic
          (fun () ->
             sprintf "%sdo {%s%s%s}%s" pc.bef " "
               (hlistl (semi_after (comm_expr curr)) (comm_expr curr)
                  {(pc) with bef = ""; aft = ""} el)
               " " pc.aft)
          (fun () ->
             sprintf "%sdo {%s%s%s}%s" pc.bef "\n"
               (vlistl (semi_after (comm_expr curr)) (comm_expr curr)
                  {(pc) with ind = pc.ind + 2; bef = tab (pc.ind + 2);
                   aft = ""}
                  el)
               ("\n" ^ tab pc.ind) pc.aft)
  | <:expr< while $e1$ do { $list:el$ } >> ->
      fun curr next pc ->
        horiz_vertic
          (fun () ->
             sprintf "%swhile %s do { %s }%s" pc.bef
               (curr {(pc) with bef = ""; aft = ""} e1)
               (hlistl (semi_after expr) curr {(pc) with bef = ""; aft = ""}
                  el)
               pc.aft)
          (fun () ->
             let s1 =
               horiz_vertic
                 (fun () ->
                    sprintf "%swhile %s do {" pc.bef
                      (curr {(pc) with bef = ""; aft = ""} e1))
                 (fun () ->
                    let s1 = sprintf "%swhile" pc.bef in
                    let s2 =
                      curr
                        {(pc) with ind = pc.ind + 2;
                         bef = tab (pc.ind + 2); aft = ""}
                        e1
                    in
                    let s3 = sprintf "%sdo {" (tab pc.ind) in
                    sprintf "%s\n%s\n%s" s1 s2 s3)
             in
             let s2 =
               vlistl (semi_after expr) curr
                 {(pc) with ind = pc.ind + 2; bef = tab (pc.ind + 2);
                  aft = ""}
                 el
             in
             let s3 = sprintf "%s}%s" (tab pc.ind) pc.aft in
             sprintf "%s\n%s\n%s" s1 s2 s3)
  | <:expr< for $v$ = $e1$ $to:d$ $e2$ do { $list:el$ } >> ->
      fun curr next pc ->
        let el =
          match el with
          [ [e] ->
              match sequencify e with
              [ Some el -> el
              | None -> el ]
          | _ -> el ]
        in
        horiz_vertic
          (fun () ->
             sprintf "%sfor %s = %s %s %s do { %s }%s" pc.bef v
               (curr {(pc) with bef = ""; aft = ""} e1)
               (if d then "to" else "downto")
               (curr {(pc) with bef = ""; aft = ""} e2)
               (hlistl (semi_after curr) curr {(pc) with bef = ""; aft = ""}
                  el) pc.aft)
          (fun () ->
             let s1 =
               horiz_vertic
                 (fun () ->
                    sprintf "%sfor %s = %s %s %s do {" pc.bef v
                      (curr {(pc) with bef = ""; aft = ""} e1)
                      (if d then "to" else "downto")
                      (curr {(pc) with bef = ""; aft = ""} e2))
                 (fun () ->
                    let s1 =
                      curr
                        {(pc) with bef = sprintf "%sfor %s = " pc.bef v;
                         aft = if d then " to" else " downto"}
                        e1
                    in
                    let s2 =
                      curr
                        {(pc) with ind = pc.ind + 4; bef = tab (pc.ind + 4);
                         aft = ""}
                        e2
                    in
                    let s3 = sprintf "%sdo {" (tab pc.ind) in
                    sprintf "%s\n%s\n%s" s1 s2 s3)
             in
             let s2 =
               vlist (semi_after curr)
                 {(pc) with ind = pc.ind + 2; bef = tab (pc.ind + 2);
                  aft = ""}
                 el
             in
             let s3 = sprintf "%s}%s" (tab pc.ind) pc.aft in
             sprintf "%s\n%s\n%s" s1 s2 s3)
  | z ->
      fun curr next pc -> next pc z ]
;

value expr_assign =
  extfun Extfun.empty with
  [ <:expr< $x$ := $y$ >> ->
      fun curr next pc -> operator pc next expr 2 ":=" x y
  | z -> fun curr next pc -> next pc z ]
;

value expr_or =
  extfun Extfun.empty with
  [ z ->
      fun curr next pc ->
        let unfold =
          fun
          [ <:expr< $lid:op$ $x$ $y$ >> ->
              if List.mem op ["||"; "or"] then Some (x, " ||", y) else None
          | _ -> None ]
        in
        right_operator pc 0 unfold next z ]
;

value expr_and =
  extfun Extfun.empty with
  [ z ->
      fun curr next pc ->
        let unfold =
          fun
          [ <:expr< $lid:op$ $x$ $y$ >> ->
              if List.mem op ["&&"; "&"] then Some (x, " &&", y) else None
          | _ -> None ]
        in
        right_operator pc 0 unfold next z ]
;

value expr_less =
  extfun Extfun.empty with
  [ <:expr< $lid:op$ $x$ $y$ >> as z ->
      fun curr next pc ->
        match op with
        [ "!=" | "<" | "<=" | "<>" | "=" | "==" | ">" | ">=" ->
            operator pc next next 0 op x y
        | _ -> next pc z ]
  | z -> fun curr next pc -> next pc z ]
;

value expr_concat =
  extfun Extfun.empty with
  [ z ->
      fun curr next pc ->
        let unfold =
          fun
          [ <:expr< $lid:op$ $x$ $y$ >> ->
              if List.mem op ["^"; "@"] then Some (x, " " ^ op, y) else None
          | _ -> None ]
        in
        right_operator pc 0 unfold next z ]
;

value expr_add =
  let ops = ["+"; "+."; "-"; "-."] in
  extfun Extfun.empty with
  [ z ->
      fun curr next pc ->
        let unfold =
          fun
          [ <:expr< $lid:op$ $x$ $y$ >> ->
              if List.mem op ops then Some (x, " " ^ op, y) else None
          | _ -> None ]
        in
        left_operator pc 0 unfold next z ]
;

value expr_mul =
  let ops = ["*"; "*."; "/"; "/."; "land"; "lor"; "lxor"; "mod"] in
  extfun Extfun.empty with
  [ z ->
      fun curr next pc ->
        let unfold =
          fun
          [ <:expr< $lid:op$ $x$ $y$ >> ->
              if List.mem op ops then Some (x, " " ^ op, y) else None
          | _ -> None ]
        in
        left_operator pc 0 unfold next z ]
;

value expr_pow =
  let ops = ["**"; "asr"; "lsl"; "lsr"] in
  extfun Extfun.empty with
  [ z ->
      fun curr next pc ->
        let unfold =
          fun
          [ <:expr< $lid:op$ $x$ $y$ >> ->
              if List.mem op ops then Some (x, " " ^ op, y) else None
          | _ -> None ]
        in
        right_operator pc 0 unfold next z ]
;

value expr_unary_minus =
  extfun Extfun.empty with
  [ <:expr< ~- $x$ >> ->
      fun curr next pc -> curr {(pc) with bef = sprintf "%s-" pc.bef} x
  | <:expr< ~-. $x$ >> ->
      fun curr next pc -> curr {(pc) with bef = sprintf "%s-." pc.bef} x
  | <:expr< $int:i$ >> ->
      fun curr next pc -> sprintf "%s%s%s" pc.bef i pc.aft
  | z ->
      fun curr next pc -> next pc z ]
;

value expr_apply =
  extfun Extfun.empty with
  [ <:expr< assert $e$ >> ->
      fun curr next pc ->
        horiz_vertic
          (fun () ->
             sprintf "%sassert %s%s" pc.bef
               (next {(pc) with bef = ""; aft = ""} e) pc.aft)
          (fun () -> not_impl "assert vertical" pc e)
  | <:expr< lazy $e$ >> ->
      fun curr next pc ->
        horiz_vertic
          (fun () ->
             sprintf "%slazy %s%s" pc.bef
               (next {(pc) with bef = ""; aft = ""} e) pc.aft)
          (fun () ->
             let s1 = sprintf "%slazy" pc.bef in
             let s2 =
               next {(pc) with ind = pc.ind + 2; bef = tab (pc.ind + 2)} e
             in
             sprintf "%s\n%s" s1 s2)
  | <:expr< $_$ $_$ >> as z ->
      fun curr next pc ->
        let inf =
          match z with
          [ <:expr< $lid:n$ $_$ $_$ >> -> is_infix n
          | <:expr< [$_$ :: $_$] >> -> True
          | _ -> False ]
        in
        if inf then next pc z
        else
          let unfold =
            fun
            [ <:expr< $x$ $y$ >> -> Some (x, "", y)
            | e -> None ]
          in
          left_operator pc 2 unfold next z
  | z ->
      fun curr next pc -> next pc z ]
;

value expr_dot =
  extfun Extfun.empty with
  [ <:expr< $x$ . $y$ >> ->
      fun curr next pc ->
        horiz_vertic
          (fun () ->
             sprintf "%s%s.%s%s" pc.bef
               (curr {(pc) with bef = ""; aft = ""} x)
               (curr {(pc) with bef = ""; aft = ""} y) pc.aft)
          (fun () ->
             let s1 = curr {(pc) with aft = "."} x in
             let s2 = curr {(pc) with bef = tab pc.ind} y in
             sprintf "%s\n%s" s1 s2)
  | <:expr< $x$ .( $y$ ) >> ->
      fun curr next pc ->
        expr
          {(pc) with bef = curr {(pc) with aft = ".("} x;
           aft = sprintf ")%s" pc.aft}
          y
  | <:expr< $x$ .[ $y$ ] >> ->
      fun curr next pc ->
        expr_short
          {(pc) with bef = curr {(pc) with aft = ".["} x;
           aft = (sprintf "]%s" pc.aft)}
          y
  | z ->
      fun curr next pc -> next pc z ]
;

value expr_simple =
  extfun Extfun.empty with
  [ <:expr< ($list:el$) >> ->
      fun curr next pc ->
        let el = List.map (fun e -> (e, ",")) el in
        plist expr 0
          {(pc) with ind = pc.ind + 1; bef = sprintf "%s(" pc.bef;
           aft = (sprintf ")%s" pc.aft)}
          el
  | <:expr< {$list:lel$} >> ->
      fun curr next pc ->
        let lxl = List.map (fun lx -> (lx, ";")) lel in
        plist (comm_patt_any record_binding) 0
          {(pc) with ind = pc.ind + 1; bef = sprintf "%s{" pc.bef;
           aft = (sprintf "}%s" pc.aft)}
          lxl
  | <:expr< {($e$) with $list:lel$} >> ->
      fun curr next pc ->
        let lxl = List.map (fun lx -> (lx, ";")) lel in
        plist record_binding 0
          {(pc) with ind = pc.ind + 1;
           bef =
             expr {(pc) with bef = sprintf "%s{(" pc.bef; aft = ") with "} e;
           aft = (sprintf "}%s" pc.aft)} lxl
  | <:expr< [| $list:el$ |] >> ->
      fun curr next pc ->
        if el = [] then sprintf "%s[| |]%s" pc.bef pc.aft
        else
          let el = List.map (fun e -> (e, ";")) el in
          plist expr 0
            {(pc) with ind = pc.ind + 3; bef = sprintf "%s[| " pc.bef;
             aft = (sprintf " |]%s" pc.aft)}
            el
  | <:expr< [$_$ :: $_$] >> as z ->
      fun curr next pc ->
        let (xl, y) = make_expr_list z in
        let xl = List.map (fun x -> (x, ";")) xl in
        match y with
        [ Some y ->
            let expr2 pc x =
              horiz_vertic
                (fun () ->
                   sprintf "%s%s :: %s]%s" pc.bef
                     (expr {(pc) with bef = ""; aft = ""} x)
                     (expr {(pc) with bef = ""; aft = ""} y) pc.aft)
                (fun () ->
                   let s1 = expr {(pc) with aft = " ::"} x in
                   let s2 =
                     expr
                       {(pc) with bef = tab pc.ind;
                        aft = sprintf "]%s" pc.aft}
                       y
                   in
                   sprintf "%s\n%s" s1 s2)
            in
            plistl expr expr2 0
              {(pc) with ind = pc.ind + 1; bef = sprintf "%s[" pc.bef} xl
        | None ->
            plist expr 0
              {(pc) with ind = pc.ind + 1; bef = sprintf "%s[" pc.bef;
               aft = sprintf "]%s" pc.aft}
              xl ]
  | <:expr< ($e$ : $t$) >> ->
      fun curr next pc ->
        horiz_vertic
          (fun () ->
             sprintf "%s(%s : %s)%s" pc.bef
               (expr {(pc) with bef = ""; aft = ""} e)
               (ctyp {(pc) with bef = ""; aft = ""} t)
               pc.aft)
          (fun () ->
             let s1 =
               expr
                 {(pc) with ind = pc.ind + 1; bef = sprintf "%s(" pc.bef;
                  aft = " :"}
                 e
             in
             let s2 =
               ctyp
                 {(pc) with ind = pc.ind + 1; bef = tab (pc.ind + 1);
                  aft = sprintf ")%s" pc.aft}
                 t
             in
             sprintf "%s\n%s" s1 s2)
  | <:expr< $int:s$ >> | <:expr< $flo:s$ >> ->
      fun curr next pc ->
        if String.length s > 0 && s.[0] = '-' then
          sprintf "%s(%s)%s" pc.bef s pc.aft
        else
          sprintf "%s%s%s" pc.bef s pc.aft
  | <:expr< $int32:s$ >> ->
      fun curr next pc ->
        let s = s ^ "l" in
        if String.length s > 0 && s.[0] = '-' then
          sprintf "%s(%s)%s" pc.bef s pc.aft
        else
          sprintf "%s%s%s" pc.bef s pc.aft
  | <:expr< $int64:s$ >> ->
      fun curr next pc ->
        let s = s ^ "L" in
        if String.length s > 0 && s.[0] = '-' then
          sprintf "%s(%s)%s" pc.bef s pc.aft
        else
          sprintf "%s%s%s" pc.bef s pc.aft
  | <:expr< $nativeint:s$ >> ->
      fun curr next pc ->
        let s = s ^ "n" in
        if String.length s > 0 && s.[0] = '-' then
          sprintf "%s(%s)%s" pc.bef s pc.aft
        else
          sprintf "%s%s%s" pc.bef s pc.aft
  | <:expr< $lid:s$ >> ->
      fun curr next pc -> var_escaped pc s
  | <:expr< $uid:s$ >> ->
      fun curr next pc -> cons_escaped pc s
  | <:expr< `$uid:s$ >> ->
      fun curr next pc -> sprintf "%s%s%s" pc.bef s pc.aft
  | <:expr< $str:s$ >> ->
      fun curr next pc -> sprintf "%s\"%s\"%s" pc.bef s pc.aft
  | <:expr< $chr:s$ >> ->
      fun curr next pc -> sprintf "%s'%s'%s" pc.bef s pc.aft
  | <:expr< ? $_$ >> | <:expr< ~ $_$ >> | <:expr< ~ $_$ : $_$ >> ->
      fun curr next pc ->
        failwith "labels not pretty printed (in expr); add pr_ro.cmo"
  | <:expr< $_$ $_$ >> | <:expr< assert $_$ >> | <:expr< lazy $_$ >> |
    <:expr< $_$ := $_$ >> |
    <:expr< fun [ $list:_$ ] >> | <:expr< if $_$ then $_$ else $_$ >> |
    <:expr< do { $list:_$ } >> |
    <:expr< for $_$ = $_$ $to:_$ $_$ do { $list:_$ } >> |
    <:expr< while $_$ do { $list:_$ } >> |
    <:expr< let $opt:_$ $list:_$ in $_$ >> |
    <:expr< match $_$ with [ $list:_$ ] >> |
    <:expr< try $_$ with [ $list:_$ ] >> as z ->
      fun curr next pc ->
        let expr_wh = if flag_where_after_lparen.val then expr_wh else expr in
        expr_wh
          {(pc) with ind = pc.ind + 1; bef = sprintf "%s(" pc.bef;
           aft = sprintf ")%s" pc.aft}
          z
  | z ->
      fun curr next pc -> not_impl "expr" pc z ]
;

value patt_top =
  extfun Extfun.empty with
  [ <:patt< $_$ | $_$ >> as z ->
      fun curr next pc ->
        let unfold =
          fun
          [ <:patt< $x$ | $y$ >> -> Some (x, " |", y)
          | _ -> None ]
        in
        left_operator pc 0 unfold next z
  | z -> fun curr next pc -> next pc z ]
;

value patt_range =
  extfun Extfun.empty with
  [ <:patt< $x$ .. $y$ >> ->
      fun curr next pc ->
        sprintf "%s..%s" (next {(pc) with aft = ""} x)
          (next {(pc) with bef = ""} y)
  | z -> fun curr next pc -> next pc z ]
;

value patt_apply =
  extfun Extfun.empty with
  [ <:patt< $_$ $_$ >> as z ->
      fun curr next pc ->
        let unfold =
          fun
          [ <:patt< [ $_$ :: $_$ ] >> -> None
          | <:patt< $x$ $y$ >> -> Some (x, "", y)
          | p -> None ]
        in
        left_operator pc 2 unfold next z
  | z -> fun curr next pc -> next pc z ]
;

value patt_dot =
  extfun Extfun.empty with
  [ <:patt< $x$ . $y$ >> ->
      fun curr next pc ->
        curr {(pc) with bef = curr {(pc) with aft = "."} x} y
  | z -> fun curr next pc -> next pc z ]
;

value patt_simple =
  extfun Extfun.empty with
  [ <:patt< ($x$ as $y$) >> ->
      fun curr next pc ->
        horiz_vertic
          (fun () ->
             sprintf "%s(%s as %s)%s" pc.bef
               (patt {(pc) with bef = ""; aft = ""} x)
               (patt {(pc) with bef = ""; aft = ""} y) pc.aft)
          (fun () ->
             let s1 =
               patt
                 {(pc) with ind = pc.ind + 1; bef = sprintf "%s(" pc.bef;
                  aft = ""}
                 x
             in
             let s2 =
               patt
                 {(pc) with ind = pc.ind + 1;
                  bef = sprintf "%sas " (tab (pc.ind + 1));
                  aft = sprintf ")%s" pc.aft}
                 y
             in
             sprintf "%s\n%s" s1 s2)
  | <:patt< ($list:pl$) >> ->
      fun curr next pc ->
        let pl = List.map (fun p -> (p, ",")) pl in
        plist patt 1
          {(pc) with bef = sprintf "%s(" pc.bef; aft = sprintf ")%s" pc.aft}
          pl
  | <:patt< {$list:lpl$} >> ->
      fun curr next pc ->
        let lxl = List.map (fun lx -> (lx, ";")) lpl in
        plist (binding patt) 0
          {(pc) with ind = pc.ind + 1; bef = sprintf "%s{" pc.bef;
           aft = sprintf "}%s" pc.aft}
          lxl
  | <:patt< [| $list:pl$ |] >> ->
      fun curr next pc ->
        if pl = [] then sprintf "%s[| |]%s" pc.bef pc.aft
        else
          let pl = List.map (fun p -> (p, ";")) pl in
          plist patt 0
            {(pc) with ind = pc.ind + 3; bef = sprintf "%s[| " pc.bef;
             aft = (sprintf " |]%s" pc.aft)}
            pl
  | <:patt< [$_$ :: $_$] >> as z ->
      fun curr next pc ->
        let (xl, y) = make_patt_list z in
        let xl = List.map (fun x -> (x, ";")) xl in
        match y with
        [ Some  y ->
            let patt2 pc x =
              horiz_vertic
                (fun () ->
                   sprintf "%s%s :: %s]%s" pc.bef
                     (patt {(pc) with bef = ""; aft = ""} x)
                     (patt {(pc) with bef = ""; aft = ""} y) pc.aft)
                (fun () ->
                   let s1 = patt {(pc) with aft = " ::"} x in
                   let s2 =
                     patt
                       {(pc) with ind = pc.ind + 2; bef = tab (pc.ind + 2);
                        aft = sprintf "]%s" pc.aft}
                       y
                   in
                   sprintf "%s\n%s" s1 s2)
            in
            plistl patt patt2 0
              {(pc) with ind = pc.ind + 1; bef = sprintf "%s[" pc.bef} xl
        | None ->
            plist patt 0
              {(pc) with ind = pc.ind + 1; bef = sprintf "%s[" pc.bef;
               aft = sprintf "]%s" pc.aft}
              xl ]
  | <:patt< ($p$ : $t$) >> ->
      fun curr next pc ->
        horiz_vertic
          (fun () ->
             sprintf "%s(%s : %s)%s" pc.bef
               (patt {(pc) with bef = ""; aft = ""} p)
               (ctyp {(pc) with bef = ""; aft = ""} t) pc.aft)
          (fun () ->
             let s1 =
               patt {(pc) with bef = sprintf "%s(" pc.bef; aft = " :"} p
             in
             let s2 =
               ctyp
                 {(pc) with ind = pc.ind + 1; bef = tab (pc.ind + 1);
                  aft = (sprintf ")%s" pc.aft)}
                 t
             in
             sprintf "%s\n%s" s1 s2)
  | <:patt< $int:s$ >> | <:patt< $flo:s$ >> ->
      fun curr next pc ->
        if String.length s > 0 && s.[0] = '-' then
          sprintf "%s(%s)%s" pc.bef s pc.aft
        else
          sprintf "%s%s%s" pc.bef s pc.aft
  | <:patt< $int32:s$ >> ->
      fun curr next pc ->
        let s = s ^ "l" in
        if String.length s > 0 && s.[0] = '-' then
          sprintf "%s(%s)%s" pc.bef s pc.aft
        else
          sprintf "%s%s%s" pc.bef s pc.aft
  | <:patt< $int64:s$ >> ->
      fun curr next pc ->
        let s = s ^ "L" in
        if String.length s > 0 && s.[0] = '-' then
          sprintf "%s(%s)%s" pc.bef s pc.aft
        else
          sprintf "%s%s%s" pc.bef s pc.aft
  | <:patt< $nativeint:s$ >> ->
      fun curr next pc ->
        let s = s ^ "n" in
        if String.length s > 0 && s.[0] = '-' then
          sprintf "%s(%s)%s" pc.bef s pc.aft
        else
          sprintf "%s%s%s" pc.bef s pc.aft
  | <:patt< $lid:s$ >> ->
      fun curr next pc -> var_escaped pc s
  | <:patt< $uid:s$ >> ->
      fun curr next pc -> cons_escaped pc s
  | <:patt< $chr:s$ >> ->
      fun curr next pc -> sprintf "%s'%s'%s" pc.bef s pc.aft
  | <:patt< $str:s$ >> ->
      fun curr next pc -> sprintf "%s\"%s\"%s" pc.bef s pc.aft
  | <:patt< _ >> ->
      fun curr next pc -> sprintf "%s_%s" pc.bef pc.aft
  | <:patt< ? $_$ >> | <:patt< ? ($_$ $opt:_$) >> |
    <:patt< ? $_$ : ($_$ $opt:_$) >> | <:patt< ~ $_$ >> |
    <:patt< ~ $_$ : $_$ >> ->
      fun curr next pc ->
        failwith "labels not pretty printed (in patt); add pr_ro.cmo"
  | <:patt< `$uid:s$ >> ->
      fun curr next pc ->
        failwith "polymorphic variants not pretty printed; add pr_ro.cmo"
  | <:patt< $_$ $_$ >> | <:patt< $_$ | $_$ >> | <:patt< $_$ .. $_$ >>
    as z ->
      fun curr next pc ->
        patt
          {(pc) with ind = pc.ind + 1; bef = sprintf "%s(" pc.bef;
           aft = sprintf ")%s" pc.aft}
          z
  | z ->
      fun curr next pc -> not_impl "patt" pc z ]
;

value string pc s = sprintf "%s\"%s\"%s" pc.bef s pc.aft;

value external_decl pc (n, t, sl) =
  horiz_vertic
    (fun () ->
       sprintf "%sexternal %s : %s = %s%s" pc.bef
         (var_escaped {(pc) with bef = ""; aft = ""} n)
         (ctyp {(pc) with bef = ""; aft = ""} t)
         (hlist string {(pc) with bef = ""; aft = ""} sl) pc.aft)
    (fun () ->
       let s1 =
         var_escaped
           {(pc) with bef = sprintf "%sexternal " pc.bef; aft = " :"} n
       in
       let s2 =
         ctyp
           {(pc) with ind = pc.ind + 2; bef = tab (pc.ind + 2);
            aft =
              if sl = [] then pc.aft
              else
                sprintf " = %s%s"
                  (hlist string {(pc) with bef = ""; aft = ""} sl) pc.aft}
           t
       in
       sprintf "%s\n%s" s1 s2)
;

value exception_decl pc (e, tl, id) =
  horiz_vertic
    (fun () ->
       sprintf "%sexception %s%s%s%s" pc.bef e
         (if tl = [] then ""
          else
            sprintf " of %s"
              (hlist2 ctyp (and_before ctyp)
                 {(pc) with bef = ""; aft = ("", "")} tl))
         (if id = [] then ""
          else sprintf " = %s" (mod_ident {(pc) with bef = ""; aft = ""} id))
         pc.aft)
    (fun () ->
       let s1 =
         sprintf "%sexception %s%s" pc.bef e (if tl = [] then "" else " of")
       in
       let s2 =
         if tl = [] then ""
         else
           let tl = List.map (fun t -> (t, " and")) tl in
           sprintf "\n%s"
             (plist ctyp 2
                {(pc) with bef = tab (pc.ind + 2);
                 aft = if id = [] then pc.aft else ""}
                tl)
       in
       let s3 =
         if id = [] then ""
         else
           sprintf "\n%s"
             (mod_ident
                {(pc) with ind = pc.ind + 2;
                 bef = sprintf "%s= " (tab (pc.ind + 2)); aft = pc.aft}
                id)
       in
       sprintf "%s%s%s" s1 s2 s3)
;

value str_item_top =
  extfun Extfun.empty with
  [ <:str_item< # $s$ $e$ >> ->
      fun curr next pc ->
        expr {(pc) with bef = sprintf "%s#%s " pc.bef s} e
  | <:str_item< declare $list:sil$ end >> ->
      fun curr next pc ->
        if flag_expand_declare.val then
          horiz_vertic
            (fun () ->
               hlist (semi_after str_item) {(pc) with bef = ""; aft = ""} sil)
            (fun () -> not_impl "expand declare vertic" pc sil)
        else if sil = [] then sprintf "%sdeclare end%s" pc.bef pc.aft
        else
          horiz_vertic
            (fun () ->
               sprintf "%sdeclare%s%s%send%s" pc.bef " "
                 (hlist (semi_after str_item) {(pc) with bef = ""; aft = ""}
                    sil)
                 " " pc.aft)
            (fun () ->
               sprintf "%sdeclare%s%s%send%s" pc.bef "\n"
                 (vlist (semi_after str_item)
                    {(pc) with ind = pc.ind + 2; bef = tab (pc.ind + 2);
                     aft = ""}
                    sil)
                 ("\n" ^ tab pc.ind) pc.aft)
  | <:str_item< exception $e$ of $list:tl$ = $id$ >> ->
      fun curr next pc -> exception_decl pc (e, tl, id)
  | <:str_item< external $n$ : $t$ = $list:sl$ >> ->
      fun curr next pc -> external_decl pc (n, t, sl)
  | <:str_item< include $me$ >> ->
      fun curr next pc ->
        module_expr {(pc) with bef = sprintf "%sinclude " pc.bef} me
  | <:str_item< module $m$ = $me$ >> ->
      fun curr next pc ->
        let (mal, me) =
          loop me where rec loop =
            fun
            [ <:module_expr< functor ($s$ : $mt$) -> $me$ >> ->
                let (mal, me) = loop me in
                ([(s, mt) :: mal], me)
            | me -> ([], me) ]
        in
        let module_arg pc (s, mt) =
          horiz_vertic
            (fun () ->
               sprintf "%s(%s : %s)%s" pc.bef s
                 (module_type {(pc) with bef = ""; aft = ""} mt) pc.aft)
            (fun () ->
               let s1 = sprintf "%s(%s :" pc.bef s in
               let s2 =
                 module_type
                   {(pc) with ind = pc.ind + 1; bef = tab (pc.ind + 1);
                    aft = sprintf ")%s" pc.aft}
                   mt
               in
               sprintf "%s\n%s" s1 s2)
        in
        let (me, mto) =
          match me with
          [ <:module_expr< ($me$ : $mt$) >> -> (me, Some mt)
          | _ -> (me, None) ]
        in
        horiz_vertic
          (fun () ->
             sprintf "%smodule %s%s%s = %s%s" pc.bef m
               (if mal = [] then ""
                else hlist module_arg {(pc) with bef = " "; aft = ""} mal)
               (match mto with
                [ Some mt ->
                    sprintf " : %s"
                      (module_type {(pc) with bef = ""; aft = ""} mt)
                | None -> "" ])
               (module_expr {(pc) with bef = ""; aft = ""} me) pc.aft)
          (fun () ->
             let s1 =
               match mto with
               [ Some mt ->
                   horiz_vertic
                     (fun () ->
                        sprintf "%smodule %s%s : %s =" pc.bef m
                          (if mal = [] then ""
                           else
                             hlist module_arg
                               {(pc) with bef = " "; aft = ""} mal)
                          (module_type {(pc) with bef = ""; aft = ""} mt))
                     (fun () ->
                        let s1 =
                          sprintf "%smodule %s%s :" pc.bef m
                            (if mal = [] then "" else
                             hlist module_arg
                               {(pc) with bef = " "; aft = ""} mal)
                        in
                        let s2 =
                          module_type
                            {(pc) with ind = pc.ind + 2;
                             bef = tab (pc.ind + 2); aft = " ="}
                            mt
                        in
                        sprintf "%s\n%s" s1 s2)
               | None ->
                   let mal = List.map (fun ma -> (ma, "")) mal in
                   plistb module_arg 2
                     {(pc) with bef = sprintf "%smodule %s" pc.bef m;
                      aft = " ="}
                     mal ]
             in
             let s2 =
               module_expr
                 {(pc) with ind = pc.ind + 2; bef = tab (pc.ind + 2);
                  aft = ""}
                 me
             in
             sprintf "%s\n%s\n%s" s1 s2 (tab pc.ind ^ pc.aft))
  | <:str_item< module type $m$ = $mt$ >> ->
      fun curr next pc ->
        horiz_vertic
          (fun () ->
             sprintf "%smodule type %s = %s%s" pc.bef m
               (module_type {(pc) with bef = ""; aft = ""} mt) pc.aft)
          (fun () ->
             let s1 = sprintf "%smodule type %s =" pc.bef m in
             let s2 =
               module_type
                 {(pc) with ind = pc.ind + 2; bef = tab (pc.ind + 2);
                  aft = ""}
                 mt
             in
             let s3 = sprintf "%s%s" (tab pc.ind) pc.aft in
             sprintf "%s\n%s\n%s" s1 s2 s3)
  | <:str_item< open $i$ >> ->
      fun curr next pc ->
        mod_ident {(pc) with bef = sprintf "%sopen " pc.bef} i
  | <:str_item< type $list:tdl$ >> ->
      fun curr next pc ->
        vlist2 type_decl (and_before type_decl)
          {(pc) with bef = sprintf "%stype " pc.bef; aft = ("", pc.aft)} tdl
  | <:str_item< value $opt:rf$ $list:pel$ >> ->
      fun curr next pc ->
        horiz_vertic
          (fun () ->
             sprintf "%svalue %s%s" pc.bef (if rf then "rec " else "")
               (hlist2 value_binding (and_before value_binding)
                  {(pc) with bef = ""; aft = ("", pc.aft)} pel))
          (fun () ->
             vlist2 value_binding (and_before value_binding)
               {(pc) with
                bef = sprintf "%svalue %s" pc.bef (if rf then "rec " else "");
                aft = ("", pc.aft)} pel)
  | <:str_item< $exp:e$ >> ->
      fun curr next pc -> expr pc e
  | <:str_item< class type $list:_$ >> | <:str_item< class $list:_$ >> ->
      fun curr next pc ->
        failwith "classes and objects not pretty printed; add pr_ro.cmo"
  | z ->
      fun curr next pc -> not_impl "str_item" pc z ]
;

value sig_item_top =
  extfun Extfun.empty with
  [ <:sig_item< exception $e$ of $list:tl$ >> ->
      fun curr next pc -> exception_decl pc (e, tl, [])
  | <:sig_item< external $n$ : $t$ = $list:sl$ >> ->
      fun curr next pc -> external_decl pc (n, t, sl)
  | <:sig_item< include $mt$ >> ->
      fun curr next pc ->
        module_type {(pc) with bef = sprintf "%sinclude " pc.bef} mt
  | <:sig_item< module $m$ : $mt$ >> ->
      fun curr next pc ->
        horiz_vertic
          (fun () ->
             sprintf "%smodule %s : %s%s" pc.bef m
               (module_type {(pc) with bef = ""; aft = ""} mt) pc.aft)
          (fun () ->
             let s1 =  sprintf "%smodule %s :" pc.bef m in
             let s2 =
               module_type
                 {(pc) with ind = pc.ind + 2; bef = tab (pc.ind + 2);
                  aft = ""}
                 mt
             in
             let s3 = sprintf "%s%s" (tab pc.ind) pc.aft in
             sprintf "%s\n%s\n%s" s1 s2 s3)
  | <:sig_item< module type $m$ = $mt$ >> ->
      fun curr next pc ->
        horiz_vertic
          (fun () ->
             sprintf "%smodule type %s = %s%s" pc.bef m
               (module_type {(pc) with bef = ""; aft = ""} mt) pc.aft)
          (fun () ->
             let s1 = sprintf "%smodule type %s =" pc.bef m in
             let s2 =
               module_type
                 {(pc) with ind = pc.ind + 2; bef = tab (pc.ind + 2);
                  aft = ""}
                 mt
             in
             let s3 = sprintf "%s%s" (tab pc.ind) pc.aft in
             sprintf "%s\n%s\n%s" s1 s2 s3)
  | <:sig_item< open $i$ >> ->
      fun curr next pc ->
        mod_ident {(pc) with bef = (sprintf "%sopen " pc.bef)} i
  | <:sig_item< type $list:tdl$ >> ->
      fun curr next pc ->
        vlist2 type_decl (and_before type_decl)
          {(pc) with bef = sprintf "%stype " pc.bef; aft = ("", pc.aft)} tdl
  | <:sig_item< value $s$ : $t$ >> ->
      fun curr next pc ->
        horiz_vertic
          (fun () ->
             sprintf "%svalue %s : %s%s" pc.bef
               (var_escaped {(pc) with bef = ""; aft = ""} s)
               (ctyp {(pc) with bef = ""; aft = ""} t) pc.aft)
          (fun () ->
             let s1 =
               sprintf "%svalue %s :" pc.bef
                 (var_escaped {(pc) with bef = ""; aft = ""} s)
             in
             let s2 =
               ctyp {(pc) with ind = pc.ind + 2; bef = tab (pc.ind + 2)} t
             in
             sprintf "%s\n%s" s1 s2)
  | <:sig_item< class type $list:_$ >> | <:sig_item< class $list:_$ >> ->
      fun curr next pc ->
        failwith "classes and objects not pretty printed; add pr_ro.cmo"
  | z ->
      fun curr next pc -> not_impl "sig_item" pc z ]
;

value str_or_sig_functor pc s mt module_expr_or_type met =
  horiz_vertic
    (fun () ->
       sprintf "%sfunctor (%s : %s) -> %s%s" pc.bef s
         (module_type {(pc) with bef = ""; aft = ""} mt)
         (module_expr_or_type {(pc) with bef = ""; aft = ""} met) pc.aft)
    (fun () ->
       let s1 =
         horiz_vertic
           (fun () ->
              sprintf "%sfunctor (%s : %s) ->" pc.bef s
                (module_type {(pc) with bef = ""; aft = ""} mt))
           (fun () ->
              let s1 = sprintf "%sfunctor" pc.bef in
              let s2 =
                horiz_vertic
                  (fun () ->
                     sprintf "%s(%s : %s)" (tab (pc.ind + 2)) s
                       (module_type {(pc) with bef = ""; aft = ""} mt))
                  (fun () ->
                     let s1 = sprintf "%s(%s :" (tab (pc.ind + 2)) s in
                     let s2 =
                       module_type
                         {(pc) with ind = pc.ind + 3;
                          bef = tab (pc.ind + 3); aft = ")"}
                         mt
                     in
                     sprintf "%s\n%s" s1 s2)
              in
              let s3 = sprintf "%s->" (tab pc.ind) in
              sprintf "%s\n%s\n%s" s1 s2 s3)
       in
       let s2 =
         module_expr_or_type
           {(pc) with ind = pc.ind + 2; bef = tab (pc.ind + 2)} met
       in
       sprintf "%s\n%s" s1 s2)
;

value module_expr_top =
  extfun Extfun.empty with
  [ <:module_expr< functor ($s$ : $mt$) -> $me$ >> ->
      fun curr next pc ->
        str_or_sig_functor pc s mt module_expr me
  | <:module_expr< struct $list:sil$ end >> ->
      fun curr next pc ->
        horiz_vertic
          (fun () ->
             if alone_in_line pc then
               (* Heuristic : I don't like to print structs horizontally
                  when alone in a line. *)
               sprintf "\n"
             else
               sprintf "%sstruct%s%s%send%s" pc.bef " "
                 (hlist (semi_after str_item) {(pc) with bef = ""; aft = ""}
                    sil)
                 " " pc.aft)
          (fun () ->
             sprintf "%sstruct%s%s%send%s" pc.bef "\n"
               (vlist (semi_after str_item)
                  {(pc) with ind = pc.ind + 2; bef = tab (pc.ind + 2);
                   aft = ""}
                  sil)
               ("\n" ^ tab pc.ind) pc.aft)
  | z ->
      fun curr next pc -> next pc z ]
;

value module_expr_apply =
  extfun Extfun.empty with
  [ <:module_expr< $x$ $y$ >> as z ->
      fun curr next pc ->
        let unfold =
          fun
          [ <:module_expr< $x$ $y$ >> -> Some (x, "", y)
          | e -> None ]
        in
        left_operator pc 2 unfold next z
  | z ->
      fun curr next pc -> next pc z ]
;

value module_expr_dot =
  extfun Extfun.empty with
  [ <:module_expr< $x$ . $y$ >> ->
      fun curr next pc ->
        curr {(pc) with bef = curr {(pc) with aft = "."} x} y
  | z -> fun curr next pc -> next pc z ]
;

value module_expr_simple =
  extfun Extfun.empty with
  [ <:module_expr< $uid:s$ >> ->
      fun curr next pc -> sprintf "%s%s%s" pc.bef s pc.aft
  | <:module_expr< ($me$ : $mt$) >> ->
      fun curr next pc ->
        horiz_vertic
          (fun () ->
             sprintf "%s(%s : %s)%s" pc.bef
               (module_expr {(pc) with bef = ""; aft = ""} me)
               (module_type {(pc) with bef = ""; aft = ""} mt) pc.aft)
          (fun () ->
             let s1 =
               module_expr
                 {(pc) with ind = pc.ind + 1; bef = sprintf "%s(" pc.bef;
                  aft = " :"}
                 me
             in
             let s2 =
               module_type
                 {(pc) with ind = pc.ind + 1; bef = tab (pc.ind + 1);
                  aft = sprintf ")%s" pc.aft}
                 mt
             in
             sprintf "%s\n%s" s1 s2)
  | <:module_expr< struct $list:_$ end >> as z ->
      fun curr next pc ->
        module_expr
          {(pc) with ind = pc.ind + 1; bef = sprintf "%s(" pc.bef;
           aft = sprintf ")%s" pc.aft}
          z
  | z ->
      fun curr next pc -> not_impl "module_expr" pc z ]
;

value with_constraint pc wc =
  match wc with
  [ <:with_constr< type $sl$ $list:tpl$ = $opt:pf$ $t$ >> ->
      let b =
        let k = hlist type_var {(pc) with bef = ""; aft = " = "} tpl in
        mod_ident {(pc) with bef = sprintf "%swith type " pc.bef; aft = k} sl
      in
      let pf = if pf then "private " else "" in
      ctyp {(pc) with bef = sprintf "%s%s" b pf} t
  | <:with_constr< module $sl$ = $me$ >> ->
      module_expr
        {(pc) with
         bef =
           mod_ident
             {(pc) with bef = sprintf "%swith module " pc.bef; aft = " = "}
             sl}
        me ]
;

value module_type_top =
  extfun Extfun.empty with
  [ <:module_type< functor ($s$ : $mt1$) -> $mt2$ >> ->
      fun curr next pc ->
        str_or_sig_functor pc s mt1 module_type mt2
  | <:module_type< sig $list:sil$ end >> ->
      fun curr next pc ->
        horiz_vertic
          (fun () ->
             if alone_in_line pc then
               (* Heuristic : I don't like to print sigs horizontally
                  when alone in a line. *)
               sprintf "\n"
             else
               sprintf "%ssig%s%s%send%s" pc.bef " "
                 (hlist (semi_after sig_item) {(pc) with bef = ""; aft = ""}
                    sil)
                 " " pc.aft)
          (fun () ->
             sprintf "%ssig%s%s%send%s" pc.bef "\n"
               (vlist (semi_after sig_item)
                  {(pc) with ind = pc.ind + 2; bef = tab (pc.ind + 2);
                   aft = ""}
                  sil)
               ("\n" ^ tab pc.ind) pc.aft)
  | <:module_type< $mt$ with $list:wcl$ >> ->
      fun curr next pc ->
        horiz_vertic
          (fun () ->
             sprintf "%s%s %s%s" pc.bef
               (module_type {(pc) with bef = ""; aft = ""} mt)
               (hlist with_constraint {(pc) with bef = ""; aft = ""} wcl)
                  pc.aft)
          (fun () -> not_impl "module type with vertic" pc wcl)
  | z ->
      fun curr next pc -> next pc z ]
;

value module_type_dot =
  extfun Extfun.empty with
  [ <:module_type< $x$ . $y$ >> ->
      fun curr next pc ->
        curr {(pc) with bef = curr {(pc) with aft = "."} x} y
  | z -> fun curr next pc -> next pc z ]
;

value module_type_simple =
  extfun Extfun.empty with
  [ <:module_type< $uid:s$ >> ->
      fun curr next pc -> sprintf "%s%s%s" pc.bef s pc.aft
  | z -> fun curr next pc -> not_impl "module_type" pc z ]
;

(* initialization or re-initialization of predefined printers *)

pr_expr.pr_levels :=
  [{pr_label = "top"; pr_rules = expr_top};
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
   {pr_label = "simple"; pr_rules = expr_simple}]
;

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

pr_str_item.pr_levels := [{pr_label = "top"; pr_rules = str_item_top}];
pr_sig_item.pr_levels := [{pr_label = "top"; pr_rules = sig_item_top}];

pr_module_expr.pr_levels :=
  [{pr_label = "top"; pr_rules = module_expr_top};
   {pr_label = "apply"; pr_rules = module_expr_apply};
   {pr_label = "dot"; pr_rules = module_expr_dot};
   {pr_label = "simple"; pr_rules = module_expr_simple}]
;

pr_module_type.pr_levels :=
  [{pr_label = "top"; pr_rules = module_type_top};
   {pr_label = "dot"; pr_rules = module_type_dot};
   {pr_label = "simple"; pr_rules = module_type_simple}]
;

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
(*
Masked part of code because the 'comment' below does not work for
stdlib/arg.ml in ocaml sources, resulting a printing of half a comment.
Another solution has to be found.
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
*)
      output_string oc s ]
;

value copy_to_end src oc first bp =
  let ilen = String.length src in
  if bp < ilen then copy_source src oc first bp ilen
  else output_string oc "\n"
;

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
    Prtools.source.val := src;
    close_in ic
  };
  let oc = stdout in
  let (first, last_pos) =
    List.fold_left
      (fun (first, last_pos) (si, loc) -> do {
         let bp = Stdpp.first_pos loc in
         let ep = Stdpp.last_pos loc in
         copy_source Prtools.source.val oc first last_pos bp;
         flush oc;
         set_comm_min_pos bp;
         output_string oc (f {ind = 0; bef = ""; aft = ";"; dang = ""} si);
         (False, ep)
       })
      (True, 0) ast
  in
  copy_to_end Prtools.source.val oc first last_pos;
  flush oc
};

Pcaml.print_interf.val := apply_printer sig_item;
Pcaml.print_implem.val := apply_printer str_item;

value is_uppercase c = Char.uppercase c = c;

value set_flags s =
  loop 0 where rec loop i =
    if i = String.length s then ()
    else do {
      match s.[i] with
      [ 'A' | 'a' -> do {
          let v = is_uppercase s.[i] in
          flag_expand_declare.val := v;
          flag_horiz_let_in.val := v;
          flag_sequ_begin_at_eol.val := v;
        }
      | 'D' | 'd' -> flag_expand_declare.val := is_uppercase s.[i]
      | 'L' | 'l' -> flag_horiz_let_in.val := is_uppercase s.[i]
      | 'S' | 's' -> flag_sequ_begin_at_eol.val := is_uppercase s.[i]
      | c -> failwith ("bad flag " ^ String.make 1 c) ];
      loop (i + 1)
    }
;

value default_flag () =
  let flag_on b t f = if b then t else "" in 
  let flag_off b t f = if b then "" else f in
  let on_off flag =
    sprintf "%s%s%s"
      (flag flag_expand_declare.val "D" "d")
      (flag flag_horiz_let_in.val "L" "l")
      (flag flag_sequ_begin_at_eol.val "S" "s")
  in
  let on = on_off flag_on in
  let off = on_off flag_off in
  if String.length on < String.length off then sprintf "a%s" on
  else sprintf "A%s" off
;

value set_wflags s =
  loop 0 where rec loop i =
    if i = String.length s then ()
    else do {
      match s.[i] with
      [ 'A' | 'a' -> do {
          let v = is_uppercase s.[i] in
          flag_where_after_in.val := v;
          flag_where_after_let_eq.val := v;
          flag_where_after_match.val := v;
          flag_where_after_field_eq.val := v;
          flag_where_in_sequences.val := v;
          flag_where_after_then.val := v;
          flag_where_after_value_eq.val := v;
          flag_where_after_arrow.val := v;
        }
      | 'I' | 'i' -> flag_where_after_in.val := is_uppercase s.[i]
      | 'L' | 'l' -> flag_where_after_let_eq.val := is_uppercase s.[i]
      | 'M' | 'm' -> flag_where_after_match.val := is_uppercase s.[i]
      | 'P' | 'p' -> flag_where_after_lparen.val := is_uppercase s.[i]
      | 'R' | 'r' -> flag_where_after_field_eq.val := is_uppercase s.[i]
      | 'S' | 's' -> flag_where_in_sequences.val := is_uppercase s.[i]
      | 'T' | 't' -> flag_where_after_then.val := is_uppercase s.[i]
      | 'V' | 'v' -> flag_where_after_value_eq.val := is_uppercase s.[i]
      | 'W' | 'w' -> flag_where_after_arrow.val := is_uppercase s.[i]
      | c -> failwith ("bad wflag " ^ String.make 1 c) ];
      loop (i + 1)
    }
;

value default_wflag () =
  let flag_on b t f = if b then t else "" in 
  let flag_off b t f = if b then "" else f in
  let on_off flag =
    sprintf "%s%s%s%s%s%s%s%s%s"
      (flag flag_where_after_in.val "I" "i")
      (flag flag_where_after_let_eq.val "L" "l")
      (flag flag_where_after_match.val "M" "m")
      (flag flag_where_after_lparen.val "P" "p")
      (flag flag_where_after_field_eq.val "R" "r")
      (flag flag_where_in_sequences.val "S" "s")
      (flag flag_where_after_then.val "T" "t")
      (flag flag_where_after_value_eq.val "V" "v")
      (flag flag_where_after_arrow.val "W" "w")
  in
  let on = on_off flag_on in
  let off = on_off flag_off in
  if String.length on < String.length off then sprintf "a%s" on
  else sprintf "A%s" off
;

Pcaml.add_option "-flag" (Arg.String set_flags)
  ("<str> Change pretty printing behaviour according to <flags>:
       A/a enable/disable all flags
       D/d enable/disable allowing expanding 'declare'
       L/l enable/disable allowing printing 'let..in' horizontally
       S/s enable/disable printing sequences beginners at end of lines
       default setting is \"" ^ default_flag () ^ "\".");

Pcaml.add_option "-wflag" (Arg.String set_wflags)
  ("<str> Change displaying 'where' statements instead of 'let':
       A/a enable/disable all flags
       I/i enable/disable 'where' after 'in'
       L/l enable/disable 'where' after 'let..='
       M/m enable/disable 'where' after 'match' and 'try'
       P/p enable/disable 'where' after left parenthesis
       R/r enable/disable 'where' after 'record_field..='
       S/s enable/disable 'where' in sequences
       T/t enable/disable 'where' after 'then' or 'else'
       V/v enable/disable 'where' after 'value..='
       W/w enable/disable 'where' after '->'
       default setting is \"" ^ default_wflag () ^ "\".");

Pcaml.add_option "-l" (Arg.Int (fun x -> Pretty.line_length.val := x))
  ("<length> Maximum line length for pretty printing (default " ^
     string_of_int Pretty.line_length.val ^ ")");

Pcaml.add_option "-sep" (Arg.String (fun x -> sep.val := Some x))
  "<string> Use this string between phrases instead of reading source.";
