(* camlp5r pa_macro.cmo q_MLast.cmo ./pa_pprintf.cmo ./pa_extfun.cmo ./pa_extprint.cmo *)
(* $Id: pr_r.ml,v 1.135 2007/12/09 11:05:35 deraugla Exp $ *)
(* Copyright (c) INRIA 2007 *)

open Pretty;
open Pcaml;
open Prtools;

value flag_comments_in_phrases = ref True;
value flag_expand_declare = ref False;
value flag_horiz_let_in = ref False;
value flag_sequ_begin_at_eol = ref True;
value flag_equilibrate_cases = Pcaml.flag_equilibrate_cases;

value flag_where_after_in = ref True;
value flag_where_after_let_eq = ref True;
value flag_where_after_match = ref True;
value flag_where_after_lparen = ref True;
value flag_where_after_field_eq = ref False;
value flag_where_in_sequences = ref False;
value flag_where_after_then = ref True;
value flag_where_after_value_eq = ref True;
value flag_where_after_arrow = ref True;

do {
  Eprinter.clear pr_expr;
  Eprinter.clear pr_patt;
  Eprinter.clear pr_ctyp;
  Eprinter.clear pr_str_item;
  Eprinter.clear pr_sig_item;
  Eprinter.clear pr_module_expr;
  Eprinter.clear pr_module_type;
  Eprinter.clear pr_class_sig_item;
  Eprinter.clear pr_class_str_item;
  Eprinter.clear pr_class_expr;
  Eprinter.clear pr_class_type;
};

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
  | <:patt< ?$_$: ($_$ = $_$) >> -> True
  | <:patt< ?$_$: ($_$) >> -> True
  | <:patt< ?$_$ >> -> True
  | <:patt< ~$_$ >> -> True
  | <:patt< ~$_$: $_$ >> -> True
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
  | <:patt< ~$_$ >> -> []
  | <:patt< ~$_$: $p$ >> -> get_defined_ident p
  | <:patt< ?$_$ >> -> []
  | <:patt< ?$_$: ($p$) >> -> get_defined_ident p
  | <:patt< ?$_$: ($p$ = $e$) >> -> get_defined_ident p
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

(*
value test = ref False;
Pcaml.add_option "-test" (Arg.Set test) " test";
*)

value sprint_break nspaces offset pc f g =
  horiz_vertic
    (fun () ->
       let sp = String.make nspaces ' ' in
       sprintf "%s%s%s" (f {(pc) with aft = ""}) sp (g {(pc) with bef = ""}))
    (fun () ->
       let s1 = f {(pc) with aft = ""} in
       let s2 =
         g {(pc) with ind = pc.ind + offset; bef = tab (pc.ind + offset)}
       in
       sprintf "%s\n%s" s1 s2)
;

value sprint_break_all nspaces pc f fl =
  horiz_vertic
    (fun () ->
       let sp = String.make nspaces ' ' in
       loop (f (if fl = [] then pc else {(pc) with aft = ""})) fl
       where rec loop s =
         fun
         [ [(_, f) :: fl] ->
             let s =
               sprintf "%s%s%s" s sp
                 (f {(pc) with bef = "";
                     aft = if fl = [] then pc.aft else ""})
             in
             loop s fl
         | [] -> s ])
    (fun () ->
       loop (f (if fl = [] then pc else {(pc) with aft = ""})) fl
       where rec loop s =
         fun
         [ [(o, f) :: fl] ->
             let s =
               sprintf "%s\n%s" s
                 (f {(pc) with ind = pc.ind + o; bef = tab (pc.ind + o);
                     aft = if fl = [] then pc.aft else ""})
             in
             loop s fl
         | [] -> s ])
;

value var_escaped pc v =
  let x =
    if is_infix v || has_special_chars v then "\\" ^ v
    else if is_keyword v then "\\" ^ v
    else v
  in
  pprintf pc "%s" x
;

value cons_escaped pc v =
  let x =
    match v with
    [ " True" -> "True_"
    | " False" -> "False_"
    | _ -> v ]
  in
  pprintf pc "%s" x
;

value rec mod_ident pc sl =
  match sl with
  [ [] -> pprintf pc ""
  | [s] -> var_escaped pc s
  | [s :: sl] -> pprintf pc "%s.%p" s mod_ident sl ]
;

value semi_after elem pc x = pprintf pc "%p;" elem x;
value star_after elem pc x = pprintf pc "%p *" elem x;
value op_after elem pc (x, op) = pprintf pc "%p%s" elem x op;

value and_before elem pc x = pprintf pc "and %p" elem x;
value bar_before elem pc x = pprintf pc "| %p" elem x;

value operator pc left right sh op x y =
  let op = if op = "" then "" else " " ^ op in
  pprintf pc "%p%s@;%p" left x op right y
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
  | _ -> plist next sh pc xl ]
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
  | _ -> plist next sh pc xl ]
;

(*
 * Extensible printers
 *)

value expr = Eprinter.apply pr_expr;
value patt = Eprinter.apply pr_patt;
value ctyp = Eprinter.apply pr_ctyp;
value str_item = Eprinter.apply pr_str_item;
value sig_item = Eprinter.apply pr_sig_item;
value module_expr = Eprinter.apply pr_module_expr;
value module_type = Eprinter.apply pr_module_type;
value expr_fun_args ge = Extfun.apply pr_expr_fun_args.val ge;

value comm_bef pc loc =
  if flag_comments_in_phrases.val then Prtools.comm_bef pc loc else ""
;

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
  [ <:patt< ($x$ as $y$) >> -> pprintf pc "%p as %p" patt x patt y
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
value binding elem pc (p, e) = pprintf pc "%p =@;%p" patt p elem e;

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
value sequence_box pc bef expr el =
  let s1 = bef {(pc) with aft = " do {"} in
  let s2 =
    vlistl (semi_after (comm_expr expr))
      (comm_expr expr)
      {(pc) with ind = pc.ind + 2; bef = tab (pc.ind + 2); aft = ""} el
  in
  let s3 = sprintf "%s}%s" (tab pc.ind) pc.aft in
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
  match sequencify body with
  [ Some el ->
      horiz_vertic
        (fun () ->
           pprintf pc "%p@ where rec %p =@;%p" expr e (hlist patt) pl
             (comm_expr expr) body)
        (fun () ->
           let expr_wh =
             if flag_where_in_sequences.val then expr_wh else expr
           in
           sequence_box pc
             (fun pc ->
                pprintf pc "%p@ where rec %p =" expr e (hlist patt) pl)
             expr_wh el)
  | None ->
      pprintf pc "%p@ where rec %p =@;%p" expr e (hlist patt) pl
        (comm_expr expr) body ]

and expr_wh pc e =
  match can_be_displayed_as_where e with
  [ Some (p, e, body) -> where_binding pc (p, e, body)
  | None -> expr pc e ]
;

value sequence_box2 bef pc el =
  let expr_wh = if flag_where_in_sequences.val then expr_wh else expr in
  sequence_box pc bef expr_wh el
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
  match sequencify e with
  [ Some el ->
      horiz_vertic
        (fun () -> pprintf pc "%p =@;%p" (hlist patt) pl expr_wh e)
        (fun () ->
           sequence_box2 (fun pc -> pprintf pc "%p =" (hlist patt) pl) pc el)
  | None ->
      pprintf pc "%p =@;%p" (hlist patt) pl expr_wh e ]
;

(* Pretty printing improvements (optional):
   - prints "let x = e" instead of "let = fun x -> e"
   - if vertical and "e" is a sequence, put the "do {" at after the "="
   - the expression after '=' is displayed with the 'where' statement if
     possible (expr_wh)
   - if "e" is a type constraint, put the constraint after the params. E.g.
        let f x y = (e : t) ...
     is displayed:
        let f x y : t = e ...
   Cancellation of all these improvements could be done by changing calls
   to this function to a call to "binding expr" above.
*)
value value_or_let_binding flag_where sequ pc (p, e) =
  let expr_wh = if flag_where.val then expr_wh else expr in
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
    [ <:expr< ($e$ : $t$) >> -> (e, Some t)
    | _ -> (e, None) ]
  in
  horiz_vertic
    (fun () ->
       pprintf pc "%s%s = %s%s"
         (hlist patt {(pc) with bef = ""; aft = ""} pl)
         (match tyo with
          [ Some t -> sprintf " : %s" (ctyp {(pc) with bef = ""; aft = ""} t)
          | None -> "" ])
         (expr_wh {(pc) with bef = ""; aft = ""} e)
         (if pc.aft = "in" then " " else ""))
    (fun () ->
       let patt_eq pc =
         let patt_tycon tyo pc p =
           match tyo with
           [ Some t ->
               patt {(pc) with aft = ctyp {(pc) with bef = " : "} t} p
           | None -> patt pc p ]
         in
         let pl = List.map (fun p -> (p, "")) pl in
         pprintf pc "%p =" (plistl patt (patt_tycon tyo) 4) pl
       in
       match sequencify e with
       [ Some el -> sequ pc patt_eq el
       | None ->
           let s1 = patt_eq {(pc) with aft = ""} in
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

value value_binding pc pe =
  let sequ pc bef el = sequence_box2 bef pc el in
  value_or_let_binding flag_where_after_value_eq sequ pc pe
;

value let_binding pc pe =
  let sequ pc bef el =
    let s = sequence_box2 bef {(pc) with aft = ""} el in
    if pc.aft = "" then s else sprintf "%s\n%s%s" s (tab pc.ind) pc.aft
  in
  value_or_let_binding flag_where_after_let_eq sequ pc pe
;

value match_assoc force_vertic pc (p, w, e) =
  let expr_wh = if flag_where_after_arrow.val then expr_wh else expr in
  horiz_vertic
    (fun () ->
       if force_vertic then sprintf "\n"
       else
         pprintf pc "%s%s -> %s"
           (patt_as {(pc) with bef = ""; aft = ""} p)
           (match w with
            [ <:vala< Some e >> ->
                sprintf " when %s" (expr {(pc) with bef = ""; aft = ""} e)
            | _ -> "" ])
           (comm_expr expr {(pc) with bef = ""; aft = ""} e))
    (fun () ->
       let patt_arrow pc =
         match w with
         [ <:vala< Some e >> ->
             pprintf pc "%p@ @[when@;%p ->@]" patt_as p expr e
         | _ ->
             pprintf pc "%p ->" patt_as p ]
       in
       match sequencify e with
       [ Some el ->
           sequence_box2
             (fun pc ->
                horiz_vertic (fun _ -> sprintf "\n")
                  (fun () -> patt_arrow pc))
             pc el
       | None ->
           let s1 = patt_arrow {(pc) with aft = ""} in
           let s2 =
             comm_expr expr_wh
               {(pc) with ind = pc.ind + 2; bef = tab (pc.ind + 2)} e
           in
           sprintf "%s\n%s" s1 s2 ])
;

value match_assoc_sh force_vertic pc pwe =
  pprintf pc "@[<2>%p@]" (match_assoc force_vertic) pwe
;

value match_assoc_list pc pwel =
  if pwel = [] then pprintf pc "[]"
  else
    let force_vertic =
      if flag_equilibrate_cases.val then
        let has_vertic =
          List.exists
            (fun pwe ->
               horiz_vertic
                 (fun () ->
                    let _ : string =
                      bar_before (match_assoc_sh False) pc pwe
                    in
                    False)
                 (fun () -> True))
            pwel
        in
        has_vertic
      else False
    in
    pprintf pc "[ %p ]"
      (vlist2 (match_assoc_sh force_vertic)
         (bar_before (match_assoc_sh force_vertic)))
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
  pprintf pc "%s'%s" (if p then "+" else if m then "-" else "")
    (Pcaml.unvala tv)
;

value type_constraint pc (t1, t2) =
  pprintf pc " constraint %p =@;%p" ctyp t1 ctyp t2
;

value type_decl pc td =
  let ((_, tn), tp, pf, te, cl) =
    (td.MLast.tdNam, td.MLast.tdPrm, td.MLast.tdPrv, td.MLast.tdDef,
     td.MLast.tdCon)
  in
  horiz_vertic
    (fun () ->
       pprintf pc "%s%s = %s%s"
         (var_escaped {(pc) with bef = ""; aft = ""} (Pcaml.unvala tn))
         (if Pcaml.unvala tp = [] then ""
          else
            sprintf " %s" (hlist type_var {(pc) with bef = ""; aft = ""}
              (Pcaml.unvala tp)))
         (ctyp {(pc) with bef = ""; aft = ""} te)
         (hlist type_constraint {(pc) with bef = ""; aft = ""}
            (Pcaml.unvala cl)))
    (fun () ->
       let s1 =
         horiz_vertic
           (fun () ->
              let pc = {(pc) with aft = ""} in
              pprintf pc "%s%s ="
                (var_escaped {(pc) with bef = ""} (Pcaml.unvala tn))
                (if Pcaml.unvala tp = [] then ""
                 else
                   sprintf " %s"
                     (hlist type_var {(pc) with bef = ""} (Pcaml.unvala tp))))
           (fun () -> not_impl "type_decl vertic 1" {(pc) with aft = ""} tn)
       in
       let s2 =
         if Pcaml.unvala cl = [] then
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
  pprintf pc "%s :%s@;%p" l (if m then " mutable" else "") ctyp t
;

value cons_decl pc (_, c, tl) =
  let c = Pcaml.unvala c in
  let tl = Pcaml.unvala tl in
  if tl = [] then cons_escaped pc c
  else
    let tl = List.map (fun t -> (t, " and")) tl in
    pprintf pc "%p of@;<1 4>%p" cons_escaped c (plist ctyp 2) tl
;

value has_cons_with_params vdl =
  List.exists
    (fun (_, _, tl) ->
       match tl with
       [ <:vala< [] >> -> False
       | _ -> True ])
    vdl
;

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

value equality_threshold = 0.51;
value are_close f x1 x2 =
  let (s1, s2) = do {
    (* the two strings; this code tries to prevents computing possible
       too long lines (which might slow down the program) *)
    let v = Pretty.line_length.val in
    Pretty.line_length.val := 2 * v;
    let s1 = horiz_vertic (fun _ -> Some (f x1)) (fun () -> None) in
    let s2 = horiz_vertic (fun _ -> Some (f x2)) (fun () -> None) in
    Pretty.line_length.val := v;
    (s1, s2)
  }
  in
  match (s1, s2) with
  [ (Some s1, Some s2) ->
      (* one string at least could hold in the line; comparing them; if
         they are "close" to each other, return True, meaning that they
         should be displayed *both* in one line or *both* in several lines *)
      let (d1, d2) =
        let a1 = Array.init (String.length s1) (String.get s1) in
        let a2 = Array.init (String.length s2) (String.get s2) in
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

(* Expressions displayed without spaces separating elements; special
   for expressions as strings or arrays indexes (x.[...] or x.(...)).
   Applied only if only containing +, -, *, /, integers and variables. *)
value expr_short pc x =
  let rec expr1 pc z =
    match z with
    [ <:expr< $lid:op$ $x$ $y$ >> ->
        if op = "+" || op = "-" then pprintf pc "%p%s%p" expr1 x op expr2 y
        else expr2 pc z
    | _ -> expr2 pc z ]
  and expr2 pc z =
    match z with
    [ <:expr< $lid:op$ $x$ $y$ >> ->
        if op = "*" || op = "/" then pprintf pc "%p%s%p" expr2 x op expr3 y
        else expr3 pc z
    | _ -> expr3 pc z ]
  and expr3 pc z =
    match z with
    [ <:expr< $lid:v$ >> ->
        if is_infix v || has_special_chars v then raise Exit
        else var_escaped pc v
    | <:expr< $int:s$ >> -> pprintf pc "%s" s
    | <:expr< $lid:op$ $_$ $_$ >> ->
        if List.mem op ["+"; "-"; "*"; "/"] then pprintf pc "(%p)" expr1 z
        else raise Exit
    | _ -> raise Exit ]
  in
  try horiz_vertic (fun () -> expr1 pc x) (fun () -> raise Exit) with
  [ Exit -> expr pc x ]
;

(* definitions of printers *)

value typevar pc tv = pprintf pc "'%s" tv;

value string pc s = pprintf pc "\"%s\"" s;

value external_decl pc (n, t, sl) =
  pprintf pc "external %p :@;%p = %s" var_escaped n ctyp t
    (hlist string {(pc) with bef = ""; aft = ""} sl)
;

value exception_decl pc (e, tl, id) =
  horiz_vertic
    (fun () ->
       pprintf pc "exception %s%s%s" e
         (if tl = [] then ""
          else
            sprintf " of %s"
              (hlist2 ctyp (and_before ctyp)
                 {(pc) with bef = ""; aft = ""} tl))
         (if id = [] then ""
          else sprintf " = %s" (mod_ident {(pc) with bef = ""; aft = ""} id)))
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

value str_module pref pc (m, me) =
  let (mal, me) =
    loop me where rec loop =
      fun
      [ <:module_expr< functor ($uid:s$ : $mt$) -> $me$ >> ->
          let (mal, me) = loop me in
          ([(s, mt) :: mal], me)
      | me -> ([], me) ]
  in
  let module_arg pc (s, mt) = pprintf pc "(%s :@;<1 1>%p)" s module_type mt in
  let (me, mto) =
    match me with
    [ <:module_expr< ($me$ : $mt$) >> -> (me, Some mt)
    | _ -> (me, None) ]
  in
  horiz_vertic
    (fun () ->
       pprintf pc "%s %s%s%s = %s" pref m
         (if mal = [] then ""
          else hlist module_arg {(pc) with bef = " "; aft = ""} mal)
         (match mto with
          [ Some mt ->
              sprintf " : %s" (module_type {(pc) with bef = ""; aft = ""} mt)
          | None -> "" ])
         (module_expr {(pc) with bef = ""; aft = ""} me))
    (fun () ->
       let s1 =
         match mto with
         [ Some mt ->
             let pc = {(pc) with aft = ""} in
             if mal = [] then
               pprintf pc "%s %s :@;%p =" pref m module_type mt
             else
               pprintf pc "%s %s %p :@;%p =" pref m (hlist module_arg) mal
                 module_type mt
         | None ->
             let mal = List.map (fun ma -> (ma, "")) mal in
             plistb module_arg 2
               {(pc) with bef = sprintf "%s%s %s" pc.bef pref m; aft = " ="}
               mal ]
       in
       let s2 =
         module_expr
           {(pc) with ind = pc.ind + 2; bef = tab (pc.ind + 2); aft = ""} me
       in
       let s3 =
         if pc.aft = "" then "" else sprintf "\n%s%s" (tab pc.ind) pc.aft
       in
       sprintf "%s\n%s%s" s1 s2 s3)
;

value sig_module_or_module_type pref defc pc (m, mt) =
  let (mal, mt) =
    loop mt where rec loop =
      fun
      [ <:module_type< functor ($uid:s$ : $mt1$) -> $mt2$ >> ->
          let (mal, mt) = loop mt2 in
          ([(s, mt1) :: mal], mt)
      | mt -> ([], mt) ]
  in
  let module_arg pc (s, mt) = pprintf pc "(%s :@;<1 1>%p)" s module_type mt in
  horiz_vertic
    (fun () ->
       pprintf pc "%s %s%s %c %s" pref m
         (if mal = [] then ""
          else hlist module_arg {(pc) with bef = " "; aft = ""} mal)
         defc (module_type {(pc) with bef = ""; aft = ""} mt))
    (fun () ->
       let s1 =
         let mal = List.map (fun ma -> (ma, "")) mal in
         plistb module_arg 2
           {(pc) with bef = sprintf "%s%s %s" pc.bef pref m;
            aft = sprintf " %c" defc}
           mal
       in
       let s2 =
         module_type
           {(pc) with ind = pc.ind + 2; bef = tab (pc.ind + 2); aft = ""} mt
       in
       let s3 =
         if pc.aft = "" then "" else sprintf "\n%s%s" (tab pc.ind) pc.aft
       in
       sprintf "%s\n%s%s" s1 s2 s3)
;

value str_or_sig_functor pc s mt module_expr_or_type met =
  pprintf pc "functor@;@[(%s :@;<1 1>%p)@]@ ->@;%p" s module_type mt
    module_expr_or_type met
;

value with_constraint pc wc =
  match wc with
  [ <:with_constr< type $sl$ $list:tpl$ = $flag:pf$ $t$ >> ->
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
        me
  | IFDEF STRICT THEN
      x -> not_impl "with_constraint" pc x
    END ]
;

EXTEND_PRINTER
  pr_expr:
    [ "top"
      [ <:expr< if $e1$ then $e2$ else $e3$ >> ->
          let expr_wh = if flag_where_after_then.val then expr_wh else expr in
          horiz_vertic
            (fun () ->
               pprintf pc "if %p then %p else %p" curr e1 curr e2 curr e3)
            (fun () ->
               let if_then force_vertic pc else_b e1 e2 =
                 horiz_vertic
                   (fun () ->
                      if force_vertic then sprintf "\n"
                      else
                        pprintf pc "%sif %p then %p" else_b curr e1 curr e2)
                   (fun () ->
                      let horiz_if_then pc =
                        pprintf pc "%sif %p then" else_b curr e1
                      in
                      let vertic_if_then pc =
                        if else_b = "" then
                          pprintf pc "@[<3>if %p@]@ then" curr e1
                        else
                          pprintf pc "@[<a>%sif@;%p@ then@]" else_b curr e1
                      in
                      match sequencify e2 with
                      [ Some el ->
                          sequence_box2
                            (fun pc ->
                               horiz_vertic (fun () -> horiz_if_then pc)
                                 (fun () -> vertic_if_then pc))
                            {(pc) with aft = ""} el
                      | None ->
                          let pc = {(pc) with aft = ""} in
                          let s1 =
                            horiz_vertic (fun () -> horiz_if_then pc)
                              (fun () -> vertic_if_then pc)
                          in
                          let s2 =
                            comm_expr expr_wh
                              {(pc) with ind = pc.ind + 2;
                               bef = tab (pc.ind + 2); aft = ""}
                              e2
                          in
                          sprintf "%s\n%s" s1 s2 ])
               in
               let (force_vertic, eel, e3) =
                 if flag_equilibrate_cases.val then
                   let (eel, e3) =
                     let then_and_else_are_close =
                       are_close (curr {(pc) with bef = ""; aft = ""}) e2 e3
                     in
                     (* if "then" and "else" cases are close, don't break
                        the "else" part into its possible "else if" in
                        order to display "then" and "else" symmetrically *)
                     if then_and_else_are_close then ([], e3)
                     else get_else_if e3
                   in
                   (* if a case does not fit on line, all cases must be cut *)
                   let has_vertic =
                     horiz_vertic
                       (fun () ->
                          let _ : string =
                            if_then False {(pc) with aft = ""} "" e1 e2
                          in
                          False)
                       (fun () -> True) ||
                     List.exists
                       (fun (e1, e2) ->
                          horiz_vertic
                            (fun () ->
                               let _ : string =
                                 if_then False
                                   {(pc) with bef = tab pc.ind; aft = ""}
                                   "else " e1 e2
                               in
                               False)
                            (fun () -> True))
                       eel ||
                     horiz_vertic
                       (fun () ->
                          let _ : string =
                            sprintf "%selse %s%s" (tab pc.ind)
                              (comm_expr curr {(pc) with bef = ""; aft = ""}
                                 e3)
                              pc.aft
                          in
                          False)
                       (fun () -> True)
                   in
                   (has_vertic, eel, e3)
                 else
                   let (eel, e3) = get_else_if e3 in
                   (False, eel, e3)
               in
               let s1 = if_then force_vertic {(pc) with aft = ""} "" e1 e2 in
               let s2 =
                 loop eel where rec loop =
                   fun
                   [ [(e1, e2) :: eel] ->
                       sprintf "\n%s%s"
                         (if_then force_vertic
                            {(pc) with bef = tab pc.ind; aft = ""}
                            "else " e1 e2)
                         (loop eel)
                   | [] -> "" ]
               in
               let s3 =
                 horiz_vertic
                   (fun () ->
                      if force_vertic then sprintf "\n"
                      else
                        sprintf "%selse %s%s" (tab pc.ind)
                          (comm_expr curr {(pc) with bef = ""; aft = ""} e3)
                             pc.aft)
                   (fun () ->
                      match sequencify e3 with
                      [ Some el ->
                          sequence_box2
                            (fun pc ->
                               horiz_vertic (fun () -> sprintf "\n")
                                 (fun () ->
                                    sprintf "%selse%s" (tab pc.ind) pc.aft))
                            pc el
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
          match pwel with
          [ [(p1, <:vala< None >>, e1)] when is_irrefut_patt p1 ->
              let (pl, e1) = expr_fun_args e1 in
              let pl = [p1 :: pl] in
              horiz_vertic
                (fun () -> pprintf pc "fun %p -> %p" (hlist patt) pl curr e1)
                (fun () ->
                   let pl = List.map (fun p -> (p, "")) pl in
                   match sequencify e1 with
                   [ Some el ->
                       sequence_box2
                         (fun pc -> pprintf pc "fun %p ->" (plist patt 4) pl)
                         pc el
                   | None ->
                       pprintf pc "fun %p ->@;%p" (plist patt 4) pl curr e1 ])
          | [] -> sprintf "%sfun []%s" pc.bef pc.aft
          | pwel ->
              let s = match_assoc_list {(pc) with bef = tab pc.ind} pwel in
              sprintf "%sfun\n%s" pc.bef s ]
      | <:expr< try $e1$ with [ $list:pwel$ ] >> |
        <:expr< match $e1$ with [ $list:pwel$ ] >> as e ->
          let expr_wh =
            if flag_where_after_match.val then expr_wh else curr
          in
          let op =
            match e with
            [ <:expr< try $_$ with [ $list:_$ ] >> -> "try"
            | _ -> "match" ]
          in
          match pwel with
          [ [(p, wo, e)] when is_irrefut_patt p ->
              horiz_vertic
                (fun () ->
                   pprintf pc "%s %p with %p" op expr_wh e1
                     (match_assoc False) (p, wo, e))
                (fun () ->
                   match
                     horiz_vertic
                       (fun () ->
                          let pc = {(pc) with aft = ""} in
                          Some
                            (pprintf pc "%s %p with %p%s ->" op
                               expr_wh e1 patt p
                               (match wo with
                                [ <:vala< Some e >> ->
                                    curr {(pc) with bef = " when"} e
                                | _ -> "" ])))
                        (fun () -> None)
                   with
                   [ Some s1 ->
                       let pc = {(pc) with bef = ""} in
                       pprintf pc "%s@;%p" s1 curr e
                   | None ->
                       match sequencify e1 with
                       [ Some el ->
                           pprintf pc "%p@ with %p"
                             (sequence_box2 (fun pc -> pprintf pc "%s" op)) el
                             (match_assoc False) (p, wo, e)
                       | None ->
                           pprintf pc "@[<a>%s@;%p@ with %p@]" op expr_wh e1
                             (match_assoc False) (p, wo, e) ] ])
          | _ ->
              horiz_vertic
                (fun () ->
                   pprintf pc "%s %p with %p" op expr_wh e1 match_assoc_list
                     pwel)
                (fun () ->
                   match sequencify e1 with
                   [ Some el ->
                       let s1 =
                         let pc = {(pc) with aft = ""} in
                         horiz_vertic
                           (fun () -> pprintf pc "%s %p with" op expr_wh e1)
                           (fun () ->
                              pprintf pc "%p@ with"
                                (sequence_box2
                                   (fun pc ->
                                      horiz_vertic (fun _ -> sprintf "\n")
                                        (fun () -> pprintf pc "%s" op)))
                                el)
                       in
                       let s2 =
                         match_assoc_list {(pc) with bef = tab pc.ind} pwel
                       in
                       sprintf "%s\n%s" s1 s2
                   | None ->
                       pprintf pc "@[<a>%s@;%p@ with@]@ %p" op expr_wh e1
                         match_assoc_list pwel ]) ]
      | <:expr< let $flag:rf$ $list:pel$ in $e$ >> as ge ->
          let expr_wh = if flag_where_after_in.val then expr_wh else curr in
          horiz_vertic
            (fun () ->
               if not flag_horiz_let_in.val then sprintf "\n"
               else
                 pprintf pc "let %s%p in %p" (if rf then "rec " else "")
                   (hlist2 let_binding (and_before let_binding)) pel curr e)
            (fun () ->
               match flatten_sequence ge with
               [ Some el ->
                   let loc = MLast.loc_of_expr ge in
                   curr pc <:expr< do { $list:el$ } >>
               | None ->
                   pprintf pc "let %s%pin@ %p" (if rf then "rec " else "")
                     (vlist2 let_binding (and_before let_binding)) pel
                     (comm_expr expr_wh) e ])
      | <:expr< let module $uid:s$ = $me$ in $e$ >> ->
          pprintf pc "@[<a>let module %s =@;%p@ in@]@ %p" s module_expr me
            curr e
      | <:expr< do { $list:el$ } >> as ge ->
          let el =
            match flatten_sequence ge with
            [ Some el -> el
            | None -> el ]
          in
          horiz_vertic
            (fun () ->
               pprintf pc "do { %p }"
                 (hlistl (semi_after (comm_expr curr)) (comm_expr curr)) el)
            (fun () ->
               pprintf pc "@[<a>do {@;%p@ }@]"
                 (vlistl (semi_after (comm_expr curr)) (comm_expr curr)) el)
      | <:expr< while $e1$ do { $list:el$ } >> ->
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
               pprintf pc "while %p do { %p }" curr e1
                 (hlistl (semi_after expr) curr) el)
            (fun () ->
               pprintf pc "@[<a>while@;%p@ do {@]@;%p@ }" curr e1
                 (vlistl (semi_after expr) curr) el)
      | <:expr< for $lid:v$ = $e1$ $to:d$ $e2$ do { $list:el$ } >> ->
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
               pprintf pc "for %s = %p %s %p do { %p }" v curr e1
                 (if d then "to" else "downto") curr e2
                 (hlistl (semi_after curr) curr) el)
            (fun () ->
               pprintf pc "@[<a>@[<a>for %s = %p %s@;<1 4>%p@ do {@]@;%p@ }@]"
                 v curr e1 (if d then "to" else "downto") curr e2
                 (vlist (semi_after curr)) el) ]
    | "assign"
      [ <:expr< $x$ := $y$ >> -> operator pc next expr 2 ":=" x y ]
    | "or"
      [ z ->
          let unfold =
            fun
            [ <:expr< $lid:op$ $x$ $y$ >> ->
                if List.mem op ["||"; "or"] then Some (x, " ||", y) else None
            | _ -> None ]
          in
          right_operator pc 0 unfold next z ]
    | "and"
      [ z ->
          let unfold =
            fun
            [ <:expr< $lid:op$ $x$ $y$ >> ->
                if List.mem op ["&&"; "&"] then Some (x, " &&", y) else None
            | _ -> None ]
          in
          right_operator pc 0 unfold next z ]
    | "less"
      [ <:expr< $lid:op$ $x$ $y$ >> as z ->
          match op with
          [ "!=" | "<" | "<=" | "<>" | "=" | "==" | ">" | ">=" ->
              operator pc next next 0 op x y
          | _ -> next pc z ] ]
    | "concat"
      [ z ->
          let unfold =
            fun
            [ <:expr< $lid:op$ $x$ $y$ >> ->
                if List.mem op ["^"; "@"] then Some (x, " " ^ op, y) else None
            | _ -> None ]
          in
          right_operator pc 0 unfold next z ]
    | "add"
      [ z ->
          let ops = ["+"; "+."; "-"; "-."] in
          let unfold =
            fun
            [ <:expr< $lid:op$ $x$ $y$ >> ->
                if List.mem op ops then Some (x, " " ^ op, y) else None
            | _ -> None ]
          in
          left_operator pc 0 unfold next z ]
    | "mul"
      [ z ->
          let ops = ["*"; "*."; "/"; "/."; "land"; "lor"; "lxor"; "mod"] in
          let unfold =
            fun
            [ <:expr< $lid:op$ $x$ $y$ >> ->
                if List.mem op ops then Some (x, " " ^ op, y) else None
            | _ -> None ]
          in
          left_operator pc 0 unfold next z ]
    | "pow"
      [ z ->
          let ops = ["**"; "asr"; "lsl"; "lsr"] in
          let unfold =
            fun
            [ <:expr< $lid:op$ $x$ $y$ >> ->
                if List.mem op ops then Some (x, " " ^ op, y) else None
            | _ -> None ]
          in
          right_operator pc 0 unfold next z ]
    | "unary"
      [ <:expr< ~- $x$ >> -> pprintf pc "-%p" curr x
      | <:expr< ~-. $x$ >> -> pprintf pc "-.%p" curr x
      | <:expr< $int:i$ >> -> pprintf pc "%s" i ]
    | "apply"
      [ <:expr< assert $e$ >> ->
          pprintf pc "assert@;%p" next e
      | <:expr< lazy $e$ >> ->
          pprintf pc "lazy@;%p" next e
      | <:expr< $_$ $_$ >> as z ->
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
            left_operator pc 2 unfold next z ]
    | "dot"
      [ <:expr< $x$ . $y$ >> ->
          pprintf pc "%p.@;<0 0>%p" curr x curr y
      | <:expr< $x$ .( $y$ ) >> ->
          pprintf pc "%p.(%p)" curr x expr_short y
      | <:expr< $x$ .[ $y$ ] >> ->
          pprintf pc "%p.[%p]" curr x expr_short y
      | <:expr< $e$ .{ $list:el$ } >> ->
          let el = List.map (fun e -> (e, ",")) el in
          pprintf pc "%p.{%p}" curr e (plist expr_short 0) el ]
    | "simple"
      [ <:expr< ($list:el$) >> ->
          let el = List.map (fun e -> (e, ",")) el in
          pprintf pc "@[<1>(%p)@]" (plist expr 0) el
      | <:expr< {$list:lel$} >> ->
          let lxl = List.map (fun lx -> (lx, ";")) lel in
          pprintf pc "@[<1>{%p}@]" (plist (comm_patt_any record_binding) 0)
            lxl
      | <:expr< {($e$) with $list:lel$} >> ->
          let lxl = List.map (fun lx -> (lx, ";")) lel in
          pprintf pc "@[<1>{(%p) with@ %p}@]" expr e (plist record_binding 0)
            lxl
      | <:expr< [| $list:el$ |] >> ->
          if el = [] then pprintf pc "[| |]"
          else
            let el = List.map (fun e -> (e, ";")) el in
            pprintf pc "@[<3>[| %p |]@]" (plist expr 0) el
      | <:expr< [$_$ :: $_$] >> as z ->
          let (xl, y) = make_expr_list z in
          let xl = List.map (fun x -> (x, ";")) xl in
          match y with
          [ Some y ->
              let expr2 pc x = pprintf pc "%p ::@ %p" expr x expr y in
              pprintf pc "@[<1>[%p]@]" (plistl expr expr2 0) xl
          | None ->
              pprintf pc "@[<1>[%p]@]" (plist expr 0) xl ]
      | <:expr< ($e$ : $t$) >> ->
          pprintf pc "@[<1>(%p :@ %p)@]" expr e ctyp t
      | <:expr< $int:s$ >> | <:expr< $flo:s$ >> ->
          if String.length s > 0 && s.[0] = '-' then pprintf pc "(%s)" s
          else pprintf pc "%s" s
      | <:expr< $int32:s$ >> ->
          if String.length s > 0 && s.[0] = '-' then pprintf pc "(%sl)" s
          else pprintf pc "%sl" s
      | <:expr< $int64:s$ >> ->
          if String.length s > 0 && s.[0] = '-' then pprintf pc "(%sL)" s
          else pprintf pc "%sL" s
      | <:expr< $nativeint:s$ >> ->
          if String.length s > 0 && s.[0] = '-' then pprintf pc "(%sn)" s
          else pprintf pc "%sn" s
      | <:expr< $lid:s$ >> ->
          var_escaped pc s
      | <:expr< $uid:s$ >> ->
          cons_escaped pc s
      | <:expr< `$s$ >> ->
          failwith "variants not pretty printed (in expr); add pr_ro.cmo"
      | <:expr< $str:s$ >> ->
          pprintf pc "\"%s\"" s
      | <:expr< $chr:s$ >> ->
          pprintf pc "'%s'" s
      | <:expr< ?$_$ >> | <:expr< ?$_$: $_$ >> |
        <:expr< ~$_$ >> | <:expr< ~$_$: $_$ >> ->
          failwith "labels not pretty printed (in expr); add pr_ro.cmo"
      | <:expr< $_$ $_$ >> | <:expr< assert $_$ >> | <:expr< lazy $_$ >> |
        <:expr< $_$ := $_$ >> |
        <:expr< fun [ $list:_$ ] >> | <:expr< if $_$ then $_$ else $_$ >> |
        <:expr< do { $list:_$ } >> |
        <:expr< for $lid:_$ = $_$ $to:_$ $_$ do { $list:_$ } >> |
        <:expr< while $_$ do { $list:_$ } >> |
        <:expr< let $flag:_$ $list:_$ in $_$ >> |
        <:expr< match $_$ with [ $list:_$ ] >> |
        <:expr< try $_$ with [ $list:_$ ] >> as z ->
          let expr_wh =
            if flag_where_after_lparen.val then expr_wh else expr
          in
          pprintf pc "@[<1>(%p)@]" expr_wh z ] ]
  ;
  pr_patt:
    [ "top"
      [ <:patt< $_$ | $_$ >> as z ->
          let unfold =
            fun
            [ <:patt< $x$ | $y$ >> -> Some (x, " |", y)
            | _ -> None ]
          in
          left_operator pc 0 unfold next z ]
    | "range"
      [ <:patt< $x$ .. $y$ >> ->
          pprintf pc "%p..%p" next x next y ]
    | "apply"
      [ <:patt< $_$ $_$ >> as z ->
          let unfold =
            fun
            [ <:patt< [ $_$ :: $_$ ] >> -> None
            | <:patt< $x$ $y$ >> -> Some (x, "", y)
            | p -> None ]
          in
          left_operator pc 2 unfold next z ]
    | "dot"
      [ <:patt< $x$ . $y$ >> ->
          pprintf pc "%p.%p" curr x curr y ]
    | "simple"
      [ <:patt< ($x$ as $y$) >> ->
          pprintf pc "@[<1>(%p@ as %p)@]" patt x patt y
      | <:patt< ($list:pl$) >> ->
          let pl = List.map (fun p -> (p, ",")) pl in
          pprintf pc "@[<1>(%p)@]" (plist patt 0) pl
      | <:patt< {$list:lpl$} >> ->
          let lxl = List.map (fun lx -> (lx, ";")) lpl in
          pprintf pc "@[<1>{%p}@]" (plist (binding patt) 0) lxl
      | <:patt< [| $list:pl$ |] >> ->
          if pl = [] then pprintf pc "[| |]"
          else
            let pl = List.map (fun p -> (p, ";")) pl in
            pprintf pc "@[<3>[| %p |]@]" (plist patt 0) pl
      | <:patt< [$_$ :: $_$] >> as z ->
          let (xl, y) = make_patt_list z in
          let xl = List.map (fun x -> (x, ";")) xl in
          match y with
          [ Some  y ->
              let patt2 pc x = pprintf pc "%p ::@ %p" patt x patt y in
              pprintf pc "@[<1>[%p]@]" (plistl patt patt2 0) xl
          | None ->
              pprintf pc "@[<1>[%p]@]" (plist patt 0) xl ]
      | <:patt< ($p$ : $t$) >> ->
          pprintf pc "@[<1>(%p :@ %p)@]" patt p ctyp t
      | <:patt< $int:s$ >> | <:patt< $flo:s$ >> ->
          if String.length s > 0 && s.[0] = '-' then pprintf pc "(%s)" s
          else pprintf pc "%s" s
      | <:patt< $int32:s$ >> ->
          if String.length s > 0 && s.[0] = '-' then pprintf pc "(%sl)" s
          else pprintf pc "%sl" s
      | <:patt< $int64:s$ >> ->
          if String.length s > 0 && s.[0] = '-' then pprintf pc "(%sL)" s
          else pprintf pc "%sL" s
      | <:patt< $nativeint:s$ >> ->
          if String.length s > 0 && s.[0] = '-' then pprintf pc "(%sn)" s
          else pprintf pc "%sn" s
      | <:patt< $lid:s$ >> ->
          var_escaped pc s
      | <:patt< $uid:s$ >> ->
          cons_escaped pc s
      | <:patt< $chr:s$ >> ->
          pprintf pc "'%s'" s
      | <:patt< $str:s$ >> ->
          pprintf pc "\"%s\"" s
      | <:patt< _ >> ->
          pprintf pc "_"
      | <:patt< ?$_$ >> | <:patt< ? ($_$ $opt:_$) >> |
        <:patt< ?$_$: ($_$ $opt:_$) >> | <:patt< ~$_$ >> |
        <:patt< ~$_$: $_$ >> ->
          failwith "labels not pretty printed (in patt); add pr_ro.cmo"
      | <:patt< `$s$ >> ->
          failwith "variants not pretty printed (in patt); add pr_ro.cmo"
      | <:patt< $_$ $_$ >> | <:patt< $_$ | $_$ >> | <:patt< $_$ .. $_$ >>
        as z ->
          pprintf pc "@[<1>(%p)@]" patt z ] ]
  ;
  pr_ctyp:
    [ "top"
      [ <:ctyp< $x$ == $y$ >> ->
          operator pc next next 2 "==" x y ]
    | "as"
      [ <:ctyp< $t1$ as $t2$ >> ->
          pprintf pc "%p@ as %p" curr t1 next t2 ]
    | "poly"
      [ <:ctyp< ! $list:pl$ . $t$ >> ->
          pprintf pc "! %p .@;%p" (hlist typevar) pl ctyp t ]
    | "arrow"
      [ <:ctyp< $_$ -> $_$ >> as z ->
          let unfold =
            fun
            [ <:ctyp< $x$ -> $y$ >> -> Some (x, " ->", y)
            | _ -> None ]
          in
          right_operator pc 2 unfold next z ]
    | "apply"
      [ <:ctyp< $_$ $_$ >> as z ->
          let unfold =
            fun
            [ <:ctyp< $x$ $y$ >> -> Some (x, "", y)
            | _ -> None ]
          in
          left_operator pc 2 unfold next z ]
    | "dot"
      [ <:ctyp< $x$ . $y$ >> ->
          pprintf pc "%p.%p" curr x curr y ]
    | "simple"
      [ <:ctyp< { $list:ltl$ } >> ->
          horiz_vertic
            (fun () ->
               pprintf pc "{ %p }"
                 (hlistl (semi_after label_decl) label_decl) ltl)
            (fun () ->
               pprintf pc "@[<2>{ %p }@]"
                 (vlistl (semi_after label_decl) label_decl) ltl)
      | <:ctyp< [ $list:vdl$ ] >> ->
          horiz_vertic
            (fun () ->
               if has_cons_with_params vdl then sprintf "\n"
               else
                 pprintf pc "[ %p ]" (hlist2 cons_decl (bar_before cons_decl))
                   vdl)
            (fun () ->
               pprintf pc "[ %p ]" (vlist2 cons_decl (bar_before cons_decl))
                 vdl)
      | <:ctyp< ($list:tl$) >> ->
          let tl = List.map (fun t -> (t, " *")) tl in
          pprintf pc "@[<1>(%p)@]" (plist ctyp 0) tl
      | <:ctyp< $lid:t$ >> ->
          var_escaped pc t
      | <:ctyp< $uid:t$ >> ->
          pprintf pc "%s" t
      | <:ctyp< ' $s$ >> ->
          pprintf pc "'%p" var_escaped s
      | <:ctyp< _ >> ->
          pprintf pc "_"
      | <:ctyp< ?$i$: $t$ >> | <:ctyp< ~$_$: $t$ >> ->
          failwith "labels not pretty printed (in type); add pr_ro.cmo"
      | <:ctyp< [ = $list:_$ ] >> | <:ctyp< [ > $list:_$ ] >> |
        <:ctyp< [ < $list:_$ ] >> | <:ctyp< [ < $list:_$ > $list:_$ ] >> ->
          failwith "variants not pretty printed (in type); add pr_ro.cmo"
      | <:ctyp< $_$ $_$ >> | <:ctyp< $_$ -> $_$ >> as z ->
          pprintf pc "@[<1>(%p)@]" ctyp z ] ]
  ;
  pr_str_item:
    [ "top"
      [ <:str_item< # $lid:s$ $e$ >> ->
          pprintf pc "#%s %p" s expr e
      | <:str_item< declare $list:sil$ end >> ->
          if flag_expand_declare.val then
            if sil = [] then pc.bef
            else vlistl (semi_after str_item) str_item pc sil
          else if sil = [] then pprintf pc "declare end"
          else
            horiz_vertic
              (fun () ->
                 pprintf pc "declare %p end"
                   (hlist (semi_after str_item)) sil)
              (fun () ->
                 pprintf pc "@[<a>declare@;%p@ end"
                   (vlist (semi_after str_item)) sil)
      | <:str_item< exception $uid:e$ of $list:tl$ = $id$ >> ->
          exception_decl pc (e, tl, id)
      | <:str_item< external $lid:n$ : $t$ = $list:sl$ >> ->
          external_decl pc (n, t, sl)
      | <:str_item< include $me$ >> ->
          pprintf pc "include %p" module_expr me
      | <:str_item< module $flag:rf$ $list:mdl$ >> ->
          let mdl = List.map (fun (m, mt) -> (Pcaml.unvala m, mt)) mdl in
          let rf = if rf then " rec" else "" in
          vlist2 (str_module ("module" ^ rf)) (str_module "and") pc
            mdl
      | <:str_item< module type $uid:m$ = $mt$ >> ->
          sig_module_or_module_type "module type" '=' pc (m, mt)
      | <:str_item< open $i$ >> ->
          pprintf pc "open %p" mod_ident i
      | <:str_item< type $list:tdl$ >> ->
          pprintf pc "type %p" (vlist2 type_decl (and_before type_decl)) tdl
      | <:str_item< value $flag:rf$ $list:pel$ >> ->
          horiz_vertic
            (fun () ->
               sprintf "%svalue %s%s" pc.bef (if rf then "rec " else "")
                 (hlist2 value_binding (and_before value_binding)
                    {(pc) with bef = ""} pel))
            (fun () ->
               vlist2 value_binding (and_before value_binding)
                 {(pc) with
                  bef =
                    sprintf "%svalue %s" pc.bef (if rf then "rec " else "")}
                 pel)
      | <:str_item< $exp:e$ >> ->
          expr pc e
      | <:str_item< class type $list:_$ >> | <:str_item< class $list:_$ >> ->
          failwith "classes and objects not pretty printed; add pr_ro.cmo" ] ]
  ;
  pr_sig_item:
    [ "top"
      [ <:sig_item< declare $list:sil$ end >> ->
          if flag_expand_declare.val then
            if sil = [] then pc.bef
            else vlistl (semi_after sig_item) sig_item pc sil
          else if sil = [] then sprintf "%sdeclare end%s" pc.bef pc.aft
          else
            horiz_vertic
              (fun () ->
                 sprintf "%sdeclare%s%s%send%s" pc.bef " "
                   (hlist (semi_after sig_item) {(pc) with bef = ""; aft = ""}
                      sil)
                   " " pc.aft)
              (fun () ->
                 sprintf "%sdeclare%s%s%send%s" pc.bef "\n"
                   (vlist (semi_after sig_item)
                      {(pc) with ind = pc.ind + 2; bef = tab (pc.ind + 2);
                       aft = ""}
                      sil)
                   ("\n" ^ tab pc.ind) pc.aft)
      | <:sig_item< exception $uid:e$ of $list:tl$ >> ->
          exception_decl pc (e, tl, [])
      | <:sig_item< external $lid:n$ : $t$ = $list:sl$ >> ->
          external_decl pc (n, t, sl)
      | <:sig_item< include $mt$ >> ->
          module_type {(pc) with bef = sprintf "%sinclude " pc.bef} mt
      | <:sig_item< module $flag:rf$ $list:mdl$ >> ->
          let mdl = List.map (fun (m, mt) -> (Pcaml.unvala m, mt)) mdl in
          let rf = if rf then " rec" else "" in
          vlist2 (sig_module_or_module_type ("module" ^ rf) ':')
            (sig_module_or_module_type "and" ':') pc mdl
      | <:sig_item< module type $uid:m$ = $mt$ >> ->
          sig_module_or_module_type " type" '=' pc (m, mt)
      | <:sig_item< open $i$ >> ->
          mod_ident {(pc) with bef = sprintf "%sopen " pc.bef} i
      | <:sig_item< type $list:tdl$ >> ->
          vlist2 type_decl (and_before type_decl)
            {(pc) with bef = sprintf "%stype " pc.bef} tdl
      | <:sig_item< value $lid:s$ : $t$ >> ->
          pprintf pc "value %p :@;%p" var_escaped s ctyp t
      | <:sig_item< class type $list:_$ >> | <:sig_item< class $list:_$ >> ->
          failwith "classes and objects not pretty printed; add pr_ro.cmo" ] ]
  ;
  pr_module_expr:
    [ "top"
      [ <:module_expr< functor ($uid:s$ : $mt$) -> $me$ >> ->
          str_or_sig_functor pc s mt module_expr me
      | <:module_expr< struct $list:sil$ end >> ->
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
                 ("\n" ^ tab pc.ind) pc.aft) ]
    | "apply"
      [ <:module_expr< $x$ $y$ >> as z ->
          let unfold =
            fun
            [ <:module_expr< $x$ $y$ >> -> Some (x, "", y)
            | e -> None ]
          in
          left_operator pc 2 unfold next z ]
    | "dot"
      [ <:module_expr< $x$ . $y$ >> ->
          curr {(pc) with bef = curr {(pc) with aft = "."} x} y ]
    | "simple"
      [ <:module_expr< $uid:s$ >> ->
          sprintf "%s%s%s" pc.bef s pc.aft
      | <:module_expr< ($me$ : $mt$) >> ->
          pprintf pc "@[<1>(%p :@ %p)@]" module_expr me module_type mt
      | <:module_expr< struct $list:_$ end >> as z ->
          module_expr
            {(pc) with ind = pc.ind + 1; bef = sprintf "%s(" pc.bef;
             aft = sprintf ")%s" pc.aft}
            z ] ]
  ;
  pr_module_type:
    [ "top"
      [ <:module_type< functor ($uid:s$ : $mt1$) -> $mt2$ >> ->
          str_or_sig_functor pc s mt1 module_type mt2
      | <:module_type< sig $list:sil$ end >> ->
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
          pprintf pc "%p@;%p" module_type mt (vlist with_constraint) wcl ]
    | "dot"
      [ <:module_type< $x$ . $y$ >> ->
          curr {(pc) with bef = curr {(pc) with aft = "."} x} y ]
    | "simple"
      [ <:module_type< $uid:s$ >> ->
          sprintf "%s%s%s" pc.bef s pc.aft
      | <:module_type< ' $s$ >> ->
          sprintf "%s'%s%s" pc.bef s pc.aft ] ]
  ;
END;

(* main part *)

value sep = Pcaml.inter_phrases;

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
  let oc =
    match Pcaml.output_file.val with
    [ Some f -> open_out_bin f
    | None -> do { set_binary_mode_out stdout True; stdout } ]
  in
  let cleanup () =
    match Pcaml.output_file.val with
    [ Some f -> close_out oc
    | None -> () ]
  in
  try do {
    let (first, last_pos) =
      List.fold_left
        (fun (first, last_pos) (si, loc) -> do {
           let bp = Ploc.first_pos loc in
           let ep = Ploc.last_pos loc in
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
  }
  with exn -> do {
    cleanup ();
    raise exn
  };
  cleanup ();
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
          flag_comments_in_phrases.val := v;
          flag_expand_declare.val := v;
          flag_equilibrate_cases.val := v;
          flag_horiz_let_in.val := v;
          flag_sequ_begin_at_eol.val := v;
        }
      | 'C' | 'c' -> flag_comments_in_phrases.val := is_uppercase s.[i]
      | 'D' | 'd' -> flag_expand_declare.val := is_uppercase s.[i]
      | 'E' | 'e' -> flag_equilibrate_cases.val := is_uppercase s.[i]
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
    sprintf "%s%s%s%s%s"
      (flag flag_comments_in_phrases.val "C" "c")
      (flag flag_expand_declare.val "D" "d")
      (flag flag_equilibrate_cases.val "E" "e")
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
  ("<str> Change pretty printing behaviour according to <str>:
       A/a enable/disable all flags
       C/c enable/disable comments in phrases
       D/d enable/disable allowing expanding 'declare'
       E/e enable/disable equilibrate cases
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

Pcaml.add_option "-sep_src" (Arg.Unit (fun () -> sep.val := None))
  "Read source file for text between phrases (default).";

Pcaml.add_option "-sep" (Arg.String (fun x -> sep.val := Some x))
  "<string> Use this string between phrases instead of reading source.";

Pcaml.add_option "-no_where" (Arg.Unit (fun () -> set_wflags "a"))
  "(obsolete since version 4.02; use rather \"-wflag a\")";

Pcaml.add_option "-cip" (Arg.Unit (fun x -> x))
  "(obsolete since version 4.02; use rather \"-flag C\")";

Pcaml.add_option "-ncip" (Arg.Unit (fun x -> x))
  "(obsolete since version 4.02; use rather \"-flag c\")";

Pcaml.add_option "-exp_dcl" (Arg.Unit (fun () -> set_flags "D"))
  "(obsolete since version 4.02; use rather \"-flag D\")";
