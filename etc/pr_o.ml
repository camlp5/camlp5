(* camlp4r q_MLast.cmo ./pa_extfun.cmo *)
(* $Id: pr_o.ml,v 1.46 2007/07/05 19:18:52 deraugla Exp $ *)
(* Copyright (c) INRIA 2007 *)

open Pretty;
open Pcaml.Printers;
open Prtools;

value flag_horiz_let_in = ref True;
value flag_semi_semi = ref False;

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

value ocaml_char =
  fun
  [ "'" -> "\\'"
  | "\"" -> "\\\""
  | "\\" -> "\\\\"
  | c -> c ]
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
  sprintf "%s\"pr_o, not impl: %s; %s\"%s" pc.bef name (String.escaped desc)
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
    [ "True" -> "true"
    | "False" -> "false"
    | " True" -> "True"
    | " False" -> "False"
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

value comma_after elem pc x = elem {(pc) with aft = sprintf ",%s" pc.aft} x;
value semi_after elem pc x =
  elem {(pc) with aft = sprintf ";%s" pc.aft; dang = ";"} x
;
value semi_semi_after elem pc x =
  elem {(pc) with aft = sprintf ";;%s" pc.aft} x
;
value star_after elem pc x = elem {(pc) with aft = sprintf " *%s" pc.aft} x;
value op_after elem pc (x, op) =
  elem {(pc) with aft = sprintf "%s%s" op pc.aft} x
;

value and_before elem pc x = elem {(pc) with bef = sprintf "%sand " pc.bef} x;
value bar_before elem pc x = elem {(pc) with bef = sprintf "%s| " pc.bef} x;
value star_before elem pc x = elem {(pc) with bef = sprintf "%s* " pc.bef} x;

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

value expr1 pc z = pr_expr.pr_fun "expr1" pc z;

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

(* utilities specific to pr_o *)

(* Basic displaying of a 'binding' (let, value, expr or patt record field).
   The pretty printing is done correctly, but there are no syntax shortcuts
   (e.g. "let f = fun x -> y" is *not* shortened as "let f x = y")

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

value record_binding is_last pc (p, e) =
  let pc_dang = if is_last then "" else ";" in
  horiz_vertic
    (fun () ->
       sprintf "%s%s = %s%s" pc.bef (patt {(pc) with bef = ""; aft = ""} p)
         (expr {(pc) with bef = ""; aft = ""; dang = pc_dang} e) pc.aft)
    (fun () ->
       sprintf "%s\n%s" (patt {(pc) with aft = " ="} p)
         (expr
            {(pc) with ind = pc.ind + 2; bef = (tab (pc.ind + 2));
             dang = pc_dang}
            e))
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

value expr_semi pc e =
  let (pc_aft, pc_dang) =
    match pc.aft with
    [ None -> (";", ";")
    | Some aft -> (aft, pc.dang) ]
  in
  comm_expr expr {(pc) with aft = pc_aft; dang = pc_dang} e
;

value expr_with_comm_except_if_sequence pc e =
  match e with
  [ <:expr< do { $list:_$ } >> -> expr pc e
  | _ -> comm_expr expr pc e ]
;

(* Pretty printing improvements (optional):
   - prints "let x = e" instead of "let = fun x -> e"
   - if "e" is a type constraint, put the constraint after the params. E.g.
        value f x y = (e : t)
     is displayed:
        value f x y : t = e
   Cancellation of all these improvements could be done by changing calls
   to this function to a call to "binding expr" above.
*)
value let_binding pc (p, e) =
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
    match (p, e) with
    [ (<:patt< $lid:_$ >>, <:expr< ($e$ : $t$) >>)  -> (e, Some t)
    | _ -> (e, None) ]
  in
  let simple_patt = pr_patt.pr_fun "simple" in
  horiz_vertic
    (fun () ->
       sprintf "%s%s%s = %s%s" pc.bef
         (hlist simple_patt {(pc) with bef = ""; aft = ""} pl)
         (match tyo with
          [ Some t -> sprintf " : %s" (ctyp {(pc) with bef = ""; aft = ""} t)
          | None -> "" ])
         (expr {(pc) with bef = ""; aft = ""} e)
         (if pc.aft = "in" then " in" else pc.aft))
    (fun () ->
       let patt_eq k =
         horiz_vertic
           (fun () ->
              sprintf "%s%s%s =%s" pc.bef
                (hlist simple_patt {(pc) with bef = ""; aft = ""} pl)
                (match tyo with
                 [ Some t ->
                     sprintf " : %s" (ctyp {(pc) with bef = ""; aft = ""} t)
                 | None -> "" ])
                k)
           (fun () ->
              let patt_tycon tyo pc p =
                match tyo with
                [ Some t ->
                    simple_patt
                      {(pc) with aft = ctyp {(pc) with bef = " : "} t} p
                | None -> simple_patt pc p ]
              in
              let pl = List.map (fun p -> (p, "")) pl in
              plistl simple_patt (patt_tycon tyo) 4
                {(pc) with aft = sprintf " =%s" k} pl)
       in
       let s1 = patt_eq "" in
       let s2 =
         expr_with_comm_except_if_sequence
           {ind = pc.ind + 2; bef = tab (pc.ind + 2); aft = ""; dang = ""} e
       in
       let s3 =
         if pc.aft = "" then "" else sprintf "\n%s%s" (tab pc.ind) pc.aft
       in
       sprintf "%s\n%s%s" s1 s2 s3)
;

value match_assoc pc (p, w, e) =
  let (pc_aft, pc_dang) =
    match pc.aft with
    [ None -> ("", "|")
    | Some aft -> (aft, pc.dang) ]
  in
  horiz_vertic
    (fun () ->
       sprintf "%s%s%s -> %s%s" pc.bef
         (patt_as {(pc) with bef = ""; aft = ""} p)
         (match w with
          [ Some e ->
              sprintf " when %s" (expr {(pc) with bef = ""; aft = ""} e)
          | None -> "" ])
         (comm_expr expr {(pc) with bef = ""; aft = ""; dang = pc_dang} e)
            pc_aft)
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
                              bef = (tab (pc.ind + 2));
                              aft = sprintf " ->%s" k}
                             e
                         in
                         sprintf "%s\n%s" s1 s2)
                  in
                  sprintf "%s\n%s" s1 s2)
         | None -> patt_as {(pc) with aft = sprintf " ->%s" k} p ]
       in
       let s1 = patt_arrow "" in
       let s2 =
         expr_with_comm_except_if_sequence
           {ind = pc.ind + 2; bef = tab (pc.ind + 2);
            aft = pc_aft; dang = pc_dang}
           e
       in
       sprintf "%s\n%s" s1 s2)
;

value match_assoc_sh pc pwe = match_assoc {(pc) with ind = pc.ind + 2} pwe;

value match_assoc_list pc pwel =
  if pwel = [] then sprintf "%s[]%s" pc.bef pc.aft
  else
    vlist2 match_assoc_sh (bar_before match_assoc_sh)
      {(pc) with bef = sprintf "%s  " pc.bef;
       aft = (None, Some pc.aft)}
      pwel
;

value raise_match_failure pc loc =
  let (fname, line, char, _) =
    if Pcaml.input_file.val <> "-" then
      Stdpp.line_of_loc Pcaml.input_file.val loc
    else
      ("-", 1, Stdpp.first_pos loc, 0)
  in
  let e =
    <:expr<
      raise
        (Match_failure
           ($str:fname$, $int:string_of_int line$, $int:string_of_int char$))
    >>
  in
  pr_expr.pr_fun "apply" pc e
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

value type_params pc tvl =
  match tvl with
  [ [] -> sprintf "%s%s" pc.bef pc.aft
  | [tv] -> type_var {(pc) with aft = sprintf " %s" pc.aft} tv
  | _ ->
      hlistl (comma_after type_var) type_var
        {(pc) with bef = sprintf "%s(" pc.bef; aft = sprintf ") %s" pc.aft}
        tvl ]
;

value type_decl pc td =
  let ((_, tn), tp, pf, te, cl) =
    (td.MLast.tdNam, td.MLast.tdPrm, td.MLast.tdPrv, td.MLast.tdDef,
     td.MLast.tdCon)
  in
  match te with
  [ <:ctyp< '$s$ >> when not (List.mem_assoc s tp) ->
      sprintf "%s%s%s%s" pc.bef
        (type_params {(pc) with bef = ""; aft = ""} tp)
        (var_escaped {(pc) with bef = ""; aft = ""} tn)
        pc.aft
  | _ ->
      horiz_vertic
        (fun () ->
           sprintf "%s%s%s = %s%s%s" pc.bef
             (type_params {(pc) with bef = ""; aft = ""} tp)
             (var_escaped {(pc) with bef = ""; aft = ""} tn)
             (ctyp {(pc) with bef = ""; aft = ""} te)
             (if cl = [] then ""
              else not_impl "type_decl cl" {(pc) with bef = ""; aft = ""} cl)
             pc.aft)
        (fun () ->
           let s1 =
             horiz_vertic
               (fun () ->
                  sprintf "%s%s%s =" pc.bef
                    (type_params {(pc) with bef = ""; aft = ""} tp)
                    (var_escaped {(pc) with bef = ""; aft = ""} tn))
               (fun () ->
                  not_impl "type_decl vertic 1" {(pc) with aft = ""} tn)
           in
           let s2 =
             if cl = [] then
               ctyp
                 {(pc) with ind = pc.ind + 2; bef = tab (pc.ind + 2);
                  aft = ""}
                 te
             else
               horiz_vertic
                 (fun () ->
                    sprintf "%s%s%s%s" (tab (pc.ind + 2))
                      (ctyp {(pc) with bef = ""; aft = ""} te)
                      (not_impl "type_decl cl 2"
                         {(pc) with bef = ""; aft = ""} cl)
                      "")
                 (fun () ->
                    not_impl "type_decl vertic 2"
                      {(pc) with bef = ""; aft = ""} tn)
           in
           let s3 =
             if pc.aft = "" then "" else sprintf "\n%s%s" (tab pc.ind) pc.aft
           in
           sprintf "%s\n%s%s" s1 s2 s3) ]
;

value label_decl pc (_, l, m, t) =
  horiz_vertic
    (fun () ->
       sprintf "%s%s%s : %s%s" pc.bef (if m then "mutable " else "") l
         (ctyp {(pc) with bef = ""; aft = ""} t) pc.aft)
    (fun () ->
       let s1 = sprintf "%s%s%s :" pc.bef (if m then " mutable" else "") l in
       let s2 = ctyp {(pc) with ind = pc.ind + 2; bef = tab (pc.ind + 2)} t in
       sprintf "%s\n%s" s1 s2)
;

value cons_decl pc (_, c, tl) =
  if tl = [] then cons_escaped pc c
  else
    let ctyp_apply = pr_ctyp.pr_fun "apply" in
    horiz_vertic
      (fun () ->
         sprintf "%s%s of %s%s" pc.bef c
           (hlist2 ctyp_apply (star_before ctyp_apply)
              {(pc) with bef = ""; aft = ("", "")} tl) pc.aft)
      (fun () ->
         let s1 = sprintf "%s%s of" pc.bef c in
         let s2 =
           horiz_vertic
             (fun () ->
                sprintf "%s%s%s" (tab (pc.ind + 4))
                  (hlist2 ctyp_apply (star_before ctyp_apply)
                     {(pc) with bef = ""; aft = ("", "")} tl) pc.aft)
             (fun () ->
                let tl = List.map (fun t -> (t, " *")) tl in
                plist ctyp_apply 2
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
      fun curr next pc -> operator pc next next 2 "=" x y
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

value ctyp_star =
  extfun Extfun.empty with
  [ <:ctyp< ($list:tl$) >> ->
      fun curr next pc ->
        horiz_vertic
          (fun () ->
             sprintf "%s%s%s" pc.bef
               (hlistl (star_after next) next {(pc) with bef = ""; aft = ""}
                  tl)
               pc.aft)
          (fun () ->
             let tl = List.map (fun t -> (t, " *")) tl in
             plist next 1 pc tl)
  | z -> fun curr next pc -> next pc z ]
;

value ctyp_apply =
  extfun Extfun.empty with
  [ <:ctyp< $_$ $_$ >> as z ->
      fun curr next pc ->
        let (t, tl) =
          loop [] z where rec loop args =
            fun
            [ <:ctyp< $x$ $y$ >> -> loop [y :: args] x
            | t -> (t, args) ]
        in
        match tl with
        [ [t2] ->
            horiz_vertic
              (fun () ->
                 sprintf "%s%s %s%s" pc.bef
                   (curr {(pc) with bef = ""; aft = ""} t2)
                   (next {(pc) with bef = ""; aft = ""} t) pc.aft)
              (fun () ->
                 let s1 = curr {(pc) with aft = ""} t2 in
                 let s2 =
                   next {(pc) with ind = pc.ind + 2; bef = tab (pc.ind + 2)}
                     t
                 in
                 sprintf "%s\n%s" s1 s2)
        | _ ->
            horiz_vertic
              (fun () ->
                 sprintf "%s(%s) %s%s" pc.bef
                   (hlistl (comma_after ctyp) ctyp
                      {(pc) with bef = ""; aft = ""} tl)
                   (curr {(pc) with bef = ""; aft = ""} t) pc.aft)
              (fun () ->
                 let s1 =
                   hlistl (comma_after ctyp) ctyp
                     {(pc) with bef = sprintf "%s(" pc.bef; aft = ")"} tl
                 in
                 let s2 =
                   curr
                     {(pc) with ind = pc.ind + 2; bef = tab (pc.ind + 2)} t
                 in
                 sprintf "%s\n%s" s1 s2) ]
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
                 {(pc) with aft = ("", pc.aft)} vdl)
          (fun () ->
             vlist2 cons_decl (bar_before cons_decl)
               {(pc) with bef = sprintf "%s  " pc.bef; aft = ("", pc.aft)}
               vdl)
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
  | <:ctyp< $_$ $_$ >> | <:ctyp< $_$ -> $_$ >> | <:ctyp< ($list:_$) >> as z ->
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
  [ <:expr< do { $list:el$ } >> ->
      fun curr next pc ->
        horiz_vertic
          (fun () ->
             sprintf "%s%s%s" pc.bef
               (hlistl (semi_after (comm_expr expr)) (comm_expr expr)
                  {(pc) with bef = ""; aft = ""} el)
               pc.aft)
          (fun () ->
             vlist2 expr_semi expr_semi {(pc) with aft = (None, Some pc.aft)}
               el)
  | z -> fun curr next pc -> next pc z ] 
;

value expr_expr1 =
  extfun Extfun.empty with
  [ <:expr< if $e1$ then $e2$ else $e3$ >> as ge ->
      fun curr next pc ->
        horiz_vertic
         (fun () ->
            match e3 with
            [ <:expr< () >> ->
                if pc.dang = "else" then next pc ge
                else
                  sprintf "%sif %s then %s%s" pc.bef
                    (curr {(pc) with bef = ""; aft = ""; dang = ""} e1)
                    (curr {(pc) with bef = ""; aft = ""} e2)
                    pc.aft
            | _ ->
                sprintf "%sif %s then %s else %s%s" pc.bef
                  (curr {(pc) with bef = ""; aft = ""; dang = ""} e1)
                  (curr {(pc) with bef = ""; aft = ""; dang = "else"} e2)
                  (curr {(pc) with bef = ""; aft = ""} e3) pc.aft ])
         (fun () ->
            let (eel, e3) = get_else_if e3 in
            let if_then pc else_b e1 e2 =
              horiz_vertic
                (fun () ->
                   sprintf "%s%sif %s then %s%s" pc.bef else_b
                     (curr {(pc) with bef = ""; aft = ""; dang = ""} e1)
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
                           {ind = pc.ind + 3;
                            bef = sprintf "%s%sif " pc.bef else_b; aft = "";
                            dang = ""}
                           e1
                       else
                         let s1 = sprintf "%s%sif" pc.bef else_b in
                         let s2 =
                           curr
                             {ind = pc.ind + 2; bef = tab (pc.ind + 2);
                              aft = ""; dang = ""}
                             e1
                         in
                         sprintf "%s\n%s" s1 s2
                     in
                     let s2 = sprintf "%sthen%s" (tab pc.ind) k in
                     sprintf "%s\n%s" s1 s2
                   in
                   let s1 =
                     horiz_vertic (fun () -> horiz_if_then "")
                       (fun () -> vertic_if_then "")
                   in
                   let s2 =
                     comm_expr expr1
                       {(pc) with ind = pc.ind + 2; bef = tab (pc.ind + 2)}
                       e2
                   in
                   sprintf "%s\n%s" s1 s2)
            in
            match e3 with
            [ <:expr< () >> when pc.dang = "else" -> next pc ge
            | _ ->
                let s1 =
                  let (pc_dang, pc_aft) =
                    match (eel, e3) with
                    [ ([], <:expr< () >>) -> (pc.dang, pc.aft)
                    | _ -> ("else", "") ]
                  in
                  if_then {(pc) with aft = pc_aft; dang = pc_dang} "" e1 e2
                in
                let s2 =
                  loop eel where rec loop =
                    fun
                    [ [(e1, e2) :: eel] ->
                        let (pc_dang, pc_aft) =
                          match (eel, e3) with
                          [ ([], <:expr< () >>) -> (pc.dang, pc.aft)
                          | _ -> ("else", "") ]
                        in
                        sprintf "\n%s%s"
                          (if_then
                             {(pc) with bef = tab pc.ind; aft = pc_aft;
                              dang = pc_dang}
                             "else " e1 e2)
                          (loop eel)
                    | [] -> "" ]
                in
                let s3 =
                  match e3 with
                  [ <:expr< () >> -> ""
                  | _ ->
                      let s =
                        horiz_vertic
                          (fun () ->
                             sprintf "%selse %s%s" (tab pc.ind)
                               (comm_expr curr
                                  {(pc) with bef = ""; aft = ""} e3)
                                  pc.aft)
                          (fun () ->
                             let s =
                               comm_expr expr1
                                 {(pc) with ind = pc.ind + 2;
                                  bef = tab (pc.ind + 2)}
                                 e3
                             in
                             sprintf "%selse\n%s" (tab pc.ind) s)
                      in
                      sprintf "\n%s" s ]
                in
                sprintf "%s%s%s" s1 s2 s3 ])
  | <:expr< fun [ $list:pwel$ ] >> as ge ->
      fun curr next pc ->
        match pwel with
        [ [(p1, None, e1)] when is_irrefut_patt p1 ->
            let (pl, e1) = expr_fun_args e1 in
            let pl = [p1 :: pl] in
            let simple_patt = pr_patt.pr_fun "simple" in
            horiz_vertic
              (fun () ->
                 let (op_begin, op_end) =
                   if List.mem pc.dang ["|"; ";"] then ("(", ")")
                   else ("", "")
                 in
                 sprintf "%s%sfun %s -> %s%s%s" pc.bef op_begin
                   (hlist simple_patt {(pc) with bef = ""; aft = ""} pl)
                   (expr {(pc) with bef = ""; aft = ""} e1) op_end pc.aft)
              (fun () ->
                 let (op_begin, sh, pc_aft, pc_dang) =
                   if List.mem pc.dang ["|"; ";"] then
                     ("(", 3, sprintf ")%s" pc.aft, "")
                   else ("", 2, pc.aft, pc.dang)
                 in
                 let fun_arrow k =
                   let pl = List.map (fun p -> (p, "")) pl in
                   plist simple_patt 4
                     {(pc) with bef = sprintf "%s%sfun " pc.bef op_begin;
                      aft = sprintf " ->%s" k}
                     pl
                 in
                 let s1 = fun_arrow "" in
                 let s2 =
                   expr
                     {ind = pc.ind + sh; bef = tab (pc.ind + sh);
                      aft = pc_aft; dang = pc_dang}
                     e1
                 in
                 sprintf "%s\n%s" s1 s2)
        | [] ->
            let loc = MLast.loc_of_expr ge in
            horiz_vertic
              (fun () ->
                 let (op_begin, op_end) =
                   if List.mem pc.dang ["|"; ";"] then ("(", ")")
                   else ("", "")
                 in
                 sprintf "%s%sfun _ -> %s%s%s" pc.bef op_begin
                   (raise_match_failure {(pc) with bef = ""; aft = ""} loc)
                   op_end pc.aft)
              (fun () ->
                 let s1 = sprintf "%sfun _ ->" pc.bef in
                 let s2 =
                   raise_match_failure
                     {(pc) with ind = pc.ind + 2; bef = tab (pc.ind + 2)} loc
                 in
                 sprintf "%s\n%s" s1 s2)
        | pwel ->
            let (op_begin, pc_aft, pc_dang, op_end) =
              if List.mem pc.dang ["|"; ";"] then
                ("(", "", "", sprintf ")%s" pc.aft)
              else ("", pc.aft, pc.dang, "")
            in
            let s =
              match_assoc_list
                {(pc) with bef = tab pc.ind; aft = pc_aft; dang = pc_dang}
                pwel
            in
            sprintf "%s%sfunction\n%s%s" pc.bef op_begin s op_end ]
  | <:expr< try $e1$ with [ $list:pwel$ ] >> |
    <:expr< match $e1$ with [ $list:pwel$ ] >> as e ->
      fun curr next pc ->
        let op =
          match e with
          [ <:expr< try $_$ with [ $list:_$ ] >> -> "try"
          | _ -> "match" ]
        in
        match pwel with
        [ [(p, wo, e)] ->
            horiz_vertic
              (fun () ->
                 let (op_begin, op_end) =
                   if List.mem pc.dang ["|"; ";"] then (sprintf "(%s" op, ")")
                   else (op, "")
                 in
                 sprintf "%s%s %s with %s%s%s" pc.bef op_begin
                   (expr {(pc) with bef = ""; aft = ""; dang = ""} e1)
                   (match_assoc {(pc) with bef = ""; aft = Some ""}
                      (p, wo, e))
                   op_end pc.aft)
              (fun () ->
                 let (op_begin, pc_aft, op_end) =
                   if List.mem pc.dang ["|"; ";"] then
                     (sprintf "begin %s" op, "",
                      sprintf "\n%send%s" (tab pc.ind) pc.aft)
                   else (op, pc.aft, "")
                 in
                 match
                   horiz_vertic
                     (fun () ->
                        Some
                          (sprintf "%s%s %s with" pc.bef op_begin
                             (expr {(pc) with bef = ""; aft = ""} e1)))
                     (fun () -> None)
                 with
                 [ Some s1 ->
                     let s2 =
                       match_assoc
                         {(pc) with ind = pc.ind + 2;
                          bef = tab (pc.ind + 2); aft = Some pc_aft}
                         (p, wo, e)
                     in
                     let s3 = op_end in
                     sprintf "%s\n%s%s" s1 s2 s3
                 | None ->
                     let s1 =
                       let s =
                         expr
                           {ind = pc.ind + 2; bef = tab (pc.ind + 2);
                            aft = ""; dang = ""}
                           e1
                       in
                       sprintf "%s%s\n%s" pc.bef op_begin s
                     in
                     let s2 =
                       match_assoc
                         {(pc) with bef = sprintf "%swith " (tab pc.ind);
                          aft = Some pc_aft}
                         (p, wo, e)
                     in
                     let s3 = op_end in
                     sprintf "%s\n%s%s" s1 s2 s3 ])
        | [] -> raise_match_failure pc (MLast.loc_of_expr e)
        | _ ->
            horiz_vertic
              (fun () ->
                 sprintf "%s%s %s with %s%s" pc.bef op
                   (expr {(pc) with bef = ""; aft = ""} e1)
                   (match_assoc_list {(pc) with bef = ""; aft = ""} pwel)
                   pc.aft)
              (fun () ->
                 let (op_begin, pc_aft, pc_dang, op_end) =
                   if List.mem pc.dang ["|"; ";"] then
                     (sprintf "begin %s" op, "", "",
                      sprintf "\n%send%s" (tab pc.ind) pc.aft)
                   else (op, pc.aft, pc.dang, "")
                 in
                 let s1 =
                   horiz_vertic
                     (fun () ->
                        sprintf "%s%s %s with" pc.bef op_begin
                          (expr {(pc) with bef = ""; aft = ""} e1))
                     (fun () ->
                        let s =
                          let s =
                            expr
                              {(pc) with ind = pc.ind + 2;
                               bef = tab (pc.ind + 2); aft = ""}
                              e1
                          in
                          sprintf "%s%s\n%s" pc.bef op_begin s
                        in
                        sprintf "%s\n%swith" s (tab pc.ind))
                 in
                 let s2 =
                   match_assoc_list
                     {(pc) with bef = tab pc.ind; aft = pc_aft;
                      dang = pc_dang}
                     pwel
                 in
                 let s3 = op_end in
                 sprintf "%s\n%s%s" s1 s2 s3) ]
  | <:expr< let $opt:rf$ $list:pel$ in $e$ >> ->
      fun curr next pc ->
        horiz_vertic
          (fun () ->
             if not flag_horiz_let_in.val then sprintf "\n"
             else
               let (begin_op, pc_aft, pc_dang, end_op) =
                 if pc.dang = ";" then ("(", "", "", ")")
                 else ("", pc.aft, pc.dang, "")
               in
               sprintf "%s%slet %s%s %s%s%s" pc.bef begin_op
                 (if rf then "rec " else "")
                 (hlist2 let_binding (and_before let_binding)
                    {(pc) with bef = ""; aft = ("", "in")} pel)
                 (expr {(pc) with bef = ""; aft = ""; dang = pc_dang} e)
                 end_op pc_aft)
          (fun () ->
             let (begin_op, ind, pc_aft, pc_dang, end_op) =
               if pc.dang = ";" then
                 ("begin ", pc.ind + 2, "", "",
                  sprintf "\n%send%s" (tab pc.ind) pc.aft)
               else ("", pc.ind, pc.aft, pc.dang, "")
             in
             let s1 =
               vlist2 let_binding (and_before let_binding)
                 {(pc) with
                  bef =
                    sprintf "%s%slet %s" pc.bef begin_op
                      (if rf then "rec " else "");
                  aft = ("", "in")}
                 pel
             in
             let s2 =
               expr_with_comm_except_if_sequence
                 {ind = ind; bef = tab ind; aft = pc_aft; dang = pc_dang} e
             in
             let s3 = end_op in
             sprintf "%s\n%s%s" s1 s2 s3)
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
  | <:expr< while $e1$ do { $list:el$ } >> ->
      fun curr next pc ->
        horiz_vertic
          (fun () ->
             sprintf "%swhile %s do %s done%s" pc.bef
               (curr {(pc) with bef = ""; aft = ""} e1)
               (hlistl (semi_after expr) curr {(pc) with bef = ""; aft = ""}
                  el)
               pc.aft)
          (fun () ->
             let s1 =
               horiz_vertic
                 (fun () ->
                    sprintf "%swhile %s do" pc.bef
                      (curr {(pc) with bef = ""; aft = ""} e1))
                 (fun () ->
                    let s1 = sprintf "%swhile" pc.bef in
                    let s2 =
                      curr
                        {(pc) with ind = pc.ind + 2;
                         bef = tab (pc.ind + 2); aft = ""}
                        e1
                    in
                    let s3 = sprintf "%sdo" (tab pc.ind) in
                    sprintf "%s\n%s\n%s" s1 s2 s3)
             in
             let s2 =
               vlistl (semi_after expr) curr
                 {(pc) with ind = pc.ind + 2; bef = tab (pc.ind + 2);
                  aft = ""}
                 el
             in
             let s3 = sprintf "%sdone%s" (tab pc.ind) pc.aft in
             sprintf "%s\n%s\n%s" s1 s2 s3)
  | <:expr< for $v$ = $e1$ $to:d$ $e2$ do { $list:el$ } >> ->
      fun curr next pc ->
        horiz_vertic
          (fun () ->
             sprintf "%sfor %s = %s %s %s do %s done%s" pc.bef v
               (curr {(pc) with bef = ""; aft = ""} e1)
               (if d then "to" else "downto")
               (curr {(pc) with bef = ""; aft = ""} e2)
               (hlistl (semi_after curr) curr
                  {(pc) with bef = ""; aft = ""; dang = ""} el)
               pc.aft)
          (fun () ->
             let s1 =
               horiz_vertic
                 (fun () ->
                    sprintf "%sfor %s = %s %s %s do" pc.bef v
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
                    let s3 = sprintf "%sdo" (tab pc.ind) in
                    sprintf "%s\n%s\n%s" s1 s2 s3)
             in
             let s2 =
               vlistl (semi_after curr) curr
                 {ind = pc.ind + 2; bef = tab (pc.ind + 2); aft = "";
                  dang = ""}
                 el
             in
             let s3 = sprintf "%sdone%s" (tab pc.ind) pc.aft in
             sprintf "%s\n%s\n%s" s1 s2 s3)
  | z ->
      fun curr next pc -> next pc z ]
;

value expr_tuple =
  extfun Extfun.empty with
  [ <:expr< ($list:el$) >> ->
      fun curr next pc ->
        let el = List.map (fun e -> (e, ",")) el in
        plist next 0 pc el
  | z -> fun curr next pc -> next pc z ]
;

value expr_assign =
  extfun Extfun.empty with
  [ <:expr< $x$.val := $y$ >> ->
      fun curr next pc -> operator pc next expr 2 ":=" x y
  | <:expr< $x$ := $y$ >> ->
      fun curr next pc -> operator pc next expr 2 "<-" x y
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

value expr_cons =
  extfun Extfun.empty with
  [ <:expr< [$_$ :: $_$] >> as z ->
      fun curr next pc ->
        let (xl, y) = make_expr_list z in
        match y with
        [ Some y ->
            let xl = List.map (fun x -> (x, " ::")) (xl @ [y]) in
            plist next 0 pc xl
        | None -> next pc z ]
  | z -> fun curr next pc -> next pc z ]
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
          let cons_args_opt =
            loop [] z where rec loop args =
              fun
              [ <:expr< $x$ $y$ >> -> loop [y :: args] x
              | <:expr< $uid:_$ >> as e -> Some (e, args)
              | <:expr< $_$ . $uid:_$ >> as e -> Some (e, args)
              | _ -> None ]
          in
          match cons_args_opt with
          [ Some (e, ([_; _ :: _] as al)) ->
              let expr_or = pr_expr.pr_fun "bar" in
              horiz_vertic
                (fun () ->
                   sprintf "%s%s (%s)%s" pc.bef
                     (next {(pc) with bef = ""; aft = ""} e)
                     (hlistl (comma_after expr_or) expr_or
                        {(pc) with bef = ""; aft = ""} al) pc.aft)
                (fun () ->
                   let al = List.map (fun a -> (a, ",")) al in
                   let s1 = next {(pc) with aft = ""} e in
                   let s2 =
                     plist expr_or 0
                       {(pc) with ind = pc.ind + 3;
                        bef = sprintf "%s(" (tab (pc.ind + 2));
                        aft = sprintf ")%s" pc.aft}
                       al
                   in
                   sprintf "%s\n%s" s1 s2)
          | _ ->
              let unfold =
                fun
                [ <:expr< $x$ $y$ >> -> Some (x, "", y)
                | e -> None ]
              in
              left_operator pc 2 unfold next z ]
  | z ->
      fun curr next pc -> next pc z ]
;

value expr_dot =
  extfun Extfun.empty with
  [ <:expr< $x$ . val >> ->
      fun curr next pc ->
        next {(pc) with bef = sprintf "%s!" pc.bef} x
  | <:expr< $x$ . $y$ >> ->
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
  [ <:expr< {$list:lel$} >> ->
      fun curr next pc ->
        let lxl = List.map (fun lx -> (lx, ";")) lel in
        plistl (comm_patt_any (record_binding False))
          (comm_patt_any (record_binding True)) 0
          {(pc) with ind = pc.ind + 1; bef = sprintf "%s{" pc.bef;
           aft = (sprintf "}%s" pc.aft)}
          lxl
  | <:expr< {($e$) with $list:lel$} >> ->
      fun curr next pc ->
        let lxl = List.map (fun lx -> (lx, ";")) lel in
        plistl (record_binding False) (record_binding True) 0
          {(pc) with ind = pc.ind + 1;
           bef =
             expr {(pc) with bef = sprintf "%s{" pc.bef; aft = " with "} e;
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
        match y with
        [ Some _ ->
            expr
              {ind = pc.ind + 1; bef = sprintf "%s(" pc.bef;
               aft = sprintf ")%s" pc.aft; dang = ""}
              z
        | None ->
            let xl = List.map (fun x -> (x, ";")) xl in
            plist expr1 0
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
      fun curr next pc -> sprintf "%s'%s'%s" pc.bef (ocaml_char s) pc.aft
  | <:expr< ? $_$ >> | <:expr< ~ $_$ >> | <:expr< ~ $_$ : $_$ >> ->
      fun curr next pc ->
        failwith "labels not pretty printed (in expr); add pr_ro.cmo"
  | <:expr< do { $list:el$ } >> ->
      fun curr next pc ->
        horiz_vertic
          (fun () ->
             sprintf "%sbegin %s end%s" pc.bef
               (hlistl (semi_after (comm_expr expr1)) (comm_expr expr1)
                  {(pc) with bef = ""; aft = ""} el)
               pc.aft)
          (fun () ->
             let s =
               vlistl (semi_after expr1) expr1
                 {(pc) with ind = pc.ind + 2; bef = tab (pc.ind + 2);
                  aft = ""}
                el
             in
             sprintf "%sbegin\n%s\n%send%s" pc.bef s (tab pc.ind) pc.aft)
  | <:expr< $_$ $_$ >> | <:expr< $_$ . $_$ >> | <:expr< assert $_$ >> |
    <:expr< lazy $_$ >> | <:expr< ($list:_$) >> | <:expr< $_$ := $_$ >> |
    <:expr< fun [ $list:_$ ] >> | <:expr< if $_$ then $_$ else $_$ >> |
    <:expr< for $_$ = $_$ $to:_$ $_$ do { $list:_$ } >> |
    <:expr< while $_$ do { $list:_$ } >> |
    <:expr< let $opt:_$ $list:_$ in $_$ >> |
    <:expr< match $_$ with [ $list:_$ ] >> |
    <:expr< try $_$ with [ $list:_$ ] >> as z ->
      fun curr next pc ->
        expr
          {ind = pc.ind + 1; bef = sprintf "%s(" pc.bef;
           aft = sprintf ")%s" pc.aft; dang = ""}
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

value patt_tuple =
  extfun Extfun.empty with
  [ <:patt< ($list:pl$) >> ->
      fun curr next pc ->
        let pl = List.map (fun p -> (p, ",")) pl in
        plist next 0 pc pl
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

value patt_cons =
  extfun Extfun.empty with
  [ <:patt< [$_$ :: $_$] >> as z ->
      fun curr next pc ->
        let (xl, y) = make_patt_list z in
        match y with
        [ Some y ->
            let xl = List.map (fun x -> (x, " ::")) (xl @ [y]) in
            plist next 0 {(pc) with ind = pc.ind + 1} xl
        | None -> next pc z ]
  | z -> fun curr next pc -> next pc z ]
;

value patt_apply =
  extfun Extfun.empty with
  [ <:patt< $_$ $_$ >> as z ->
      fun curr next pc ->
        let p_pl_opt =
          loop [] z where rec loop pl =
            fun
            [ <:patt< $x$ $y$ >> -> loop [y :: pl] x
            | <:patt< $uid:"::"$ >> -> None
            | p -> Some (p, pl) ]
        in
        match p_pl_opt with
        [ None -> next pc z
        | Some (p1, [p2]) ->
            horiz_vertic
              (fun () ->
                 sprintf "%s%s %s%s" pc.bef
                   (curr {(pc) with bef = ""; aft = ""} p1)
                   (next {(pc) with bef = ""; aft = ""} p2) pc.aft)
              (fun () ->
                 let s1 = curr {(pc) with aft = ""} p1 in
                 let s2 =
                   next
                     {(pc) with ind = pc.ind + 2; bef = tab (pc.ind + 2)} p2
                 in
                 sprintf "%s\n%s" s1 s2)
        | Some (p, pl) ->
            let patt = pr_patt.pr_fun "range" in
            horiz_vertic
              (fun () ->
                 sprintf "%s%s (%s)%s" pc.bef
                   (next {(pc) with bef = ""; aft = ""} p)
                   (hlistl (comma_after patt) patt
                      {(pc) with bef = ""; aft = ""} pl) pc.aft)
              (fun () ->
                 let al = List.map (fun a -> (a, ",")) pl in
                 let s1 = next {(pc) with aft = ""} p in
                 let s2 =
                   plist patt 0
                     {(pc) with ind = pc.ind + 3;
                      bef = sprintf "%s(" (tab (pc.ind + 2));
                      aft = sprintf ")%s" pc.aft}
                     al
                 in
                 sprintf "%s\n%s" s1 s2) ]
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
        match y with
        [ Some  y ->
            let xl = List.map (fun x -> (x, " ::")) (xl @ [y]) in
            plist patt 0
              {(pc) with ind = pc.ind + 1; bef = sprintf "%s(" pc.bef;
               aft = sprintf ")%s" pc.aft}
              xl
        | None ->
            let xl = List.map (fun x -> (x, ";")) xl in
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
      fun curr next pc -> sprintf "%s'%s'%s" pc.bef (ocaml_char s) pc.aft
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
  | <:patt< $_$ $_$ >> | <:patt< $_$ | $_$ >> | <:patt< $_$ .. $_$ >> |
    <:patt< ($list:_$) >> as z ->
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
              (hlist2 ctyp (star_before ctyp)
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
           let tl = List.map (fun t -> (t, " *")) tl in
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
        expr
          {(pc) with bef = sprintf "%s(* #%s " pc.bef s;
           aft = sprintf "%s *)" pc.aft}
        e
  | <:str_item< declare $list:sil$ end >> ->
      fun curr next pc ->
        if sil = [] then sprintf "%s(* *)" pc.bef
        else
          let str_item_sep =
            if flag_semi_semi.val then semi_semi_after str_item else str_item
          in
          vlistl str_item_sep str_item pc sil
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
             let s3 =
               if pc.aft = "" then ""
               else sprintf "\n%s%s" (tab pc.ind) pc.aft
             in
             sprintf "%s\n%s%s" s1 s2 s3)
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
             let s3 =
               if pc.aft = "" then ""
               else sprintf "\n%s%s" (tab pc.ind) pc.aft
             in
             sprintf "%s\n%s%s" s1 s2 s3)
  | <:str_item< open $i$ >> ->
      fun curr next pc ->
        mod_ident {(pc) with bef = sprintf "%sopen " pc.bef} i
  | <:str_item< type $list:tdl$ >> ->
      fun curr next pc ->
        vlist2 type_decl (and_before type_decl)
          {(pc) with bef = sprintf "%stype " pc.bef; aft = ("", pc.aft)}
          tdl
  | <:str_item< value $opt:rf$ $list:pel$ >> ->
      fun curr next pc ->
        horiz_vertic
          (fun () ->
             sprintf "%slet %s%s" pc.bef (if rf then "rec " else "")
               (hlist2 let_binding (and_before let_binding)
                  {(pc) with bef = ""; aft = ("", pc.aft)} pel))
          (fun () ->
             vlist2 let_binding (and_before let_binding)
               {(pc) with
                bef = sprintf "%slet %s" pc.bef (if rf then "rec " else "");
                aft = ("", pc.aft)} pel)
  | <:str_item< $exp:e$ >> ->
      fun curr next pc ->
        if pc.aft = ";;" then expr pc e
        else
          let loc = MLast.loc_of_expr e in
          curr pc <:str_item< value _ = $e$ >>
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
  | <:sig_item< declare $list:sil$ end >> ->
      fun curr next pc ->
        if sil = [] then sprintf "%s(* *)" pc.bef
        else
          let sig_item_sep =
            if flag_semi_semi.val then semi_semi_after sig_item else sig_item
          in
          vlistl sig_item_sep sig_item pc sil
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
             let s3 =
               if pc.aft = "" then ""
               else sprintf "\n%s%s" (tab pc.ind) pc.aft
             in
             sprintf "%s\n%s%s" s1 s2 s3)
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
             let s3 =
               if pc.aft = "" then ""
               else sprintf "\n%s%s" (tab pc.ind) pc.aft
             in
             sprintf "%s\n%s%s" s1 s2 s3)
  | <:sig_item< open $i$ >> ->
      fun curr next pc ->
        mod_ident {(pc) with bef = (sprintf "%sopen " pc.bef)} i
  | <:sig_item< type $list:tdl$ >> ->
      fun curr next pc ->
        vlist2 type_decl (and_before type_decl)
          {(pc) with bef = sprintf "%stype " pc.bef; aft = ("", pc.aft)}
          tdl
  | <:sig_item< value $s$ : $t$ >> ->
      fun curr next pc ->
        horiz_vertic
          (fun () ->
             sprintf "%sval %s : %s%s" pc.bef
               (var_escaped {(pc) with bef = ""; aft = ""} s)
               (ctyp {(pc) with bef = ""; aft = ""} t) pc.aft)
          (fun () ->
             let s1 =
               sprintf "%sval %s :" pc.bef
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
        let str_item_sep =
          if flag_semi_semi.val then semi_semi_after str_item else str_item
        in
        horiz_vertic
          (fun () ->
             if alone_in_line pc then
               (* Heuristic : I don't like to print structs horizontally
                  when alone in a line. *)
               sprintf "\n"
             else
               sprintf "%sstruct%s%s%send%s" pc.bef " "
                 (hlist str_item_sep {(pc) with bef = ""; aft = ""} sil)
                 " " pc.aft)
          (fun () ->
             sprintf "%sstruct%s%s%send%s" pc.bef "\n"
               (vlist str_item_sep
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
        let sig_item_sep =
          if flag_semi_semi.val then semi_semi_after sig_item else sig_item
        in
        horiz_vertic
          (fun () ->
             if alone_in_line pc then
               (* Heuristic : I don't like to print sigs horizontally
                  when alone in a line. *)
               sprintf "\n"
             else
               sprintf "%ssig%s%s%send%s" pc.bef " "
                 (hlist sig_item_sep {(pc) with bef = ""; aft = ""} sil)
                 " " pc.aft)
          (fun () ->
             sprintf "%ssig%s%s%send%s" pc.bef "\n"
               (vlist sig_item_sep
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
   {pr_label = "expr1"; pr_rules = expr_expr1};
   {pr_label = "tuple"; pr_rules = expr_tuple};
   {pr_label = "assign"; pr_rules = expr_assign};
   {pr_label = "bar"; pr_rules = expr_or};
   {pr_label = "amp"; pr_rules = expr_and};
   {pr_label = "less"; pr_rules = expr_less};
   {pr_label = "concat"; pr_rules = expr_concat};
   {pr_label = "cons"; pr_rules = expr_cons};
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
   {pr_label = "tuple"; pr_rules = patt_tuple};
   {pr_label = "range"; pr_rules = patt_range};
   {pr_label = "cons"; pr_rules = patt_cons};
   {pr_label = "apply"; pr_rules = patt_apply};
   {pr_label = "dot"; pr_rules = patt_dot};
   {pr_label = "simple"; pr_rules = patt_simple}]
;

pr_ctyp.pr_levels :=
  [{pr_label = "top"; pr_rules = ctyp_top};
   {pr_label = "arrow"; pr_rules = ctyp_arrow};
   {pr_label = "star"; pr_rules = ctyp_star};
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
         let k = if flag_semi_semi.val then ";;" else "" in
         output_string oc (f {ind = 0; bef = ""; aft = k; dang = ""} si);
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
          flag_horiz_let_in.val := v;
          flag_semi_semi.val := v;
        }
      | 'L' | 'l' -> flag_horiz_let_in.val := is_uppercase s.[i]
      | 'M' | 'm' -> flag_semi_semi.val := is_uppercase s.[i]
      | c -> failwith ("bad flag " ^ String.make 1 c) ];
      loop (i + 1)
    }
;

value default_flag () =
  let flag_on b t f = if b then t else "" in 
  let flag_off b t f = if b then "" else f in
  let on_off flag =
    sprintf "%s%s"
      (flag flag_horiz_let_in.val "L" "l")
      (flag flag_semi_semi.val "M" "m")
  in
  let on = on_off flag_on in
  let off = on_off flag_off in
  if String.length on < String.length off then sprintf "a%s" on
  else sprintf "A%s" off
;

Pcaml.add_option "-flag" (Arg.String set_flags)
  ("<str> Change pretty printing behaviour according to <flags>:
       A/a enable/disable all flags
       L/l enable/disable allowing printing 'let..in' horizontally
       M/m enable/disable printing double semicolons
       default setting is \"" ^ default_flag () ^ "\".");

Pcaml.add_option "-l" (Arg.Int (fun x -> Pretty.line_length.val := x))
  ("<length> Maximum line length for pretty printing (default " ^
     string_of_int Pretty.line_length.val ^ ")");

Pcaml.add_option "-sep" (Arg.String (fun x -> sep.val := Some x))
  "<string> Use this string between phrases instead of reading source.";

Pcaml.add_option "-ss" (Arg.Set flag_semi_semi)
  "Print double semicolons (equivalent to -flag M).";

(* camlp4r q_MLast.cmo ./pa_extfun.cmo *)
(* $Id: pr_o.ml,v 1.46 2007/07/05 19:18:52 deraugla Exp $ *)
(* Copyright (c) INRIA 2007 *)

(* Pretty printing extension for objects and labels *)

open Pretty;
open Pcaml.Printers;
open Prtools;

value not_impl name pc x =
  let desc =
    if Obj.tag (Obj.repr x) = Obj.tag (Obj.repr "") then
      sprintf "\"%s\"" (Obj.magic x)
    else if Obj.is_block (Obj.repr x) then
      "tag = " ^ string_of_int (Obj.tag (Obj.repr x))
    else "int_val = " ^ string_of_int (Obj.magic x)
  in
  sprintf "%s\"pr_o, not impl: %s; %s\"%s" pc.bef name (String.escaped desc)
    pc.aft
;

value is_infix = do {
  let infixes = Hashtbl.create 73 in
  List.iter (fun s -> Hashtbl.add infixes s True)
    ["!="; "&&"; "*"; "**"; "*."; "+"; "+."; "-"; "-."; "/"; "/."; "<"; "<=";
     "<>"; "="; "=="; ">"; ">="; "@"; "^"; "asr"; "land"; "lor"; "lsl"; "lsr";
     "lxor"; "mod"; "or"; "||"; "~-"; "~-."];
  fun s -> try Hashtbl.find infixes s with [ Not_found -> False ]
};

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

value var_escaped pc v =
  let x =
    if is_infix v || has_special_chars v then "\\" ^ v
    else if is_keyword v then v ^ "__"
    else v
  in
  sprintf "%s%s%s" pc.bef x pc.aft
;

value alone_in_line pc =
  (pc.aft = "" || pc.aft = ";") && pc.bef <> "" &&
  loop 0 where rec loop i =
    if i >= String.length pc.bef then True
    else if pc.bef.[i] = ' ' then loop (i + 1)
    else False
;

value expr pc z = pr_expr.pr_fun "top" pc z;
value patt pc z = pr_patt.pr_fun "top" pc z;
value ctyp pc z = pr_ctyp.pr_fun "top" pc z;
value class_expr pc z = pr_class_expr.pr_fun "top" pc z;
value class_type pc z = pr_class_type.pr_fun "top" pc z;
value class_str_item pc z = pr_class_str_item.pr_fun "top" pc z;
value class_sig_item pc z = pr_class_sig_item.pr_fun "top" pc z;

value rec mod_ident pc sl =
  match sl with
  [ [] -> sprintf "%s%s" pc.bef pc.aft
  | [s] -> sprintf "%s%s%s" pc.bef s pc.aft
  | [s :: sl] -> mod_ident {(pc) with bef = sprintf "%s%s." pc.bef s} sl ]
;

value semi_after elem pc x = elem {(pc) with aft = sprintf ";%s" pc.aft} x;
value amp_before elem pc x = elem {(pc) with bef = sprintf "%s& " pc.bef} x;
value and_before elem pc x = elem {(pc) with bef = sprintf "%sand " pc.bef} x;
value bar_before elem pc x = elem {(pc) with bef = sprintf "%s| " pc.bef} x;

value type_var pc (tv, (p, m)) =
  sprintf "%s%s'%s%s" pc.bef (if p then "+" else if m then "-" else "") tv
    pc.aft
;

value class_type_params pc ctp =
  if ctp = [] then sprintf "%s%s" pc.bef pc.aft
  else
    let ctp = List.map (fun ct -> (ct, ",")) ctp in
    plist type_var 1
      {(pc) with bef = sprintf "%s[" pc.bef; aft = sprintf "] %s" pc.aft}
      ctp
;

value class_def_or_type_decl char pc ci =
  horiz_vertic
    (fun () ->
       sprintf "%s%s%s %s%c %s%s" pc.bef
         (if ci.MLast.ciVir then " virtual" else "") ci.MLast.ciNam
         (class_type_params {(pc) with bef = ""; aft = ""}
            (snd ci.MLast.ciPrm))
         char
         (class_type {(pc) with bef = ""; aft = ""} ci.MLast.ciExp) pc.aft)
    (fun () ->
       let s1 =
         sprintf "%s%s%s %s%c" pc.bef
           (if ci.MLast.ciVir then "virtual " else "")
           ci.MLast.ciNam
           (class_type_params {(pc) with bef = ""; aft = ""}
              (snd ci.MLast.ciPrm))
           char
       in
       let s2 =
         class_type {(pc) with ind = pc.ind + 2; bef = tab (pc.ind + 2)}
           ci.MLast.ciExp
       in
       sprintf "%s\n%s" s1 s2)
;
value class_def = class_def_or_type_decl ':';
value class_type_decl = class_def_or_type_decl '=';

value class_type_decl_list pc cd =
  horiz_vertic
    (fun () ->
       sprintf "%sclass type %s%s" pc.bef
         (hlist2 class_type_decl (and_before class_type_decl)
            {(pc) with bef = ""; aft = ("", "")} cd)
         pc.aft)
    (fun () ->
       vlist2 class_type_decl (and_before class_type_decl)
         {(pc) with bef = sprintf "%sclass type " pc.bef; aft = ("", pc.aft)}
         cd)
;

value class_decl pc ci =
  horiz_vertic
    (fun () ->
       sprintf "%s%s%s %s= %s%s" pc.bef
         (if ci.MLast.ciVir then "virtual " else "") ci.MLast.ciNam
         (class_type_params {(pc) with bef = ""; aft = ""}
            (snd ci.MLast.ciPrm))
         (class_expr {(pc) with bef = ""; aft = ""} ci.MLast.ciExp) pc.aft)
    (fun () ->
       let s1 =
         sprintf "%s%s%s %s=" pc.bef
           (if ci.MLast.ciVir then "virtual " else "")
           ci.MLast.ciNam
           (class_type_params {(pc) with bef = ""; aft = ""}
              (snd ci.MLast.ciPrm))
       in
       let s2 =
         class_expr
           {(pc) with ind = pc.ind + 2; bef = tab (pc.ind + 2)}
           ci.MLast.ciExp
       in
       sprintf "%s\n%s" s1 s2)
;

value variant_decl pc pv =
  match pv with
  [ <:poly_variant< `$c$ >> ->
       sprintf "%s`%s%s" pc.bef c pc.aft
  | <:poly_variant< `$c$ of $opt:ao$ $list:tl$ >> ->
       horiz_vertic
         (fun () ->
            sprintf "%s`%s of %s%s%s" pc.bef c (if ao then "& " else "")
              (hlist2 ctyp (amp_before ctyp)
                 {(pc) with bef = ""; aft = ("", "")} tl) pc.aft)
         (fun () ->
            let s1 =
              sprintf "%s`%s of%s" pc.bef c (if ao then " &" else "")
            in
            let s2 =
               horiz_vertic
                 (fun () ->
                    sprintf "%s%s%s" (tab (pc.ind + 6))
                      (hlist2 ctyp (amp_before ctyp)
                         {(pc) with bef = ""; aft = ("", "")} tl) pc.aft)
                 (fun () ->
                    let tl = List.map (fun t -> (t, " &")) tl in
                    plist ctyp 2
                      {(pc) with ind = pc.ind + 6; bef = tab (pc.ind + 5)} tl)
             in
             sprintf "%s\n%s" s1 s2)
  | <:poly_variant< $t$ >> ->
       ctyp pc t ]
;

value variant_decl_list char pc pvl =
  horiz_vertic
    (fun () ->
       hlist2 variant_decl (bar_before variant_decl)
         {(pc) with bef = sprintf "%s[ %c " pc.bef char;
          aft = ("", sprintf " ]%s" pc.aft)}
         pvl)
    (fun () ->
       let s1 = sprintf "%s[ %c" pc.bef char in
       let s2 =
         vlist2 variant_decl (bar_before variant_decl)
           {(pc) with bef = tab (pc.ind + 2);
            aft = ("", sprintf " ]%s" pc.aft)}
           pvl
       in
       sprintf "%s\n%s" s1 s2)
;

value rec class_longident pc cl =
  match cl with
  [ [] -> sprintf "%s%s" pc.bef pc.aft
  | [c] -> sprintf "%s%s%s" pc.bef c pc.aft
  | [c :: cl] ->
      sprintf "%s%s.%s" pc.bef c (class_longident {(pc) with bef = ""} cl) ]
;

value binding elem pc (p, e) =
  horiz_vertic
    (fun () ->
       sprintf "%s %s%s" (patt {(pc) with aft = " ="} p)
         (elem {(pc) with bef = ""; aft = ""} e) pc.aft)
    (fun () ->
       sprintf "%s\n%s" (patt {(pc) with aft = " ="} p)
         (elem {(pc) with ind = pc.ind + 2; bef = tab (pc.ind + 2)} e))
;

value field pc (s, t) =
  horiz_vertic
    (fun () ->
       sprintf "%s%s : %s%s" pc.bef s (ctyp {(pc) with bef = ""; aft = ""} t)
         pc.aft)
    (fun () ->
       let s1 = sprintf "%s%s :" pc.bef s in
       let s2 = ctyp {(pc) with ind = pc.ind + 2; bef = tab (pc.ind + 2)} t in
       sprintf "%s\n%s" s1 s2)
;

value field_expr pc (s, e) =
  horiz_vertic
    (fun () ->
       sprintf "%s%s = %s%s" pc.bef s (expr {(pc) with bef = ""; aft = ""} e)
         pc.aft)
    (fun () -> not_impl "field expr vertic" pc s)
;

value patt_tcon pc p =
  match p with
  [ <:patt< ($p$ : $t$) >> ->
      horiz_vertic
        (fun () ->
           sprintf "%s%s : %s%s" pc.bef
             (patt {(pc) with bef = ""; aft = ""} p)
             (ctyp {(pc) with bef = ""; aft = ""} t) pc.aft)
        (fun () -> not_impl "patt_tcon vertic" pc p)
  | p -> patt pc p ]
;

value typevar pc tv = sprintf "%s'%s%s" pc.bef tv pc.aft;

value class_object pc (csp, csl) =
  let class_str_item_sep =
    if flag_semi_semi.val then semi_semi_after class_str_item
    else class_str_item
  in
  horiz_vertic
    (fun () ->
       sprintf "%sobject%s %s end%s" pc.bef
         (match csp with
          [ Some (<:patt< ($_$ : $_$) >> as p) ->
              patt {(pc) with bef = " "; aft = ""} p
          | Some p -> patt {(pc) with bef = " ("; aft = ")"} p
          | None -> "" ])
         (hlist class_str_item_sep
            {(pc) with bef = ""; aft = ""} csl) pc.aft)
    (fun () ->
       let s1 =
         match csp with
         [ None -> sprintf "%sobject" pc.bef
         | Some p ->
             horiz_vertic
               (fun () ->
                  sprintf "%sobject %s" pc.bef
                    (match p with
                     [ <:patt< ($_$ : $_$) >> ->
                         patt {(pc) with bef = ""; aft = ""} p
                     | p ->
                         patt {(pc) with bef = "("; aft = ")"} p ]))
               (fun () ->
                  not_impl "class_type vertic 1" {(pc) with aft = ""}
                    p) ]
       in
       let s2 =
         vlist class_str_item_sep
           {(pc) with ind = pc.ind + 2; bef = tab (pc.ind + 2);
            aft = ""}
           csl
       in
       let s3 = sprintf "%send%s" (tab pc.ind) pc.aft in
       sprintf "%s\n%s\n%s" s1 s2 s3)
;

(* *)

let lev = find_pr_level "simple" pr_patt.pr_levels in
lev.pr_rules :=
  extfun lev.pr_rules with
  [ <:patt< ? $s$ >> ->
      fun curr next pc -> sprintf "%s?%s%s" pc.bef s pc.aft
  | <:patt< ? ($p$ $opt:eo$) >> ->
      fun curr next pc ->
        horiz_vertic
          (fun () ->
             sprintf "%s?(%s%s)%s" pc.bef
               (patt_tcon {(pc) with bef = ""; aft = ""} p)
               (match eo with
                [ Some e ->
                    sprintf " = %s" (expr {(pc) with bef = ""; aft = ""} e)
                | None -> "" ])
               pc.aft)
          (fun () -> not_impl "patt ?(p=e) vertic" pc p)
  | <:patt< ? $i$ : ($p$ $opt:eo$) >> ->
      fun curr next pc ->
        horiz_vertic
          (fun () ->
             sprintf "%s?%s:(%s%s)%s" pc.bef i
               (patt {(pc) with bef = ""; aft = ""} p)
               (match eo with
                [ Some e ->
                    sprintf " = %s" (expr {(pc) with bef = ""; aft = ""} e)
                | None -> "" ])
               pc.aft)
          (fun () -> not_impl "patt ?i:(p=e) vertic" pc i)
  | <:patt< ~ $s$ >> ->
      fun curr next pc -> sprintf "%s~%s%s" pc.bef s pc.aft
  | <:patt< ~ $s$ : $p$ >> ->
      fun curr next pc -> curr {(pc) with bef = sprintf "%s~%s:" pc.bef s} p
  | <:patt< `$uid:s$ >> ->
      fun curr next pc -> sprintf "%s`%s%s" pc.bef s pc.aft
  | <:patt< # $list:sl$ >> ->
      fun curr next pc ->
        mod_ident {(pc) with bef = sprintf "%s#" pc.bef} sl ]
;

let lev = find_pr_level "apply" pr_expr.pr_levels in
lev.pr_rules :=
  extfun lev.pr_rules with
  [ <:expr< new $list:cl$ >> ->
      fun curr next pc ->
        horiz_vertic
          (fun () ->
             sprintf "%snew %s%s" pc.bef
               (class_longident {(pc) with bef = ""; aft = ""} cl) pc.aft)
          (fun () -> not_impl "new vertic" pc cl)
  | <:expr< object $opt:csp$ $list:csl$ end >> ->
      fun curr next pc ->
        class_object pc (csp, csl) ]
;

value expr_label =
  extfun Extfun.empty with
  [ <:expr< ? $s$ >> ->
      fun curr next pc -> sprintf "%s?%s%s" pc.bef s pc.aft
  | <:expr< ? $i$ : $e$ >> ->
      fun curr next pc -> curr {(pc) with bef = sprintf "%s?%s:" pc.bef i} e
  | <:expr< ~ $s$ >> ->
      fun curr next pc -> sprintf "%s~%s%s" pc.bef s pc.aft
  | <:expr< ~ $s$ : $e$ >> ->
      fun curr next pc ->
        pr_expr.pr_fun "dot" {(pc) with bef = sprintf "%s~%s:" pc.bef s} e
  | z ->
      fun curr next pc -> next pc z ]
;

let lev = find_pr_level "dot" pr_expr.pr_levels in
lev.pr_rules :=
  extfun lev.pr_rules with
  [ <:expr< $e$ # $s$ >> ->
      fun curr next pc ->
        horiz_vertic
          (fun () ->
             sprintf "%s%s#%s%s" pc.bef
               (curr {(pc) with bef = ""; aft = ""} e) s pc.aft)
          (fun () -> not_impl "# vertic" pc e) ]
;

let lev = find_pr_level "simple" pr_expr.pr_levels in
lev.pr_rules :=
  extfun lev.pr_rules with
  [ <:expr< ( $e$ : $t$ :> $t2$ ) >> ->
      fun curr next pc ->
        horiz_vertic
          (fun () ->
             sprintf "%s(%s : %s :> %s)%s" pc.bef
               (expr {(pc) with bef = ""; aft = ""} e)
               (ctyp {(pc) with bef = ""; aft = ""} t)
               (ctyp {(pc) with bef = ""; aft = ""} t2) pc.aft)
          (fun () ->
             let s1 =
               expr {(pc) with bef = sprintf "%s(" pc.bef; aft = " :"} e
             in
             let s2 =
               ctyp {(pc) with bef = tab (pc.ind + 1); aft = " :>"} t
             in
             let s3 =
               ctyp
                 {(pc) with bef = tab (pc.ind + 1);
                  aft = sprintf ")%s" pc.aft}
                 t2
             in
             sprintf "%s\n%s\n%s" s1 s2 s3)
  | <:expr< ( $e$ :> $t$ ) >> ->
      fun curr next pc ->
        horiz_vertic
          (fun () ->
             sprintf "%s(%s :> %s)%s" pc.bef
               (expr {(pc) with bef = ""; aft = ""} e)
               (ctyp {(pc) with bef = ""; aft = ""} t) pc.aft)
          (fun () ->
             let s1 =
               expr
                 {(pc) with ind = pc.ind + 1; bef = sprintf "%s(" pc.bef;
                  aft = " :>"}
                 e
             in
             let s2 =
               ctyp
                 {(pc) with ind = pc.ind + 1; bef = tab (pc.ind + 1);
                  aft = sprintf ")%s" pc.aft}
                 t
             in
             sprintf "%s\n%s" s1 s2)
  | <:expr< {< $list:fel$ >} >> ->
      fun curr next pc ->
        if fel = [] then sprintf "%s{< >}%s" pc.bef pc.aft
        else
          let fel = List.map (fun fe -> (fe, ";")) fel in
          plist field_expr 3
            {(pc) with bef = sprintf "%s{< " pc.bef;
             aft = sprintf " >}%s" pc.aft}
            fel
  | <:expr< new $list:_$ >> as z ->
      fun curr next pc ->
        expr
          {(pc) with ind = pc.ind + 1; bef = sprintf "%s(" pc.bef;
           aft = sprintf ")%s" pc.aft}
          z ]
;

let lev = find_pr_level "simple" pr_ctyp.pr_levels in
lev.pr_rules :=
  extfun lev.pr_rules with
  [ <:ctyp< ? $i$ : $t$ >> ->
      fun curr next pc -> curr {(pc) with bef = sprintf "%s?%s:" pc.bef i} t
  | <:ctyp< ~ $i$ : $t$ >> ->
      fun curr next pc -> curr {(pc) with bef = sprintf "%s~%s:" pc.bef i} t
  | <:ctyp< < $list:ml$ $opt:v$ > >> ->
      fun curr next pc ->
        if ml = [] then
          sprintf "%s<%s >%s" pc.bef (if v then " .." else "") pc.aft
        else
          let ml = List.map (fun e -> (e, ";")) ml in
          plist field 0
            {(pc) with ind = pc.ind + 2; bef = sprintf "%s< " pc.bef;
             aft = sprintf "%s >%s" (if v then " .." else "") pc.aft}
            ml
  | <:ctyp< # $list:id$ >> ->
      fun curr next pc ->
        class_longident {(pc) with bef = sprintf "%s#" pc.bef}  id
  | <:ctyp< [ = $list:pvl$ ] >> ->
      fun curr next pc -> variant_decl_list '=' pc pvl
  | <:ctyp< [ > $list:pvl$ ] >> ->
      fun curr next pc -> variant_decl_list '>' pc pvl
  | <:ctyp< [ < $list:pvl$ ] >> ->
      fun curr next pc -> variant_decl_list '<' pc pvl
  | <:ctyp< [ < $list:pvl$ > $list:_$ ] >> ->
      fun curr next pc -> not_impl "variants 4" pc pvl
  | <:ctyp< $_$ as $_$ >> as z ->
      fun curr next pc ->
        ctyp
          {(pc) with ind = pc.ind + 1; bef = sprintf "%s(" pc.bef;
           aft = sprintf ")%s" pc.aft}
          z ]
;

let lev = find_pr_level "top" pr_sig_item.pr_levels in
lev.pr_rules :=
  extfun lev.pr_rules with
  [ <:sig_item< class $list:cd$ >> ->
      fun curr next pc ->
        horiz_vertic
          (fun () ->
             sprintf "%sclass %s%s" pc.bef
               (hlist2 class_def (and_before class_def)
                  {(pc) with bef = ""; aft = ("", "")} cd)
               pc.aft)
          (fun () ->
             vlist2 class_def (and_before class_def)
               {(pc) with bef = sprintf "%sclass " pc.bef; aft = ("", pc.aft)}
               cd)
  | <:sig_item< class type $list:cd$ >> ->
      fun curr next pc -> class_type_decl_list pc cd ]
;

let lev = find_pr_level "top" pr_str_item.pr_levels in
lev.pr_rules :=
  extfun lev.pr_rules with
  [ <:str_item< class $list:cd$ >> ->
      fun curr next pc ->
        horiz_vertic
          (fun () ->
             sprintf "%sclass %s%s" pc.bef
               (hlist2 class_decl (and_before class_decl)
                  {(pc) with bef = ""; aft = ("", "")} cd)
               pc.aft)
          (fun () ->
             vlist2 class_decl (and_before class_decl)
               {(pc) with bef = sprintf "%sclass " pc.bef; aft = ("", pc.aft)}
               cd)
  | <:str_item< class type $list:cd$ >> ->
      fun curr next pc -> class_type_decl_list pc cd ]
;

value class_type_top =
  extfun Extfun.empty with
  [ <:class_type< [ $t$ ] -> $ct$ >> ->
      fun curr next pc ->
        horiz_vertic
          (fun () ->
             sprintf "%s[%s] -> %s%s" pc.bef
               (ctyp {(pc) with bef = ""; aft = ""} t)
               (curr {(pc) with bef = ""; aft = ""} ct) pc.aft)
          (fun () ->
             let s1 =
               ctyp {(pc) with bef = sprintf "%s[" pc.bef; aft = "] ->"} t
             in
             let s2 =
               curr {(pc) with ind = pc.ind + 2; bef = tab (pc.ind + 2)} ct
             in
             sprintf "%s\n%s" s1 s2)
  | <:class_type< object $opt:cst$ $list:csi$ end >> ->
      fun curr next pc ->
        horiz_vertic
          (fun () ->
             if alone_in_line pc then
               (* Heuristic : I don't like to print it horizontally
                  when alone in a line. *)
               sprintf "\n"
             else
               sprintf "%sobject%s %s end%s" pc.bef
                 (match cst with
                 [ Some t ->
                      sprintf " (%s)" (ctyp {(pc) with bef = ""; aft = ""} t)
                  | None -> "" ])
                 (hlist (semi_after class_sig_item)
                    {(pc) with bef = ""; aft = ""} csi) pc.aft)
          (fun () ->
             let s1 =
               match cst with
               [ None -> sprintf "%sobject" pc.bef
               | Some t ->
                   horiz_vertic
                     (fun () ->
                        sprintf "%sobject (%s)" pc.bef
                          (ctyp {(pc) with bef = ""; aft = ""} t))
                     (fun () ->
                        not_impl "class_type vertic 1" {(pc) with aft = ""}
                          t) ]
             in
             let s2 =
               vlist (semi_after class_sig_item)
                 {(pc) with ind = pc.ind + 2; bef = tab (pc.ind + 2);
                  aft = ""}
                 csi
             in
             let s3 = sprintf "%send%s" (tab pc.ind) pc.aft in
             sprintf "%s\n%s\n%s" s1 s2 s3)
  | <:class_type< $list:cl$ >> ->
      fun curr next pc -> class_longident pc cl
  | <:class_type< $list:cl$ [ $list:ctcl$ ] >> ->
      fun curr next pc ->
        let ctcl = List.map (fun ct -> (ct, ",")) ctcl in
        horiz_vertic
          (fun  () ->
             sprintf "%s%s [%s]%s" pc.bef
               (class_longident {(pc) with bef = ""; aft = ""} cl)
               (plist ctyp 0 {(pc) with bef = ""; aft = ""} ctcl)
               pc.aft)
          (fun  () -> not_impl "class_type c [t, t] vertic" pc cl)
  | z -> fun curr next pc -> not_impl "class_type" pc z ]
;

value class_expr_top =
  extfun Extfun.empty with
  [ <:class_expr< fun $p$ -> $ce$ >> ->
      fun curr next pc ->
        horiz_vertic
          (fun () ->
             sprintf "%sfun %s -> %s%s" pc.bef
               (patt {(pc) with bef = ""; aft = ""} p)
               (curr {(pc) with bef = ""; aft = ""} ce) pc.aft)
          (fun () ->
             let s1 =
               patt {(pc) with bef = sprintf "%sfun " pc.bef; aft = " ->"} p
             in
             let s2 =
               curr {(pc) with ind = pc.ind + 2; bef = tab (pc.ind + 2)} ce
             in
             sprintf "%s\n%s" s1 s2)
  | <:class_expr< let $opt:rf$ $list:pel$ in $ce$ >> ->
      fun curr next pc ->
        horiz_vertic
          (fun () ->
             let s1 =
               hlist2 (binding expr) (and_before (binding expr))
                 {(pc) with
                  bef = sprintf "%slet %s" pc.bef (if rf then "rec " else "");
                  aft = ("", " in")}
                 pel
             in
             let s2 = class_expr {(pc) with bef = ""} ce in
             sprintf "%s %s" s1 s2)
          (fun () ->
             let s1 =
               vlist2 (binding expr) (and_before (binding expr))
                 {(pc) with
                  bef = sprintf "%slet %s" pc.bef (if rf then "rec " else "");
                  aft = ("", " in")}
                 pel
             in
             let s2 = class_expr {(pc) with bef = tab pc.ind} ce in
             sprintf "%s\n%s" s1 s2)
  | z -> fun curr next pc -> next pc z ]
;

value class_expr_apply =
  extfun Extfun.empty with
  [ <:class_expr< $ce$ $e$ >> ->
      fun curr next pc ->
        horiz_vertic
          (fun () ->
             sprintf "%s%s %s%s" pc.bef
               (curr {(pc) with bef = ""; aft = ""} ce)
               (pr_expr.pr_fun "label" {(pc) with bef = ""; aft = ""} e)
               pc.aft)
          (fun () -> not_impl "class_expr_apply" pc ce)
  | z -> fun curr next pc -> next pc z ]
;

value class_expr_simple =
  extfun Extfun.empty with
  [ <:class_expr< $list:cl$ >> ->
      fun curr next pc -> class_longident pc cl
  | <:class_expr< $list:cl$ [ $list:ctcl$ ] >> ->
      fun curr next pc ->
        let ctcl = List.map (fun ct -> (ct, ",")) ctcl in
        horiz_vertic
          (fun  () ->
             sprintf "%s%s [%s]%s" pc.bef
               (class_longident {(pc) with bef = ""; aft = ""} cl)
               (plist ctyp 0 {(pc) with bef = ""; aft = ""} ctcl)
               pc.aft)
          (fun  () -> not_impl "class_expr c [t, t] vertic" pc cl)
  | <:class_expr< object $opt:csp$ $list:csl$ end >> ->
      fun curr next pc ->
        class_object pc (csp, csl)      
  | <:class_expr< ($ce$ : $ct$) >> ->
      fun curr next pc ->
        horiz_vertic
          (fun () ->
             sprintf "%s(%s : %s)%s" pc.bef
               (curr {(pc) with bef = ""; aft = ""} ce)
               (class_type {(pc) with bef = ""; aft = ""} ct) pc.aft)
          (fun () ->
             let s1 =
               curr
                 {(pc) with ind = pc.ind + 1; bef = sprintf "%s(" pc.bef;
                  aft = " :"}
                 ce
             in
             let s2 =
               class_type
                 {(pc) with ind = pc.ind + 1; bef = tab (pc.ind + 1);
                  aft = sprintf ")%s" pc.aft}
                 ct
             in
             sprintf "%s\n%s" s1 s2)
  | z -> fun curr next pc -> not_impl "class_expr" pc z ]
;

value method_or_method_virtual pc virt priv s t =
  horiz_vertic
    (fun () ->
       sprintf "%smethod%s%s %s : %s%s" pc.bef virt
         (if priv then " private" else "") s
         (ctyp {(pc) with bef = ""; aft = ""} t) pc.aft)
    (fun () ->
       let s1 =
         sprintf "%smethod%s%s %s:" pc.bef virt
           (if priv then " private" else "") s
       in
       let s2 =
         ctyp {(pc) with ind = pc.ind + 2; bef = tab (pc.ind + 2)} t
       in
       sprintf "%s\n%s" s1 s2)
;

value class_sig_item_top =
  extfun Extfun.empty with
  [ <:class_sig_item< inherit $ct$ >> ->
      fun curr next pc ->
        horiz_vertic
          (fun () ->
             sprintf "%sinherit %s%s" pc.bef
               (class_type {(pc) with bef = ""; aft = ""} ct) pc.aft)
          (fun () -> not_impl "class_sig_item inherit vertic" pc ct)
  | <:class_sig_item< method $opt:priv$ $s$ : $t$ >> ->
      fun curr next pc ->
        method_or_method_virtual pc "" priv s t
  | <:class_sig_item< method virtual $opt:priv$ $s$ : $t$ >> ->
      fun curr next pc ->
        method_or_method_virtual pc " virtual" priv s t
  | <:class_sig_item< value $opt:mf$ $s$ : $t$ >> ->
      fun curr next pc ->
        horiz_vertic
          (fun () ->
             sprintf "%svalue%s %s : %s%s" pc.bef
               (if mf then " mutable" else "")
               (var_escaped {(pc) with bef = ""; aft = ""} s)
               (ctyp {(pc) with bef = ""; aft = ""} t) pc.aft)
          (fun () ->
             let s1 =
               sprintf "%svalue%s %s :" pc.bef (if mf then " mutable" else "")
                 (var_escaped {(pc) with bef = ""; aft = ""} s)
             in
             let s2 =
               ctyp {(pc) with ind = pc.ind + 2; bef = tab (pc.ind + 2)} t
             in
             sprintf "%s\n%s" s1 s2) 
  | z -> fun curr next pc -> not_impl "class_sig_item" pc z ]
;

value class_str_item_top =
  extfun Extfun.empty with
  [ <:class_str_item< inherit $ce$ $opt:pb$ >> ->
      fun curr next pc ->
        horiz_vertic
          (fun () ->
             sprintf "%sinherit %s%s%s" pc.bef
               (class_expr {(pc) with bef = ""; aft = ""} ce)
               (match pb with
                [ Some s -> sprintf " as %s" s
                | None -> "" ]) pc.aft)
          (fun () -> not_impl "inherit vertic" pc ce)
  | <:class_str_item< initializer $e$ >> ->
      fun curr next pc ->
        horiz_vertic
          (fun () ->
             sprintf "%sinitializer %s%s" pc.bef
               (expr {(pc) with bef = ""; aft = ""} e) pc.aft)
          (fun () ->
             let s1 = sprintf "%sinitializer" pc.bef in
             let s2 =
               expr {(pc) with ind = pc.ind + 2; bef = tab (pc.ind + 2)} e
             in
             sprintf "%s\n%s" s1 s2)
  | <:class_str_item< method virtual $opt:priv$ $s$ : $t$ >> ->
      fun curr next pc ->
        horiz_vertic
          (fun () ->
             sprintf "%smethod virtual%s %s : %s%s" pc.bef
               (if priv then " private" else "") s
               (ctyp {(pc) with bef = ""; aft = ""} t) pc.aft)
          (fun () ->
             let s1 =
               horiz_vertic
                 (fun () ->
                    sprintf "%smethod virtual%s %s :" pc.bef
                      (if priv then " private" else "") s)
                 (fun () -> not_impl "method vertic 2" pc s)
             in
             let s2 =
               ctyp {(pc) with ind = pc.ind + 2; bef = tab (pc.ind + 2)} t
             in
             sprintf "%s\n%s" s1 s2)
  | <:class_str_item< method $opt:priv$ $s$ $opt:topt$ = $e$ >> ->
      fun curr next pc ->
        horiz_vertic
          (fun () ->
             sprintf "%smethod%s %s%s = %s%s" pc.bef
               (if priv then " private" else "") s
               (match topt with
                [ Some t ->
                    sprintf " : %s" (ctyp {(pc) with bef = ""; aft = ""} t)
                | None -> "" ])
               (expr {(pc) with bef = ""; aft = ""} e) pc.aft)
          (fun () ->
             let s1 =
               match topt with
               [ None ->
                   sprintf "%smethod%s %s =" pc.bef
                     (if priv then " private" else "") s
               | Some t ->
                   horiz_vertic
                     (fun () ->
                        sprintf "%smethod%s %s : %s =" pc.bef
                          (if priv then " private" else "") s
                          (ctyp {(pc) with bef = ""; aft = ""} t))
                     (fun () ->
                        let s1 =
                          sprintf "%smethod%s %s :" pc.bef
                            (if priv then " private" else "") s
                        in
                        let s2 =
                          ctyp
                            {(pc) with ind = pc.ind + 4;
                             bef = tab (pc.ind + 4); aft = " ="}
                            t
                        in
                        sprintf "%s\n%s" s1 s2) ]
             in
             let s2 =
               expr {(pc) with ind = pc.ind + 2; bef = tab (pc.ind + 2)} e
             in
             sprintf "%s\n%s" s1 s2)
  | <:class_str_item< type $t1$ = $t2$ >> ->
      fun curr next pc ->
        horiz_vertic
          (fun () ->
             sprintf "%stype %s = %s%s" pc.bef
               (ctyp {(pc) with bef = ""; aft = ""} t1)
               (ctyp {(pc) with bef = ""; aft = ""} t2) pc.aft)
          (fun () -> not_impl "class_str_item type vertic" pc t1)
  | <:class_str_item< value $opt:mf$ $s$ = $e$ >> ->
      fun curr next pc ->
        horiz_vertic
          (fun () ->
             sprintf "%sval%s %s = %s%s" pc.bef
               (if mf then " mutable" else "") s
               (expr {(pc) with bef = ""; aft = ""} e) pc.aft)
          (fun () ->
             let s1 =
               sprintf "%sval%s %s =" pc.bef (if mf then " mutable" else "")
                 s
             in
             let s2 =
               expr {(pc) with ind = pc.ind + 2; bef = tab (pc.ind + 2)} e
             in
             sprintf "%s\n%s" s1 s2)
  | z -> fun curr next pc -> not_impl "class_str_item" pc z ]
;

value ctyp_as =
  extfun Extfun.empty with
  [ <:ctyp< $t1$ as $t2$ >> ->
      fun curr next pc ->
        horiz_vertic
          (fun () ->
             sprintf "%s%s as %s%s" pc.bef
               (curr {(pc) with bef = ""; aft = ""} t1)
               (next {(pc) with bef = ""; aft = ""} t2) pc.aft)
          (fun () -> not_impl "ctyp as vertic" pc t1)
  | z -> fun curr next pc -> next pc z ]
;

value ctyp_poly =
  extfun Extfun.empty with
  [ <:ctyp< ! $list:pl$ . $t$ >> ->
      fun curr next pc ->
        horiz_vertic
          (fun () ->
             sprintf "%s! %s . %s%s" pc.bef
               (hlist typevar {(pc) with bef = ""; aft = ""} pl)
               (ctyp {(pc) with bef = ""; aft = ""} t) pc.aft)
          (fun () ->
             let s1 =
               sprintf "%s! %s ." pc.bef
                 (hlist typevar {(pc) with bef = ""; aft = ""} pl)
             in
             let s2 =
               ctyp {(pc) with ind = pc.ind + 2; bef = tab (pc.ind + 2)} t
             in
             sprintf "%s\n%s" s1 s2)
  | z -> fun curr next pc -> next pc z ]
;

pr_expr.pr_levels :=
  [find_pr_level "top" pr_expr.pr_levels;
   find_pr_level "expr1" pr_expr.pr_levels;
   find_pr_level "tuple" pr_expr.pr_levels;
   find_pr_level "assign" pr_expr.pr_levels;
   find_pr_level "bar" pr_expr.pr_levels;
   find_pr_level "amp" pr_expr.pr_levels;
   find_pr_level "less" pr_expr.pr_levels;
   find_pr_level "concat" pr_expr.pr_levels;
   find_pr_level "cons" pr_expr.pr_levels;
   find_pr_level "add" pr_expr.pr_levels;
   find_pr_level "mul" pr_expr.pr_levels;
   find_pr_level "pow" pr_expr.pr_levels;
   find_pr_level "unary" pr_expr.pr_levels;
   find_pr_level "apply" pr_expr.pr_levels;
   {pr_label = "label"; pr_rules = expr_label};
   find_pr_level "dot" pr_expr.pr_levels;
   find_pr_level "simple" pr_expr.pr_levels]
;

pr_ctyp.pr_levels :=
  [find_pr_level "top" pr_ctyp.pr_levels;
   {pr_label = "as"; pr_rules = ctyp_as};
   {pr_label = "poly"; pr_rules = ctyp_poly};
   find_pr_level "arrow" pr_ctyp.pr_levels;
   find_pr_level "star" pr_ctyp.pr_levels;
   find_pr_level "apply" pr_ctyp.pr_levels;
   find_pr_level "dot" pr_ctyp.pr_levels;
   find_pr_level "simple" pr_ctyp.pr_levels]
;

pr_class_expr.pr_levels :=
  [{pr_label = "top"; pr_rules = class_expr_top};
   {pr_label = "apply"; pr_rules = class_expr_apply};
   {pr_label = "simple"; pr_rules = class_expr_simple}]
;

pr_class_type.pr_levels :=
  [{pr_label = "top"; pr_rules = class_type_top}]
;

pr_class_sig_item.pr_levels :=
  [{pr_label = "top"; pr_rules = class_sig_item_top}]
;

pr_class_str_item.pr_levels :=
  [{pr_label = "top"; pr_rules = class_str_item_top}]
;
