(* camlp5r pa_macro.cmo q_MLast.cmo ./pa_extfun.cmo ./pa_extprint.cmo *)
(* $Id: pr_o.ml,v 1.133 2007/12/23 12:17:23 deraugla Exp $ *)
(* Copyright (c) INRIA 2007 *)

open Pretty;
open Pcaml;
open Prtools;

value flag_comments_in_phrases = ref True;
value flag_equilibrate_cases = Pcaml.flag_equilibrate_cases;
value flag_horiz_let_in = ref True;
value flag_semi_semi = ref False;

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

(**)
value test = ref False;
Pcaml.add_option "-test" (Arg.Set test) " test";
(**)

value not_impl name pc x =
  let desc =
    if Obj.tag (Obj.repr x) = Obj.tag (Obj.repr "") then
      "\"" ^ Obj.magic x ^ "\""
    else if Obj.is_block (Obj.repr x) then
      "tag = " ^ string_of_int (Obj.tag (Obj.repr x))
    else "int_val = " ^ string_of_int (Obj.magic x)
  in
  pprintf pc "\"pr_o, not impl: %s; %s\"" name (String.escaped desc)
;

value var_escaped pc v =
  let x =
    if v.[0] = '*' || v.[String.length v - 1] = '*' then "( " ^ v ^ " )"
    else if is_infix v || has_special_chars v then "(" ^ v ^ ")"
    else v
  in
  pprintf pc "%s" x
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
  pprintf pc "%s" x
;

value rec mod_ident pc sl =
  match sl with
  [ [] -> pprintf pc ""
  | [s] -> var_escaped pc s
  | [s :: sl] -> pprintf pc "%s.%p" s mod_ident sl ]
;

value comma_after elem pc x = pprintf pc "%p," elem x;
value semi_after elem pc x = pprintf pc "%q;" elem x ";";
value semi_semi_after elem pc x = pprintf pc "%p;;" elem x;
value star_after elem pc x = pprintf pc "%p *" elem x;
value op_after elem pc (x, op) = pprintf pc "%p%s" elem x op;

value and_before elem pc x = pprintf pc "and %p" elem x;
value bar_before elem pc x = pprintf pc "| %p" elem x;
value star_before elem pc x = pprintf pc "* %p" elem x;

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

value expr = Eprinter.apply pr_expr;
value patt = Eprinter.apply pr_patt;
value ctyp = Eprinter.apply pr_ctyp;
value str_item = Eprinter.apply pr_str_item;
value sig_item = Eprinter.apply pr_sig_item;
value module_expr = Eprinter.apply pr_module_expr;
value module_type = Eprinter.apply pr_module_type;
value expr_fun_args ge = Extfun.apply pr_expr_fun_args.val ge;

value expr1 = Eprinter.apply_level pr_expr "expr1";

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
  [ <:patt< ($x$ as $y$) >> ->
      pprintf pc "%p as %s" patt x (patt {(pc) with bef = ""; aft = ""} y)
  | z -> patt pc z ]
;

(* utilities specific to pr_o *)

(* Basic displaying of a 'binding' (let, value, expr or patt record field).
   The pretty printing is done correctly, but there are no syntax shortcuts
   (e.g. "let f = fun x -> y" is *not* shortened as "let f x = y")

   Some functions follow (some of them with '_binding' in their name) which
   use syntax or pretty printing shortcuts.
*)
value binding elem pc (p, e) = pprintf pc "%p =@;%p" patt p elem e;

value record_binding is_last pc (p, e) =
  pprintf pc "%p =@;%q" patt p expr1 e (if is_last then pc.dang else ";")
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

value expr_semi pc (e, is_last) =
  let (pc_aft, pc_dang) =
    if not is_last then (";", ";") else (pc.aft, pc.dang)
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
        let f x y = (e : t)
     is displayed:
        let f x y : t = e
   Cancellation of all these improvements could be done by changing calls
   to this function to a call to "binding expr" above.
*)
value let_binding pc (p, e) =
  let (pl, e) =
    match p with
    [ <:patt< ($_$ : $_$) >> -> ([], e)
    | _ -> expr_fun_args e ]
  in
  let pl = [p :: pl] in
  let (e, tyo) =
    match (p, e) with
    [ (<:patt< $lid:_$ >>, <:expr< ($e$ : $t$) >>) -> (e, Some t)
    | _ -> (e, None) ]
  in
  let simple_patt = Eprinter.apply_level pr_patt "simple" in
  let patt_tycon tyo pc p =
    match tyo with
    [ Some t -> pprintf pc "%p : %p" simple_patt p ctyp t
    | None -> simple_patt pc p ]
  in
  let pl = List.map (fun p -> (p, "")) pl in
  let pc = {(pc) with dang = ""} in
  match pc.aft with
  [ "" ->
      pprintf pc "%p =@;%q"
        (plistl simple_patt (patt_tycon tyo) 4) pl
        expr_with_comm_except_if_sequence e ""
  | "in" ->
      pprintf pc "@[<a>%p =@;%q@ @]"
        (plistl simple_patt (patt_tycon tyo) 4) pl
        expr_with_comm_except_if_sequence e ""
  | _ ->
      pprintf pc "@[<a>%p =@;%q@;<0 0>@]"
        (plistl simple_patt (patt_tycon tyo) 4) pl
        expr_with_comm_except_if_sequence e "" ]
;

value match_assoc force_vertic pc ((p, w, e), is_last) =
  let (pc_aft, pc_dang) =
    if not is_last then ("", "|") else (pc.aft, pc.dang)
  in
  horiz_vertic
    (fun () ->
       if force_vertic then sprintf "\n"
       else
         pprintf pc "%p%p -> %q" patt_as p
           (fun pc ->
              fun
              [ <:vala< Some e >> -> pprintf pc " when %p" expr e
              | _ -> pprintf pc "" ])
           w
           (comm_expr expr) e pc_dang)
    (fun () ->
       pprintf pc "%p@;%q"
         (fun pc ->
            fun
            [ <:vala< Some e >> ->
                pprintf pc "%p@ @[when@;%p ->@]" patt_as p expr e
            | _ ->
                pprintf pc "%p ->" patt_as p ])
         w expr_with_comm_except_if_sequence e pc_dang)
;

value match_assoc_sh force_vertic pc pwe =
  match_assoc force_vertic {(pc) with ind = pc.ind + 2} pwe
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
                      bar_before (match_assoc_sh False) pc (pwe, False)
                    in
                    False)
                 (fun () -> True))
            pwel
        in
        has_vertic
      else False
    in
    pprintf pc "  %p"
      (vlist3 (match_assoc_sh force_vertic)
         (bar_before (match_assoc_sh force_vertic)))
      pwel
;

value raise_match_failure pc loc =
  let (fname, line, char, _) =
    if Pcaml.input_file.val <> "-" then
      Ploc.from_file Pcaml.input_file.val loc
    else
      ("-", 1, Ploc.first_pos loc, 0)
  in
  let e =
    <:expr<
      raise
        (Match_failure
           ($str:fname$, $int:string_of_int line$, $int:string_of_int char$))
    >>
  in
  Eprinter.apply_level pr_expr "apply" pc e
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

value type_params pc tvl =
  match tvl with
  [ [] -> pprintf pc ""
  | [tv] -> pprintf pc "%p " type_var tv
  | _ -> pprintf pc "(%p) " (hlistl (comma_after type_var) type_var) tvl ]
;

value mem_tvar s tpl = List.exists (fun (t, _) -> Pcaml.unvala t = s) tpl;

value type_decl pc td =
  let ((_, tn), tp, pf, te, cl) =
    (td.MLast.tdNam, td.MLast.tdPrm, td.MLast.tdPrv, td.MLast.tdDef,
     td.MLast.tdCon)
  in
  match te with
  [ <:ctyp< '$s$ >> when not (mem_tvar s (Pcaml.unvala tp)) ->
      pprintf pc "%p%p" type_params  (Pcaml.unvala tp)
        var_escaped (Pcaml.unvala tn)
  | _ ->
      if pc.aft = "" then
        pprintf pc "%p%p =@;%p%p" type_params (Pcaml.unvala tp)
          var_escaped (Pcaml.unvala tn) ctyp te
          (hlist type_constraint) (Pcaml.unvala cl)
      else
        horiz_vertic
          (fun () ->
             pprintf pc "%p%p = %p%p" type_params (Pcaml.unvala tp)
               var_escaped (Pcaml.unvala tn) ctyp te
               (hlist type_constraint) (Pcaml.unvala cl))
          (fun () ->
             pprintf pc "@[<a>%p%p =@;%p%p@ @]" type_params (Pcaml.unvala tp)
               var_escaped (Pcaml.unvala tn) ctyp te
               (hlist type_constraint) (Pcaml.unvala cl)) ]
;

value label_decl pc (_, l, m, t) =
  pprintf pc "%s%s :@;%p" (if m then "mutable " else "") l ctyp t
;

value cons_decl pc (_, c, tl) =
  let c = Pcaml.unvala c in
  let tl = Pcaml.unvala tl in
  if tl = [] then cons_escaped pc c
  else
    let ctyp_apply = Eprinter.apply_level pr_ctyp "apply" in
    let tl = List.map (fun t -> (t, " *")) tl in
    pprintf pc "%p of@;<1 4>%p" cons_escaped c (plist ctyp_apply 2) tl
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

value flatten_sequ e =
  let rec get_sequence =
    fun
    [ <:expr< do { $list:el$ } >> -> Some el
    | _ -> None ]
  in
  match get_sequence e with
  [ Some el ->
      let rec list_of_sequence =
        fun
        [ [e :: el] ->
            match get_sequence e with
            [ Some el1 -> list_of_sequence (el1 @ el)
            | None -> [e :: list_of_sequence el] ]
        | [] -> [] ]
      in
      Some (list_of_sequence el)
  | None -> None ]
;

value string pc s = pprintf pc "\"%s\"" s;

value external_decl pc (n, t, sl) =
  pprintf pc "external %p :@;%p@[ = %p@]" var_escaped n ctyp t
    (hlist string) sl
;

value exception_decl pc (e, tl, id) =
  let ctyp_apply = Eprinter.apply_level pr_ctyp "apply" in
  match id with
  [ [] ->
      match tl with
      [ [] -> pprintf pc "exception %s" e
      | tl ->
          let tl = List.map (fun t -> (t, " *")) tl in
          pprintf pc "exception %s of@;%p" e (plist ctyp_apply 2) tl ]
  | id ->
      match tl with
      [ [] -> pprintf pc "exception %s =@;%p" e mod_ident id
      | tl ->
          let tl = List.map (fun t -> (t, " *")) tl in
          pprintf pc "exception %s of@;%p =@;%p" e
            (plist ctyp_apply 2) tl mod_ident id ] ]
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
  if pc.aft = "" then
    match mto with
    [ Some mt ->
        pprintf pc "%s %s%s%p :@;%p =@;%p" pref m
          (if mal = [] then "" else " ") (hlist module_arg) mal
          module_type mt module_expr me
    | None ->
        let mal = List.map (fun ma -> (ma, "")) mal in
        pprintf pc "%s %s%p =@;%p" pref m (plistb module_arg 2) mal
          module_expr me ]
  else
    match mto with
    [ Some mt ->
        pprintf pc "%s %s%s%p :@;%p =@;%p@;<0 0>" pref m
          (if mal = [] then "" else " ") (hlist module_arg) mal
          module_type mt module_expr me
    | None ->
        let mal = List.map (fun ma -> (ma, "")) mal in
        pprintf pc "@[<a>%s %s%p =@;%p@;<0 0>@]" pref m (plistb module_arg 2)
          mal module_expr me ]
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
  match mt with
  [ <:module_type< ' $s$ >> ->
      pprintf pc "%s %s%s%p" pref m (if mal = [] then "" else " ")
        (hlist module_arg) mal
  | _ ->
      let mal = List.map (fun ma -> (ma, "")) mal in
      if pc.aft = "" then
        pprintf pc "%s %s%p %c@;%p" pref m
          (plistb module_arg 2) mal defc module_type mt
      else
        pprintf pc "@[<a>%s %s%p %c@;%p@;<0 0>@]" pref m
          (plistb module_arg 2) mal defc module_type mt ]
;

value str_or_sig_functor pc s mt module_expr_or_type met =
  pprintf pc "functor@;@[(%s :@;<1 1>%p)@]@ ->@;%p" s module_type mt
    module_expr_or_type met
;

value with_constraint pc wc =
  match wc with
  [ <:with_constr< type $sl$ $list:tpl$ = $flag:pf$ $t$ >> ->
      pprintf pc "with type %p%p =%s %p" mod_ident sl (hlist type_var) tpl
        (if pf then " private" else "") ctyp t
  | <:with_constr< module $sl$ = $me$ >> ->
      pprintf pc "with module %p = %p" mod_ident sl module_expr me
  | IFDEF STRICT THEN
      x -> not_impl "with_constraint" pc x
    END ]
;

EXTEND_PRINTER
  pr_expr:
    [ "top"
      [ <:expr< do { $list:el$ } >> as ge ->
          let el =
            match flatten_sequ ge with
            [ Some el -> el
            | None -> el ]
          in
          horiz_vertic
            (fun () ->
               pprintf pc "%p"
                 (hlistl (semi_after (comm_expr expr)) (comm_expr expr)) el)
            (fun () ->
               vlist3 expr_semi expr_semi pc el) ]
    | "expr1"
      [ <:expr< if $e1$ then $e2$ else $e3$ >> as ge ->
          horiz_vertic
            (fun () ->
               match e3 with
               [ <:expr< () >> ->
                   if pc.dang = "else" then next pc ge
                   else pprintf pc "if %q then %p" curr e1 "" curr e2
               | _ ->
                   pprintf pc "if %q then %q else %p" curr e1 "" curr e2 ""
                     curr e3 ])
            (fun () ->
               let if_then force_vertic pc else_b e1 e2 =
                 horiz_vertic
                   (fun () ->
                      if force_vertic then sprintf "\n"
                      else
                        pprintf pc "%sif %q then %p" else_b curr e1 ""
                          curr e2)
                   (fun () ->
                      if else_b = "" then
                        pprintf pc "@[<3>%sif %q@]@ then@;%p" else_b
                          curr e1 "" (comm_expr expr1) e2
                      else
                        pprintf pc "@[<a>%sif@;%q@ then@]@;%p" else_b
                          curr e1 "" (comm_expr expr1) e2)
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
                            let pc = {(pc) with bef = tab pc.ind} in
                            pprintf pc "else %p" (comm_expr curr) e3
                          in
                          False)
                       (fun () -> True)
                   in
                   (has_vertic, eel, e3)
                 else
                   let (eel, e3) = get_else_if e3 in
                   (False, eel, e3)
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
                     if_then force_vertic
                       {(pc) with aft = pc_aft; dang = pc_dang} "" e1 e2
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
                             (if_then force_vertic
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
                           let pc = {(pc) with bef = tab pc.ind} in
                           pprintf pc "else@;%p" (comm_expr curr) e3
                         in
                         sprintf "\n%s" s ]
                   in
                   sprintf "%s%s%s" s1 s2 s3 ])
      | <:expr< fun [ $list:pwel$ ] >> as ge ->
          match pwel with
          [ [(p1, <:vala< None >>, e1)] when is_irrefut_patt p1 ->
              let (pl, e1) = expr_fun_args e1 in
              let pl = [p1 :: pl] in
              let simple_patt = Eprinter.apply_level pr_patt "simple" in
              let pl = List.map (fun p -> (p, "")) pl in
              if List.mem pc.dang ["|"; ";"] then
                pprintf pc "(fun %p ->@;<1 3>%q)" (plist simple_patt 4) pl
                  expr e1 ""
              else
                pprintf pc "fun %p ->@;%p" (plist simple_patt 4) pl expr e1
          | [] ->
              let loc = MLast.loc_of_expr ge in
              if List.mem pc.dang ["|"; ";"] then
                pprintf pc "(fun _ ->@;%p)" raise_match_failure loc
              else
                pprintf pc "fun _ ->@;%p" raise_match_failure loc
          | pwel ->
              if List.mem pc.dang ["|"; ";"] then
                pprintf pc "@[<1>(function@ %p)@]"match_assoc_list pwel
              else
                pprintf pc "@[<b>function@ %p@]" match_assoc_list pwel ]
      | <:expr< try $e1$ with [ $list:pwel$ ] >> |
        <:expr< match $e1$ with [ $list:pwel$ ] >> as e ->
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
                     if List.mem pc.dang ["|"; ";"] then
                       (sprintf "(%s" op, ")")
                     else (op, "")
                   in
                   sprintf "%s%s %s with %s%s%s" pc.bef op_begin
                     (expr {(pc) with bef = ""; aft = ""; dang = ""} e1)
                     (match_assoc False {(pc) with bef = ""; aft = ""}
                        ((p, wo, e), True))
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
                               (expr {(pc) with bef = ""; aft = ""; dang = ""}
                                  e1)))
                       (fun () -> None)
                   with
                   [ Some s1 ->
                       let s2 =
                         match_assoc False
                           {(pc) with ind = pc.ind + 2;
                            bef = tab (pc.ind + 2); aft = pc_aft}
                           ((p, wo, e), True)
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
                         match_assoc False
                           {(pc) with bef = sprintf "%swith " (tab pc.ind);
                            aft = pc_aft}
                           ((p, wo, e), True)
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
      | <:expr< let $flag:rf$ $list:pel$ in $e$ >> ->
          horiz_vertic
            (fun () ->
               if not flag_horiz_let_in.val then sprintf "\n"
               else
                 let (begin_op, pc_dang, end_op) =
                   if pc.dang = ";" then ("(", "", ")")
                   else ("", pc.dang, "")
                 in
                 sprintf "%s%slet %s%s %s%s%s" pc.bef begin_op
                   (if rf then "rec " else "")
                   (hlist2 let_binding (and_before let_binding)
                      {(pc) with bef = ""; aft = "in"; dang = ""} pel)
                   (expr {(pc) with bef = ""; aft = ""; dang = pc_dang} e)
                   end_op pc.aft)
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
                    aft = "in"; dang = ""}
                   pel
               in
               let s2 =
                 expr_with_comm_except_if_sequence
                   {ind = ind; bef = tab ind; aft = pc_aft; dang = pc_dang} e
               in
               let s3 = end_op in
               sprintf "%s\n%s%s" s1 s2 s3)
      | <:expr< let module $uid:s$ = $me$ in $e$ >> ->
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
      | <:expr< for $lid:v$ = $e1$ $to:d$ $e2$ do { $list:el$ } >> ->
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
               sprintf "%s\n%s\n%s" s1 s2 s3) ]
    | "tuple"
      [ <:expr< ($list:el$) >> ->
          let el = List.map (fun e -> (e, ",")) el in
          plist next 0 pc el ]
    | "assign"
      [ <:expr< $x$.val := $y$ >> -> operator pc next expr 2 ":=" x y
      | <:expr< $x$ := $y$ >> -> operator pc next expr 2 "<-" x y ]
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
    | "cons"
      [ <:expr< [$_$ :: $_$] >> as z ->
          let (xl, y) = make_expr_list z in
          match y with
          [ Some y ->
              let xl = List.map (fun x -> (x, " ::")) (xl @ [y]) in
              plist next 0 pc xl
          | None -> next pc z ] ]
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
      [ <:expr< ~- $x$ >> -> curr {(pc) with bef = sprintf "%s-" pc.bef} x
      | <:expr< ~-. $x$ >> -> curr {(pc) with bef = sprintf "%s-." pc.bef} x
      | <:expr< $int:i$ >> -> sprintf "%s%s%s" pc.bef i pc.aft ]
    | "apply"
      [ <:expr< assert $e$ >> ->
          pprintf pc "assert@;%p" next e
      | <:expr< lazy $e$ >> ->
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
                let expr_or = Eprinter.apply_level pr_expr "or" in
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
                left_operator pc 2 unfold next z ] ]
    | "dot"
      [ <:expr< $x$ . val >> -> next {(pc) with bef = sprintf "%s!" pc.bef} x
      | <:expr< $x$ . $y$ >> ->
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
          expr
            {(pc) with bef = curr {(pc) with aft = ".("} x;
             aft = sprintf ")%s" pc.aft}
            y
      | <:expr< $x$ .[ $y$ ] >> ->
          expr_short
            {(pc) with bef = curr {(pc) with aft = ".["} x;
             aft = (sprintf "]%s" pc.aft)}
            y
      | <:expr< $e$ .{ $list:el$ } >> ->
          let el = List.map (fun e -> (e, ",")) el in
          plist expr_short 0
            {(pc) with bef = curr {(pc) with aft = ".{"} e;
             aft = (sprintf "}%s" pc.aft)}
            el ]
    | "simple"
      [ <:expr< {$list:lel$} >> ->
          let lxl = List.map (fun lx -> (lx, ";")) lel in
          plistl (comm_patt_any (record_binding False))
            (comm_patt_any (record_binding True)) 0
            {(pc) with ind = pc.ind + 1; bef = sprintf "%s{" pc.bef;
             aft = (sprintf "}%s" pc.aft)}
            lxl
      | <:expr< {($e$) with $list:lel$} >> ->
          let lxl = List.map (fun lx -> (lx, ";")) lel in
          let dot_expr = Eprinter.apply_level pr_expr "dot" in
          plistl (record_binding False) (record_binding True) 0
            {(pc) with ind = pc.ind + 1;
             bef =
               dot_expr
                 {(pc) with bef = sprintf "%s{" pc.bef; aft = " with "} e;
             aft = (sprintf "}%s" pc.aft)} lxl
      | <:expr< [| $list:el$ |] >> ->
          if el = [] then sprintf "%s[| |]%s" pc.bef pc.aft
          else
            let el = List.map (fun e -> (e, ";")) el in
            plist expr 0
              {(pc) with ind = pc.ind + 3; bef = sprintf "%s[| " pc.bef;
               aft = (sprintf " |]%s" pc.aft)}
              el
      | <:expr< [$_$ :: $_$] >> as z ->
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
          if String.length s > 0 && s.[0] = '-' then
            sprintf "%s(%s)%s" pc.bef s pc.aft
          else
            sprintf "%s%s%s" pc.bef s pc.aft
      | <:expr< $int32:s$ >> ->
          let s = s ^ "l" in
          if String.length s > 0 && s.[0] = '-' then
            sprintf "%s(%s)%s" pc.bef s pc.aft
          else
            sprintf "%s%s%s" pc.bef s pc.aft
      | <:expr< $int64:s$ >> ->
          let s = s ^ "L" in
          if String.length s > 0 && s.[0] = '-' then
            sprintf "%s(%s)%s" pc.bef s pc.aft
          else
            sprintf "%s%s%s" pc.bef s pc.aft
      | <:expr< $nativeint:s$ >> ->
          let s = s ^ "n" in
          if String.length s > 0 && s.[0] = '-' then
            sprintf "%s(%s)%s" pc.bef s pc.aft
          else
            sprintf "%s%s%s" pc.bef s pc.aft
      | <:expr< $lid:s$ >> -> var_escaped pc s
      | <:expr< $uid:s$ >> -> cons_escaped pc s
      | <:expr< `$s$ >> ->
          failwith "variants not pretty printed (in expr); add pr_ro.cmo"
      | <:expr< $str:s$ >> -> sprintf "%s\"%s\"%s" pc.bef s pc.aft
      | <:expr< $chr:s$ >> -> sprintf "%s'%s'%s" pc.bef (ocaml_char s) pc.aft
      | <:expr< ?$_$ >> | <:expr< ~$_$ >> | <:expr< ~$_$: $_$ >> ->
          failwith "labels not pretty printed (in expr); add pr_ro.cmo"
      | <:expr< do { $list:el$ } >> ->
          horiz_vertic
            (fun () ->
               sprintf "%sbegin %s end%s" pc.bef
                 (hlistl (semi_after (comm_expr expr1)) (comm_expr expr1)
                    {(pc) with bef = ""; aft = ""} el)
                 pc.aft)
            (fun () ->
               let s =
                 vlistl (semi_after (comm_expr expr1)) (comm_expr expr1)
                   {(pc) with ind = pc.ind + 2; bef = tab (pc.ind + 2);
                    aft = ""}
                  el
               in
               sprintf "%sbegin\n%s\n%send%s" pc.bef s (tab pc.ind) pc.aft)
      | <:expr< $_$ $_$ >> | <:expr< $_$ . $_$ >> | <:expr< $_$ .( $_$ ) >> |
        <:expr< $_$ .[ $_$ ] >> | <:expr< $_$ .{ $_$ } >> |
        <:expr< assert $_$ >> | <:expr< lazy $_$ >> | <:expr< ($list:_$) >> |
        <:expr< $_$ := $_$ >> | <:expr< fun [ $list:_$ ] >> |
        <:expr< if $_$ then $_$ else $_$ >> |
        <:expr< for $lid:_$ = $_$ $to:_$ $_$ do { $list:_$ } >> |
        <:expr< while $_$ do { $list:_$ } >> |
        <:expr< let $flag:_$ $list:_$ in $_$ >> |
        <:expr< match $_$ with [ $list:_$ ] >> |
        <:expr< try $_$ with [ $list:_$ ] >> as z ->
          expr
            {ind = pc.ind + 1; bef = sprintf "%s(" pc.bef;
             aft = sprintf ")%s" pc.aft; dang = ""}
            z ] ]
  ;
  pr_patt:
    [ "top"
      [ <:patt< ($x$ as $y$) >> ->
          horiz_vertic
            (fun () ->
               sprintf "%s%s as %s%s" pc.bef
                 (patt {(pc) with bef = ""; aft = ""} x)
                 (patt {(pc) with bef = ""; aft = ""} y) pc.aft)
            (fun () ->
               let s1 = patt {(pc) with aft = ""} x in
               let s2 =
                 patt {(pc) with bef = sprintf "%sas " (tab (pc.ind + 1))} y
               in
               sprintf "%s\n%s" s1 s2) ]
    | "or"
      [ <:patt< $_$ | $_$ >> as z ->
          let unfold =
            fun
            [ <:patt< $x$ | $y$ >> -> Some (x, " |", y)
            | _ -> None ]
          in
          left_operator pc 0 unfold next z ]
    | "tuple"
      [ <:patt< ($list:pl$) >> ->
          let pl = List.map (fun p -> (p, ",")) pl in
          plist next 0 pc pl ]
    | "range"
      [ <:patt< $x$ .. $y$ >> ->
          sprintf "%s..%s" (next {(pc) with aft = ""} x)
            (next {(pc) with bef = ""} y) ]
    | "cons"
      [ <:patt< [$_$ :: $_$] >> as z ->
          let (xl, y) = make_patt_list z in
          match y with
          [ Some y ->
              let xl = List.map (fun x -> (x, " ::")) (xl @ [y]) in
              plist next 0 {(pc) with ind = pc.ind + 1} xl
          | None -> next pc z ] ]
    | "apply"
      [ <:patt< $_$ $_$ >> as z ->
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
              let patt = Eprinter.apply_level pr_patt "range" in
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
                   sprintf "%s\n%s" s1 s2) ] ]
    | "dot"
      [ <:patt< $x$ . $y$ >> ->
          curr {(pc) with bef = curr {(pc) with aft = "."} x} y ]
    | "simple"
      [ <:patt< {$list:lpl$} >> ->
          let lxl = List.map (fun lx -> (lx, ";")) lpl in
          plist (binding patt) 0
            {(pc) with ind = pc.ind + 1; bef = sprintf "%s{" pc.bef;
             aft = sprintf "}%s" pc.aft}
            lxl
      | <:patt< [| $list:pl$ |] >> ->
          if pl = [] then sprintf "%s[| |]%s" pc.bef pc.aft
          else
            let pl = List.map (fun p -> (p, ";")) pl in
            plist patt 0
              {(pc) with ind = pc.ind + 3; bef = sprintf "%s[| " pc.bef;
               aft = (sprintf " |]%s" pc.aft)}
              pl
      | <:patt< [$_$ :: $_$] >> as z ->
          let (xl, y) = make_patt_list z in
          match y with
          [ Some  y ->
              patt
                {(pc) with ind = pc.ind + 1; bef = sprintf "%s(" pc.bef;
                 aft = sprintf ")%s" pc.aft}
                z
          | None ->
              let xl = List.map (fun x -> (x, ";")) xl in
              plist patt 0
                {(pc) with ind = pc.ind + 1; bef = sprintf "%s[" pc.bef;
                 aft = sprintf "]%s" pc.aft}
                xl ]
      | <:patt< ($p$ : $t$) >> ->
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
          if String.length s > 0 && s.[0] = '-' then
            sprintf "%s(%s)%s" pc.bef s pc.aft
          else
            sprintf "%s%s%s" pc.bef s pc.aft
      | <:patt< $int32:s$ >> ->
          let s = s ^ "l" in
          if String.length s > 0 && s.[0] = '-' then
            sprintf "%s(%s)%s" pc.bef s pc.aft
          else
            sprintf "%s%s%s" pc.bef s pc.aft
      | <:patt< $int64:s$ >> ->
          let s = s ^ "L" in
          if String.length s > 0 && s.[0] = '-' then
            sprintf "%s(%s)%s" pc.bef s pc.aft
          else
            sprintf "%s%s%s" pc.bef s pc.aft
      | <:patt< $nativeint:s$ >> ->
          let s = s ^ "n" in
          if String.length s > 0 && s.[0] = '-' then
            sprintf "%s(%s)%s" pc.bef s pc.aft
          else
            sprintf "%s%s%s" pc.bef s pc.aft
      | <:patt< $lid:s$ >> -> var_escaped pc s
      | <:patt< $uid:s$ >> -> cons_escaped pc s
      | <:patt< $chr:s$ >> -> sprintf "%s'%s'%s" pc.bef (ocaml_char s) pc.aft
      | <:patt< $str:s$ >> -> sprintf "%s\"%s\"%s" pc.bef s pc.aft
      | <:patt< _ >> -> sprintf "%s_%s" pc.bef pc.aft
      | <:patt< ?$_$ >> | <:patt< ? ($_$ $opt:_$) >> |
        <:patt< ?$_$: ($_$ $opt:_$) >> | <:patt< ~$_$ >> |
        <:patt< ~$_$: $_$ >> ->
          failwith "labels not pretty printed (in patt); add pr_ro.cmo"
      | <:patt< `$s$ >> ->
          failwith "polymorphic variants not pretty printed; add pr_ro.cmo"
      | <:patt< $_$ $_$ >> | <:patt< $_$ | $_$ >> | <:patt< $_$ .. $_$ >> |
        <:patt< ($list:_$) >> | <:patt< ($_$ as $_$) >> as z ->
          patt
            {(pc) with ind = pc.ind + 1; bef = sprintf "%s(" pc.bef;
             aft = sprintf ")%s" pc.aft}
            z ] ]
  ;
  pr_ctyp:
    [ "top"
      [ <:ctyp< $x$ == $y$ >> -> operator pc next next 2 "=" x y ]
    | "arrow"
      [ <:ctyp< $_$ -> $_$ >> as z ->
          let unfold =
            fun
            [ <:ctyp< $x$ -> $y$ >> -> Some (x, " ->", y)
            | _ -> None ]
          in
          right_operator pc 2 unfold next z ]
    | "star"
      [ <:ctyp< ($list:tl$) >> ->
          horiz_vertic
            (fun () ->
               sprintf "%s%s%s" pc.bef
                 (hlistl (star_after next) next {(pc) with bef = ""; aft = ""}
                    tl)
                 pc.aft)
            (fun () ->
               let tl = List.map (fun t -> (t, " *")) tl in
               plist next 2 pc tl) ]
    | "apply"
      [ <:ctyp< $_$ $_$ >> as z ->
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
                   sprintf "%s\n%s" s1 s2) ] ]
    | "dot"
      [ <:ctyp< $x$ . $y$ >> ->
            curr {(pc) with bef = curr {(pc) with aft = "."} x} y ]
    | "simple"
      [ <:ctyp< { $list:ltl$ } >> ->
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
          horiz_vertic
            (fun () ->
               if has_cons_with_params vdl then sprintf "\n"
               else hlist2 cons_decl (bar_before cons_decl) pc vdl)
            (fun () ->
               vlist2 cons_decl (bar_before cons_decl)
                 {(pc) with bef = sprintf "%s  " pc.bef} vdl)
      | <:ctyp< $lid:t$ >> ->
          var_escaped pc t
      | <:ctyp< $uid:t$ >> ->
          sprintf "%s%s%s" pc.bef t pc.aft
      | <:ctyp< ' $s$ >> ->
          var_escaped {(pc) with bef = sprintf "%s'" pc.bef} s
      | <:ctyp< _ >> ->
          sprintf "%s_%s" pc.bef pc.aft
      | <:ctyp< ?$_$: $_$ >> | <:ctyp< ~$_$: $_$ >> ->
          failwith "labels not pretty printed (in type); add pr_ro.cmo"
      | <:ctyp< [ = $list:_$ ] >> | <:ctyp< [ > $list:_$ ] >> |
        <:ctyp< [ < $list:_$ ] >> | <:ctyp< [ < $list:_$ > $list:_$ ] >> ->
          failwith "variants not pretty printed (in type); add pr_ro.cmo"
      | <:ctyp< $_$ $_$ >> | <:ctyp< $_$ -> $_$ >> | <:ctyp< ($list:_$) >>
        as z ->
          ctyp
            {(pc) with ind = pc.ind + 1; bef = sprintf "%s(" pc.bef;
             aft = sprintf ")%s" pc.aft}
            z ] ]
  ;
  pr_str_item:
    [ "top"
      [ <:str_item< # $lid:s$ $e$ >> ->
          expr
            {(pc) with bef = sprintf "%s(* #%s " pc.bef s;
             aft = sprintf "%s *)" pc.aft}
          e
      | <:str_item< declare $list:sil$ end >> ->
          if sil = [] then sprintf "%s(* *)" pc.bef
          else
            let str_item_sep =
              if flag_semi_semi.val then semi_semi_after str_item
              else str_item
            in
            vlistl str_item_sep str_item pc sil
      | <:str_item< exception $uid:e$ of $list:tl$ = $id$ >> ->
          exception_decl pc (e, tl, id)
      | <:str_item< external $lid:n$ : $t$ = $list:sl$ >> ->
          external_decl pc (n, t, sl)
      | <:str_item< include $me$ >> ->
          module_expr {(pc) with bef = sprintf "%sinclude " pc.bef} me
      | <:str_item< module $flag:rf$ $list:mdl$ >> ->
          let mdl = List.map (fun (m, mt) -> (Pcaml.unvala m, mt)) mdl in
          let rf = if rf then " rec" else "" in
          vlist2 (str_module ("module" ^ rf)) (str_module "and") pc
            mdl
      | <:str_item< module type $uid:m$ = $mt$ >> ->
          sig_module_or_module_type "module type" '=' pc (m, mt)
      | <:str_item< open $i$ >> ->
          mod_ident {(pc) with bef = sprintf "%sopen " pc.bef} i
      | <:str_item< type $list:tdl$ >> ->
          vlist2 type_decl (and_before type_decl)
            {(pc) with bef = sprintf "%stype " pc.bef} tdl
      | <:str_item< value $flag:rf$ $list:pel$ >> ->
          horiz_vertic
            (fun () ->
               sprintf "%slet %s%s" pc.bef (if rf then "rec " else "")
                 (hlist2 let_binding (and_before let_binding)
                    {(pc) with bef = ""} pel))
            (fun () ->
               vlist2 let_binding (and_before let_binding)
                 {(pc) with
                  bef = sprintf "%slet %s" pc.bef (if rf then "rec " else "")}
                  pel)
      | <:str_item< $exp:e$ >> ->
          if pc.aft = ";;" then expr pc e
          else
            horiz_vertic
              (fun () ->
                 sprintf "%slet _ = %s%s" pc.bef
                   (expr {(pc) with bef = ""; aft = ""} e) pc.aft)
              (fun () ->
                 let s =
                   expr
                     {(pc) with ind = pc.ind + 2; bef = tab (pc.ind + 2)} e
                 in
                 sprintf "%slet _ =\n%s" pc.bef s)
      | <:str_item< class type $list:_$ >> | <:str_item< class $list:_$ >> ->
          failwith "classes and objects not pretty printed; add pr_ro.cmo" ] ]
  ;
  pr_sig_item:
    [ "top"
      [ <:sig_item< exception $uid:e$ of $list:tl$ >> ->
          exception_decl pc (e, tl, [])
      | <:sig_item< external $lid:n$ : $t$ = $list:sl$ >> ->
          external_decl pc (n, t, sl)
      | <:sig_item< include $mt$ >> ->
          module_type {(pc) with bef = sprintf "%sinclude " pc.bef} mt
      | <:sig_item< declare $list:sil$ end >> ->
          if sil = [] then sprintf "%s(* *)" pc.bef
          else
            let sig_item_sep =
              if flag_semi_semi.val then semi_semi_after sig_item
              else sig_item
            in
            vlistl sig_item_sep sig_item pc sil
      | <:sig_item< module $flag:rf$ $list:mdl$ >> ->
          let mdl = List.map (fun (m, mt) -> (Pcaml.unvala m, mt)) mdl in
          let rf = if rf then " rec" else "" in
          vlist2 (sig_module_or_module_type ("module" ^ rf) ':')
            (sig_module_or_module_type "and" ':') pc mdl
      | <:sig_item< module type $uid:m$ = $mt$ >> ->
          sig_module_or_module_type "module type" '=' pc (m, mt)
      | <:sig_item< open $i$ >> ->
          mod_ident {(pc) with bef = sprintf "%sopen " pc.bef} i
      | <:sig_item< type $list:tdl$ >> ->
          vlist2 type_decl (and_before type_decl)
            {(pc) with bef = sprintf "%stype " pc.bef} tdl
      | <:sig_item< value $lid:s$ : $t$ >> ->
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
          failwith "classes and objects not pretty printed; add pr_ro.cmo" ] ]
  ;
  pr_module_expr:
    [ "top"
      [ <:module_expr< functor ($uid:s$ : $mt$) -> $me$ >> ->
          str_or_sig_functor pc s mt module_expr me
      | <:module_expr< struct $list:sil$ end >> ->
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
                 ("\n" ^ tab pc.ind) pc.aft) ]
    | "apply"
      [ <:module_expr< $x$ $y$ >> ->
          let mod_exp2 pc (is_first, me) =
            match me with
            [ <:module_expr< $uid:_$ >> | <:module_expr< $_$ . $_$ >>
              when not is_first ->
                next
                  {(pc) with bef = sprintf "%s(" pc.bef;
                   aft = sprintf ")%s" pc.aft}
                  me
            | _ -> next pc me ]
          in
          let (me, mel) =
            loop [(False, y)] x where rec loop mel =
              fun
              [ <:module_expr< $x$ $y$ >> -> loop [(False, y) :: mel] x
              | me -> ((True, me), mel) ]
          in
          horiz_vertic
            (fun () ->
               sprintf "%s%s%s" pc.bef
                 (hlist mod_exp2 {(pc) with bef = ""; aft = ""} [me :: mel])
                 pc.aft)
            (fun () ->
               let mel = List.map (fun me -> (me, "")) [me :: mel] in
               plist mod_exp2 2 pc mel) ]
    | "dot"
      [ <:module_expr< $x$ . $y$ >> ->
          curr {(pc) with bef = curr {(pc) with aft = "."} x} y ]
    | "simple"
      [ <:module_expr< $uid:s$ >> -> sprintf "%s%s%s" pc.bef s pc.aft
      | <:module_expr< ($me$ : $mt$) >> ->
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
          horiz_vertic
            (fun () ->
               sprintf "%s%s %s%s" pc.bef
                 (module_type {(pc) with bef = ""; aft = ""} mt)
                 (hlist with_constraint {(pc) with bef = ""; aft = ""} wcl)
                    pc.aft)
            (fun () ->
               let s1 = module_type {(pc) with aft = ""} mt in
               let s2 =
                 vlist with_constraint
                   {(pc) with ind = pc.ind + 2; bef = tab (pc.ind + 2)} wcl
               in
               sprintf "%s\n%s" s1 s2) ]
    | "dot"
      [ <:module_type< $x$ . $y$ >> ->
          curr {(pc) with bef = curr {(pc) with aft = "."} x} y ]
    | "simple"
      [ <:module_type< $uid:s$ >> -> sprintf "%s%s%s" pc.bef s pc.aft ] ]
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
           let k = if flag_semi_semi.val then ";;" else "" in
           output_string oc (f {ind = 0; bef = ""; aft = k; dang = ""} si);
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
          flag_equilibrate_cases.val := v;
          flag_horiz_let_in.val := v;
          flag_semi_semi.val := v;
        }
      | 'C' | 'c' -> flag_comments_in_phrases.val := is_uppercase s.[i]
      | 'E' | 'e' -> flag_equilibrate_cases.val := is_uppercase s.[i]
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
    sprintf "%s%s%s%s"
      (flag flag_comments_in_phrases.val "C" "c")
      (flag flag_equilibrate_cases.val "E" "e")
      (flag flag_horiz_let_in.val "L" "l")
      (flag flag_semi_semi.val "M" "m")
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
       E/e enable/disable equilibrate cases
       L/l enable/disable allowing printing 'let..in' horizontally
       M/m enable/disable printing double semicolons
       default setting is \"" ^ default_flag () ^ "\".");

Pcaml.add_option "-l" (Arg.Int (fun x -> Pretty.line_length.val := x))
  ("<length> Maximum line length for pretty printing (default " ^
     string_of_int Pretty.line_length.val ^ ")");

Pcaml.add_option "-sep_src" (Arg.Unit (fun () -> sep.val := None))
  "Read source file for text between phrases (default).";

Pcaml.add_option "-sep" (Arg.String (fun x -> sep.val := Some x))
  "<string> Use this string between phrases instead of reading source.";

Pcaml.add_option "-ss" (Arg.Set flag_semi_semi)
  "(obsolete since version 4.02; use rather \"-flag M\").";

Pcaml.add_option "-no_ss" (Arg.Clear flag_semi_semi)
  "(obsolete since version 4.02; use rather \"-flag m\").";

Pcaml.add_option "-cip" (Arg.Unit (fun x -> x))
  "(obsolete since version 4.02; use rather \"-flag C\")";

Pcaml.add_option "-ncip" (Arg.Unit (fun x -> x))
  "(obsolete since version 4.02; use rather \"-flag c\")";

(* Pretty printing extension for objects and labels *)

value class_expr = Eprinter.apply pr_class_expr;
value class_type = Eprinter.apply pr_class_type;
value class_str_item = Eprinter.apply pr_class_str_item;
value class_sig_item = Eprinter.apply pr_class_sig_item;

value amp_before elem pc x = elem {(pc) with bef = sprintf "%s& " pc.bef} x;

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
       sprintf "%s%s%s%s %c %s%s" pc.bef
         (if Pcaml.unvala ci.MLast.ciVir then " virtual" else "")
         (class_type_params {(pc) with bef = ""; aft = ""}
            (Pcaml.unvala (snd ci.MLast.ciPrm)))
         (Pcaml.unvala ci.MLast.ciNam) char
         (class_type {(pc) with bef = ""; aft = ""} ci.MLast.ciExp) pc.aft)
    (fun () ->
       let s1 =
         sprintf "%s%s%s%s %c" pc.bef
           (if Pcaml.unvala ci.MLast.ciVir then "virtual " else "")
           (class_type_params {(pc) with bef = ""; aft = ""}
              (Pcaml.unvala (snd ci.MLast.ciPrm)))
           (Pcaml.unvala ci.MLast.ciNam) char
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
            {(pc) with bef = ""; aft = ""} cd)
         pc.aft)
    (fun () ->
       vlist2 class_type_decl (and_before class_type_decl)
         {(pc) with bef = sprintf "%sclass type " pc.bef} cd)
;

value class_decl pc ci =
  let (pl, ce) =
    loop ci.MLast.ciExp where rec loop =
      fun
      [ <:class_expr< fun $p$ -> $ce$ >> as gce ->
          if is_irrefut_patt p then
            let (pl, ce) = loop ce in
            ([p :: pl], ce)
          else ([], gce)
      | ce -> ([], ce) ]
  in
  horiz_vertic
    (fun () ->
       sprintf "%s%s%s%s%s = %s%s" pc.bef
         (if Pcaml.unvala ci.MLast.ciVir then "virtual " else "")
         (class_type_params {(pc) with bef = ""; aft = ""}
            (Pcaml.unvala (snd ci.MLast.ciPrm)))
         (Pcaml.unvala ci.MLast.ciNam)
         (if pl = [] then "" else
          hlist patt {(pc) with bef = " "; aft = ""} pl)
         (class_expr {(pc) with bef = ""; aft = ""} ce) pc.aft)
    (fun () ->
       let s1 =
         sprintf "%s%s%s%s%s =" pc.bef
           (if Pcaml.unvala ci.MLast.ciVir then "virtual " else "")
           (class_type_params {(pc) with bef = ""; aft = ""}
              (Pcaml.unvala (snd ci.MLast.ciPrm)))
           (Pcaml.unvala ci.MLast.ciNam)
           (if pl = [] then ""
            else hlist patt {(pc) with bef = " "; aft = ""} pl)
       in
       let s2 =
         class_expr
           {(pc) with ind = pc.ind + 2; bef = tab (pc.ind + 2)} ce
       in
       sprintf "%s\n%s" s1 s2)
;

value variant_decl pc pv =
  match pv with
  [ <:poly_variant< `$c$ >> ->
       sprintf "%s`%s%s" pc.bef c pc.aft
  | <:poly_variant< `$c$ of $flag:ao$ $list:tl$ >> ->
       horiz_vertic
         (fun () ->
            sprintf "%s`%s of %s%s%s" pc.bef c (if ao then "& " else "")
              (hlist2 ctyp (amp_before ctyp)
                 {(pc) with bef = ""; aft = ""} tl) pc.aft)
         (fun () ->
            let s1 =
              sprintf "%s`%s of%s" pc.bef c (if ao then " &" else "")
            in
            let s2 =
               horiz_vertic
                 (fun () ->
                    sprintf "%s%s%s" (tab (pc.ind + 6))
                      (hlist2 ctyp (amp_before ctyp)
                         {(pc) with bef = ""; aft = ""} tl) pc.aft)
                 (fun () ->
                    let tl = List.map (fun t -> (t, " &")) tl in
                    plist ctyp 2
                      {(pc) with ind = pc.ind + 6; bef = tab (pc.ind + 5)} tl)
             in
             sprintf "%s\n%s" s1 s2)
  | <:poly_variant< $t$ >> ->
       ctyp pc t
  | IFDEF STRICT THEN
      _ -> failwith "Pr_ro.variant_decl"
    END ]
;

value variant_decl_list char pc pvl =
  if pvl = [] then sprintf "%s[%s ]%s" pc.bef char pc.aft
  else
    horiz_vertic
      (fun () ->
         hlist2 variant_decl (bar_before variant_decl)
           {(pc) with bef = sprintf "%s[%s " pc.bef char;
            aft = sprintf " ]%s" pc.aft}
           pvl)
      (fun () ->
         vlist2 variant_decl (bar_before variant_decl)
           {(pc) with bef = sprintf "%s[%s " (tab pc.ind) char;
            aft = sprintf " ]%s" pc.aft}
           pvl)
;

value rec class_longident pc cl =
  match cl with
  [ [] -> sprintf "%s%s" pc.bef pc.aft
  | [c] -> sprintf "%s%s%s" pc.bef c pc.aft
  | [c :: cl] ->
      sprintf "%s%s.%s" pc.bef c (class_longident {(pc) with bef = ""} cl) ]
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

EXTEND_PRINTER
  pr_patt: LEVEL "simple"
    [ [ <:patt< ?$s$ >> -> sprintf "%s?%s%s" pc.bef s pc.aft
      | <:patt< ? ($p$ $opt:eo$) >> ->
          match eo with
          [ Some e -> pprintf pc "?(%p =@;%p)" patt_tcon p expr e
          | None -> pprintf pc "?(%p)" patt_tcon p ]
      | <:patt< ?$i$: ($p$ $opt:eo$) >> ->
          match eo with
          [ Some e ->
              pprintf pc "?%s:@;<0 1>@[<1>(%p =@ %p)@]" i patt p expr e
          | None ->
              pprintf pc "?%s:@;<0 1>(%p)" i patt p ]
      | <:patt< ~$s$ >> ->
          sprintf "%s~%s%s" pc.bef s pc.aft
      | <:patt< ~$s$: $p$ >> ->
          curr {(pc) with bef = sprintf "%s~%s:" pc.bef s} p
      | <:patt< `$s$ >> ->
          sprintf "%s`%s%s" pc.bef s pc.aft
      | <:patt< # $list:sl$ >> ->
          mod_ident {(pc) with bef = sprintf "%s#" pc.bef} sl ] ]
  ;
  pr_expr: LEVEL "apply"
    [ [ <:expr< new $list:cl$ >> ->
          pprintf pc "new@;%p" class_longident cl
      | <:expr< object $opt:csp$ $list:csl$ end >> ->
          class_object pc (csp, csl) ] ]
  ;
  pr_expr: LEVEL "dot"
    [ [ <:expr< $e$ # $lid:s$ >> -> pprintf pc "%p#@;<0 0>%s" curr e s ] ]
  ;
  pr_expr: LEVEL "simple"
    [ [ <:expr< ( $e$ : $t$ :> $t2$ ) >> ->
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
          if fel = [] then sprintf "%s{< >}%s" pc.bef pc.aft
          else
            let fel = List.map (fun fe -> (fe, ";")) fel in
            plist field_expr 3
              {(pc) with bef = sprintf "%s{< " pc.bef;
               aft = sprintf " >}%s" pc.aft}
              fel
      | <:expr< `$s$ >> ->
          sprintf "%s`%s%s" pc.bef s pc.aft
      | <:expr< new $list:_$ >> | <:expr< object $list:_$ end >> as z ->
          expr
            {(pc) with ind = pc.ind + 1; bef = sprintf "%s(" pc.bef;
             aft = sprintf ")%s" pc.aft}
            z ] ]
  ;
  pr_ctyp: LEVEL "simple"
    [ [ <:ctyp< < $list:ml$ $flag:v$ > >> ->
          if ml = [] then
            sprintf "%s<%s >%s" pc.bef (if v then " .." else "") pc.aft
          else
            let ml = List.map (fun e -> (e, ";")) ml in
            plist field 0
              {(pc) with ind = pc.ind + 2; bef = sprintf "%s< " pc.bef;
               aft = sprintf "%s >%s" (if v then "; .." else "") pc.aft}
              ml
      | <:ctyp< # $list:id$ >> ->
          class_longident {(pc) with bef = sprintf "%s#" pc.bef}  id
      | <:ctyp< [ = $list:pvl$ ] >> ->
          variant_decl_list "" pc pvl
      | <:ctyp< [ > $list:pvl$ ] >> ->
          variant_decl_list ">" pc pvl
      | <:ctyp< [ < $list:pvl$ ] >> ->
          variant_decl_list "<" pc pvl
      | <:ctyp< [ < $list:pvl$ > $list:_$ ] >> ->
          not_impl "variants 4" pc pvl
      | <:ctyp< $_$ as $_$ >> as z ->
          ctyp
            {(pc) with ind = pc.ind + 1; bef = sprintf "%s(" pc.bef;
             aft = sprintf ")%s" pc.aft}
            z ] ]
  ;
  pr_sig_item: LEVEL "top"
    [ [ <:sig_item< class $list:cd$ >> ->
          horiz_vertic
            (fun () ->
               sprintf "%sclass %s%s" pc.bef
                 (hlist2 class_def (and_before class_def)
                    {(pc) with bef = ""; aft = ""} cd)
                 pc.aft)
            (fun () ->
               vlist2 class_def (and_before class_def)
                 {(pc) with bef = sprintf "%sclass " pc.bef} cd)
      | <:sig_item< class type $list:cd$ >> ->
          class_type_decl_list pc cd ] ]
  ;
  pr_str_item: LEVEL "top"
    [ [ <:str_item< class $list:cd$ >> ->
          horiz_vertic
            (fun () ->
               sprintf "%sclass %s%s" pc.bef
                 (hlist2 class_decl (and_before class_decl)
                    {(pc) with bef = ""; aft = ""} cd)
                 pc.aft)
            (fun () ->
               vlist2 class_decl (and_before class_decl)
                 {(pc) with bef = sprintf "%sclass " pc.bef} cd)
      | <:str_item< class type $list:cd$ >> ->
          class_type_decl_list pc cd ] ]
  ;
END;

value sig_method_or_method_virtual pc virt priv s t =
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

value poly_type pc =
  fun
  [ <:ctyp< ! $list:tpl$ . $t$ >> ->
      horiz_vertic
        (fun () ->
           sprintf "%s%s . %s%s" pc.bef
             (hlist typevar {(pc) with bef = ""; aft = ""} tpl)
             (ctyp {(pc) with bef = ""; aft = ""} t) pc.aft)
        (fun () ->
           let s1 =
             sprintf "%s%s ." pc.bef
               (hlist typevar {(pc) with bef = ""; aft = ""} tpl)
           in
           let s2 =
             ctyp {(pc) with ind = pc.ind + 2; bef = tab (pc.ind + 2)} t
           in
           sprintf "%s\n%s" s1 s2)
  | t -> ctyp pc t ]
;

EXTEND_PRINTER
  pr_expr: AFTER "apply"
    [ "label"
      [ <:expr< ?$s$ >> -> sprintf "%s?%s%s" pc.bef s pc.aft
      | <:expr< ?$i$: $e$ >> ->
          curr {(pc) with bef = sprintf "%s?%s:" pc.bef i} e
      | <:expr< ~$s$ >> ->
          sprintf "%s~%s%s" pc.bef s pc.aft
      | <:expr< ~$s$: $e$ >> ->
          Eprinter.apply_level pr_expr "dot"
            {(pc) with bef = sprintf "%s~%s:" pc.bef s} e ] ]
  ;
  pr_ctyp: AFTER "top"
    [ "as"
      [ <:ctyp< $t1$ as $t2$ >> ->
          horiz_vertic
            (fun () ->
               sprintf "%s%s as %s%s" pc.bef
                 (curr {(pc) with bef = ""; aft = ""} t1)
                 (next {(pc) with bef = ""; aft = ""} t2) pc.aft)
            (fun () -> not_impl "ctyp as vertic" pc t1) ]
    | "poly"
      [ <:ctyp< ! $list:_$ . $_$ >> as z -> poly_type pc z ] ]
  ;
  pr_ctyp: AFTER "arrow"
    [ "label"
      [ <:ctyp< ?$i$: $t$ >> ->
          curr {(pc) with bef = sprintf "%s?%s:" pc.bef i} t
      | <:ctyp< ~$i$: $t$ >> ->
          curr {(pc) with bef = sprintf "%s%s:" pc.bef i} t ] ]
  ;
  pr_class_expr:
    [ "top"
      [ <:class_expr< fun $p$ -> $ce$ >> ->
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
      | <:class_expr< let $flag:rf$ $list:pel$ in $ce$ >> ->
          horiz_vertic
            (fun () ->
               let s1 =
                 hlist2 (binding expr) (and_before (binding expr))
                   {(pc) with
                    bef =
                      sprintf "%slet %s" pc.bef (if rf then "rec " else "");
                    aft = " in"}
                   pel
               in
               let s2 = class_expr {(pc) with bef = ""} ce in
               sprintf "%s %s" s1 s2)
            (fun () ->
               let s1 =
                 vlist2 (binding expr) (and_before (binding expr))
                   {(pc) with
                    bef =
                      sprintf "%slet %s" pc.bef (if rf then "rec " else "");
                    aft = " in"}
                   pel
               in
               let s2 = class_expr {(pc) with bef = tab pc.ind} ce in
               sprintf "%s\n%s" s1 s2) ]
    | "apply"
      [ <:class_expr< $ce$ $e$ >> ->
          pprintf pc "%p@;%p" curr ce (Eprinter.apply_level pr_expr "label")
            e ]
    | "simple"
      [ <:class_expr< $list:cl$ >> -> class_longident pc cl
      | <:class_expr< $list:cl$ [ $list:ctcl$ ] >> ->
          let ctcl = List.map (fun ct -> (ct, ",")) ctcl in
          horiz_vertic
            (fun  () ->
               sprintf "%s[%s] %s%s" pc.bef
                 (plist ctyp 0 {(pc) with bef = ""; aft = ""} ctcl)
                 (class_longident {(pc) with bef = ""; aft = ""} cl)
                 pc.aft)
            (fun  () -> not_impl "class_expr c [t, t] vertic" pc cl)
      | <:class_expr< object $opt:csp$ $list:csl$ end >> ->
          class_object pc (csp, csl)
      | <:class_expr< ($ce$ : $ct$) >> ->
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
               sprintf "%s\n%s" s1 s2) ] ]
  ;
  pr_class_type:
    [ "top"
      [ <:class_type< [ $t$ ] -> $ct$ >> ->
          horiz_vertic
            (fun () ->
               sprintf "%s%s -> %s%s" pc.bef
                 (ctyp {(pc) with bef = ""; aft = ""} t)
                 (curr {(pc) with bef = ""; aft = ""} ct) pc.aft)
            (fun () ->
               let s1 = ctyp {(pc) with aft = " ->"} t in
               let s2 =
                 curr {(pc) with ind = pc.ind + 2; bef = tab (pc.ind + 2)} ct
               in
               sprintf "%s\n%s" s1 s2)
      | <:class_type< object $opt:cst$ $list:csi$ end >> ->
          let class_sig_item_sep =
            if flag_semi_semi.val then semi_semi_after class_sig_item
            else class_sig_item
          in
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
                        sprintf " (%s)"
                          (ctyp {(pc) with bef = ""; aft = ""} t)
                    | None -> "" ])
                   (hlist class_sig_item_sep
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
                 vlist class_sig_item_sep
                   {(pc) with ind = pc.ind + 2; bef = tab (pc.ind + 2);
                    aft = ""}
                   csi
               in
               let s3 = sprintf "%send%s" (tab pc.ind) pc.aft in
               sprintf "%s\n%s\n%s" s1 s2 s3)
      | <:class_type< $list:cl$ >> ->
          class_longident pc cl
      | <:class_type< $list:cl$ [ $list:ctcl$ ] >> ->
          let ctcl = List.map (fun ct -> (ct, ",")) ctcl in
          horiz_vertic
            (fun  () ->
               sprintf "%s[%s] %s%s" pc.bef
                 (plist ctyp 0 {(pc) with bef = ""; aft = ""} ctcl)
                 (class_longident {(pc) with bef = ""; aft = ""} cl)
                 pc.aft)
            (fun  () -> not_impl "class_type c [t, t] vertic" pc cl) ] ]
  ;
  pr_class_sig_item:
    [ "top"
      [ <:class_sig_item< inherit $ct$ >> ->
          horiz_vertic
            (fun () ->
               sprintf "%sinherit %s%s" pc.bef
                 (class_type {(pc) with bef = ""; aft = ""} ct) pc.aft)
            (fun () -> not_impl "class_sig_item inherit vertic" pc ct)
      | <:class_sig_item< method $flag:priv$ $lid:s$ : $t$ >> ->
          sig_method_or_method_virtual pc "" priv s t
      | <:class_sig_item< method virtual $flag:priv$ $lid:s$ : $t$ >> ->
          sig_method_or_method_virtual pc " virtual" priv s t
      | <:class_sig_item< value $flag:mf$ $lid:s$ : $t$ >> ->
          horiz_vertic
            (fun () ->
               sprintf "%sval%s %s : %s%s" pc.bef
                 (if mf then " mutable" else "")
                 (var_escaped {(pc) with bef = ""; aft = ""} s)
                 (ctyp {(pc) with bef = ""; aft = ""} t) pc.aft)
            (fun () ->
               let s1 =
                 sprintf "%sval%s %s :" pc.bef (if mf then " mutable" else "")
                   (var_escaped {(pc) with bef = ""; aft = ""} s)
               in
               let s2 =
                 ctyp {(pc) with ind = pc.ind + 2; bef = tab (pc.ind + 2)} t
               in
               sprintf "%s\n%s" s1 s2) ] ]
  ;
  pr_class_str_item:
    [ "top"
      [ <:class_str_item< inherit $ce$ $opt:pb$ >> ->
          horiz_vertic
            (fun () ->
               sprintf "%sinherit %s%s%s" pc.bef
                 (class_expr {(pc) with bef = ""; aft = ""} ce)
                 (match pb with
                  [ Some s -> sprintf " as %s" s
                  | None -> "" ]) pc.aft)
            (fun () ->
               let s =
                 class_expr
                   {(pc) with ind = pc.ind + 2; bef = tab (pc.ind + 2);
                    aft =
                      match pb with
                      [ Some s -> sprintf " as %s%s" s pc.aft
                      | None -> pc.aft ]}
                   ce
               in
               sprintf "%sinherit\n%s" pc.bef s)
      | <:class_str_item< initializer $e$ >> ->
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
      | <:class_str_item< method virtual $flag:priv$ $lid:s$ : $t$ >> ->
          sig_method_or_method_virtual pc " virtual" priv s t
      | <:class_str_item< method $flag:priv$ $lid:s$ $opt:topt$ = $e$ >> ->
          let (pl, e) =
            match topt with
            [ Some _ -> ([], e)
            | None -> expr_fun_args e ]
          in
          let simple_patt = Eprinter.apply_level pr_patt "simple" in
          let args =
            if pl = [] then ""
            else hlist simple_patt {(pc) with bef = " "; aft = ""} pl
          in
          horiz_vertic
            (fun () ->
               sprintf "%smethod%s %s%s%s = %s%s" pc.bef
                 (if priv then " private" else "") s args
                 (match topt with
                  [ Some t ->
                      sprintf " : %s"
                        (poly_type {(pc) with bef = ""; aft = ""} t)
                  | None -> "" ])
                 (expr {(pc) with bef = ""; aft = ""} e) pc.aft)
            (fun () ->
               let s1 =
                 match topt with
                 [ None ->
                     sprintf "%smethod%s %s%s =" pc.bef
                       (if priv then " private" else "") s args
                 | Some t ->
                     horiz_vertic
                       (fun () ->
                          sprintf "%smethod%s %s%s : %s =" pc.bef
                            (if priv then " private" else "") s args
                            (poly_type {(pc) with bef = ""; aft = ""} t))
                       (fun () ->
                          let s1 =
                            sprintf "%smethod%s %s%s :" pc.bef
                              (if priv then " private" else "") s args
                          in
                          let s2 =
                            poly_type
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
          horiz_vertic
            (fun () ->
               sprintf "%sconstraint %s = %s%s" pc.bef
                 (ctyp {(pc) with bef = ""; aft = ""} t1)
                 (ctyp {(pc) with bef = ""; aft = ""} t2) pc.aft)
            (fun () -> not_impl "class_str_item type vertic" pc t1)
      | <:class_str_item< value $flag:mf$ $lid:s$ = $e$ >> ->
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
               sprintf "%s\n%s" s1 s2) ] ]
  ;
END;
