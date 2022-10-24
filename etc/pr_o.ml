(* camlp5r *)
(* pr_o.ml,v *)
(* Copyright (c) INRIA 2007-2017 *)

#directory ".";
#load "q_MLast.cmo";
#load "pa_extfun.cmo";
#load "pa_extprint.cmo";
#load "pa_macro.cmo";
#load "pa_macro_print.cmo";
#load "pa_pprintf.cmo";

open Asttools;
open Pretty;
open Pcaml;
open Prtools;
open Versdep;
open Mlsyntax.Original;
open Pp_debug ;

value flag_add_locations = ref False;
value flag_comments_in_phrases = Pcaml.flag_comments_in_phrases;
value flag_equilibrate_cases = Pcaml.flag_equilibrate_cases;
value flag_expand_letop_syntax = Pcaml.flag_expand_letop_syntax;
value flag_extensions_are_irrefutable = ref True;

value flag_horiz_let_in = ref True;
value flag_semi_semi = ref False;

value pr_attribute_body = Eprinter.make "pr_attribute_body";

do {
  Eprinter.clear pr_expr;
  Eprinter.clear pr_patt;
  Eprinter.clear pr_ctyp;
  Eprinter.clear pr_str_item;
  Eprinter.clear pr_sig_item;
  Eprinter.clear pr_longident;
  Eprinter.clear pr_module_expr;
  Eprinter.clear pr_module_type;
  Eprinter.clear pr_class_sig_item;
  Eprinter.clear pr_class_str_item;
  Eprinter.clear pr_class_expr;
  Eprinter.clear pr_class_type;
};

(* general functions *)

value error loc msg = Ploc.raise loc (Failure msg);

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
  | "\\" -> "\\\\"
  | c -> c ]
;

value rec is_irrefut_patt =
  fun
  [
    <:patt< $p$ [@ $_attribute:_$ ] >> -> is_irrefut_patt p
  |  <:patt< $lid:_$ >> -> True
  | <:patt< $uid:"()"$ >> -> True
  | <:patt< _ >> -> True
  | <:patt< $longid:_$ . $y$ >> -> is_irrefut_patt y
  | <:patt< ($x$ as $y$) >> -> is_irrefut_patt x && is_irrefut_patt y
  | <:patt< { $list:fpl$ } >> ->
      List.for_all (fun (_, p) -> is_irrefut_patt p) fpl
  | <:patt< ($p$ : $_$) >> -> is_irrefut_patt p
  | <:patt< ($list:pl$) >> -> List.for_all is_irrefut_patt pl
  | <:patt< (type $lid:_$) >> -> True
  | <:patt< (module $uidopt:_$ : $_$) >> -> True
  | <:patt< (module $uidopt:_$) >> -> True
  | <:patt< ~{$list:_$} >> -> True
  | <:patt< ?{$_$ $opt:_$} >> -> True
  | <:patt< [% $_extension:_$ ] >> -> flag_extensions_are_irrefutable.val
  | _ -> False ]
;

value rec get_defined_ident =
  fun
  [ <:patt< $longid:_$ . $p$ >> -> get_defined_ident p
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
  | <:patt< # $lilongid:_$ >> -> []
  | <:patt< $p1$ $p2$ >> -> get_defined_ident p1 @ get_defined_ident p2
  | <:patt< { $list:lpl$ } >> ->
      List.flatten (List.map (fun (lab, p) -> get_defined_ident p) lpl)
  | <:patt< $p1$ | $p2$ >> -> get_defined_ident p1 @ get_defined_ident p2
  | <:patt< $p1$ .. $p2$ >> -> get_defined_ident p1 @ get_defined_ident p2
  | <:patt< ($p$ : $_$) >> -> get_defined_ident p
  | <:patt< ~{$_$} >> -> []
  | <:patt< ~{$_$ = $p$} >> -> get_defined_ident p
  | <:patt< ?{$_$} >> -> []
  | <:patt< ?{$lid:s$ = $_$} >> -> [s]
  | <:patt< ?{$_$ = ?{$lid:s$ = $e$}} >> -> [s]
  | <:patt< $anti:p$ >> -> get_defined_ident p
  | _ -> [] ]
;

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

(* for 'lprintf' statement  *)

value expand_lprintf pc loc f =
  if flag_add_locations.val then do {
    let (bl, bc, el, ec, len) = Ploc.get loc in
    pprintf pc "@[(*loc: [\"%s\": %d:%d-%d %d-%d] *)@ %p@]"
      (Ploc.file_name loc) bl bc (bc + len) el ec (fun pc () -> f pc) ()
  }
  else f pc
;

value var_escaped pc (loc, v) =
  let x =
    if v.[0] = '*' || v.[String.length v - 1] = '*' then "( " ^ v ^ " )"
    else if is_infix v || has_special_chars v || is_letop v || is_andop v then "(" ^ v ^ ")"
    else v
  in
  lprintf pc "%s" x
;

value cons_escaped pc (loc, v) =
  let x =
    match v with
    [ "True" -> "true"
    | "False" -> "false"
    | "True_" -> "True"
    | "False_" -> "False"
    | "[]" -> "[]"
    | "()" -> "()"
    | "::" -> "( :: )"
    | _ -> v ]
  in
  pprintf pc "%s" x
;

value rec mod_ident pc (loc, sl) =
  match sl with
  [ [] -> pprintf pc ""
  | [s] -> var_escaped pc (loc, s)
  | [s :: sl] -> pprintf pc "%s.%p" s mod_ident (loc, sl) ]
;

value comma_after elem pc x = pprintf pc "%p," elem x;
value semi_after elem pc x = pprintf pc "%q;" elem x ";";
value semi_semi_after elem pc x = pprintf pc "%p;;" elem x;
value op_after elem pc (x, op) = pprintf pc "%p%s" elem x op;

value and_before elem pc x = pprintf pc "and %p" elem x;
value bar_before elem pc x = pprintf pc "| %p" elem x;
value space_before elem pc x = pprintf pc " %p" elem x;

value andop_before elem pc ((andop, _) as x) = pprintf pc "%s %p" andop elem x;

value operator pc left right sh (loc, op) x y =
  let op = if op = "" then "" else " " ^ op in
  pprintf pc "%p%s@;%p" left x op right y
;

value left_operator pc loc sh unfold next x =
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

value right_operator pc loc sh unfold next x =
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

value uidopt_to_maybe_blank = fun [
  Some s -> Pcaml.unvala s
|  None ->
  IFDEF OCAML_VERSION < OCAML_4_10_0 THEN
    invalid_arg "pr_o.ml: uidopt_to_blank: blank module-names not supported"
  ELSE
    "_"
  END
]
;

(*
 * Extensible printers
 *)

value expr = Eprinter.apply pr_expr;
value patt = Eprinter.apply pr_patt;
value ctyp = Eprinter.apply pr_ctyp;
value ctyp_below_alg_attribute x = Eprinter.apply_level pr_ctyp "below_alg_attribute" x;
value str_item = Eprinter.apply pr_str_item;
value sig_item = Eprinter.apply pr_sig_item;
value longident = Eprinter.apply pr_longident;
value module_expr = Eprinter.apply pr_module_expr;
value module_type = Eprinter.apply pr_module_type;
value module_type_level_sig = Eprinter.apply_level pr_module_type "sig";
value expr_fun_args ge = Extfun.apply pr_expr_fun_args.val ge;

value simple_patt = Eprinter.apply_level pr_patt "simple" ;
value expr1 = Eprinter.apply_level pr_expr "expr1";
value attribute_body = Eprinter.apply pr_attribute_body;
value pr_attribute atstring pc attr =
  pprintf pc "[%s%p]" atstring attribute_body (Pcaml.unvala attr)
;
value pr_extension atstring pc attr =
  pprintf pc "[%s%p]" atstring attribute_body (Pcaml.unvala attr)
;

value longident_lident pc (lio, id) =
  match lio with
  [ None -> pprintf pc "%s" (Pcaml.unvala id)
  | Some li -> pprintf pc "%p.%s" longident (Pcaml.unvala li) (Pcaml.unvala id)
  ]
;

value comm_bef pc loc =
  if flag_comments_in_phrases.val then Prtools.comm_bef pc.ind loc else ""
;

value only_spaces s =
  loop 0 where rec loop i =
    if i = String.length s then True
    else if s.[i] = ' ' then loop (i + 1)
    else False
;

value strip_heading_spaces s =
  loop 0 where rec loop i =
    if i = String.length s then ""
    else if s.[i] = ' ' then loop (i + 1)
    else String.sub s i (String.length s - i)
;

value strip_char c s = do {
  let s = string_copy (bytes_of_string s) in
  bytes_to_string (loop 0 0) where rec loop i j =
    if i = string_length s then string_sub s 0 j
    else if string_get s i = '_' then loop (i + 1) j
    else do {
      string_set s j (string_get s i);
      loop (i + 1) (j + 1)
    }
};

(* expression with adding the possible comment before *)
value comm_expr expr pc z =
  let loc = MLast.loc_of_expr z in
  let ccc = comm_bef pc loc in
  if ccc = "" then expr pc z
  else if only_spaces pc.bef then sprintf "%s%s" ccc (expr pc z)
  else
    expr
      {(pc) with
       bef =
         sprintf "%s%s%s" pc.bef (strip_heading_spaces ccc)
           (String.make (String.length pc.bef) ' ')}
     z
;

(*
value comm_expr expr pc z =
  let loc = MLast.loc_of_expr z in
  let ccc = comm_bef pc loc in
  sprintf "%s%s" ccc (expr pc z)
;
*)

(* couple pattern/anytype with adding the possible comment before *)
value comm_patt_any f pc z =
  let ccc = comm_bef pc (MLast.loc_of_patt (fst z)) in
  sprintf "%s%s" ccc (f pc z)
;

value patt_as pc z =
  match z with
  [ <:patt:< ($x$ as $y$) >> -> pprintf pc "%p@[ as %p@]" patt x patt y
  | z -> patt pc z ]
;

(* utilities specific to pr_o *)

value label_patt pc p =
  match p with [
    <:patt:< $longid:x$ . $lid:y$ >> -> pprintf pc "%p.%p" longident x var_escaped (loc, y)
  | <:patt:< $lid:y$ >> -> var_escaped pc (loc, y)
  | z -> Ploc.raise (MLast.loc_of_patt z)
      (Failure (sprintf "label_patt %d" (Obj.tag (Obj.repr z))))
  ]
;


(* Basic displaying of a 'binding' (let, value, expr or patt record field).
   The pretty printing is done correctly, but there are no syntax shortcuts
   (e.g. "let f = fun x -> y" is *not* shortened as "let f x = y")

   Some functions follow (some of them with '_binding' in their name) which
   use syntax or pretty printing shortcuts.
*)
value binding pelem eelem pc (p, e, attrs) =
  pprintf pc "%p =@;%p%p" pelem p eelem e
  (hlist (pr_attribute "@@")) (Pcaml.unvala attrs)
;

value record_binding is_last pc (p, e) =
  pprintf pc "%p =@;%q" label_patt p expr1 e (if is_last then pc.dang else ";")
;

value is_polytype_constraint = fun [
  <:patt< ( $_$ : ! $list:_$ . $_$ ) >> -> True
| _ -> False
]
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
  if not is_last then
    pprintf pc "%q;" (comm_expr expr) e ";"
  else
    pprintf pc "%p" (comm_expr expr) e
;

value expr_with_comm_except_if_sequence pc e =
  match e with
  [ <:expr< do { $list:_$ } >> -> expr pc e
  | _ -> comm_expr expr pc e ]
;

(* Pretty printing improvements (optional):
   - prints "let f x = e" instead of "let f = fun x -> e"
   - if "e" is a type constraint, put the constraint after the params. E.g.
        let f x y = (e : t)
     is displayed:
        let f x y : t = e
   Cancellation of all these improvements could be done by changing calls
   to this function to a call to "binding expr" above.
*)
value let_binding pc (p, e, attrs) =
  let (pl, e) =
    match p with
    [ <:patt< ($_$ : $_$) >> -> ([], e)
    | _ -> expr_fun_args e ]
  in
  let (p, e, tyo) =
    match (p, e) with [
      (<:patt< (_ : $_$) >>, _)  -> (p, e, None)
    | (<:patt< _ >>, _)  -> (p, e, None)
    | (<:patt< ($p0$ : $t$) >>, _) when is_polytype_constraint p -> (p0, e, Some t)
    | (<:patt< ($_$ : $_$) >>, _) -> (p, e, None)
    | (_, <:expr< ( $e$ : $t$ ) >>) -> (p, e, Some t)
    | _ -> (p, e, None) ]
  in
  let patt_tycon tyo pc p =
    match tyo with
    [ Some t -> pprintf pc "%p : %p" simple_patt p ctyp t
    | None -> simple_patt pc p ]
  in
  let pl = [p :: pl] in
  let pl = List.map (fun p -> (p, "")) pl in
  let pc = {(pc) with dang = ""} in
  match pc.aft with
  [ "" ->
      pprintf pc "%p =@;%q%p"
        (plistl simple_patt (patt_tycon tyo) 4) pl
        expr_with_comm_except_if_sequence e ""
        (hlist (pr_attribute "@@")) (Pcaml.unvala attrs)
  | "in" ->
      pprintf pc "@[<a>%p =@;%q%p@ @]"
        (plistl simple_patt (patt_tycon tyo) 4) pl
        expr_with_comm_except_if_sequence e ""
        (hlist (pr_attribute "@@")) (Pcaml.unvala attrs)
  | _ ->
      pprintf pc "@[<a>%p =@;%q%p@;<0 0>@]"
        (plistl simple_patt (patt_tycon tyo) 4) pl
        expr_with_comm_except_if_sequence e ""
        (hlist (pr_attribute "@@")) (Pcaml.unvala attrs)
  ]
;

value letop_binding pc (_, (p, e, attrs)) = let_binding pc (p, e, attrs)
;

value match_assoc force_vertic pc ((p, w, e), is_last) =
  let expr pc = fun [
    <:expr< . >> -> pprintf pc "." | e -> expr pc e
  ] in
  let expr_with_comm_except_if_sequence pc = fun [
    <:expr< . >> -> pprintf pc "." | e -> expr_with_comm_except_if_sequence pc e
  ] in
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
       pprintf pc "@[<i>%p@;%q@]" force_vertic
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

value match_assoc_list loc pc pwel =
  if pwel = [] then pprintf pc "[]"
  else
    let force_vertic =
      if flag_equilibrate_cases.val then
        let has_vertic =
          List.exists
            (fun ((p, w, e) as pwe) ->
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
  let fname = Ploc.file_name loc in
  let line = Ploc.line_nb loc in
  let char = Ploc.first_pos loc - Ploc.bol_pos loc in
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

value type_var pc v =
  if String.contains v '\'' then
    pprintf pc "' %s" v
  else pprintf pc "'%s" v
;

value tv_or_blank pc = fun [
  Some v -> pprintf pc "%p" type_var v
| None -> pprintf pc "_"
]
;

value type_param pc (loc, (tv, (vari, inj))) =
  let tv = Pcaml.unvala tv in
  pprintf pc "%s%s%p"
    (match vari with
     [ Some True -> "+"
     | Some False -> "-"
     | None -> "" ])
    (match inj with
       [ True -> "!"
       | False -> ""
       ])
    tv_or_blank tv
;

value type_constraint pc (t1, t2) =
  pprintf pc " constraint %p =@;%p" ctyp t1 ctyp t2
;

value type_params pc (loc, tvl) =
  match tvl with
  [ [] -> pprintf pc ""
  | [tv] -> pprintf pc "%p " type_param (loc, tv)
  | _ ->
      let tvl = List.map (fun tv -> (loc, tv)) tvl in
      pprintf pc "(%p) " (hlistl (comma_after type_param) type_param) tvl ]
;

value mem_tvar s tpl =
  List.exists (fun (t, _) -> Pcaml.unvala t = Some s) tpl
;

value type_decl pc td =
  let ((_, tn), is_decl, tp, pf, te, cl,attrs) =
    (Pcaml.unvala td.MLast.tdNam, td.MLast.tdIsDecl, td.MLast.tdPrm, Pcaml.unvala td.MLast.tdPrv,
     td.MLast.tdDef, td.MLast.tdCon, td.MLast.tdAttributes)
  in
  let asgn = if Pcaml.unvala is_decl then "=" else ":=" in
  match te with
  [ <:ctyp:< '$s$ >> when not (mem_tvar s (Pcaml.unvala tp))
                          && not (List.exists (fun [ (t1, t2) -> Ast2pt.ctyp_mentions s t1 || Ast2pt.ctyp_mentions s t2 ]) (Pcaml.unvala cl)) ->
      pprintf pc "%p%p%p%p" type_params (loc, Pcaml.unvala tp)
        var_escaped (loc, Pcaml.unvala tn)
        (hlist type_constraint) (Pcaml.unvala cl)
        (hlist (pr_attribute "@@")) (Pcaml.unvala attrs)
  | _ ->
      let loc = MLast.loc_of_ctyp te in
      if pc.aft = "" then
        pprintf pc "%p%p %s@;%s%p%p%p"
          type_params (loc, Pcaml.unvala tp)
          var_escaped (loc, Pcaml.unvala tn)
          asgn
          (if pf then "private " else "")
          ctyp te
          (hlist type_constraint) (Pcaml.unvala cl)
        (hlist (pr_attribute "@@")) (Pcaml.unvala attrs)
      else
        horiz_vertic
          (fun () ->
             pprintf pc "%p%p %s %s%p%p%p"
               type_params (loc, Pcaml.unvala tp)
               var_escaped (loc, Pcaml.unvala tn)
               asgn
               (if pf then "private " else "")
               ctyp te
               (hlist type_constraint) (Pcaml.unvala cl)
               (hlist (pr_attribute "@@")) (Pcaml.unvala attrs))
          (fun () ->
             pprintf pc "@[<a>%p%p %s@;%s%p%p%p@ @]"
               type_params
               (loc, Pcaml.unvala tp) var_escaped (loc, Pcaml.unvala tn)
               asgn
               (if pf then "private " else "")
               ctyp
               te (hlist type_constraint) (Pcaml.unvala cl)
               (hlist (pr_attribute "@@")) (Pcaml.unvala attrs)) ]
;

value label_decl pc (_, l, m, t, attrs) =
  pprintf pc "%s%s :@;%p%p" (if m then "mutable " else "") l ctyp_below_alg_attribute t
  (hlist (pr_attribute "@")) (Pcaml.unvala attrs)
;

value typevars_binder pc = fun [
  [] -> pprintf pc ""
| l -> pprintf pc "%p . " (hlist type_var) l
]
;

value cons_decl pc = fun [
  <:constructor:< $_uid:c$ of $_list:tyvars$ . $_list:tl$ $_rto:rto$ $_algattrs:alg_attrs$ >>
 ->
  let c = Pcaml.unvala c in
  let tl = Pcaml.unvala tl in
  if tl = [] then do {
    match (Pcaml.unvala tyvars, Pcaml.unvala rto) with
    [ ([], Some rt) -> pprintf pc "%p : %p%p" cons_escaped (loc, c) ctyp_below_alg_attribute rt
                   (hlist (pr_attribute "@")) (Pcaml.unvala alg_attrs)
    | (l, Some rt) -> pprintf pc "%p : %p%p%p" cons_escaped (loc, c) typevars_binder l ctyp_below_alg_attribute rt
                   (hlist (pr_attribute "@")) (Pcaml.unvala alg_attrs)
    | (_, None) -> pprintf pc "%p%p" cons_escaped (loc, c)
                   (hlist (pr_attribute "@")) (Pcaml.unvala alg_attrs)
    ]
  }
  else do {
    let ctyp_apply = Eprinter.apply_level pr_ctyp "apply" in
    let tl = List.map (fun t -> (t, " *")) tl in
    match (Pcaml.unvala tyvars, Pcaml.unvala rto) with
    [ ([], Some rt) ->
        pprintf pc "%p :@;<1 4>%p -> %p%p" cons_escaped (loc, c)
          (plist ctyp_apply 2) tl ctyp_below_alg_attribute rt
          (hlist (pr_attribute "@")) (Pcaml.unvala alg_attrs)
    | (l, Some rt) ->
        pprintf pc "%p :@;<1 4>%p%p -> %p%p" cons_escaped (loc, c) typevars_binder l
          (plist ctyp_apply 2) tl ctyp_below_alg_attribute rt
          (hlist (pr_attribute "@")) (Pcaml.unvala alg_attrs)
    | (_, None) ->
        pprintf pc "%p of@;<1 4>%p%p" cons_escaped (loc, c) (plist ctyp_apply 2)
          tl (hlist (pr_attribute "@")) (Pcaml.unvala alg_attrs) ]
  }
]
;

value extension_constructor loc pc ec = match ec with [
  MLast.EcTuple _ gc -> cons_decl pc gc

| <:extension_constructor:< $uid:e$ = $longid:li$ $algattrs:alg_attrs$ >> ->
      pprintf pc "%p@;= %p%p" cons_escaped (loc, e) longident li
        (hlist (pr_attribute "@")) alg_attrs
| _ -> error loc "extension_constructor: internal error"
]
;

value has_ecs_with_params vdl =
  List.exists
    (fun [
       MLast.EcTuple _ (_, _, _, tl, rto,_) ->
       match tl with
         [ <:vala< [] >> -> False
         | _ -> True ]
       | MLast.EcRebind _ _ _ _ -> True
     ])
    vdl
;

value extension_constructors loc pc vdl =
  horiz_vertic
    (fun () ->
       if has_ecs_with_params vdl then sprintf "\n"
       else hlist2 (extension_constructor loc) (bar_before (extension_constructor loc)) pc vdl)
    (fun () ->
       pprintf pc "  %p"
         (vlist2 (extension_constructor loc) (bar_before (extension_constructor loc))) vdl)
;

value type_extension loc pc te =
  let (tn, tp, pf, ecstrs, attrs) =
    (Pcaml.unvala te.MLast.teNam, te.MLast.tePrm, Pcaml.unvala te.MLast.tePrv,
     te.MLast.teECs, te.MLast.teAttributes)
  in
      if pc.aft = "" then
        pprintf pc "%p%p +=@;%s%p%p"
          type_params (loc, Pcaml.unvala tp)
          longident_lident tn
          (if pf then "private " else "")
          (extension_constructors loc) (Pcaml.unvala ecstrs)
          (hlist (pr_attribute "@@")) (Pcaml.unvala attrs)
      else
        horiz_vertic
          (fun () ->
             pprintf pc "%p%p += %s%p%p"
               type_params (loc, Pcaml.unvala tp)
               longident_lident tn
               (if pf then "private " else "")
               (extension_constructors loc) (Pcaml.unvala ecstrs)
               (hlist (pr_attribute "@@")) (Pcaml.unvala attrs))
          (fun () ->
             pprintf pc "@[<a>%p%p +=@;%s%p%p@ @]"
               type_params
               (loc, Pcaml.unvala tp) longident_lident tn
               (if pf then "private " else "")
               (extension_constructors loc) (Pcaml.unvala ecstrs)
               (hlist (pr_attribute "@@")) (Pcaml.unvala attrs))
;

value has_cons_with_params vdl =
  List.exists
    (fun (_, _, _, tl, rto,_) ->
       match tl with
       [ <:vala< [] >> -> False
       | _ -> True ])
    vdl
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

(* if statement *)

value rec get_else_if =
  fun
  [ <:expr< if $e1$ then $e2$ else $e3$ >> ->
      let (eel, e3) = get_else_if e3 in
      ([(e1, e2) :: eel], e3)
  | e -> ([], e) ]
;

value if_then force_vertic curr pc (e1, e2) =
  horiz_vertic
    (fun () ->
       if force_vertic then sprintf "\n"
       else pprintf pc "if %q then %p" curr e1 "" curr e2)
    (fun () ->
       pprintf pc "@[<3>if %q@]@ then@;%p" curr e1 "" expr1 e2)
;

value else_if_then force_vertic curr pc (e1, e2) =
  horiz_vertic
    (fun () ->
       if force_vertic then sprintf "\n"
       else
         pprintf pc "else if %q then %p" curr e1 ""
           curr e2)
    (fun () ->
       pprintf pc "@[<i>else if@;%q@ then@]@;%p" force_vertic curr e1 ""
         ((*comm_expr*) expr1) e2)
;

value loop_else_if_no_else force_vertic curr pc eel =
  loop pc eel where rec loop pc =
    fun
    [ [(e1, e2)] ->
        pprintf pc "@[<b>@ %p@]" (else_if_then force_vertic curr) (e1, e2)
    | [(e1, e2) :: eel] ->
        pprintf pc "@[<b>@ %q%p@]"
          (else_if_then force_vertic curr) (e1, e2) "else" loop eel
    | [] ->
        pprintf pc "" ]
;

value loop_else_if_and_else force_vertic curr pc (eel, e3) =
  loop pc eel where rec loop pc =
    fun
    [ [(e1, e2) :: eel] ->
        pprintf pc "@[<b>@ %q%p@]"
          (else_if_then force_vertic curr) (e1, e2) "else" loop eel
    | [] ->
        pprintf pc "@[<b>@ @[else@;%p@]@]" curr e3 ]
;

value if_case_has_vertic curr pc e1 e2 eel e3 =
  horiz_vertic
    (fun () ->
       let _ : string = if_then False curr {(pc) with aft = ""} (e1, e2) in
       False)
    (fun () -> True) ||
  List.exists
    (fun (e1, e2) ->
       horiz_vertic
         (fun () ->
            let _ : string =
              else_if_then False curr {(pc) with bef = tab pc.ind; aft = ""}
                (e1, e2)
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
    [ <:expr:< $lid:v$ >> ->
        if is_infix v || has_special_chars v then raise Exit
        else var_escaped pc (loc, v)
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

value lident pc s = pprintf pc "%s" s;
value string pc s = pprintf pc "\"%s\"" s;

value external_decl pc (loc, n, tyvars, t, sl, attrs) =
  pprintf pc "external %p :@;%p%p@[ = %p%p@]" var_escaped (loc, n) typevars_binder tyvars ctyp t
    (hlist string) sl
    (hlist (pr_attribute "@@")) attrs
;

value exception_decl pc (loc, e, tl, id, alg_attrs, item_attrs) =
  let ctyp_apply = Eprinter.apply_level pr_ctyp "apply" in
  match id with
  [ [] ->
      match tl with
      [ [] -> pprintf pc "exception %p%p%p" cons_escaped (loc, e)
                (hlist (pr_attribute "@")) alg_attrs
                (hlist (pr_attribute "@@")) item_attrs
      | tl ->
          let tl = List.map (fun t -> (t, " *")) tl in
          pprintf pc "exception %p of@;%p%p%p" cons_escaped (loc, e)
            (plist ctyp_apply 2) tl
            (hlist (pr_attribute "@")) alg_attrs
            (hlist (pr_attribute "@@")) item_attrs
      ]
  | id ->
      match tl with
      [ [] ->
          pprintf pc "exception %p =@;%p%p%p" cons_escaped (loc, e)
            mod_ident (loc, id)
            (hlist (pr_attribute "@")) alg_attrs
            (hlist (pr_attribute "@@")) item_attrs
      | tl ->
          let tl = List.map (fun t -> (t, " *")) tl in
          pprintf pc "exception %p of@;%p =@;%p%p%p" cons_escaped (loc, e)
            (plist ctyp_apply 2) tl mod_ident (loc, id)
            (hlist (pr_attribute "@")) alg_attrs
            (hlist (pr_attribute "@@")) item_attrs
      ] ]
;

value functor_parameter_unvala arg =
  match arg with [
    None -> None
  | Some (idopt, mt) -> Some (option_map Pcaml.unvala (Pcaml.unvala idopt), mt)
  ]
;

value str_module pref pc (m, me, item_attrs) =
  let m = match m with [ None -> "_" | Some s -> s ] in
  let (mal, me) =
    loop me where rec loop =
      fun
      [ <:module_expr< functor $fp:arg$ -> $me$ >> ->
          let (mal, me) = loop me in
          ([functor_parameter_unvala arg :: mal], me)
      | me -> ([], me) ]
  in
  let module_arg pc = fun [
    Some (Some s, mt) -> pprintf pc "(%s :@;<1 1>%p)" s module_type mt
  | Some (None, mt) ->
    IFDEF OCAML_VERSION < OCAML_4_10_0 THEN
      invalid_arg "pr_o.ml: str_module_pref: blank module-name in functor module-type is unsupported"
    ELSE
      pprintf pc "(_ :@;<1 1>%p)" module_type mt
    END
  | None ->
    IFDEF OCAML_VERSION < OCAML_4_10_0 THEN
      invalid_arg "pr_o.ml: str_module_pref: empty module-arg () in functor-expression is unsupported"
    ELSE
      pprintf pc "()"
    END
  ] in
  let (me, mto) =
    match me with
    [ <:module_expr< ($me$ : $mt$) >> -> (me, Some mt)
    | _ -> (me, None) ]
  in
  if pc.aft = "" then
    match mto with
    [ Some mt ->
        pprintf pc "%s %s%s%p :@;%p =@;%p%p" pref m
          (if mal = [] then "" else " ") (hlist module_arg) mal
          module_type mt module_expr me
          (hlist (pr_attribute "@@")) (Pcaml.unvala item_attrs)
    | None ->
        let mal = List.map (fun ma -> (ma, "")) mal in
        pprintf pc "%s %s%p =@;%p%p" pref m (plistb module_arg 2) mal
          module_expr me
          (hlist (pr_attribute "@@")) (Pcaml.unvala item_attrs)
    ]
  else
    match mto with
    [ Some mt ->
        pprintf pc "%s %s%s%p :@;%p =@;%p%p@;<0 0>" pref m
          (if mal = [] then "" else " ") (hlist module_arg) mal
          module_type mt module_expr me
          (hlist (pr_attribute "@@")) (Pcaml.unvala item_attrs)
    | None ->
        let mal = List.map (fun ma -> (ma, "")) mal in
        pprintf pc "@[<a>%s %s%p =@;%p%p@;<0 0>@]" pref m (plistb module_arg 2)
          mal module_expr me
          (hlist (pr_attribute "@@")) (Pcaml.unvala item_attrs)
    ]
;

value sig_module_or_module_type pref unfun defs pc (m, mt, item_attrs) =
  let m = match m with [ None -> "_" | Some s -> s ] in
  let (mal, mt) =
    if unfun then
      loop mt where rec loop =
        fun
        [ <:module_type< functor $fp:arg$ -> $mt2$ >> ->
            let (mal, mt) = loop mt2 in
            ([functor_parameter_unvala arg :: mal], mt)
        | mt -> ([], mt) ]
    else ([], mt)
  in
  let module_arg pc = fun [
    Some(Some s, mt) -> pprintf pc "(%s :@;<1 1>%p)" s module_type mt 
  | Some(None, mt) ->
    IFDEF OCAML_VERSION < OCAML_4_10_0 THEN
      invalid_arg "pr_o.ml: sig_module_or_module_type: blank module-name in functor module-type is unsupported"
    ELSE
      pprintf pc "(_ :@;<1 1>%p)" module_type mt 
    END
  | None -> 
    IFDEF OCAML_VERSION < OCAML_4_10_0 THEN
      invalid_arg "pr_o.ml: sig_module_or_module_type: empty module-arg () in functor module-type is unsupported"
    ELSE
      pprintf pc "()"
    END
  ] in
  match mt with
  [ <:module_type< ' $s$ >> ->
      pprintf pc "%s %s%s%p%p" pref m (if mal = [] then "" else " ")
        (hlist module_arg) mal
        (hlist (pr_attribute "@@")) (Pcaml.unvala item_attrs)

  | _ ->
      let mal = List.map (fun ma -> (ma, "")) mal in
      if pc.aft = "" then
        pprintf pc "%s %s%p %s@;%p%p" pref m
          (plistb module_arg 2) mal defs module_type_level_sig mt
          (hlist (pr_attribute "@@")) (Pcaml.unvala item_attrs)

      else
        pprintf pc "@[<a>%s %s%p %s@;%p%p@;<0 0>@]" pref m
          (plistb module_arg 2) mal defs module_type_level_sig mt
          (hlist (pr_attribute "@@")) (Pcaml.unvala item_attrs)
  ]
;

value str_or_sig_functor pc farg module_expr_or_type met =
  match farg with [
    Some (Some s, mt) -> pprintf pc "functor@;@[(%s :@;<1 1>%p)@]@ ->@;%p" s module_type mt
      module_expr_or_type met
  | Some (None, mt) ->
    IFDEF OCAML_VERSION < OCAML_4_10_0 THEN
    invalid_arg "pr_o.ml: str_or_sig_functor: blank module-name in functor-expression is unsupported"
    ELSE
    pprintf pc "functor@;@[(_ :@;<1 1>%p)@]@ ->@;%p" module_type mt
      module_expr_or_type met
    END
  | None ->
    IFDEF OCAML_VERSION < OCAML_4_10_0 THEN
    invalid_arg "pr_o.ml: str_or_sig_functor: empty module-arg () in functor-expression is unsupported"
    ELSE
    pprintf pc "functor@;@[()@]@ ->@;%p"
      module_expr_or_type met
    END
  ]
;

value con_typ_pat pc (loc, sl, tpl) =
  let tpl = List.map (fun tp -> (loc, tp)) tpl in
  match tpl with
  [ [] -> pprintf pc "%p" longident_lident sl
  | [tp] -> pprintf pc "%p %p" type_param tp longident_lident sl
  | _ ->
      pprintf pc "(%p) %p"
        (hlistl (comma_after type_param) type_param) tpl longident_lident sl ]
;

value with_constraint pc wc =
  match wc with
  [ <:with_constr:< type $lilongid:sl$ $list:tpl$ = $flag:pf$ $t$ >> ->
      pprintf pc "type %p =@;%s%p" con_typ_pat (loc, sl, tpl)
        (if pf then "private " else "") ctyp t
  | <:with_constr:< type $lilongid:sl$ $list:tpl$ := $t$ >> ->
      pprintf pc "type %p :=@;%p" con_typ_pat (loc, sl, tpl) ctyp t
  | <:with_constr:< module $longid:sl$ = $me$ >> ->
      pprintf pc "module %p =@;%p" longident sl module_expr me
  | <:with_constr:< module $longid:sl$ := $me$ >> ->
      pprintf pc "module %p :=@;%p" longident sl module_expr me
  | <:with_constr:< module type $longid:sl$ = $mt$ >> ->
      pprintf pc "module type %p =@;%p" longident sl module_type mt
  | <:with_constr:< module type $longid:sl$ := $mt$ >> ->
      pprintf pc "module type %p :=@;%p" longident sl module_type mt
  | IFDEF STRICT THEN
      x -> not_impl "with_constraint" pc x
    END ]
;

value is_unary =
  fun
  [ "-" | "-." -> True
  | _ -> False ]
;

value unary op_pred expr pc x =
  match x with
  [ <:expr< $lid:f$ $_$ >> when op_pred f -> pprintf pc "(%p)" expr x
  | <:expr< $_$.val >> -> pprintf pc "(%p)" expr x
  | x -> pprintf pc "%p" expr x ]
;
value map_option f =
  fun
  [ Some x -> Some (f x)
  | None -> None ]
;

value pr_letlike letop pc loc rf pel e =
  horiz_vertic
    (fun () ->
      if not flag_horiz_let_in.val then sprintf "\n"
      else if pc.dang = ";" then
        pprintf pc "(%s%s %q in %q)"
          letop
          (if rf then " rec" else "")
          (hlist2 letop_binding (andop_before letop_binding)) pel ""
          (comm_expr expr) e ""
      else
        pprintf pc "%s%s %q in %p"
          letop
          (if rf then " rec" else "")
          (hlist2 letop_binding (andop_before letop_binding)) pel ""
          (comm_expr expr) e)
    (fun () ->
      if pc.dang = ";" then
        pprintf pc "@[<a>begin %s%s %qin@;%q@ end@]"
          letop
          (if rf then " rec" else "")
          (vlist2 letop_binding (andop_before letop_binding)) pel ""
          expr_with_comm_except_if_sequence e ""
      else
        pprintf pc "%s%s %qin@ %p" letop (if rf then " rec" else "")
          (vlist2 letop_binding (andop_before letop_binding)) pel ""
          (**)
          (if Ploc.first_pos loc =
                Ploc.first_pos (MLast.loc_of_expr e)
           then
             (* comes from a 'where' in revised syntax *)
             expr
           else expr_with_comm_except_if_sequence)
          (*
                   expr_with_comm_except_if_sequence
           *)
          e)
;

EXTEND_PRINTER
  pr_attribute_body:
    [ "top"
      [ <:attribute_body< $attrid:(_, id)$ $exp:e$ ; >> ->
        pprintf pc "%s%p" id (space_before expr) e
      | <:attribute_body< $attrid:(_, id)$ $structure:st$ >> ->
        pprintf pc "%s%p" id (hlist (space_before (semi_semi_after str_item))) st
      | <:attribute_body< $attrid:(_, id)$ : $signature:si$ >> ->
        pprintf pc "%s:%p" id (hlist (space_before (semi_semi_after sig_item))) si
      | <:attribute_body< $attrid:(_, id)$ : $type:ty$ >> ->
        pprintf pc "%s:%p" id (space_before ctyp) ty
      | <:attribute_body< $attrid:(_, id)$ ? $patt:p$ >> ->
        pprintf pc "%s?%p" id (space_before patt) p
      | <:attribute_body< $attrid:(_, id)$ ? $patt:p$ when $expr:e$ >> ->
        pprintf pc "%s?%p when %p" id (space_before patt) p expr e
      ]
    ]
    ;
  pr_expr:
    [ "top"
      [ <:expr:< do { $list:el$ } >> as ge ->
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
               [  <:expr< $uid:"()"$ >> ->
                   if pc.dang = "else" then next pc ge
                   else pprintf pc "if %q then %p" curr e1 "" curr e2
               | _ ->
                   pprintf pc "if %q then %q else %p" curr e1 "" curr e2 ""
                     curr e3 ])
            (fun () ->
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
                   let has_vertic = if_case_has_vertic curr pc e1 e2 eel e3 in
                   (has_vertic, eel, e3)
                 else
                   let (eel, e3) = get_else_if e3 in
                   (False, eel, e3)
               in
               match e3 with
               [ <:expr< () >> ->
                   if pc.dang = "else" then next pc ge
                   else if eel = [] then if_then force_vertic curr pc (e1, e2)
                   else
                     pprintf pc "%q%p"
                       (if_then force_vertic curr) (e1, e2) "else"
                       (loop_else_if_no_else force_vertic curr) eel
               | _ ->
                   pprintf pc "%q%p"
                     (if_then force_vertic curr) (e1, e2) "else"
                     (loop_else_if_and_else force_vertic curr) (eel, e3) ])
      | <:expr:< fun [ $list:pwel$ ] >> as ge ->
          let use_function =
            List.exists (fun [ (_, _, <:expr< . >>) -> True | _ -> False ]) pwel in
          let funtok = if use_function then "function" else "fun" in
          match pwel with
          [ [(p1, <:vala< None >>, e1)] when is_irrefut_patt p1 ->
              let (pl, e1) = expr_fun_args e1 in
              let pl = [p1 :: pl] in
              let simple_patt = Eprinter.apply_level pr_patt "simple" in
              let pl = List.map (fun p -> (p, "")) pl in
              let comm_expr expr =
                match e1 with
                [ <:expr< do { $list:_$ } >> -> expr
                | <:expr< . >> -> (fun pc _ -> pprintf pc ".")
                | _ -> comm_expr expr ]
              in
              if List.mem pc.dang ["|"; ";"] then
                pprintf pc "(%s %p ->@;<1 3>%q)" funtok (plist simple_patt 4) pl
                  (comm_expr expr) e1 ""
              else
                pprintf pc "%s %p ->@;%p" funtok (plist simple_patt 4) pl
                  (comm_expr expr) e1
          | [] ->
              let loc = MLast.loc_of_expr ge in
              if List.mem pc.dang ["|"; ";"] then
                pprintf pc "(fun _ ->@;%p)" raise_match_failure loc
              else
                pprintf pc "fun _ ->@;%p" raise_match_failure loc
          | pwel ->
              if List.mem pc.dang ["|"; ";"] then
                pprintf pc "@[<1>(function@ %p)@]" (match_assoc_list loc) pwel
              else
                pprintf pc "@[<b>function@ %p@]" (match_assoc_list loc) pwel ]
      | <:expr:< try $e1$ with [ $list:pwel$ ] >> |
        <:expr:< match $e1$ with [ $list:pwel$ ] >> as e ->
          let op =
            match e with
            [ <:expr< try $_$ with [ $list:_$ ] >> -> "try"
            | _ -> "match" ]
          in
          match pwel with
          [ [(p, wo, e)] ->
              horiz_vertic
                (fun () ->
                   if List.mem pc.dang ["|"; ";"] then
                     pprintf pc "(%s %p with %p)" op expr e1
                       (match_assoc False) ((p, wo, e), True)
                   else
                     pprintf pc "%s %p with %p" op expr e1
                       (match_assoc False) ((p, wo, e), True))
                (fun () ->
                   if List.mem pc.dang ["|"; ";"] then
                     match
                       horiz_vertic
                         (fun () ->
                            let pc = {(pc) with aft = ""} in
                            Some
                              (pprintf pc "begin %s %q with" op expr e1 ""))
                         (fun () -> None)
                     with
                     [ Some s1 ->
                         let pc = {(pc) with bef = ""} in
                         pprintf pc "%s@;%p@ end" s1 (match_assoc False)
                           ((p, wo, e), True)
                     | None ->
                         pprintf pc "@[<a>begin %s@;%q@ with %p@ end@]" op
                           expr e1 "" (match_assoc False) ((p, wo, e), True) ]
                   else
                     match
                       horiz_vertic
                         (fun () ->
                            let pc = {(pc) with aft = ""} in
                            Some (pprintf pc "%s %q with" op expr e1 ""))
                         (fun () -> None)
                     with
                     [ Some _ ->
                         pprintf pc "%s %q with@;%p" op expr e1 ""
                           (match_assoc False) ((p, wo, e), True)
                     | None ->
                         pprintf pc "@[<a>%s@;%q@ with %p@]" op expr e1 ""
                           (match_assoc False) ((p, wo, e), True) ])
          | [] -> raise_match_failure pc (MLast.loc_of_expr e)
          | _ ->
              if List.mem pc.dang ["|"; ";"] then
                pprintf pc "@[<a>begin %s@;%p@ with@]@ %q@ end" op expr e1
                  (match_assoc_list loc) pwel ""
              else
                 pprintf pc "@[<a>%s@;%p@ with@]@ %p" op expr e1
                   (match_assoc_list loc) pwel ]
      | <:expr:< let $flag:rf$ $list:pel$ in $e$ >> as e0 ->
        let andop = "and" in
        let pel = List.map (fun x -> (andop, x)) pel in
        let loc = MLast.loc_of_expr e0 in
          pr_letlike "let" pc loc rf pel e

      | <:expr:< let exception $uid:e$ of $list:tl$ $algattrs:attrs$ in $x$ >> ->
          pprintf pc "@[<a>let %p@ in@] %p" exception_decl (loc, e, tl, [], attrs, []) curr x

      | <:expr< $lid:letop$ $arg$ (fun $bindpat$ -> $body$) >> as e0
           when not Pcaml.flag_expand_letop_syntax.val && is_letop letop ->
        let loc = MLast.loc_of_expr e0 in
        let rec deconstruct_ands acc = fun [
              (<:patt< ( $pat1$, $pat2$ ) >>, <:expr< $lid:andop$ $e1$ $e2$ >>) when is_andop andop ->
                deconstruct_ands [ (andop, (pat2, e2, <:vala< [] >>)) :: acc ] (pat1, e1)
            | (pat, exp) -> [ ("andop_unused", (pat, exp, <:vala< [] >>))::acc ]
        ] in
        let pel = deconstruct_ands [] (bindpat, arg) in
          pr_letlike letop pc loc False pel body

      | <:expr< let module $uidopt:s$ = $me$ in $e$ >> ->
          let s = uidopt_to_maybe_blank s in
          if pc.dang = ";" then
            pprintf pc "(@[<a>let module %s =@;%p@ in@]@ %p)" s module_expr me
              curr e
          else
            pprintf pc "@[<a>let module %s =@;%p@ in@]@ %p" s module_expr me
              curr e
      | <:expr< let open $!:ovf$ $m$ in $e$ >> ->
          if pc.dang = ";" then
            pprintf pc "(@[<a>let open%s %p@ in@]@ %p)" (if ovf then "!" else "") module_expr m curr e
          else
            pprintf pc "@[<a>let open%s %p@ in@]@ %p" (if ovf then "!" else "") module_expr m curr e
      | <:expr:< while $e1$ do { $list:el$ } >> ->
          pprintf pc "@[<a>@[<a>while@;%p@ do@]@;%p@ done@]" curr e1
            (hvlistl (semi_after expr) curr) el
      | <:expr:< for $v$ = $e1$ $to:d$ $e2$ do { $list:el$ } >> ->
          pprintf pc
            "@[<a>@[<a>for %p = %p %s@;<1 4>%p@ do@]@;%q@ done@]"
            patt v
            curr e1 (if d then "to" else "downto") curr e2
            (hvlistl (semi_after curr) curr) el "" ]
    | "tuple"
      [ <:expr< ($list:el$) >> ->
          let el = List.map (fun e -> (e, ",")) el in
          plist next 0 pc el ]
    | "assign"
      [ <:expr:< $x$ . val := $y$ >> -> operator pc next expr 2 (loc, ":=") x y
      | <:expr:< $x$ := $y$ >> -> operator pc next expr 2 (loc, "<-") x y ]
    | "or"
      [ z ->
          let unfold =
            fun
            [ <:expr< $lid:op$ $x$ $y$ >> ->
                if List.mem op ["||"; "or"] then
                   Some (x, " "^op, y)
                else None
            | _ -> None ]
          in
          let loc = MLast.loc_of_expr z in
          right_operator pc loc 0 unfold next z ]
    | "and"
      [ z ->
          let unfold =
            fun
            [ <:expr< $lid:op$ $x$ $y$ >> ->
                if List.mem op ["&&"; "&"] then
                  Some (x, " "^op, y)
                else None
            | _ -> None ]
          in
          let loc = MLast.loc_of_expr z in
          right_operator pc loc 0 unfold next z ]
    | "less"
      [ <:expr:< $lid:op$ $x$ $y$ >> as z ->
        if List.mem op ["!="; "<"; "<="; "<>"; "="; "=="; ">"; ">="] || is_infixop0 op then
              operator pc next next 0 (loc, op) x y
        else next pc z ]
    | "concat"
      [ z ->
          let unfold =
            fun
            [ <:expr< $lid:op$ $x$ $y$ >> ->
                if List.mem op ["^"; "@"] || is_infixop1 op then Some (x, " " ^ op, y) else None
            | _ -> None ]
          in
          let loc = MLast.loc_of_expr z in
          right_operator pc loc 0 unfold next z ]
    | "alg_attribute"
      [ <:expr< $e$ [@ $attribute:attr$] >> ->
        pprintf pc "%p[@%p]" curr e attribute_body attr
      ]

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
                if List.mem op ops || is_infixop2 op then Some (x, " " ^ op, y) else None
            | _ -> None ]
          in
          let loc = MLast.loc_of_expr z in
          left_operator pc loc 0 unfold next z ]
    | "mul"
      [ z ->
          let ops = ["*"; "*."; "/"; "/."; "%" ; "land"; "lor"; "lxor"; "mod"] in
          let unfold =
            fun
            [ <:expr< $lid:op$ $x$ $y$ >> ->
                if List.mem op ops || is_infixop3 op then Some (x, " " ^ op, y) else None
            | _ -> None ]
          in
          let loc = MLast.loc_of_expr z in
          left_operator pc loc 0 unfold next z ]
    | "pow"
      [ z ->
          let ops = ["**"; "asr"; "lsl"; "lsr"] in
          let unfold =
            fun
            [ <:expr< $lid:op$ $x$ $y$ >> ->
                if List.mem op ops || is_infixop4 op then Some (x, " " ^ op, y) else None
            | _ -> None ]
          in
          let loc = MLast.loc_of_expr z in
          right_operator pc loc 0 unfold next z ]
    | "unary_minus"
      [ <:expr< $lid:op$ $x$ >> as z ->
        let ops = [("-","-") ; ("-.","-."); ("~+","+"); ("~+.","+.")] in
        let in_ops x = List.mem_assoc x ops in
        if in_ops op then
          pprintf pc "%s%p" (List.assoc op ops) (unary in_ops curr) x
        else next pc z
      ]
    | "apply"
      [ <:expr< assert $e$ >> ->
          pprintf pc "assert@;%p" next e
      | <:expr< lazy $e$ >> ->
          pprintf pc "lazy@;%p" next e
      | <:expr:< $_$ $_$ >> as z ->
          let inf =
            match z with
            [ <:expr< $lid:n$ $_$ $_$ >> -> is_infix n || is_infix_operator n
            | <:expr< [$_$ :: $_$] >> -> True
            | _ -> False ]
          in
          if inf then next pc z
          else
            let cons_args_opt =
              loop [] z where rec loop args =
                fun
                [ <:expr< $x$ $y$ >> -> loop [y :: args] x
                | <:expr< $longid:_$ >> as e -> Some (e, args)
                | _ -> None ]
            in
            match cons_args_opt with
            [ Some (e, ([_; _ :: _] as al)) ->
                let expr_or = Eprinter.apply_level pr_expr "or" in
                let al = List.map (fun a -> (a, ",")) al in
                pprintf pc "%p@;@[<1>(%p)@]" next e (plist expr_or 0) al
            | _ ->
                let unfold =
                  fun
                  [
                     <:expr< [$_$ :: $_$] >> -> None
                  |  <:expr< $lid:n$ $_$ $_$ >> when is_infix n || is_infix_operator n -> None
                  |  <:expr< $lid:n$ $_$ >> when is_unary n || is_prefixop n -> None
                  |  <:expr< $x$ $y$ >> -> Some (x, "", y)
                  | e -> None ]
                in
                left_operator pc loc 2 unfold next z ] ]
    | "dot"
      [ <:expr< $longid:li$ . ( $e$ ) >> ->
        match e with [
          <:expr< $uid:"[]"$ >> -> pprintf pc "%p.@;<0 0>@[<a>[]@]" longident li
        | <:expr< [ $_$ :: $_$ ] >> -> pprintf pc "%p.@;<0 0>%p" longident li curr e

        | <:expr< { $list:_$ } >> -> pprintf pc "%p.@;<0 0>%p" longident li curr e
        | <:expr< {($_$) with $list:_$ } >> -> pprintf pc "%p.@;<0 0>%p" longident li curr e
        | <:expr:< $lid:v$ >> -> pprintf pc "%p.@;<0 0>%p" longident li var_escaped (loc,v)

        | e -> pprintf pc "%p.@;<0 0>@[<a>(%p)@]" longident li expr e
        ]

      | <:expr< $x$ . $lid:"val"$ >> -> pprintf pc "!%p" next x

      | <:expr:< $e$ . $lid:v$ >> -> pprintf pc "%p.@;<0 0>%p" curr e var_escaped (loc,v)
      | <:expr< $e$ . $lilongid:lili$ >> -> pprintf pc "%p.@;<0 0>%p" curr e longident_lident lili

      | <:expr< $longid:li$ >> -> longident pc li

      | <:expr< $x$ .( $y$ ) >> ->
          pprintf pc "%p@;<0 0>.(%p)" curr x expr_short y

      | <:expr< $x$ $dotop:op$ ( $list:el$ ) >> ->
          let el = List.map (fun e -> (e, ";")) el in
          pprintf pc "%p@;<0 0>%s(%p)" curr x op (plist expr_short 0) el

      | <:expr< $x$ .[ $y$ ] >> ->
          pprintf pc "%p@;<0 0>.[%p]" curr x expr_short y

      | <:expr< $x$ $dotop:op$ [ $list:el$ ] >> ->
          let el = List.map (fun e -> (e, ";")) el in
          pprintf pc "%p@;<0 0>%s[%p]" curr x op (plist expr_short 0) el

      | <:expr< $e$ .{ $list:el$ } >> ->
          let el = List.map (fun e -> (e, ",")) el in
          pprintf pc "%p.{%p}" curr e (plist expr_short 0) el

      | <:expr< $x$ $dotop:op$ { $list:el$ } >> ->
          let el = List.map (fun e -> (e, ";")) el in
          pprintf pc "%p@;<0 0>%s{%p}" curr x op (plist expr_short 0) el
      ]
    | "~."
      [ <:expr< $lid:op$ $x$ >> as z ->
        let in_ops x = is_prefixop x in
        if in_ops op then
          pprintf pc "%s%p" op (unary in_ops curr) x
        else next pc z
      ]
    | "simple"
      [ <:expr< {$list:lel$} >> ->
          let lxl = List.map (fun lx -> (lx, ";")) lel in
          pprintf pc "@[{%p}@]"
            (plistl (comm_patt_any (record_binding False))
               (comm_patt_any (record_binding True)) 1)
            lxl
      | <:expr< {($e$) with $list:lel$} >> -> do {
          do {
            let dot_expr = Eprinter.apply_level pr_expr "dot" in
            let lxl = List.map (fun lx -> (lx, ";")) lel in
            pprintf pc "@[{%p with @]%p}" dot_expr e
              (plistl (comm_patt_any (record_binding False))
                 (comm_patt_any (record_binding True)) 1)
              lxl
          }
        }
      | <:expr< [| $list:el$ |] >> ->
          if el = [] then pprintf pc "[| |]"
          else
            let el = List.map (fun e -> (e, ";")) el in
            pprintf pc "@[<3>[| %p |]@]" (plist expr 0) el
      | <:expr< [$_$ :: $_$] >> as z ->
          let (xl, y) = make_expr_list z in
          match y with
          [ Some _ -> pprintf pc "@[<1>(%q)@]" expr z ""
          | None ->
              let xl = List.map (fun x -> (x, ";")) xl in
              pprintf pc "@[<1>[%p]@]" (plist (comm_expr expr1) 0) xl ]
      | <:expr< ($e$ : $t$) >> ->
          pprintf pc "@[<1>(%p :@ %p)@]" expr e ctyp t
      | <:expr< (module $me$ : $mt$) >> ->
          pprintf pc "@[<1>(module %p :@ %p)@]" module_expr me module_type mt
      | <:expr< (module $me$) >> ->
          pprintf pc "(module %p)" module_expr me
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
      | <:expr:< . >> ->
          Ploc.raise loc
            (Failure "pr_expr of (PaUnr _) not allowed except at rhs of match-case")
      | <:expr:< $lid:s$ >> -> var_escaped pc (loc, s)
      | <:expr< `$s$ >> ->
          failwith "variants not pretty printed (in expr); add pr_ro.cmo"
      | <:expr< $str:s$ >> ->
          pprintf pc "\"%s\"" s
      | <:expr< [% $_extension:e$ ] >> ->
          pprintf pc "%p" (pr_extension "%") e
      | <:expr< $chr:s$ >> ->
          pprintf pc "'%s'" (ocaml_char s)
      | <:expr:< ?{$_$} >> | <:expr:< ~{$_$} >> | <:expr:< ~{$_$ = $_$} >> ->
          error loc ("labels not pretty printed (in expr)")
      | <:expr:< do { $list:el$ } >> ->
          let pc = {(pc) with dang = ""} in
          pprintf pc "@[<a>begin@;%p@ end@]"
            (hvlistl (semi_after (comm_expr expr1)) (comm_expr expr1)) el ]

    | "bottom"
      [ z ->
        let fail () =
          Ploc.raise (MLast.loc_of_expr z)
            (Failure (sprintf "pr_expr %d" (Obj.tag (Obj.repr z)))) in
          pprintf pc "@[<1>(%q)@]" (bottom ~{fail=fail}) z ""
      ] ]
  ;
  pr_patt:
    [ "top"
      [ <:patt< ($x$ as $y$) >> -> pprintf pc "%p@[ as %p@]" patt x patt y ]
    | "or"
      [ <:patt:< $_$ | $_$ >> as z ->
          let unfold =
            fun
            [ <:patt< $x$ | $y$ >> -> Some (x, " |", y)
            | _ -> None ]
          in
          left_operator pc loc 0 unfold next z ]
    | "tuple"
      [ <:patt< ($list:pl$) >> ->
          let pl = List.map (fun p -> (p, ",")) pl in
          plist next 0 pc pl ]
    | "alg_attribute"
      [ <:patt< $p$ [@ $attribute:attr$] >> ->
        pprintf pc "%p[@%p]" curr p attribute_body attr
      ]
    | [ <:patt:< exception $p$ >> ->
          pprintf pc "exception %p" next p ]
    | "range"
      [ <:patt< $x$ .. $y$ >> ->
          pprintf pc "%p..%p" next x next y ]
    | "cons"
      [ <:patt< [$_$ :: $_$] >> as z ->
          let (xl, y) = make_patt_list z in
          match y with
          [ Some y ->
              let xl = List.map (fun x -> (x, " ::")) (xl @ [y]) in
              plist next 0 pc xl
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
          | Some (p1, [p2]) -> pprintf pc "%p@;%p" curr p1 next p2
          | Some (p, pl) ->
              let patt = Eprinter.apply_level pr_patt "range" in
              let al = List.map (fun a -> (a, ",")) pl in
              pprintf pc "%p@;@[<1>(%p)@]" next p (plist patt 0) al ] ]
    | "simple"
      [ <:patt:< $longid:li$ . $lid:y$ >> -> pprintf pc "%p.(%p)" longident li var_escaped (loc, y)
      | <:patt< $longid:li$ . $p$ >> -> pprintf pc "%p.%p" longident li curr p
      | <:patt< $longid:li$ >> -> pprintf pc "%p" longident li
      | <:patt< $longid:li$ (type $list:l$) >> ->
        pprintf pc "%p (type %p)" longident li (hlist lident) (List.map snd l)
      ]
    | "atomic"
      [ 
        <:patt< lazy $p$ >> -> pprintf pc "lazy@;%p" curr p
      | <:patt< {$list:lpl$} >> ->
          let (lpl, closed) =
            List.fold_right
              (fun lp (lpl, closed) ->
                 match lp with
                 [ (<:patt< _ >>, <:patt< _ >>) -> (lpl, True)
                 | lp -> ([lp :: lpl], closed) ])
              lpl ([], False)
          in
          let lxl = List.map (fun (a,b) -> ((a,b,<:vala< []>>), ";")) lpl in
          pprintf pc "@[<1>{%p%s}@]" (plist (binding label_patt patt) 0) lxl
            (if closed then "; _" else "")
      | <:patt< [| $list:pl$ |] >> ->
          if pl = [] then pprintf pc "[| |]"
          else
            let pl = List.map (fun p -> (p, ";")) pl in
            pprintf pc "@[<3>[| %p |]@]" (plist patt 0) pl
      | <:patt< [$_$ :: $_$] >> as z ->
          let (xl, y) = make_patt_list z in
          match y with
          [ Some y -> pprintf pc "@[<1>(%p)@]" patt z
          | None ->
              let xl = List.map (fun x -> (x, ";")) xl in
              pprintf pc "@[<1>[%p]@]" (plist patt 0) xl ]
      | <:patt< ($p$ : $t$) >> ->
          pprintf pc "(%p :@;<1 1>%p)" patt p ctyp t
      | <:patt< (type $lid:s$) >> ->
          pprintf pc "(type %s)" s
      | <:patt< (module $uidopt:s$ : $mt$) >> ->
          let s = uidopt_to_maybe_blank s in
          pprintf pc "@[<1>(module %s :@ %p)@]" s module_type mt
      | <:patt< (module $uidopt:s$) >> ->
          let s = uidopt_to_maybe_blank s in
          pprintf pc "(module %s)" s
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
      | <:patt< [% $_extension:e$ ] >> ->
          pprintf pc "%p" (pr_extension "%") e
      | <:patt:< $lid:s$ >> -> var_escaped pc (loc, s)
      | <:patt:< $uid:s$ >> -> cons_escaped pc (loc, s)
      | <:patt< $chr:s$ >> -> pprintf pc "'%s'" (ocaml_char s)
      | <:patt< $str:s$ >> -> pprintf pc "\"%s\"" s
      | <:patt< _ >> -> pprintf pc "_"
      | <:patt:< ?{$_$} >> | <:patt:< ?{$_$ = $_$} >> | <:patt:< ?{$_$} >> |
        <:patt:< ?{$_$ = ?{$_$ = $_$}} >> | <:patt:< ?{$_$ = $_$} >> |
        <:patt:< ~{$list:_$} >> ->
          error loc "labels not pretty printed (in patt)"
      | <:patt< `$s$ >> ->
          failwith "polymorphic variants not pretty printed; add pr_ro.cmo" ]

    | "bottom"
      [ z ->
          let fail () = 
          Ploc.raise (MLast.loc_of_patt z)
            (Failure (sprintf "pr_patt %d: %s" (Obj.tag (Obj.repr z))
                        (Pp_MLast.show_patt z))) in
          pprintf pc "@[<1>(%p)@]" (bottom ~{fail=fail}) z
      ] ]
  ;
  pr_ctyp:
    [ "top"
      [ <:ctyp:< $x$ == $priv:pf$ $y$ >> ->
          let op = if pf then "= private" else "=" in
          operator pc next next 2 (loc, op) x y ]
    | "alg_attribute"
      [ <:ctyp< $ct$ [@ $attribute:attr$] >> ->
        pprintf pc "%p[@%p]" curr ct attribute_body attr
      ]
    | "below_alg_attribute"
      [ z -> next pc z ]
    | "arrow"
      [ <:ctyp:< $_$ -> $_$ >> as z ->
          let unfold =
            fun
            [ <:ctyp< $x$ -> $y$ >> -> Some (x, " ->", y)
            | _ -> None ]
          in
          right_operator pc loc 2 unfold next z ]
    | "star"
      [ <:ctyp< ($list:tl$) >> ->
          let tl = List.map (fun t -> (t, " *")) tl in
          plist next 2 pc tl ]
   | "apply"
      [ <:ctyp:< $t1$ $t2$ >> ->
          match t1 with
          [ <:ctyp< $_$ $_$ >> ->
              let (t, tl) =
                loop [t2] t1 where rec loop args =
                  fun
                  [ <:ctyp< $x$ $y$ >> -> loop [y :: args] x
                  | t -> (t, args) ]
              in
              pprintf pc "(%p)@;%p" (hlistl (comma_after ctyp) ctyp)
                tl curr t
          | _ ->
              match t2 with
              [ <:ctyp< $_$ $_$ >> -> pprintf pc "%p@;%p" curr t2 next t1
              | t -> pprintf pc "%p@;%p" next t2 next t1 ] ] ]
    | "dot"
      [
          <:ctyp< $longid:me$ . $lid:lid$ >> -> pprintf pc "%p.%s" longident me lid
      ]
    | "simple"
      [ <:ctyp:< { $list:ltl$ } >> ->
          pprintf pc "@[<a>@[<2>{ %p }@]@]"
            (hvlistl (semi_after label_decl) label_decl) ltl
      | <:ctyp:< [ $list:vdl$ ] >> ->
          if vdl = [] then pprintf pc "|"
          else
            horiz_vertic
              (fun () ->
                 if has_cons_with_params vdl then sprintf "\n"
                 else hlist2 cons_decl (bar_before cons_decl) pc vdl)
              (fun () ->
                 pprintf pc "  %p"
                   (vlist2 cons_decl (bar_before cons_decl)) vdl)
      | <:ctyp< ( module $mt$ ) >> ->
          pprintf pc "@[<1>(module@ %p)@]" module_type mt
      | <:ctyp:< $lid:t$ >> ->
          var_escaped pc (loc, t)
      | <:ctyp:< ' $s$ >> ->
          pprintf pc "%p" type_var s
      | <:ctyp< _ >> ->
          pprintf pc "_"
      | <:ctyp< .. >> -> pprintf pc ".."
      | <:ctyp< [% $_extension:e$ ] >> ->
          pprintf pc "%p" (pr_extension "%") e
      | <:ctyp:< ?$_$: $_$ >> | <:ctyp:< ~$_$: $_$ >> ->
          error loc "labels not pretty printed (in type)"
      | <:ctyp< [ = $list:_$ ] >> | <:ctyp< [ > $list:_$ ] >> |
        <:ctyp< [ < $list:_$ ] >> | <:ctyp< [ < $list:_$ > $list:_$ ] >> ->
          failwith "variants not pretty printed (in type); add pr_ro.cmo"
      ]
    | "bottom"
      [ z ->
          let fail() = 
          Ploc.raise (MLast.loc_of_ctyp z)
            (Failure (sprintf "[INTERNAL ERROR] pr_ctyp %d" (Obj.tag (Obj.repr z)))) in
          pprintf pc "@[<1>(%p)@]" (bottom ~{fail=fail}) z
      ] ]
  ;
  pr_str_item:
    [ "top"
      [ <:str_item< # $lid:s$ $e$ >> ->
          let pc = {(pc) with aft = ""} in
          pprintf pc "(* #%s %p *)" s expr e
      | <:str_item:< declare $list:sil$ end >> ->
          if sil = [] then
            let pc = {(pc) with aft = ""} in
            pprintf pc "(* *)"
          else
            let str_item_sep =
              if flag_semi_semi.val then semi_semi_after str_item
              else str_item
            in
            vlistl str_item_sep str_item pc sil

      | <:str_item:< exception $excon:ec$ $_itemattrs:item_attrs$ >> ->
          pprintf pc "exception %p%p" (extension_constructor loc) ec
            (hlist (pr_attribute "@@")) (Pcaml.unvala item_attrs)
      | <:str_item:< external $lid:n$ : $list:tyvars$ . $t$ = $list:sl$ $itemattrs:attrs$ >> ->
          external_decl pc (loc, n, tyvars, t, sl, attrs)
      | <:str_item< include $me$ $_itemattrs:attrs$ >> ->
          pprintf pc "include %p%p" module_expr me (hlist (pr_attribute "@@")) (Pcaml.unvala attrs)
      | <:str_item< module $flag:rf$ $list:mdl$ >> ->
          let mdl = List.map (fun (m, mt, item_attrs) -> (map_option Pcaml.unvala (Pcaml.unvala m), mt, item_attrs)) mdl in
          let rf = if rf then " rec" else "" in
          vlist2 (str_module ("module" ^ rf)) (str_module "and") pc mdl
      | <:str_item< module type $m$ = $mt$ $_itemattrs:item_attrs$ >> ->
          sig_module_or_module_type "module type" False "=" pc (Some m, mt, item_attrs)
      | <:str_item< module type $m$ = ' $id$ $_itemattrs:item_attrs$ >> ->
          pprintf pc "module type %s%p" m (hlist (pr_attribute "@@")) (Pcaml.unvala item_attrs)
      | <:str_item:< open $_!:ovf$ $me$ $_itemattrs:attrs$ >> ->
          pprintf pc "open%s %p%p" (if (Pcaml.unvala ovf) then "!" else "")
            module_expr me (hlist (pr_attribute "@@")) (Pcaml.unvala attrs)
      | <:str_item:< type $flag:nonrf$ $list:tdl$ >> ->
          pprintf pc "type%s %p" (if nonrf then " nonrec" else "")
            (vlist2 type_decl (and_before type_decl)) tdl
      | MLast.StTypExten loc te ->
          pprintf pc "type %p" (type_extension loc) te
      | <:str_item:< value $flag:rf$ $list:pel$ >> ->
          horiz_vertic
            (fun () ->
               pprintf pc "let%s %p" (if rf then " rec" else "")
                 (hlist2 let_binding (and_before let_binding)) pel)
            (fun () ->
               pprintf pc "let%s %p" (if rf then " rec" else "")
                 (vlist2 let_binding (and_before let_binding)) pel)
      | <:str_item< $exp:e$ $itemattrs:attrs$ >> ->
          if pc.aft = ";;" then
            pprintf pc "%p%p" expr e (hlist (pr_attribute "@@")) attrs
          else
            pprintf pc "let _ =@;%p%p" expr e (hlist (pr_attribute "@@")) attrs
      | <:str_item< class type $list:_$ >> | <:str_item< class $list:_$ >> ->
          failwith "classes and objects not pretty printed; add pr_ro.cmo"
      | MLast.StUse _ fn sl ->
          let pc = {(pc) with aft = ""} in
          pprintf pc ""
      | <:str_item< [@@@ $_attribute:attr$ ] >> ->
          pprintf pc "%p" (pr_attribute "@@@") attr
      | <:str_item< [%% $_extension:e$ ] $itemattrs:attrs$ >> ->
          pprintf pc "%p%p" (pr_extension "%%") e (hlist (pr_attribute "@@")) attrs
      ] ]
  ;
  pr_sig_item:
    [ "top"
      [ <:sig_item< # $lid:s$ $e$ >> ->
          let pc = {(pc) with aft = ""} in
          pprintf pc "(* #%s %p *)" s expr e
      | MLast.SgExc _ gc item_attrs -> pprintf pc "exception %p%p" cons_decl gc
            (hlist (pr_attribute "@@")) (Pcaml.unvala item_attrs)

      | <:sig_item:< external $lid:n$ : $list:tyvars$ . $t$ = $list:sl$ $itemattrs:attrs$ >> ->
          external_decl pc (loc, n, tyvars, t, sl, attrs)

      | <:sig_item< include $mt$ $_itemattrs:item_attrs$ >> ->
          pprintf pc "include %p%p" module_type mt (hlist (pr_attribute "@@")) (Pcaml.unvala item_attrs)
      | <:sig_item:< declare $list:sil$ end >> ->
          if sil = [] then
            let pc = {(pc) with aft = ""} in
            pprintf pc "(* *)"
          else
            let sig_item_sep =
              if flag_semi_semi.val then semi_semi_after sig_item
              else sig_item
            in
            vlistl sig_item_sep sig_item pc sil
      | <:sig_item< module $flag:rf$ $list:mdl$ >> ->
          let mdl = List.map (fun (m, mt, item_attrs) -> (map_option Pcaml.unvala (Pcaml.unvala m), mt, item_attrs)) mdl in
          let rf = if rf then " rec" else "" in
          vlist2 (sig_module_or_module_type ("module" ^ rf) True ":")
            (sig_module_or_module_type "and" True ":") pc mdl
      | <:sig_item< module $uid:i$ := $longid:li$  $_itemattrs:item_attrs$ >> ->
          pprintf pc "module %s := %p%p" i longident li (hlist (pr_attribute "@@")) (Pcaml.unvala item_attrs)
      | <:sig_item:< module alias $uid:i$ = $longid:li$ $itemattrs:item_attrs$ >> ->
          pprintf pc "module %s = %p%p" i longident li (hlist (pr_attribute "@@")) item_attrs
      | <:sig_item< module type $m$ = $mt$ $_itemattrs:item_attrs$ >> ->
          sig_module_or_module_type "module type" False "=" pc (Some m, mt, item_attrs)
      | <:sig_item< module type $m$ := $mt$ $_itemattrs:item_attrs$ >> ->
          sig_module_or_module_type "module type" False ":=" pc (Some m, mt, item_attrs)
      | <:sig_item< module type $m$ = ' $id$ $_itemattrs:item_attrs$ >> ->
          pprintf pc "module type %s%p" m (hlist (pr_attribute "@@")) (Pcaml.unvala item_attrs)
      | <:sig_item< open $longid:i$ $_itemattrs:item_attrs$ >> ->
          pprintf pc "open %p%p" longident i (hlist (pr_attribute "@@")) (Pcaml.unvala item_attrs)
      | <:sig_item:< type $flag:nonrf$ $list:tdl$ >> ->
          pprintf pc "type%s %p"
            (if nonrf then " nonrec" else "")
            (vlist2 type_decl (and_before type_decl)) tdl
      | MLast.SgTypExten loc te ->
          pprintf pc "type %p" (type_extension loc) te
      | <:sig_item:< value $lid:s$ : $t$ $itemattrs:attrs$ >> ->
          pprintf pc "val %p :@;%p%p" var_escaped (loc, s) ctyp t (hlist (pr_attribute "@@")) attrs
      | <:sig_item< class type $list:_$ >> | <:sig_item< class $list:_$ >> ->
          failwith "classes and objects not pretty printed; add pr_ro.cmo"
      | <:sig_item< [@@@ $_attribute:attr$ ] >> ->
          pprintf pc "%p" (pr_attribute "@@@") attr
      | <:sig_item< [%% $_extension:e$ ] $itemattrs:attrs$ >> ->
          pprintf pc "%p%p" (pr_extension "%%") e (hlist (pr_attribute "@@")) attrs
      ] ]
  ;
  pr_longident:
    [ "dot"
      [ <:extended_longident:< $longid:x$ . $uid:uid$ >> ->
          pprintf pc "%p.%p" curr x cons_escaped (loc, uid)
      | <:extended_longident< $longid:x$ ( $longid:y$ ) >> ->
          pprintf pc "%p(%p)" longident x longident y
      | <:extended_longident:< $uid:s$ >> ->
          pprintf pc "%p" cons_escaped (loc, s)
      ]
    | "bottom" [
        z -> pprintf pc "[INTERNAL ERROR(pr_module_longident): unexpected longident]"
      ]
    ]
  ;
  pr_module_expr:
    [ "top"
      [ <:module_expr< functor $fp:arg$ -> $me$ >> ->
          str_or_sig_functor pc (functor_parameter_unvala arg) module_expr me ]
    | "alg_attribute"
      [ <:module_expr< $ct$ [@ $attribute:attr$] >> ->
        pprintf pc "%p[@%p]" curr ct attribute_body attr
      ]
    | [ <:module_expr:< struct $list:sil$ end >> ->
          let str_item_sep =
            if flag_semi_semi.val then semi_semi_after str_item
            else str_item
          in
          horiz_vertic
            (fun () ->
               if alone_in_line pc then
                 (* Heuristic : I don't like to print structs horizontally
                    when alone in a line. *)
                 sprintf "\n"
               else
                 pprintf pc "struct %p end" (hlist str_item_sep) sil)
            (fun () ->
               pprintf pc "@[<b>struct@;%p@ end@]" (vlist str_item_sep) sil) ]
   | "apply"
      [ <:module_expr< $x$ $y$ >> ->
          let mod_exp2 pc (is_first, me) =
            if is_first then
              next pc me
            else pprintf pc "(%p)" module_expr me
          in
          let (me, mel) =
            loop [(False, y)] x where rec loop mel =
              fun
              [ <:module_expr< $x$ $y$ >> -> loop [(False, y) :: mel] x
              | me -> ((True, me), mel) ]
          in
          let mel = List.map (fun me -> (me, "")) [me :: mel] in
          plist mod_exp2 2 pc mel ]
    | "dot"
      [ <:module_expr< $x$ . $y$ >> ->
          pprintf pc "%p.%p" curr x curr y ]
    | "simple"
      [ <:module_expr< $uid:s$ >> ->
          pprintf pc "%s" s
      | <:module_expr< (value $e$ : $mt1$ :> $mt2$) >> ->
          pprintf pc "@[<1>(val %p :@ %p :>@ %p)@]" expr e module_type mt1 module_type mt2
      | <:module_expr< (value $e$ : $mt$) >> ->
          pprintf pc "@[<1>(val %p :@ %p)@]" expr e module_type mt
      | <:module_expr< (value $e$) >> ->
          pprintf pc "(val %p)" expr e
      | <:module_expr< ($me$ : $mt$) >> ->
          pprintf pc "@[<1>(%p :@ %p)@]" module_expr me module_type mt
      | <:module_expr< [% $_extension:e$ ] >> ->
          pprintf pc "%p" (pr_extension "%") e ]
    | [ z ->
          let fail() =
          Ploc.raise (MLast.loc_of_module_expr z)
            (Failure (sprintf "pr_module_expr %d" (Obj.tag (Obj.repr z)))) in
          pprintf pc "@[<1>(%p)@]" (bottom ~{fail=fail}) z
      ] ]
  ;
  pr_module_type:
    [ "top"
      [ <:module_type< functor $fp:arg$ -> $mt2$ >> ->
          str_or_sig_functor pc (functor_parameter_unvala arg) module_type mt2 ]
    | [ <:module_type< module type of $me$ >> ->
          pprintf pc "@[module type of@ %p@]" module_expr me ]
    | "alg_attribute"
      [ <:module_type< $ct$ [@ $attribute:attr$] >> ->
        pprintf pc "%p[@%p]" curr ct attribute_body attr
      ]
    | "with" [ <:module_type< $mt$ with $list:wcl$ >> ->
        pprintf pc "%p with@;%p" module_type mt
          (vlist2 with_constraint (and_before with_constraint)) wcl ]
    | "sig" [ <:module_type:< sig $list:sil$ end >> ->
          let sig_item_sep =
            if flag_semi_semi.val then semi_semi_after sig_item
            else sig_item
          in
          horiz_vertic
            (fun () ->
               if alone_in_line pc then
                 (* Heuristic : I don't like to print sigs horizontally
                    when alone in a line. *)
                 sprintf "\n"
               else
                 pprintf pc "sig %p end" (hlist sig_item_sep) sil)
            (fun () ->
               pprintf pc "sig@;%p@ end" (vlist sig_item_sep) sil)
      ]
    | "dot"
      [ <:module_type< $longid:li$ . $lid:s$ >> ->
          pprintf pc "%p.%s" longident li s
      | <:module_type< $longid:li$ >> ->
          pprintf pc "%p" longident li
      | <:module_type< $lid:s$ >> ->
          pprintf pc "%s" s
    ]
    | "simple"
      [ <:module_type< $uid:s$ >> ->
          pprintf pc "%s" s
      | <:module_type< [% $_extension:e$ ] >> ->
          pprintf pc "%p" (pr_extension "%") e ]
    | "bottom"
      [ z ->
          let fail() =
          Ploc.raise (MLast.loc_of_module_type z)
            (Failure (sprintf "pr_module_type %d" (Obj.tag (Obj.repr z)))) in
          pprintf pc "(%p)" (bottom ~{fail=fail}) z ] ]
  ;
END;

value space_before elem pc x = pprintf pc " %p" elem x;
value or_before elem pc x = pprintf pc "or %p" elem x;
value amp_after elem pc x = pprintf pc "%p &" elem x;

value option elem pc x =
  match x with
  [ Some x -> elem pc x
  | None -> pprintf pc "" ]
;

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

value apply_printer f (ast, eoi_loc) = do {
  let oc =
    match Pcaml.output_file.val with
    [ Some f -> open_out_bin f
    | None -> do { pervasives_set_binary_mode_out stdout True; stdout } ]
  in
  let cleanup () =
    match Pcaml.output_file.val with
    [ Some f -> close_out oc
    | None -> () ]
  in
  try do {
    let _ =
      List.fold_left
        (fun first (si, loc) -> do {
           match sep.val with
           [ Some str -> if first then () else output_string_eval oc str
           | None -> output_string oc (Ploc.comment loc) ];
           flush oc;
           let k = if flag_semi_semi.val then ";;" else "" in
           output_string oc (f {ind = 0; bef = ""; aft = k; dang = ""} si);
           False
         })
        True ast
    in
    output_string oc (Ploc.comment eoi_loc);
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

value is_uppercase c = char_uppercase c = c;

value set_flags s =
  loop 0 where rec loop i =
    if i = String.length s then ()
    else do {
      let is_upp = is_uppercase s.[i] in
      match s.[i] with
      [ 'A' | 'a' -> do {
          flag_comments_in_phrases.val := is_upp;
          flag_equilibrate_cases.val := is_upp;
          flag_expand_letop_syntax.val := is_upp;
          flag_extensions_are_irrefutable.val := is_upp;
          flag_horiz_let_in.val := is_upp;
          flag_semi_semi.val := is_upp;
        }
      | 'C' | 'c' -> flag_comments_in_phrases.val := is_upp
      | 'E' | 'e' -> flag_equilibrate_cases.val := is_upp
      | 'I' | 'i' -> flag_extensions_are_irrefutable.val := is_uppercase s.[i]
      | 'L' | 'l' -> flag_horiz_let_in.val := is_upp
      | 'M' | 'm' -> flag_semi_semi.val := is_upp
      | 'O' | 'o' -> flag_add_locations.val := is_upp
      | 'X' | 'x' -> flag_expand_letop_syntax.val := is_upp
      | c -> failwith ("bad flag " ^ String.make 1 c) ];
      loop (i + 1)
    }
;

value default_flag () =
  let flag_on b t f = if b then t else "" in
  let flag_off b t f = if b then "" else f in
  let on_off flag =
    sprintf "%s%s%s%s%s%s%s"
      (flag flag_comments_in_phrases.val "C" "c")
      (flag flag_equilibrate_cases.val "E" "e")
      (flag flag_extensions_are_irrefutable.val "I" "i")
      (flag flag_horiz_let_in.val "L" "l")
      (flag flag_semi_semi.val "M" "m")
      (flag flag_add_locations.val "O" "o")
      (flag flag_expand_letop_syntax.val "X" "x")
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
       I/i enable/disable extensions in patterns treated as irrefutable
       L/l enable/disable allowing printing 'let..in' horizontally
       M/m enable/disable printing double semicolons
       O/o enable/disable adding location comments
       Z/z enable/disable compatibility with old versions of OCaml
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

value amp_before elem pc x = pprintf pc "& %p" elem x;

value class_type_params pc (loc, ctp) =
  if ctp = [] then pprintf pc ""
  else
    let ctp = List.map (fun ct -> ((loc, ct), ",")) ctp in
    pprintf pc "[%p]@;" (plist type_param 1) ctp
;

value class_def pc ci =
  pprintf pc "%s%p%s :@;%p%p"
    (if Pcaml.unvala ci.MLast.ciVir then "virtual " else "")
    class_type_params (ci.MLast.ciLoc, Pcaml.unvala (snd ci.MLast.ciPrm))
    (Pcaml.unvala ci.MLast.ciNam) class_type ci.MLast.ciExp
    (hlist (pr_attribute "@@")) (Pcaml.unvala ci.MLast.ciAttributes)
;

value class_type_decl pc ci =
  pprintf pc "%s%p%s =@;%p%p"
    (if Pcaml.unvala ci.MLast.ciVir then "virtual " else "")
    class_type_params (ci.MLast.ciLoc, Pcaml.unvala (snd ci.MLast.ciPrm))
    (Pcaml.unvala ci.MLast.ciNam) class_type ci.MLast.ciExp
    (hlist (pr_attribute "@@")) (Pcaml.unvala ci.MLast.ciAttributes)
;

value class_type_decl_list pc loc cd =
  horiz_vertic
    (fun () ->
       pprintf pc "class type %p"
         (hlist2 class_type_decl (and_before class_type_decl)) cd)
    (fun () ->
       pprintf pc "class type %p"
         (vlist2 class_type_decl (and_before class_type_decl)) cd)
;

value class_type_opt pc =
  fun
  [ Some ct -> pprintf pc " :@ %p" class_type ct
  | None -> pprintf pc "" ]
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
  let (ce, ct_opt) =
    match ce with
    [ <:class_expr< ($ce$ : $ct$) >> -> (ce, Some ct)
    | ce -> (ce, None) ]
  in
  let cdef pc () =
    horiz_vertic
      (fun () ->
         pprintf pc "%s%p%s%s%p%p ="
           (if Pcaml.unvala ci.MLast.ciVir then "virtual " else "")
           class_type_params (ci.MLast.ciLoc, Pcaml.unvala (snd ci.MLast.ciPrm))
           (Pcaml.unvala ci.MLast.ciNam) (if pl = [] then "" else " ")
           (hlist simple_patt) pl class_type_opt ct_opt)
      (fun () ->
         let pl = List.map (fun p -> (p, "")) pl in
         let pc =
           {(pc) with
            bef =
              sprintf "%s%s%s%s " pc.bef
                (if Pcaml.unvala ci.MLast.ciVir then "virtual " else "")
                (class_type_params Pprintf.empty_pc
                   (ci.MLast.ciLoc, Pcaml.unvala (snd ci.MLast.ciPrm)))
                (Pcaml.unvala ci.MLast.ciNam)}
         in
         pprintf pc "%p%p =" (plistl simple_patt simple_patt 4) pl class_type_opt ct_opt)
  in
  pprintf pc "@[%p@;%p%p@]" cdef () class_expr ce
    (hlist (pr_attribute "@@")) (Pcaml.unvala ci.MLast.ciAttributes)
;

value variant_decl pc pv =
  match pv with
  [ <:poly_variant< `$c$ $_algattrs:alg_attrs$ >> ->
       pprintf pc "`%s%p" c (hlist (pr_attribute "@")) (Pcaml.unvala alg_attrs)
  | <:poly_variant< `$c$ of $flag:ao$ $list:tl$ $_algattrs:alg_attrs$ >> ->
       let tl = List.map (fun t -> (t, " &")) tl in
       pprintf pc "`%s of%s@;<1 5>%p%p" c (if ao then " &" else "")
         (plist ctyp 2) tl (hlist (pr_attribute "@")) (Pcaml.unvala alg_attrs)
  | <:poly_variant< $t$ >> ->
       ctyp pc t
  | IFDEF STRICT THEN
      _ -> failwith "Pr_ro.variant_decl"
    END ]
;

value bquote_ident pc s = pprintf pc "`%s" s;

value variant_decl_list char loc pc pvl sl =
  if pvl = [] then pprintf pc "[%s ]" char
  else
    horiz_vertic
      (fun () ->
         pprintf pc "[%s %p%p ]" char
           (hlist2 variant_decl (bar_before variant_decl)) pvl
           (fun pc → fun
            | [] → pprintf pc ""
            | sl → pprintf pc " > %p" (hlist bquote_ident) sl
            end) sl)
      (fun () ->
         pprintf pc "[%s %p%p ]" char
           (vlist2 variant_decl (bar_before variant_decl)) pvl
           (fun pc → fun
            | [] → pprintf pc ""
            | sl → pprintf pc " > %p" (hlist bquote_ident) sl
            end) sl)
;

value field pc = fun [
  (Some s, t,attrs) -> pprintf pc "%s :@;%p%p" s ctyp t
    (hlist (pr_attribute "@")) (Pcaml.unvala attrs)
| (None, t,attrs) -> pprintf pc "@;%p%p" ctyp t
    (hlist (pr_attribute "@")) (Pcaml.unvala attrs)
]
;

value field_expr pc (s, e) = pprintf pc "%s =@;%p" s expr e;

value patt_tcon pc p =
  match p with
  [ <:patt< ($p$ : $t$) >> -> pprintf pc "%p :@ %p" patt p ctyp t
  | p -> patt pc p ]
;

value typevar pc tv = pprintf pc "'%s" tv;

value class_object loc pc (csp, csl) =
  let class_str_item_sep =
(*
    if flag_semi_semi.val then semi_semi_after class_str_item
    else *) class_str_item
  in
  horiz_vertic
    (fun () ->
       pprintf pc "object%p %p end"
         (fun pc ->
            fun
            [ Some (<:patt< ($_$ : $_$) >> as p) -> pprintf pc " %p" patt p
            | Some p -> pprintf pc " (%p)" patt p
            | None -> pprintf pc "" ])
         csp (hlist class_str_item_sep) csl)
    (fun () ->
       pprintf pc "@[<a>object%p@;%p@ end@]"
         (fun pc ->
            fun
            [ Some (<:patt< ($_$ : $_$) >> as p) -> pprintf pc " %p" patt p
            | Some p -> pprintf pc " (%p)" patt p
            | None -> pprintf pc "" ])
         csp (vlist class_str_item_sep) csl)
;

value simple_expr = Eprinter.apply_level pr_expr "simple";

(* *)

value label_ipatt_eq_patt curr pc (p, op) =
  match Pcaml.unvala op with
  [ Some p2 -> pprintf pc "~%p:%p" patt p curr p2
  | None -> pprintf pc "~%p" patt p ]
;

EXTEND_PRINTER
  pr_patt: LEVEL "simple"
    [ [ <:patt< ~{$list:lpop$} >> ->
          let lpop = List.map (fun poe -> (poe, "")) lpop in
          pprintf pc "%p" (plist (label_ipatt_eq_patt curr) 1) lpop
      | <:patt< ?{$lid:p$ : $t$} >> ->
          pprintf pc "?(%s :@;%p)" p ctyp t
      | <:patt< ?{$lid:p$ : $t$ = $e$} >> ->
          pprintf pc "?(%s :@;%p =@;%p)" p ctyp t expr e
      | <:patt< ?{$p1$ = ?{$p2$ = $e$}} >> ->
          pprintf pc "?%p:(%p =@;%p)" patt p1 patt p2 expr e
      | <:patt< ?{$p1$ = ?{$p2$}} >> ->
          pprintf pc "?%p:(%p)" patt p1 patt p2
      | <:patt< ?{$p$ = $e$} >> ->
          pprintf pc "?(%p =@;%p)" patt p expr e
      | <:patt< ?{$p$} >> ->
          pprintf pc "?%p" curr p

      | <:patt< `$s$ >> ->
          pprintf pc "`%s" s
      | <:patt:< # $lilongid:lili$ >> ->
          pprintf pc "#%p" longident_lident lili ] ]
  ;
  pr_expr: LEVEL "apply"
    [ [ <:expr< new $lilongid:lili$ >> ->
          pprintf pc "new@;%p" longident_lident lili
      | <:expr:< object $opt:csp$ $list:csl$ end >> ->
          class_object loc pc (csp, csl) ] ]
  ;
  pr_expr: LEVEL "dot"
    [ [ <:expr< $e$ # $lid:s$ >> -> pprintf pc "%p#@;<0 0>%s" curr e s
      | <:expr< $lid:op$ $e1$ $e2$ >> when is_hashop op ->
        pprintf pc "%p %s@;<1 0>%p" curr e1 op next e2
      ] ]
  ;
  pr_expr: LEVEL "simple"
    [ [ <:expr< ( $e$ : $t$ :> $t2$ ) >> ->
          pprintf pc "@[<a>(%p :@;<1 1>%p :>@;<1 1>%p)@]" expr e ctyp t
            ctyp t2
      | <:expr< ( $e$ :> $t$ ) >> ->
          pprintf pc "@[<1>(%p :>@ %p)@]" expr e ctyp t
      | <:expr< {< $list:fel$ >} >> ->
          if fel = [] then pprintf pc "{< >}"
          else
            let fel = List.map (fun fe -> (fe, ";")) fel in
            pprintf pc "{< %p >}" (plist field_expr 3) fel
      | <:expr< `$s$ >> ->
          pprintf pc "`%s" s
      | <:expr< new $lid:_$ >> | <:expr< new $longid:_$ . $lid:_$ >>
      | <:expr< object $list:_$ end >> as z ->
          pprintf pc "@[<1>(%p)@]" expr z ] ]
  ;
  pr_ctyp: AFTER "star"
    [ "label"
      [ <:ctyp< ?$i$: $t$ >> -> pprintf pc "?%s:%p" i curr t
      | <:ctyp< ~$i$: $t$ >> -> pprintf pc "%s:%p" i curr t ] ]
  ;
  pr_ctyp: LEVEL "simple"
    [ [ <:ctyp< < $list:ml$ $flag:v$ > >> ->
          if ml = [] then pprintf pc "<%s >" (if v then " .." else "")
          else
            let ml = List.map (fun e -> (e, ";")) ml in
            pprintf pc "< %p%s >@;<1 0>" (plist field 0) ml
              (if v then "; .." else "")
      | <:ctyp< # $lilongid:lili$ >> ->
          pprintf pc "#%p" longident_lident lili
      | <:ctyp:< [ = $list:pvl$ ] >> ->
          let prefix = match pvl with [
            [] -> ""
          | [ <:poly_variant< $_$ >> :: _ ] -> " |"
          | _ -> ""
          ] in
          variant_decl_list prefix loc pc pvl []
      | <:ctyp:< [ > $list:pvl$ ] >> ->
          variant_decl_list ">" loc pc pvl []
      | <:ctyp:< [ < $list:pvl$ ] >> ->
          variant_decl_list "<" loc pc pvl []
      | <:ctyp:< [ < $list:pvl$ > $list:vdl$ ] >> ->
          variant_decl_list "<" loc pc pvl vdl
      | <:ctyp< $_$ as $_$ >> as z ->
          pprintf pc "@[<1>(%p)@]" ctyp z ] ]
  ;
  pr_sig_item: LEVEL "top"
    [ [ <:sig_item:< class $list:cd$ >> ->
          horiz_vertic
            (fun () ->
               pprintf pc "class %p"
                 (hlist2 class_def (and_before class_def)) cd)
            (fun () ->
               pprintf pc "class %p"
                 (vlist2 class_def (and_before class_def)) cd)
      | <:sig_item:< class type $list:cd$ >> ->
          class_type_decl_list pc loc cd ] ]
  ;
  pr_str_item: LEVEL "top"
    [ [ <:str_item:< class $list:cd$ >> ->
          horiz_vertic
            (fun () ->
               pprintf pc "class %p"
                 (hlist2 class_decl (and_before class_decl)) cd)
            (fun () ->
               pprintf pc "class %p"
                 (vlist2 class_decl (and_before class_decl)) cd)
      | <:str_item:< class type $list:cd$ >> ->
          class_type_decl_list pc loc cd ] ]
  ;
END;

value sig_method_or_method_virtual pc virt priv s t item_attrs =
  pprintf pc "method%s%s %s :@;%p%p" virt (if priv then " private" else "")
    s ctyp t (hlist (pr_attribute "@@")) (Pcaml.unvala item_attrs)

;

value poly_type pc =
  fun
  [ <:ctyp< ! $list:tpl$ . $t$ >> ->
      pprintf pc "%p .@;%p" (hlist typevar) tpl ctyp t
  | t -> ctyp pc t ]
;

value label_ipatt expr pc (p, oe) =
  match Pcaml.unvala oe with
  [ Some e -> pprintf pc "~%p:%p" patt p expr e
  | None -> pprintf pc "~%p" patt p ]
;

EXTEND_PRINTER
  pr_expr: AFTER "apply"
    [ "label"
      [ <:expr< ~{$list:lpoe$} >> ->
          let lpoe = List.map (fun poe -> (poe, "")) lpoe in
          pprintf pc "%p" (plist (label_ipatt curr) 1) lpoe
      | <:expr< ?{$p$ = $e$} >> ->
          pprintf pc "?%p:%p" patt p curr e
      | <:expr< ?{$p$} >> ->
          pprintf pc "?%p" patt p ] ]
  ;
  pr_ctyp: AFTER "below_alg_attribute"
    [ "as"
      [ <:ctyp< $t1$ as $t2$ >> -> pprintf pc "%p@[ as %p@]" curr t1 next t2 ]
    | "poly"
      [ <:ctyp< ! $list:_$ . $_$ >> as z -> poly_type pc z
      | <:ctyp:< type $list:pl$ . $t$ >> ->
          pprintf pc "type %p .@;%p" (hlist lident) pl ctyp t ] ]
  ;
  pr_ctyp: AFTER "arrow"
    [ "label"
      [ <:ctyp< ?$i$: $t$ >> -> pprintf pc "?%s:%p" i curr t
      | <:ctyp< ~$i$: $t$ >> -> pprintf pc "%s:%p" i curr t ] ]
  ;
  pr_ctyp: AFTER "bottom"
    [ "catch-poly"
      [ <:ctyp< ! $list:_$ . $_$ >> 
      | <:ctyp:< type $list:pl$ . $t$ >> as z ->
          pprintf pc "@[<1>(%p)@]" ctyp z
      ]
    ]
  ;
  pr_class_expr:
    [ "top"
      [ <:class_expr< fun $p$ -> $ce$ >> ->
          pprintf pc "fun %p ->@;%p" patt p curr ce
      | <:class_expr:< let $flag:rf$ $list:pel$ in $ce$ >> ->
          horiz_vertic
            (fun () ->
               pprintf pc "let%s %p in %p" (if rf then " rec" else "")
                 (hlist2 (binding patt expr) (and_before (binding patt expr))) pel
                 class_expr ce)
            (fun () ->
               pprintf pc "let%s %p in@ %p" (if rf then " rec" else "")
                 (vlist2 (binding patt expr) (and_before (binding patt expr))) pel
                 class_expr ce)
      | <:class_expr< let open $_!:ovf$ $longid:li$ in $ce$ >> ->
          let ovf = if (Pcaml.unvala ovf) then "!" else "" in
          if pc.dang = ";" then
            pprintf pc "(@[<a>let open%s %p@ in@]@ %p)" ovf longident li curr ce
          else
            pprintf pc "@[<a>let open%s %p@ in@]@ %p" ovf longident li curr ce
      ]
    | "alg_attribute"
      [ <:class_expr< $ct$ [@ $attribute:attr$] >> ->
        pprintf pc "%p[@%p]" curr ct attribute_body attr
      ]

    | [ <:class_expr< [% $_extension:e$ ] >> ->
          pprintf pc "%p" (pr_extension "%") e
      ]

    | "apply"
      [ <:class_expr< $ce$ $e$ >> ->
          pprintf pc "%p@;%p" curr ce (Eprinter.apply_level pr_expr "label")
            e ]
    | "simple"
      [ <:class_expr< $lilongid:lili$ >> -> longident_lident pc lili
      | <:class_expr< [ $list:ctcl$ ] $lilongid:lili$ >> ->
          let ctcl = List.map (fun ct -> (ct, ",")) ctcl in
          pprintf pc "[%p]@;%p" (plist ctyp 0) ctcl longident_lident lili
      | <:class_expr:< object $opt:csp$ $list:csl$ end >> ->
          class_object loc pc (csp, csl)
      | <:class_expr< ($ce$ : $ct$) >> ->
          pprintf pc "@[<1>(%p :@ %p)@]" class_expr ce class_type ct
      | <:class_expr< $_$ $_$ >> | <:class_expr< fun $_$ -> $_$ >>
        | <:class_expr< [% $_extension:_$ ] >>
        | <:class_expr< let $flag:_$ $list:_$ in $_$ >>
        | <:class_expr< let open $_!:_$ $longid:_$ in $_$ >>
        as z ->
          pprintf pc "@[<1>(%p)@]" class_expr z ]
    | "bottom"
      [ z ->
          error (MLast.loc_of_class_expr z)
            (sprintf "pr_class_expr %d" (Obj.tag (Obj.repr z))) ] ]
  ;
  pr_class_type:
    [ "top"
      [ <:class_type< [ $t$ ] -> $ct$ >> ->
          pprintf pc "%p ->@;%p" (Eprinter.apply_level pr_ctyp "star") t curr
            ct
      | <:class_type< let open $_!:ovf$ $longid:li$ in $ce$ >> ->
          let ovf = if (Pcaml.unvala ovf) then "!" else "" in
          if pc.dang = ";" then
            pprintf pc "(@[<a>let open%s %p@ in@]@ %p)" ovf longident li curr ce
          else
            pprintf pc "@[<a>let open%s %p@ in@]@ %p" ovf longident li curr ce
      ]
    | "alg_attribute"
      [ <:class_type< $ct$ [@ $attribute:attr$] >> ->
        pprintf pc "%p[@%p]" curr ct attribute_body attr
      ]

    | [ <:class_type:< object $opt:cst$ $list:csi$ end >> ->
          let class_sig_item_sep =
            (* if flag_semi_semi.val then semi_semi_after class_sig_item
            else *) class_sig_item
          in
          horiz_vertic
            (fun () ->
               if alone_in_line pc then
                 (* Heuristic : I don't like to print it horizontally
                    when alone in a line. *)
                 sprintf "\n"
               else
                 pprintf pc "object%p %p end"
                   (fun pc ->
                      fun
                       [ Some t -> pprintf pc " (%p)" ctyp t
                       | None -> pprintf pc "" ])
                   cst (hlist class_sig_item_sep) csi)
            (fun () ->
               pprintf pc "@[<a>%p@;%p@ end@]"
                 (fun pc ->
                    fun
                    [ Some t -> pprintf pc "object@;(%p)" ctyp t
                    | None -> pprintf pc "object" ])
                  cst (vlist class_sig_item_sep) csi)
      | <:class_type< $ct$ [ $list:ctcl$ ] >> ->
          let ctcl = List.map (fun ct -> (ct, ",")) ctcl in
          pprintf pc "@[<1>[%p]@;%p@]" (plist ctyp 0) ctcl curr ct ]
    | "dot"
      [
        <:class_type< $longid:li$ . $lid:s$ >> ->
          pprintf pc "%p.%s" longident li s
      | <:class_type< $lid:s$ >> ->
          pprintf pc "%s" s
    ]

    | [ <:class_type< [% $_extension:e$ ] >> ->
          pprintf pc "%p" (pr_extension "%") e ]
    | "bottom"
      [ z ->
          error (MLast.loc_of_class_type z)
            (sprintf "pr_class_type %d" (Obj.tag (Obj.repr z))) ] ]
  ;
  pr_class_sig_item:
    [ "top"
      [ <:class_sig_item< inherit $ct$ $_itemattrs:item_attrs$ >> ->
          pprintf pc "inherit@;%p%p" class_type ct
            (hlist (pr_attribute "@@")) (Pcaml.unvala item_attrs)
      | <:class_sig_item< method $flag:priv$ $lid:s$ : $t$ $_itemattrs:attrs$ >> ->
          sig_method_or_method_virtual pc "" priv s t attrs
      | <:class_sig_item< method virtual $flag:priv$ $lid:s$ : $t$ $_itemattrs:attrs$  >> ->
          sig_method_or_method_virtual pc " virtual" priv s t attrs
      | <:class_sig_item< type $t1$ = $t2$ $_itemattrs:item_attrs$ >> ->
          pprintf pc "constraint %p =@;%p%p" ctyp t1 ctyp t2
            (hlist (pr_attribute "@@")) (Pcaml.unvala item_attrs)
      | <:class_sig_item:< value $flag:mf$ $flag:vf$ $lid:s$ : $t$ $_itemattrs:item_attrs$ >> ->
          pprintf pc "val%s%s %p :@;%p%p"
            (if mf then " mutable" else "")
            (if vf then " virtual" else "")
            var_escaped (loc, s) ctyp t
            (hlist (pr_attribute "@@")) (Pcaml.unvala item_attrs)
      | <:class_sig_item< [@@@ $_attribute:attr$ ] >> ->
          pprintf pc "%p" (pr_attribute "@@@") attr
      | <:class_sig_item< [%% $_extension:e$ ] >> ->
          pprintf pc "%p" (pr_extension "%%") e ]
    | "bottom"
      [ z ->
          error (MLast.loc_of_class_sig_item z)
            (sprintf "pr_class_sig_item %d" (Obj.tag (Obj.repr z))) ] ]
  ;
  pr_class_str_item:
    [ "top"
      [ <:class_str_item< inherit $!:ovf$ $ce$ $opt:pb$ $_itemattrs:item_attrs$ >> ->
          pprintf pc "inherit%s@;%p@[%p%p@]" (if ovf then "!" else "") class_expr ce
            (fun pc ->
               fun
               [ Some s -> pprintf pc " as %s" s
               | None -> pprintf pc "" ])
            pb
            (hlist (pr_attribute "@@")) (Pcaml.unvala item_attrs)
      | <:class_str_item< initializer $e$ $_itemattrs:item_attrs$ >> ->
          pprintf pc "initializer@;%p%p" expr e
            (hlist (pr_attribute "@@")) (Pcaml.unvala item_attrs)
      | <:class_str_item< method virtual $flag:priv$ $lid:s$ : $t$ $_itemattrs:item_attrs$ >> ->
          sig_method_or_method_virtual pc " virtual" priv s t item_attrs
      | <:class_str_item<
          method $!:ov$ $priv:priv$ $lid:s$ $opt:topt$ = $e$ $_itemattrs:item_attrs$
        >> ->
          let (pl, e) =
            match topt with
            [ Some _ -> ([], e)
            | None -> expr_fun_args e ]
          in
          let simple_patt = Eprinter.apply_level pr_patt "simple" in
          match topt with
          [ None ->
              pprintf pc "method%s%s %s%s%p =@;%p%p"
                (if ov then "!" else "") (if priv then " private" else "") s
                (if pl = [] then "" else " ") (hlist simple_patt) pl
                expr e (hlist (pr_attribute "@@")) (Pcaml.unvala item_attrs)
          | Some t ->
              pprintf pc "method%s%s %s%s%p :@;<1 4>%p =@;%p%p"
                (if ov then "!" else "") (if priv then " private" else "") s
                (if pl = [] then "" else " ") (hlist simple_patt) pl
                poly_type t expr e (hlist (pr_attribute "@@")) (Pcaml.unvala item_attrs) ]
      | <:class_str_item< type $t1$ = $t2$ $_itemattrs:item_attrs$ >> ->
          pprintf pc "constraint %p =@;%p%p" ctyp t1 ctyp t2
            (hlist (pr_attribute "@@")) (Pcaml.unvala item_attrs)
      | <:class_str_item< value $!:ovf$ $flag:mf$ $lid:s$ = $e$ $_itemattrs:item_attrs$ >> ->
          pprintf pc "val%s%s %s =@;%p%p" (if ovf then "!" else "")
            (if mf then " mutable" else "") s expr e
            (hlist (pr_attribute "@@")) (Pcaml.unvala item_attrs)
      | <:class_str_item< value virtual $flag:mf$ $lid:s$ : $t$ $_itemattrs:item_attrs$ >> ->
          pprintf pc "val virtual%s %s :@;%p%p"
            (if mf then " mutable" else "") s ctyp t
            (hlist (pr_attribute "@@")) (Pcaml.unvala item_attrs)
      | <:class_str_item< [@@@ $_attribute:attr$ ] >> ->
          pprintf pc "%p" (pr_attribute "@@@") attr
      | <:class_str_item< [%% $_extension:e$ ] >> ->
          pprintf pc "%p" (pr_extension "%%") e ]
    | "bottom"
      [ z ->
          error (MLast.loc_of_class_str_item z)
            (sprintf "pr_class_str_item %d" (Obj.tag (Obj.repr z)))
      ] ]
  ;
END;
