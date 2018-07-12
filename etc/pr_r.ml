(* camlp5r *)
(* pr_r.ml,v *)
(* Copyright (c) INRIA 2007-2017 *)

#directory ".";
#load "pa_macro.cmo";
#load "q_MLast.cmo";
#load "pa_extfun.cmo";
#load "pa_extprint.cmo";
#load "pa_pprintf.cmo";

open Pretty;
open Pcaml;
open Prtools;
open Versdep;

value flag_add_locations = ref False;
value flag_comments_in_phrases = Pcaml.flag_comments_in_phrases;
value flag_expand_declare = ref False;
value flag_horiz_let_in = ref False;
value flag_sequ_begin_at_eol = ref True;
value flag_equilibrate_cases = Pcaml.flag_equilibrate_cases;

value flag_where_after_in = ref True;
value flag_where_after_let_eq = ref True;
value flag_where_after_match = ref True;
value flag_where_after_lparen = ref True;
value flag_where_after_field_eq = ref False;
value flag_where_in_sequences = ref True;
value flag_where_after_then = ref True;
value flag_where_after_value_eq = ref True;
value flag_where_after_arrow = ref True;

value sep = Pcaml.inter_phrases;

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

value error loc msg = Ploc.raise loc (Failure msg);

value horiz_vertic_if force_vertic f g =
  horiz_vertic (fun () -> if force_vertic then sprintf "\n" else f ()) g
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
  let keywords = ["declare"; "value"; "where"] in
  fun s -> List.mem s keywords
;

value has_special_chars s =
  if String.length s = 0 then False
  else
    match s.[0] with
    | '0'..'9' | 'A'..'Z' | 'a'..'z' | '_' -> False
    | _ ->
        match (greek_ascii_equiv s).[0] with
        | 'A'..'Z' | 'a'..'z' → False
        | _ → True
        end
    end
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
  | <:patt< (type $lid:_$) >> -> True
  | <:patt< (module $uid:_$ : $_$) >> -> True
  | <:patt< (module $uid:_$) >> -> True
  | <:patt< ~{$list:lppo$} >> ->
      List.for_all (fun (p, _) -> is_irrefut_patt p) lppo
  | <:patt< ?{$p$ $opt:_$} >> -> is_irrefut_patt p
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
  | <:patt< ~{$p$ $opt:_$} >> -> get_defined_ident p
  | MLast.PaOlb _ p _ -> get_defined_ident p
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
      "\"" ^ Obj.magic x ^ "\""
    else if Obj.is_block (Obj.repr x) then
      "tag = " ^ string_of_int (Obj.tag (Obj.repr x))
    else "int_val = " ^ string_of_int (Obj.magic x)
  in
  pprintf pc "\"pr_r, not impl: %s; %s\"" name (String.escaped desc)
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
  if is_infix v || has_special_chars v then lprintf pc "\\%s@ " v
  else if is_keyword v then lprintf pc "\\%s@ " v
  else lprintf pc "%s" v
;

value cons_escaped pc s = pprintf pc "%s" s;

IFDEF OCAML_VERSION <= OCAML_1_07 THEN
  value with_bef = Pprintf.with_bef;
  value with_bef_aft = Pprintf.with_bef_aft;
  value with_aft = Pprintf.with_aft;
END;

value rec mod_ident pc (loc, sl) =
  match sl with
  [ [] -> pprintf pc ""
  | [s] -> var_escaped pc (loc, s)
  | [s :: sl] -> pprintf pc "%s.%p" s mod_ident (loc, sl) ]
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
  if flag_comments_in_phrases.val then Prtools.comm_bef pc.ind loc else ""
;

value only_spaces s =
  loop 0 where rec loop i =
    if i = String.length s then True
    else if s.[i] = ' ' then loop (i + 1)
    else False
;

value has_newlines s =
  loop 0 where rec loop i =
    if i = String.length s then False
    else if s.[i] = '\n' then True
    else loop (i + 1)
;

value strip_heading_spaces s =
  loop 0 where rec loop i =
    if i = String.length s then ""
    else if s.[i] = ' ' then loop (i + 1)
    else String.sub s i (String.length s - i)
;

value strip_one_heading_space s =
  if String.length s > 0 && s.[0] = ' ' then
    String.sub s 1 (String.length s - 1)
  else s
;

(* expression with adding the possible comment before *)
value comm_expr expr pc z =
  let loc = MLast.loc_of_expr z in
  let ccc = comm_bef pc loc in
  if ccc = "" then expr pc z
  else if only_spaces ccc then
    sprintf "%s%s" ccc (expr pc z)
  else if has_newlines ccc then
    expr
      {(pc) with
       bef =
         sprintf "%s%s%s" pc.bef (strip_heading_spaces ccc)
           (String.make (String.length pc.bef) ' ')}
     z
  else
    expr
      {(pc) with
       bef = sprintf "%s%s" pc.bef (strip_one_heading_space ccc);
       aft = sprintf "%s%s" pc.aft (Ploc.comment_last loc)}
      z
;

(* couple pattern/anytype with adding the possible comment before *)
value comm_patt_any f pc z =
  let loc = MLast.loc_of_patt (fst z) in
  let ccc = comm_bef pc loc in
  sprintf "%s%s" ccc (f pc z)
;

value patt_as pc z =
  match z with
  [ <:patt< ($x$ as $y$) >> -> pprintf pc "%p as @[%p@]" patt x patt y
  | z -> patt pc z ]
;

(* utilities specific to pr_r *)

value default_lang =
  try Sys.getenv "LC_ALL" with
  [ Not_found ->
      try Sys.getenv "LC_MESSAGES" with
      [ Not_found -> try Sys.getenv "LANG" with [ Not_found -> "" ] ] ]
;

value utf8 =
  let s = default_lang in
  let utf8_str = "utf-8" in
  let slen = String.length s in
  let ulen = String.length utf8_str in
  slen >= ulen &&
  string_lowercase (String.sub s (slen - ulen) ulen) = utf8_str
;

value arrow () = if utf8 then "→" else "->";

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

type seq =
  [ SE_let of Ploc.t and bool and list (MLast.patt * MLast.expr) and seq
  | SE_let_module of Ploc.t and string and MLast.module_expr and seq
  | SE_let_open of Ploc.t and MLast.module_expr and seq
  | SE_closed of MLast.expr and seq
  | SE_other of MLast.expr and option seq ]
;

value rec seq_of_expr e =
  match e with
  [ <:expr< do { $list:[e :: el]$ } >> ->
      seq_of_expr_ne_list e el
  | <:expr:< let $flag:rf$ $list:pel$ in $e$ >> ->
      SE_let loc rf pel (seq_of_expr e)
  | <:expr:< let module $uid:s$ = $me$ in $e$ >> ->
      SE_let_module loc s me (seq_of_expr e)
  | <:expr:< let open $m$ in $e$ >> ->
      SE_let_open loc m (seq_of_expr e)
  | e ->
      SE_other e None ]
and seq_of_expr_ne_list e1 el =
  match e1 with
  [ <:expr< do { $list:[e2 :: el]$ } >> ->
      seq_of_expr_ne_list e2 el
  | <:expr:< let $flag:rf$ $list:pel$ in $e$ >> ->
      match el with
      [ [] -> SE_let loc rf pel (seq_of_expr e)
      | [e2 :: el] -> SE_closed e1 (seq_of_expr_ne_list e2 el) ]
  | <:expr:< let module $uid:s$ = $me$ in $e$ >> ->
      match el with
      [ [] -> SE_let_module loc s me (seq_of_expr e)
      | [e2 :: el] -> SE_closed e1 (seq_of_expr_ne_list e2 el) ]
  | <:expr:< let open $m$ in $e$ >> ->
      match el with
      [ [] -> SE_let_open loc m (seq_of_expr e)
      | [e2 :: el] -> SE_closed e1 (seq_of_expr_ne_list e2 el) ]
  | e1 ->
      let seo =
        match el with
        [ [] -> None
        | [e2 :: el] -> Some (seq_of_expr_ne_list e2 el) ]
      in
      SE_other e1 seo ]
;

value rec true_sequence =
  fun
  [ SE_let _ _ _ s -> true_sequence s
  | SE_let_module _ _ _ s -> true_sequence s
  | SE_let_open _ _ s -> true_sequence s
  | SE_closed _ _ -> True
  | SE_other _ (Some _) -> True
  | SE_other _ None  -> False ]
;

value flatten_sequence e =
  let se = seq_of_expr e in
  if true_sequence se then Some se else None
;

value sequencify e =
  if not flag_sequ_begin_at_eol.val then None else flatten_sequence e
;

(* Pretty printing improvement (optional):
   - test a "let" binding can be displayed as "where"
 *)
value can_be_displayed_as_where rf pel e =
  match pel with
  [ [(p, body)] ->
      let e1 =
        loop e where rec loop =
          fun
          [ <:expr< $e$ $_$ >> -> loop e
          | e -> e ]
      in
      match (p, e1, body) with
      [ (<:patt< $lid:f$ >>, <:expr< $lid:g$ >>,
         <:expr< fun [ $list:_$ ] >>) ->
          if f = g then Some (rf, p, e, body) else None
      | _ -> None ]
  | [_ :: _] | [] -> None ]
;

value forward_expr_wh = ref (fun []);
value expr_wh pc e = forward_expr_wh.val pc e;

(* Pretty printing improvements (optional):
   - prints "let f x = e" instead of "let f = fun x -> e"
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
value value_or_let_binding sequence_box pc (p, e) =
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
    [ <:expr< ($e$ : $t$) >> -> (e, Some t)
    | _ -> (e, None) ]
  in
  let patt_tycon pc p =
    match tyo with
    [ Some t -> pprintf pc "%p : %p" patt p ctyp t
    | None -> patt pc p ]
  in
  horiz_vertic
    (fun () ->
       pprintf pc "%p = %p%s" (hlistl patt patt_tycon) pl (comm_expr expr_wh)
         e (if pc.aft = "in" then " " else ""))
    (fun () ->
       let patt_eq pc () =
         let pl = List.map (fun p -> (p, "")) pl in
         pprintf pc "%p =" (plistl patt patt_tycon 4) pl
       in
       match sequencify e with
       [ Some se ->
           sequence_box (fun pc () -> pprintf pc "%p " patt_eq ()) pc se
       | None ->
           if pc.aft = "" then
             pprintf pc "%p@;%p" patt_eq () (comm_expr expr_wh) e
           else
             pprintf pc "@[<a>%p@;%p@ @]" patt_eq () (comm_expr expr_wh) e ])
;

(* Pretty printing improvement (optional):
   - print the sequence beginner at end of previous lines,
     therefore printing the sequence with one tabulation less
       example:
            value f x =
              do {
                ...
              }
       is printed :
            value f x = do {
              ...
            }
   - may change a 'let' into a 'where' for the last statement of
     the sequence.
 *)
value rec sequence_box bef pc se =
  pprintf pc "%pdo {@;%p@ }" bef () hvseq se

and hvseq pc se =
  let expr_wh = if flag_where_in_sequences.val then expr_wh else expr in
  let force_vertic = not (Pretty.horizontally ()) in
  loop pc se where rec loop pc =
    fun
    [ SE_let loc rf pel (SE_other e None) ->
        let disp_as_where =
          if flag_where_in_sequences.val then
            can_be_displayed_as_where rf pel e
          else None
        in
        match disp_as_where with
        [ Some params ->
            sprintf "%s%s" (comm_bef pc loc) (where_binding pc params)
        | None ->
            sprintf "%s%s" (comm_bef pc loc)
              (pprintf pc "@[<i>%p@ %p@]" force_vertic let_up_to_in
                 (rf, pel) (comm_expr expr_wh) e) ]
    | SE_let loc rf pel se ->
        sprintf "%s%s" (comm_bef pc loc)
          (pprintf pc "@[<i>%p@ %p@]" force_vertic let_up_to_in (rf, pel)
            loop se)
    | SE_let_module loc s me se ->
        sprintf "%s%s" (comm_bef pc loc)
          (pprintf pc "@[<i>%p@ %p@]" force_vertic let_module_up_to_in
            (s, me) loop se)
    | SE_let_open loc m se ->
        sprintf "%s%s" (comm_bef pc loc)
          (pprintf pc "@[<i>%p@ %p@]" force_vertic let_open_up_to_in m
             loop se)
    | SE_closed e se ->
        pprintf pc "@[<i>@[<1>(%p);@]@ %p@]" force_vertic (comm_expr expr_wh)
          e loop se
    | SE_other e (Some se) ->
        pprintf pc "@[<i>%p;@ %p@]" force_vertic (comm_expr expr_wh) e loop
          se
    | SE_other e None -> comm_expr expr_wh pc e ]

and let_up_to_in pc (rf, pel) =
  let let_binding pc pe =
    let sequ bef pc se =
      if pc.aft = "" then pprintf pc "%p" (sequence_box bef) se
      else pprintf pc "%p@ " (sequence_box bef) se
    in
    value_or_let_binding sequ pc pe
  in
  let pc = {(pc) with aft = ""} in
  horiz_vertic_if True
    (fun () ->
       pprintf pc "let %s%p in" (if rf then "rec " else "")
         (hlist2 let_binding (and_before let_binding)) pel)
    (fun () ->
       pprintf pc "let %s%pin" (if rf then "rec " else "")
         (vlist2 let_binding (and_before let_binding)) pel)
and let_module_up_to_in pc (s, me) =
  pprintf pc "@[<a>let module %s =@;%p@ in@]" s module_expr me
and let_open_up_to_in pc m =
  pprintf pc "@[<a>let open %p@ in@]" module_expr m

(* Pretty printing improvement (optional):
   - display a "let" binding with the "where" construct
*)
and where_binding pc (rf, p, e, body) =
  let (pl, body) = expr_fun_args body in
  let pl = [p :: pl] in
  match sequencify body with
  [ Some se ->
      let bef pc () =
        pprintf pc "%p@ where%s %p = " expr e (if rf then " rec" else "")
          (hlist patt) pl
      in
      sequence_box bef pc se
  | None ->
      pprintf pc "%p@ where%s %p =@;%p" expr e (if rf then " rec" else "")
        (hlist patt) pl (comm_expr expr) body ]
;

value expr_wh pc e =
  match
    match e with
    [ <:expr< let $flag:rf$ $list:pel$ in $e$ >> ->
        can_be_displayed_as_where rf pel e
    | _ -> None ]
  with
  [ Some params -> where_binding pc params
  | None -> expr pc e ]
;
forward_expr_wh.val := expr_wh;

value value_binding pc pe = value_or_let_binding sequence_box pc pe;

value match_assoc force_vertic pc (p, w, e) =
  let expr_wh = if flag_where_after_arrow.val then expr_wh else expr in
  let patt_arrow pc (p, w) =
    match w with
    [ <:vala< Some e >> ->
        pprintf pc "%p@ @[when@;%p %s@]" patt_as p expr e (arrow ())
    | _ ->
        pprintf pc "%p %s" patt_as p (arrow ()) ]
  in
  horiz_vertic_if force_vertic
    (fun () -> pprintf pc "%p %p" patt_arrow (p, w) (comm_expr expr) e)
    (fun () ->
       match sequencify e with
       [ Some se ->
           sequence_box
             (fun pc () ->
                if Pretty.horizontally () then "\n"
                else pprintf pc "%p " patt_arrow (p, w)) pc
             se
       | None ->
           pprintf pc "@[<i>%p@;%p@]" force_vertic patt_arrow (p, w)
             (comm_expr expr_wh) e ])
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
           sequence_box (fun pc () -> pprintf pc "%p = " (hlist patt) pl) pc
             el)
  | None ->
      pprintf pc "%p =@;%p" (hlist patt) pl (comm_expr expr_wh) e ]
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
      let (xl, c, last_comm) = make_expr_list y in
      ([x :: xl], c, last_comm)
  | <:expr:< [] >> -> ([], None, Ploc.comment_last loc)
  | x -> ([], Some x, "") ]
;

value rec make_patt_list =
  fun
  [ <:patt< [$x$ :: $y$] >> ->
      let (xl, c) = make_patt_list y in
      ([x :: xl], c)
  | <:patt< [] >> -> ([], None)
  | x -> ([], Some x) ]
;

value start_with s s_ini =
  let len = String.length s_ini in
  String.length s >= len && String.sub s 0 len = s_ini
;

(* Type variables in Greek *)

value greek_tab =
  [| "α"; "β"; "γ"; "δ"; "ε"; "ζ"; "η"; "θ"; "ι"; "κ"; "λ"; "μ"; "ν"; "ξ";
     "ο"; "π"; "ρ"; "σ"; "τ"; "υ"; "φ"; "χ"; "ψ"; "ω" |]
;
value index_tab = [| ""; "₁"; "₂"; "₃"; "₄"; "₅"; "₆"; "₇"; "₈"; "₉" |];

value try_greek s = do {
  if utf8 then do {
    if String.length s = 1 then do {
      let c = Char.code s.[0] - Char.code 'a' in
      let g = greek_tab.(c mod Array.length greek_tab) in
      let n = c / Array.length greek_tab in
      if n < Array.length index_tab then ("", g ^ index_tab.(n))
      else ("'", s)
    }
    else ("'", s)
  }
  else ("'", s)
};

value type_var pc (tv, vari) =
  let tv = Pcaml.unvala tv in
  pprintf pc "%s%s"
    (match vari with
     [ Some True -> "+"
     | Some False -> "-"
     | None -> "" ])
    (match tv with
     [ Some s ->
         let (q, s) = try_greek s in
         q ^ s
     | None -> "_" ])
;

value type_constraint pc (t1, t2) =
  pprintf pc " constraint %p =@;%p" ctyp t1 ctyp t2
;

value type_decl pc td =
  let ((_, tn), tp, pf, te, cl) =
    (Pcaml.unvala td.MLast.tdNam, td.MLast.tdPrm, Pcaml.unvala td.MLast.tdPrv,
     td.MLast.tdDef, td.MLast.tdCon)
  in
  let loc = MLast.loc_of_ctyp te in
  horiz_vertic
    (fun () ->
       pprintf pc "%p%s%p = %s%p%p" var_escaped (loc, Pcaml.unvala tn)
         (if Pcaml.unvala tp = [] then "" else " ")
         (hlist type_var) (Pcaml.unvala tp)
         (if pf then "private " else "") ctyp te
         (hlist type_constraint) (Pcaml.unvala cl))
    (fun () ->
       if pc.aft = "" then
         pprintf pc "%p%s%p =@;%s%p%p" var_escaped (loc, Pcaml.unvala tn)
           (if Pcaml.unvala tp = [] then "" else " ")
           (hlist type_var) (Pcaml.unvala tp)
           (if pf then "private " else "") ctyp te
           (hlist type_constraint) (Pcaml.unvala cl)
       else
         pprintf pc "@[<a>%p%s%p =@;%s%p%p@ @]" var_escaped
           (loc, Pcaml.unvala tn) (if Pcaml.unvala tp = [] then "" else " ")
           (hlist type_var) (Pcaml.unvala tp)
           (if pf then "private " else "") ctyp te
           (hlist type_constraint) (Pcaml.unvala cl))
;

value label_decl pc (loc, l, m, t) =
  pprintf pc "%p :%s@;%p" var_escaped (loc, l)
    (if m then " mutable" else "") ctyp t
;

value cons_decl pc (_, c, tl, rto) =
  let c = Pcaml.unvala c in
  let tl = Pcaml.unvala tl in
  if tl = [] then do {
    match rto with
    [ Some rt -> pprintf pc "%p : %p" cons_escaped c ctyp rt
    | None -> cons_escaped pc c ]
  }
  else do {
    match rto with
    [ Some rt ->
        let loc = Ploc.dummy in
        let t = List.fold_right (fun t rt -> <:ctyp< $t$ -> $rt$ >>) tl rt in
        pprintf pc "%p :@;<1 4>%p" cons_escaped c ctyp t
    | None ->
        let tl = List.map (fun t -> (t, " and")) tl in
        pprintf pc "%p of@;<1 4>%p" cons_escaped c (plist ctyp 2) tl ]
  }
;

value has_cons_with_params vdl =
  List.exists
    (fun (_, _, tl, _) ->
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
  let expr_wh = if flag_where_in_sequences.val then expr_wh else expr in
  horiz_vertic_if force_vertic
    (fun () -> pprintf pc "if %p then %p" curr e1 (comm_expr curr) e2)
    (fun () ->
       let if_e1_then pc () = pprintf pc "@[<3>if %p@]@ then" curr e1 in
       match sequencify e2 with
       [ Some el ->
           sequence_box (fun pc () -> pprintf pc "%p " if_e1_then ()) pc el
       | None ->
           pprintf pc "@[<i>%p@;%p@]" force_vertic if_e1_then ()
             (comm_expr expr_wh) e2 ])
;

value else_if_then force_vertic curr pc (e1, e2) =
  let expr_wh = if flag_where_in_sequences.val then expr_wh else expr in
  horiz_vertic_if force_vertic
    (fun () ->
       pprintf pc "else if %p then %p" curr e1 curr e2)
    (fun () ->
       let if_e1_then pc () = pprintf pc "@[<a>else if@;%p@ then@]" curr e1 in
       match sequencify e2 with
       [ Some se ->
           sequence_box
             (fun pc () ->
                if Pretty.horizontally () then pprintf pc "\n"
                else pprintf pc "%p@ " if_e1_then ())
             pc se
       | None ->
           pprintf pc "@[<i>%p@;%p@]" force_vertic if_e1_then ()
             (comm_expr expr_wh) e2 ])
;

value rec loop_else_if force_vertic curr pc =
  fun
  [ [(e1, e2) :: eel] ->
      pprintf pc "@[<b>@ %p%p@]" (else_if_then force_vertic curr) (e1, e2)
        (loop_else_if force_vertic curr) eel
  | [] ->
      pprintf pc "" ]
;

value ending_else force_vertic curr pc e3 =
  let expr_wh = if flag_where_in_sequences.val then expr_wh else expr in
  horiz_vertic_if force_vertic
    (fun () ->
       pprintf pc "else %p" curr e3)
    (fun () ->
       match sequencify e3 with
       [ Some se -> sequence_box (fun pc () -> pprintf pc "else ") pc se
       | None ->
           pprintf pc "@[<i>else@;%p@]" force_vertic (comm_expr expr_wh) e3 ])
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
         pprintf pc "else %p" curr e3
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

value string pc s = pprintf pc "\"%s\"" s;
value lident pc s = pprintf pc "%s" s;
value typevar pc tv =
  let (q, s) = try_greek tv in
  pprintf pc "%s%s" q s
;

value external_decl pc (loc, n, t, sl) =
  pprintf pc "external %p :@;%p = %s" var_escaped (loc, n) ctyp t
    (hlist string {(pc) with bef = ""; aft = ""} sl)
;

value exception_decl pc (loc, e, tl, id) =
  match id with
  [ [] ->
      match tl with
      [ [] -> pprintf pc "exception %p" cons_escaped e
      | tl ->
          let tl = List.map (fun t -> (t, " and")) tl in
          pprintf pc "exception %p of@;%p" cons_escaped e (plist ctyp 0) tl ]
  | id ->
      match tl with
      [ [] ->
          pprintf pc "exception %p@;= %p" cons_escaped e mod_ident (loc, id)
      | tl ->
          let tl = List.map (fun t -> (t, " and")) tl in
          pprintf pc "exception %p of@;%p@;= %p" cons_escaped e
            (plist ctyp 0) tl mod_ident (loc, id) ] ]
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
  let mal = List.map (fun ma -> (ma, "")) mal in
  if pc.aft = "" then
    pprintf pc "%s %s%p %c@;%p" pref m (plistb module_arg 2) mal defc
      module_type mt
  else
    pprintf pc "@[<a>%s %s%p %c@;%p@;<0 0>@]" pref m (plistb module_arg 2) mal
      defc module_type mt
;

value str_or_sig_functor pc s mt module_expr_or_type met =
  pprintf pc "functor@;@[(%s :@;<1 1>%p)@]@ %s@;%p" s module_type mt
    (arrow ()) module_expr_or_type met
;

value con_typ_pat pc (loc, sl, tpl) =
  if tpl = [] then
    pprintf pc "%p" mod_ident (loc, sl)
  else
    pprintf pc "%p %p" mod_ident (loc, sl) (hlist type_var) tpl
;

value string_eval s =
  let b = Buffer.create (String.length s) in
  loop 0 where rec loop i =
    if i == String.length s then Buffer.contents b
    else if i == String.length s - 1 then do {
      Buffer.add_char b s.[i];
      Buffer.contents b
    }
    else do {
      match (s.[i], s.[i + 1]) with
      | ('\\', 'n') -> do { Buffer.add_char b '\n'; loop (i + 2) }
      | (c, _) -> do { Buffer.add_char b c; loop (i + 1) }
      end
    }
;

value with_constraint pc wc =
  match wc with
  [ <:with_constr:< type $sl$ $list:tpl$ = $flag:pf$ $t$ >> ->
      pprintf pc "type %p =@;%s%p" con_typ_pat (loc, sl, tpl)
        (if pf then "private " else "") ctyp t
  | <:with_constr:< type $sl$ $list:tpl$ := $t$ >> ->
      pprintf pc "type %p :=@;%p" con_typ_pat (loc, sl, tpl) ctyp t
  | <:with_constr:< module $sl$ = $me$ >> ->
      pprintf pc "module %p =@;%p" mod_ident (loc, sl) module_expr me
  | <:with_constr:< module $sl$ := $me$ >> ->
      pprintf pc "module %p :=@;%p" mod_ident (loc, sl) module_expr me
  | IFDEF STRICT THEN
      x ->
         not_impl "with_constraint" pc x
    END ]
;

value is_unary =
  fun
  [ "-" | "-." | "~-" | "~-." -> True
  | _ -> False ]
;

value unary expr pc x =
  match x with
  [ <:expr< $lid:f$ $_$ >> when is_unary f -> pprintf pc "(%p)" expr x
  | x -> pprintf pc "%p" expr x ]
;

value rec nlist3 elem elem2 pc xl =
  match xl with
  [ [] -> invalid_arg "slist3"
  | [x] -> elem pc (x, True)
  | [x :: xl] ->
      sprintf "%s%s" (elem {(pc) with aft = ""} (x, False))
        (nlist3 elem2 elem2 {(pc) with bef = ""} xl) ]
;

EXTEND_PRINTER
  pr_expr:
    [ "top"
      [ <:expr< if $e1$ then $e2$ else $e3$ >> ->
          horiz_vertic
            (fun () ->
               pprintf pc "if %p then %p else %p" curr e1 curr e2 curr e3)
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
               pprintf pc "@[<b>%p%p@ %p@]"
                 (if_then force_vertic curr) (e1, e2)
                 (loop_else_if force_vertic curr) eel
                 (ending_else force_vertic curr) e3)
      | <:expr< fun [ $list:pwel$ ] >> ->
          match pwel with
          [ [(p1, <:vala< None >>, e1)] when is_irrefut_patt p1 ->
              let (pl, e1) = expr_fun_args e1 in
              let pl = [p1 :: pl] in
              horiz_vertic
                (fun () ->
                   pprintf pc "fun %p %s %p" (hlist patt) pl (arrow ()) curr e1)
                (fun () ->
                   let pl = List.map (fun p -> (p, "")) pl in
                   match sequencify e1 with
                   [ Some se ->
                       sequence_box (fun pc () -> pprintf pc "fun %p -> "
                         (plist patt 4) pl) pc se
                   | None ->
                       pprintf pc "fun %p %s@;%p" (plist patt 4) pl (arrow ())
                         (comm_expr curr) e1 ])
          | [] -> pprintf pc "fun []"
          | pwel -> pprintf pc "@[<b>fun@ %p@]" match_assoc_list pwel ]
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
                                    curr {(pc) with bef = " when "} e
                                | _ -> "" ])))
                        (fun () -> None)
                   with
                   [ Some s1 ->
                       let pc = {(pc) with bef = ""} in
                       pprintf pc "%s@;%p" s1 curr e
                   | None ->
                       match sequencify e1 with
                       [ Some se ->
                           pprintf pc "%p@ with %p"
                             (sequence_box (fun pc () -> pprintf pc "%s " op))
                             se (match_assoc False) (p, wo, e)
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
                   [ Some se ->
                       horiz_vertic
                         (fun () ->
                            pprintf pc "%s %p with@ %p" op expr_wh e1
                              match_assoc_list pwel)
                         (fun () ->
                            pprintf pc "%p@ with@ %p"
                              (sequence_box
                                 (fun pc () ->
                                    horiz_vertic (fun _ -> sprintf "\n")
                                      (fun () -> pprintf pc "%s " op)))
                              se match_assoc_list pwel)
                   | None ->
                       pprintf pc "@[<a>%s@;%p@ with@]@ %p" op expr_wh e1
                         match_assoc_list pwel ]) ]
      | <:expr:< let $flag:rf$ $list:pel$ in $e$ >> as ge ->
          match flatten_sequence ge with
          [ Some se -> pprintf pc "do {@;%p@ }" hvseq se
          | None ->
              let expr_wh =
                if flag_where_after_in.val then expr_wh else curr
              in
              pprintf pc "%p@ %p" let_up_to_in (rf, pel) (comm_expr expr_wh)
                e ]
      | <:expr< let module $uid:s$ = $me$ in $e$ >> as ge ->
          match flatten_sequence ge with
          [ Some se -> pprintf pc "do {@;%p@ }" hvseq se
          | None -> pprintf pc "%p@ %p" let_module_up_to_in (s, me) curr e ]
      | <:expr< let open $m$ in $e$ >> as ge ->
          match flatten_sequence ge with
          [ Some se -> pprintf pc "do {@;%p@ }" hvseq se
          | None -> pprintf pc "%p@ %p" let_open_up_to_in m curr e ]
      | <:expr< do { $list:el$ } >> ->
          match el with
          [ [] -> pprintf pc "do {}"
          | [e :: el] ->
              let se = seq_of_expr_ne_list e el in
              pprintf pc "do {@;%p@ }" hvseq se ]
      | <:expr:< while $e1$ do { $list:el$ } >> ->
          let bef pc () = pprintf pc "while@;%p@ " curr e1 in
          match el with
          [ [] -> pprintf pc "%pdo {}" bef ()
          | [e :: el] ->
              let se = seq_of_expr_ne_list e el in
              pprintf pc "%pdo {@;%p@ }" bef () hvseq se ]
      | <:expr:< for $lid:v$ = $e1$ $to:d$ $e2$ do { $list:el$ } >> ->
          let bef pc () =
            pprintf pc "@[<a>for %s = %p %s@;<1 4>%p@ @]" v curr e1
              (if d then "to" else "downto") curr e2
          in
          match el with
          [ [] -> pprintf pc "%pdo {}" bef ()
          | [e :: el] ->
              let se = seq_of_expr_ne_list e el in
              pprintf pc "@[<a>%pdo {@;%p@ }@]" bef () hvseq se ] ]
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
      [ <:expr< - $x$ >> -> pprintf pc "-%p" (unary curr) x
      | <:expr< -. $x$ >> -> pprintf pc "-.%p" (unary curr) x
      | <:expr< ~- $x$ >> -> pprintf pc "~-%p" (unary curr) x
      | <:expr< ~-. $x$ >> -> pprintf pc "~-.%p" (unary curr) x ]
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
          pprintf pc "@[{%p}@]" (plist (comm_patt_any record_binding) 1)
            lxl
      | <:expr< {($e$) with $list:lel$} >> ->
          let lxl = List.map (fun lx -> (lx, ";")) lel in
          pprintf pc "@[{(%p) with@ %p}@]" expr e
            (plist (comm_patt_any record_binding) 1) lxl
      | <:expr< [| $list:el$ |] >> ->
          if el = [] then pprintf pc "[| |]"
          else
            let el = List.map (fun e -> (e, ";")) el in
            pprintf pc "@[<3>[| %p |]@]" (plist expr 0) el
      | <:expr< [$_$ :: $_$] >> as z ->
          let (xl, y, last_comm) = make_expr_list z in
          let xl = List.map (fun x -> (x, ";")) xl in
          match y with
          [ Some y ->
              let expr2 pc x = pprintf pc "%p ::@ %p" expr x expr y in
              pprintf pc "@[<1>[%p]@]" (plistl expr expr2 0) xl
          | None ->
              pprintf pc "@[<1>[%p]@]" (plist (comm_expr expr) 0) xl ]
      | <:expr< ($e$ : $t$) >> ->
          pprintf pc "@[<1>(%p :@ %p)@]" expr e ctyp t
      |  <:expr< (module $me$ : $mt$) >> ->
          pprintf pc "@[<1>(module %p :@ %p)@]" module_expr me module_type mt
      |  <:expr< (module $me$) >> ->
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
      | <:expr:< $lid:s$ >> ->
          var_escaped pc (loc, s)
      | <:expr< $uid:s$ >> ->
          cons_escaped pc s
      | <:expr< `$s$ >> ->
          failwith "variants not pretty printed (in expr); add pr_ro.cmo"
      | <:expr< $str:s$ >> ->
          pprintf pc "\"%s\"" s
      | <:expr< $chr:s$ >> ->
          pprintf pc "'%s'" s
      | MLast.ExOlb loc _ _ | MLast.ExLab loc _ ->
          error loc "labels not pretty printed (in expr); add pr_ro.cmo"
      | <:expr< $_$ $_$ >> | <:expr< assert $_$ >> | <:expr< lazy $_$ >> |
        <:expr< $_$ := $_$ >> |
        <:expr< fun [ $list:_$ ] >> | <:expr< if $_$ then $_$ else $_$ >> |
        <:expr< do { $list:_$ } >> |
        <:expr< for $lid:_$ = $_$ $to:_$ $_$ do { $list:_$ } >> |
        <:expr< while $_$ do { $list:_$ } >> |
        <:expr< let $flag:_$ $list:_$ in $_$ >> |
        <:expr< let module $uid:_$ = $_$ in $_$ >> |
        <:expr< let open $_$ in $_$ >> |
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
          [ Some y ->
              let patt2 pc x = pprintf pc "%p ::@ %p" patt x patt y in
              pprintf pc "@[<1>[%p]@]" (plistl patt patt2 0) xl
          | None ->
              pprintf pc "@[<1>[%p]@]" (plist patt 0) xl ]
      | <:patt< ($p$ : $t$) >> ->
          pprintf pc "@[<1>(%p :@ %p)@]" patt p ctyp t
      | <:patt< (type $lid:s$) >> ->
          pprintf pc "(type %s)" s
      | <:patt< (module $uid:s$ : $mt$) >> ->
          pprintf pc "@[<1>(module %s :@ %p)@]" s module_type mt
      | <:patt< (module $uid:s$) >> ->
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
      | <:patt:< $lid:s$ >> ->
          var_escaped pc (loc, s)
      | <:patt< $uid:s$ >> ->
          cons_escaped pc s
      | <:patt< $chr:s$ >> ->
          pprintf pc "'%s'" s
      | <:patt< $str:s$ >> ->
          pprintf pc "\"%s\"" s
      | <:patt< _ >> ->
          pprintf pc "_"
      | MLast.PaLab loc _ | MLast.PaOlb loc _ _ ->
          error loc "labels not pretty printed (in patt); add pr_ro.cmo"
      | <:patt< `$s$ >> ->
          failwith "variants not pretty printed (in patt); add pr_ro.cmo"
      | <:patt< $_$ $_$ >> | <:patt< $_$ | $_$ >> | <:patt< $_$ .. $_$ >>
        as z ->
          pprintf pc "@[<1>(%p)@]" patt z
      | z ->
          Ploc.raise (MLast.loc_of_patt z)
            (Failure (sprintf "pr_patt %d" (Obj.tag (Obj.repr z)))) ] ]
  ;
  pr_ctyp:
    [ "top"
      [ <:ctyp< $x$ == $priv:pf$ $y$ >> ->
          let op = if pf then "== private" else "==" in
          operator pc next next 2 op x y ]
    | "as"
      [ <:ctyp< $t1$ as $t2$ >> ->
          pprintf pc "%p@ as %p" curr t1 next t2 ]
    | "poly"
      [ <:ctyp< ! $list:pl$ . $t$ >> ->
          pprintf pc "! %p .@;%p" (hlist typevar) pl ctyp t
      | <:ctyp:< type $list:pl$ . $t$ >> ->
          pprintf pc "type %p .@;%p" (hlist lident) pl ctyp t ]
    | "arrow"
      [ <:ctyp< $_$ -> $_$ >> as z ->
          let unfold =
            fun
            [ <:ctyp< $x$ -> $y$ >> -> Some (x, " " ^ arrow (), y)
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
          if vdl = [] then pprintf pc "[]"
          else
            horiz_vertic_if (has_cons_with_params vdl)
              (fun () ->
                 pprintf pc "[ %p ]" (hlist2 cons_decl (bar_before cons_decl))
                   vdl)
              (fun () ->
                 pprintf pc "[ %p ]" (vlist2 cons_decl (bar_before cons_decl))
                   vdl)
      | <:ctyp< ($list:tl$) >> ->
          let tl = List.map (fun t -> (t, " *")) tl in
          pprintf pc "@[<1>(%p)@]" (plist ctyp 0) tl
      | <:ctyp< module $mt$ >> ->
          pprintf pc "@[module@ %p@]" module_type mt
      | <:ctyp:< $lid:t$ >> ->
          var_escaped pc (loc, t)
      | <:ctyp< $uid:t$ >> ->
          pprintf pc "%s" t
      | <:ctyp:< ' $s$ >> ->
          pprintf pc "%p" typevar s
      | <:ctyp< _ >> ->
          pprintf pc "_"
      | <:ctyp< ?$i$: $t$ >> | <:ctyp< ~$_$: $t$ >> ->
          failwith "labels not pretty printed (in type); add pr_ro.cmo"
      | <:ctyp< [ = $list:_$ ] >> | <:ctyp< [ > $list:_$ ] >> |
       (* <:ctyp< [ < $list:_$ ] >> | *) <:ctyp< [ < $list:_$ > $list:_$ ] >> ->
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
            let str_item_fst pc (si, is_last) =
              if is_last then str_item pc si else semi_after str_item pc si
            in
            let str_item_with_comm pc (si, is_last) =
              let ccc =
                match sep.val with
                | Some str -> string_eval str
                | None -> Ploc.comment (MLast.loc_of_str_item si)
                end
              in
              sprintf "%s%s" ccc (str_item_fst pc (si, is_last))
            in
            if sil = [] then pc.bef
            else
              match sep.val with
              | Some str -> nlist3 str_item_fst str_item_with_comm pc sil
              | None -> vlist3 str_item_fst str_item_with_comm pc sil
              end
          else if sil = [] then pprintf pc "declare end"
          else
            horiz_vertic
              (fun () ->
                 pprintf pc "declare %p end"
                   (hlist (semi_after str_item)) sil)
              (fun () ->
                 pprintf pc "@[<a>declare@;%p@ end@]"
                   (vlist (semi_after str_item)) sil)
      | <:str_item:< exception $uid:e$ of $list:tl$ = $id$ >> ->
          exception_decl pc (loc, e, tl, id)
      | <:str_item:< external $lid:n$ : $t$ = $list:sl$ >> ->
          external_decl pc (loc, n, t, sl)
      | <:str_item< include $me$ >> ->
          pprintf pc "include %p" module_expr me
      | <:str_item< module $flag:rf$ $list:mdl$ >> ->
          let mdl = List.map (fun (m, mt) -> (Pcaml.unvala m, mt)) mdl in
          let rf = if rf then " rec" else "" in
          vlist2 (str_module ("module" ^ rf)) (str_module "and") pc mdl
      | <:str_item< module type $m$ = $mt$ >> ->
          sig_module_or_module_type "module type" '=' pc (m, mt)
      | <:str_item:< open $i$ >> ->
          pprintf pc "open %p" mod_ident (loc, i)
      | <:str_item< type $flag:nonrf$ $list:tdl$ >> ->
          pprintf pc "type%s %p" (if nonrf then " nonrec" else "")
            (vlist2 type_decl (and_before type_decl)) tdl
      | <:str_item< value $flag:rf$ $list:pel$ >> ->
          horiz_vertic
            (fun () ->
               pprintf pc "value%s %p" (if rf then " rec" else "")
                 (hlist2 value_binding (and_before value_binding)) pel)
            (fun () ->
               pprintf pc "value%s %p" (if rf then " rec" else "")
                 (vlist2 value_binding (and_before value_binding)) pel)
      | <:str_item< $exp:e$ >> ->
          expr pc e
      | <:str_item< class type $list:_$ >> | <:str_item< class $list:_$ >> ->
          failwith "classes and objects not pretty printed; add pr_ro.cmo"
      | MLast.StUse _ fn sl ->
          let pc = {(pc) with aft = ""} in
          pprintf pc "" ] ]
  ;
  pr_sig_item:
    [ "top"
      [ <:sig_item< # $lid:s$ $e$ >> ->
          let pc = {(pc) with aft = ""} in
          pprintf pc "(* #%s %p *)" s expr e
      | <:sig_item< declare $list:sil$ end >> ->
          if flag_expand_declare.val then
            if sil = [] then pc.bef
            else vlistl (semi_after sig_item) sig_item pc sil
          else if sil = [] then pprintf pc "declare end"
          else
            horiz_vertic
              (fun () ->
                 pprintf pc "declare %p end"
                   (hlist (semi_after sig_item)) sil)
              (fun () ->
                 pprintf pc "@[<a>declare@;%p@ end@]"
                   (vlist (semi_after sig_item)) sil)
      | <:sig_item:< exception $uid:e$ of $list:tl$ >> ->
          exception_decl pc (loc, e, tl, [])
      | <:sig_item:< external $lid:n$ : $t$ = $list:sl$ >> ->
          external_decl pc (loc, n, t, sl)
      | <:sig_item< include $mt$ >> ->
          pprintf pc "include %p" module_type mt
      | <:sig_item< module $flag:rf$ $list:mdl$ >> ->
          let mdl = List.map (fun (m, mt) -> (Pcaml.unvala m, mt)) mdl in
          let rf = if rf then " rec" else "" in
          vlist2 (sig_module_or_module_type ("module" ^ rf) ':')
            (sig_module_or_module_type "and" ':') pc mdl
      | <:sig_item< module type $m$ = $mt$ >> ->
          sig_module_or_module_type "module type" '=' pc (m, mt)
      | <:sig_item:< open $i$ >> ->
          pprintf pc "open %p" mod_ident (loc, i)
      | <:sig_item< type $list:tdl$ >> ->
          pprintf pc "type %p" (vlist2 type_decl (and_before type_decl)) tdl
      | <:sig_item:< value $lid:s$ : $t$ >> ->
          pprintf pc "value %p :@;%p" var_escaped (loc, s) ctyp t
      | <:sig_item< class type $list:_$ >> | <:sig_item< class $list:_$ >> ->
          failwith "classes and objects not pretty printed; add pr_ro.cmo"
      | MLast.SgUse _ fn sl ->
          let pc = {(pc) with aft = ""} in
          pprintf pc "" ] ]
  ;
  pr_module_expr:
    [ "top"
      [ <:module_expr< functor ($uid:s$ : $mt$) -> $me$ >> ->
          str_or_sig_functor pc s mt module_expr me
      | <:module_expr< struct $list:sil$ end >> ->
          (* Heuristic : I don't like to print structs horizontally
             when alone in a line. *)
          horiz_vertic_if (alone_in_line pc)
            (fun () ->
               pprintf pc "struct %p end" (hlist (semi_after str_item)) sil)
            (fun () ->
               pprintf pc "@[<b>struct@;%p@ end@]"
                 (vlist (semi_after str_item)) sil) ]
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
          pprintf pc "%p.%p" curr x curr y ]
    | "simple"
      [ <:module_expr< $uid:s$ >> ->
          pprintf pc "%s" s
      | <:module_expr< (value $e$ : $mt$) >> ->
          pprintf pc "@[<1>(value %p :@ %p)@]" expr e module_type mt
      | <:module_expr< (value $e$) >> ->
          pprintf pc "(value %p)" expr e
      | <:module_expr< ($me$ : $mt$) >> ->
          pprintf pc "@[<1>(%p :@ %p)@]" module_expr me module_type mt
      | <:module_expr< functor ($uid:_$ : $_$) -> $_$ >> |
        <:module_expr< struct $list:_$ end >> | <:module_expr< $_$ . $_$ >> |
        <:module_expr< $_$ $_$ >> as z ->
          pprintf pc "@[<1>(%p)@]" module_expr z ] ]
  ;
  pr_module_type:
    [ "top"
      [ <:module_type< functor ($uid:s$ : $mt1$) -> $mt2$ >> ->
          str_or_sig_functor pc s mt1 module_type mt2
      | <:module_type< sig $list:sil$ end >> ->
         (* Heuristic : I don't like to print sigs horizontally
            when alone in a line. *)
          horiz_vertic_if (alone_in_line pc)
            (fun () ->
               pprintf pc "sig %p end" (hlist (semi_after sig_item)) sil)
            (fun () ->
               pprintf pc "@[<b>sig@;%p@ end@]"
                 (vlist (semi_after sig_item)) sil)
      | <:module_type< module type of $me$ >> ->
          pprintf pc "@[module type of@ %p@]" module_expr me
      | <:module_type< $mt$ with $list:wcl$ >> ->
          pprintf pc "%p with@;%p" module_type mt
            (vlist2 with_constraint (and_before with_constraint)) wcl ]
    | "apply"
      [ <:module_type< $x$ $y$ >> ->
          pprintf pc "%p %p" curr x next y ]
    | "dot"
      [ <:module_type< $x$ . $y$ >> ->
          pprintf pc "%p.%p" curr x curr y ]
    | "simple"
      [ <:module_type< $uid:s$ >> ->
          pprintf pc "%s" s
      | <:module_type< ' $s$ >> ->
          pprintf pc "'%s" s
      | <:module_type< $_$ $_$ >> as z ->
          pprintf pc "(%p)" module_type z
      | z ->
          Ploc.raise (MLast.loc_of_module_type z)
            (Failure (sprintf "pr_module_type %d" (Obj.tag (Obj.repr z)))) ] ]
  ;
END;

(* main part *)

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
           [ Some str ->
               if first then () else output_string oc (string_eval str)
           | None ->
               output_string oc (Ploc.comment loc) ];
           flush oc;
           output_string oc (f {ind = 0; bef = ""; aft = ";"; dang = ""} si);
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
      | 'O' | 'o' -> flag_add_locations.val := is_uppercase s.[i]
      | 'S' | 's' -> flag_sequ_begin_at_eol.val := is_uppercase s.[i]
      | c -> failwith ("bad flag " ^ String.make 1 c) ];
      loop (i + 1)
    }
;

value default_flag () =
  let flag_on b t f = if b then t else "" in
  let flag_off b t f = if b then "" else f in
  let on_off flag =
    Printf.sprintf "%s%s%s%s%s%s"
      (flag flag_comments_in_phrases.val "C" "c")
      (flag flag_expand_declare.val "D" "d")
      (flag flag_equilibrate_cases.val "E" "e")
      (flag flag_horiz_let_in.val "L" "l")
      (flag flag_add_locations.val "O" "o")
      (flag flag_sequ_begin_at_eol.val "S" "s")
  in
  let on = on_off flag_on in
  let off = on_off flag_off in
  if String.length on < String.length off then Printf.sprintf "a%s" on
  else Printf.sprintf "A%s" off
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
    Printf.sprintf "%s%s%s%s%s%s%s%s%s"
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
  if String.length on < String.length off then Printf.sprintf "a%s" on
  else Printf.sprintf "A%s" off
;

Pcaml.add_option "-flag" (Arg.String set_flags)
  ("<str> Change pretty printing behaviour according to <str>:
       A/a enable/disable all flags
       C/c enable/disable comments in phrases
       D/d enable/disable allowing expanding 'declare'
       E/e enable/disable equilibrate cases
       L/l enable/disable allowing printing 'let..in' horizontally
       O/o enable/disable adding location comments
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
