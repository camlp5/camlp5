(* camlp5r *)
(* pr_r.ml,v *)
(* Copyright (c) INRIA 2007-2017 *)

#directory ".";
#load "parse_q_MLast.cmo";
#load "q_MLast.cmo";
#load "pa_extfun.cmo";
#load "pa_extprint.cmo";
#load "pa_macro.cmo";
#load "pa_macro_print.cmo";
#load "pa_pprintf.cmo";

open Asttools;
open Pretty;
open Prtools;
open Versdep;
open Mlsyntax.Revised;
open Pp_debug ;

value flag_add_locations = ref False;
value flag_comments_in_phrases = Pcaml.flag_comments_in_phrases;
value flag_extensions_are_irrefutable = ref True;
value flag_expand_declare = ref False;
value flag_horiz_let_in = ref False;
value flag_sequ_begin_at_eol = ref True;
value flag_equilibrate_cases = Pcaml.flag_equilibrate_cases;
value flag_expand_letop_syntax = Pcaml.flag_expand_letop_syntax;

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

module PP(Base : Mlsyntax.PRINTBASESIG) = struct
open Base.Printers ;
open Base ;
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

value uv = Pcaml.unvala ;

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
  let kwdhash = R_keywords.keywords_hash in
  fun s -> Hashtbl.mem kwdhash s
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
  [ 
    <:patt< $p$ [@ $_attribute:_$ ] >> -> is_irrefut_patt p
  | <:patt< $lid:_$ >> -> True
  | <:patt< $uid:"()"$ >> -> True
  | <:patt< _ >> -> True
  | <:patt< $longid:_$ . $p$ >> -> is_irrefut_patt p
  | <:patt< ($x$ as $y$) >> -> is_irrefut_patt x && is_irrefut_patt y
  | <:patt< { $list:fpl$ } >> ->
      List.for_all (fun (_, p) -> is_irrefut_patt p) fpl
  | <:patt< ($p$ : $_$) >> -> is_irrefut_patt p
  | <:patt< ($list:pl$, $closed:_$) >> -> List.for_all is_irrefut_patt pl
  | <:patt< (type $lid:_$) >> -> True
  | <:patt< (module $uidopt:_$ : $_$) >> -> True
  | <:patt< (module $uidopt:_$) >> -> True
  | <:patt< ~{$p$ $opt:_$} >> -> is_irrefut_patt p
  | <:patt< ?{$p$ $opt:_$} >> -> is_irrefut_patt p
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
  | <:patt< ($list:pl$, $closed:_$) >> -> List.flatten (List.map get_defined_ident pl)
  | <:patt< ` $_$ >> -> []
  | <:patt< # $lilongid:_$ >> -> []
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


value qstring pc s = pprintf pc "\"%s\"" s;

value pr_xtr pc s =
  match Plexing.parse_antiloc s with [
      None ->
      error Ploc.dummy Fmt.(str "Print_patr.pr_xtr: unrecognized Xtr payload %a@."
                              string s)
    | Some (_,"",txt) ->
       pprintf pc "$%s$" txt
    | Some (_,kind,_) ->
      error Ploc.dummy Fmt.(str "Print_patr.pr_xtr: Xtr should not have kind %a@."
                              string s)
    ]
;

value pr_vala_with ~{vaval} ~{vaant} pc = fun [
  Ploc.VaVal x -> vaval pc x
| VaAnt s ->
   match Plexing.parse_antiloc s with [
       None ->
       error Ploc.dummy Fmt.(str "Print_patr.pr_vala: unrecognized VaAnt payload %a@."
                               string s)
     | Some (_,kind,txt) ->
        vaant pc (Printf.sprintf "$%s:%s$" kind txt)
     ]
] ;

value pr_vala prvaval pc x =
  pr_vala_with ~{vaval=prvaval} ~{vaant=(fun pc anti -> pprintf pc "%s" anti)} pc x
;

value pr_string pc s = pprintf pc "%s" s ;
value pr_bool (tv,fv) pc b =
  pprintf pc "%s" (if b then tv else fv)
;

value lident pc v =
  if is_keyword v then pprintf pc "\\#%s@ " v
  else pprintf pc "%s" v
;

value var_escaped pc (loc, v) =
  if is_infix v || has_special_chars v then lprintf pc "\\%s@ " v
  else lident pc v
;

value var_escaped_noloc pc v = var_escaped pc (Ploc.dummy, v) ;

value cons_escaped pc s =
  let s = match s with [
    "[]" -> "[]"
  | "::" -> "( :: )"
  | "()" ->  "()"
  | s -> s ]
  in
  pprintf pc "%s" s
;

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
value space_before elem pc x = pprintf pc " %p" elem x;

value andop_before elem pc ((andop,_) as x) = pprintf pc "%s %p" andop elem x;

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

value uidopt_to_maybe_blank = fun [
  Some s -> uv s
|  None ->
    "_"
]
;

(*
 * Extensible printers
 *)

value expr = Eprinter.apply pr_expr;
value patt = Eprinter.apply pr_patt;
value simple_patt x = Eprinter.apply_level pr_patt "simple" x;
value ctyp = Eprinter.apply pr_ctyp;
value ctyp_below_alg_attribute x = Eprinter.apply_level pr_ctyp "below_alg_attribute" x;
value ctyp_arrow x = Eprinter.apply_level pr_ctyp "arrow" x;
value str_item = Eprinter.apply pr_str_item;
value sig_item = Eprinter.apply pr_sig_item;
value longident = Eprinter.apply pr_longident;
value module_expr = Eprinter.apply pr_module_expr;
value module_type = Eprinter.apply pr_module_type;
value module_type_level_sig = Eprinter.apply_level pr_module_type "sig";
value expr_fun_args ge = Extfun.apply pr_expr_fun_args.val ge;
value attribute_body = Eprinter.apply pr_attribute_body;
value pr_attribute atstring pc attr =
  pprintf pc "[%s%p]" atstring (pr_vala attribute_body) attr
;
value pr_extension atstring pc attr =
  pprintf pc "[%s%p]" atstring (pr_vala attribute_body) attr
;

value label_of_ctyp pc lab =
  match lab with [
      None -> pprintf pc ""
    | Some l -> pprintf pc "%p:" (pr_vala pr_string) l
    ]
;
value labeled_ctyp pc (lab, ct) =
  pprintf pc "%p%p" (pr_vala label_of_ctyp) lab ctyp ct
;

value longident_lident pc (lio, id) =
  match lio with
  [ None -> pprintf pc "%p" (pr_vala lident) id
  | Some li -> pprintf pc "%p.%p" (pr_vala longident) li (pr_vala lident) id
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


value is_polytype_constraint = fun [
  <:patt< ( $_$ : ! $list:_$ . $_$ ) >> -> True
| _ -> False
]
;

value is_type_constraint = fun [
  <:patt< ( $_$ : $_$ ) >> -> True
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

type seq =
  [ SE_let of Ploc.t and Ploc.vala bool and Ploc.vala (list (MLast.patt * MLast.expr * MLast.attributes)) and seq
  | SE_let_str_item of Ploc.vala MLast.str_item and seq
  | SE_closed of MLast.expr and seq
  | SE_other of MLast.expr and option seq ]
;

value rec seq_of_expr e =
  match e with
  [ <:expr< do { $list:[e :: el]$ } >> ->
      seq_of_expr_ne_list e el
  | <:expr:< let $_flag:rf$ $_list:pel$ in $e$ >> ->
      SE_let loc rf pel (seq_of_expr e)
  | <:expr< let $_stri:si$ in $e$ >> ->
      SE_let_str_item si (seq_of_expr e)
  | e ->
      SE_other e None ]
and seq_of_expr_ne_list e1 el =
  match e1 with
  [ <:expr< do { $list:[e2 :: el]$ } >> ->
      seq_of_expr_ne_list e2 el
  | <:expr:< let $_flag:rf$ $_list:pel$ in $e$ >> ->
      match el with
      [ [] -> SE_let loc rf pel (seq_of_expr e)
      | [e2 :: el] -> SE_closed e1 (seq_of_expr_ne_list e2 el) ]
  | <:expr< let $_stri:si$ in $e$ >> ->
      match el with
      [ [] -> SE_let_str_item si (seq_of_expr e)
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
  | SE_let_str_item _ s -> true_sequence s
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
  Pcaml.vala_mapa
    (fun pel ->
  match pel with
  [ [(p, body, _)] ->
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
  | [_ :: _] | [] -> None ])
    (fun _ -> None)
    pel
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
value value_or_let_binding sequence_box pc (p, e, attrs) =
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
  let (pl, e) = if is_type_constraint p then ([], e)
    else expr_fun_args e in
  let (p, tyo) =
    match p with
    [ <:patt< ($p$ : $t$) >> -> (p, Some t)
    | _ -> (p, None) ]
  in
  let (e, tyo) = match (e, tyo) with [
    (<:expr< ($e$ : $t$) >>, None) -> (e, Some t)
  | _ -> (e, tyo)
  ] in
  let patt_tycon pc p =
    match tyo with
    [ Some t -> pprintf pc "%p : %p" patt p ctyp t
    | None -> patt pc p ]
  in
  let pl = [p :: pl] in
  horiz_vertic
    (fun () ->
       pprintf pc "%p = %p%p%s" (hlistl patt patt_tycon) pl (comm_expr expr_wh)
         e (pr_vala (hlist (pr_attribute "@@"))) attrs
         (if pc.aft = "in" then " " else ""))
    (fun () ->
       let patt_eq pc () =
         let pl = List.map (fun p -> (p, "")) pl in
         pprintf pc "%p =" (plistl patt patt_tycon 4) pl
       in
       match sequencify e with
       [ Some se ->
           pprintf pc "%p%p"
             (sequence_box (fun pc () -> pprintf pc "%p " patt_eq ())) se
             (pr_vala (hlist (pr_attribute "@@"))) attrs
       | None ->
           if pc.aft = "" then
             pprintf pc "%p@;%p%p" patt_eq () (comm_expr expr_wh) e
               (pr_vala (hlist (pr_attribute "@@"))) attrs
           else
             pprintf pc "@[<a>%p@;%p%p@ @]" patt_eq () (comm_expr expr_wh) e
               (pr_vala (hlist (pr_attribute "@@"))) attrs ])
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
           let pel = Pcaml.vala_map (List.map (fun x -> ("and",x))) pel in
            sprintf "%s%s" (comm_bef pc loc)
              (pprintf pc "@[<i>%p@ %p@]" force_vertic (letop_up_to_in "let")
                 (rf, pel) (comm_expr expr_wh) e) ]
    | SE_let loc rf pel se ->
       let pel = Pcaml.vala_map (List.map (fun x -> ("and",x))) pel in
        sprintf "%s%s" (comm_bef pc loc)
          (pprintf pc "@[<i>%p@ %p@]" force_vertic (letop_up_to_in "let") (rf, pel)
            loop se)
    | SE_let_str_item si se ->
       let loc = Pcaml.vala_mapa MLast.loc_of_str_item (fun _ -> Ploc.dummy) si in
        sprintf "%s%s" (comm_bef pc loc)
          (pprintf pc "@[<i>let %p@ in %p@]" force_vertic (pr_vala str_item) si loop se)
    | SE_closed e se ->
        pprintf pc "@[<i>@[<1>(%p);@]@ %p@]" force_vertic (comm_expr expr_wh)
          e loop se
    | SE_other e (Some se) ->
        pprintf pc "@[<i>%p;@ %p@]" force_vertic (comm_expr expr_wh) e loop
          se
    | SE_other e None -> comm_expr expr_wh pc e ]

and letop_up_to_in letop pc (rf, pel) =
  let letop_binding pc (_,pe) =
    let sequ bef pc se =
      if pc.aft = "" then pprintf pc "%p" (sequence_box bef) se
      else pprintf pc "%p@ " (sequence_box bef) se
    in
    value_or_let_binding sequ pc pe
  in
  let pc = {(pc) with aft = ""} in
  horiz_vertic_if True
    (fun () ->
       pprintf pc "%s %p%p in" letop (pr_vala (pr_bool ("rec ",""))) rf
         (pr_vala (hlist2 letop_binding (andop_before letop_binding))) pel)
    (fun () ->
       pprintf pc "%s %p%pin" letop (pr_vala (pr_bool ("rec ",""))) rf
         (pr_vala (vlist2 letop_binding (andop_before letop_binding))) pel)
and let_module_up_to_in pc (s, me) =
    let s = uidopt_to_maybe_blank s in
    pprintf pc "@[<a>let module %s =@;%p@ in@]" s module_expr me
and let_open_up_to_in pc (ovf, m) =
  pprintf pc "@[<a>let open%s %p@ in@]" (if ovf then "!" else "") module_expr m
and let_str_item_up_to_in pc si =
  pprintf pc "@[<a>let %p@ in@]" str_item si

(* Pretty printing improvement (optional):
   - display a "let" binding with the "where" construct
*)
and where_binding pc (rf, p, e, body) =
  let (pl, body) = expr_fun_args body in
  let pl = [p :: pl] in
  match sequencify body with
  [ Some se ->
      let bef pc () =
        pprintf pc "%p@ where%p %p = " expr e (pr_vala (pr_bool (" rec", ""))) rf
          (hlist patt) pl
      in
      sequence_box bef pc se
  | None ->
      pprintf pc "%p@ where%p %p =@;%p" expr e (pr_vala (pr_bool (" rec", ""))) rf
        (hlist patt) pl (comm_expr expr) body ]
;

value expr_wh pc e =
  match
    match e with
    [ <:expr< let $_flag:rf$ $_list:pel$ in $e$ >> ->
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
    pr_vala_with
      ~{vaant=(fun pc anti ->
          pprintf pc "%p@ @[when@;%s %s@]" patt_as p anti (arrow ()))}
      ~{vaval=(fun pc w ->
          match w with
            [ Some e ->
              pprintf pc "%p@ @[when@;%p %s@]" patt_as p expr e (arrow ())
            | _ ->
               pprintf pc "%p %s" patt_as p (arrow ()) ])}
      pc w
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


value label_patt pc p =
  match p with [
    <:patt:< $longid:x$ . $lid:y$ >> -> pprintf pc "%p.%p" longident x var_escaped (loc, y)
  | <:patt:< $longid:x$ >> -> pprintf pc "%p" longident x
  | <:patt:< $lid:y$ >> -> var_escaped pc (loc, y)
  | <:patt:< _ >> -> pprintf pc "_"
  | z -> Ploc.raise (MLast.loc_of_patt z)
      (Failure (sprintf "label_patt %d" (Obj.tag (Obj.repr z))))
  ]
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
      pprintf pc "%p =@;%p" (hlist label_patt) pl (comm_expr expr_wh) e ]
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
      if n < Array.length index_tab then Some (g ^ index_tab.(n))
      else None
    }
    else None
  }
  else None
};

value typevar pc s =
  match try_greek s with [
    Some s -> pprintf pc "%s" s
  | None ->
    if String.contains s '\'' then
      pprintf pc "' %s" s
    else if is_keyword s then
      pprintf pc "'\#%s" s
    else
      pprintf pc "'%s" s
   ]
;

value type_param pc (tv, vastr) =
  let tv_or_blank pc = fun [
    Some tv -> pprintf pc "%p" typevar tv
  | None -> pprintf pc "_" ] in
  pprintf pc "%p%p"
    (pr_vala pr_string) vastr
    (pr_vala tv_or_blank) tv
;

value type_constraint pc (t1, t2) =
  pprintf pc " constraint %p =@;%p" ctyp t1 ctyp t2
;

value tdname pc (loc,v) =
  pr_vala (fun pc v -> var_escaped pc (loc, v)) pc v
;

value prepend_nelist s pf pc l =
  if l = [] then
    pprintf pc "%p" pf l
  else
    pprintf pc "%s%p" s pf l
;

value prepend_space_nelist pf pc l =
  prepend_nelist " " pf pc l
;

value type_decl pc td =
  let (tn, is_decl, tp, pf, te, cl, attrs) =
    (td.MLast.tdNam, td.MLast.tdIsDecl, td.MLast.tdPrm, td.MLast.tdPrv,
     td.MLast.tdDef, td.MLast.tdCon, td.MLast.tdAttributes)
  in
  horiz_vertic
    (fun () ->
       pprintf pc "%p%p %p %p%p%p%p" (pr_vala tdname) tn
         (pr_vala (prepend_space_nelist (hlist type_param))) tp
         (pr_vala (pr_bool ("=",":="))) is_decl
         (pr_vala (pr_bool ("private ",""))) pf
         ctyp te
         (pr_vala (hlist type_constraint)) cl
        (pr_vala (hlist (pr_attribute "@@"))) attrs)
    (fun () ->
       if pc.aft = "" then
         pprintf pc "%p%p %p@;%p%p%p%p" (pr_vala tdname) tn
           (pr_vala (prepend_space_nelist (hlist type_param))) tp
           (pr_vala (pr_bool ("=",":="))) is_decl
           (pr_vala (pr_bool ("private ",""))) pf
           ctyp te
           (pr_vala (hlist type_constraint)) cl
           (pr_vala (hlist (pr_attribute "@@"))) attrs
       else
         pprintf pc "@[<a>%p%p %p@;%p%p%p%p@ @]" (pr_vala tdname) tn
           (pr_vala (prepend_space_nelist (hlist type_param))) tp
           (pr_vala (pr_bool ("=",":="))) is_decl
           (pr_vala (pr_bool ("private ",""))) pf
           ctyp te
           (pr_vala (hlist type_constraint)) cl
           (pr_vala (hlist (pr_attribute "@@"))) attrs)
;

value label_decl pc (loc, l, m, t, attrs) =
  pprintf pc "%p :%s@;%p%p" var_escaped (loc, l)
    (if m then " mutable" else "") ctyp_below_alg_attribute t
    (pr_vala (hlist (pr_attribute "@"))) attrs
;

value typevars_binder pc = fun [
  [] -> pprintf pc ""
| l -> pprintf pc "%p . " (hlist typevar) l
]
;

value pr_rto pc rto =
  match rto with [
      None -> pprintf pc ""
    | Some rt -> pprintf pc ": %p" ctyp_below_alg_attribute rt
    ]
;

value pr_list_vala pr_nil pr_cons pc x =
  if Pcaml.vala_mapa (fun [ [] -> True | _ -> False ]) (fun _ -> False) x then
    pr_nil pc ()
  else pr_cons pc x
;

value cons_decl pc = fun [
  <:constructor< $_uid:c$ of $_list:tyvars$ . $_list:tl$ $_rto:rto$ $_algattrs:alg_attrs$ >>
 ->
 pr_list_vala
   (fun pc () ->
     pprintf pc "%p %p%p%p"
       (pr_vala cons_escaped) c
       (pr_vala typevars_binder) tyvars
       (pr_vala pr_rto) rto
       (pr_vala (hlist (pr_attribute "@"))) alg_attrs)
   (fun pc tl ->
     let tl = Pcaml.vala_map (List.map (fun t -> (t, " and"))) tl in
     pprintf pc "%p of@;<1 4>%p%p %p%p"
       (pr_vala cons_escaped) c
       (pr_vala typevars_binder) tyvars
       (pr_vala (plist ctyp_below_alg_attribute 2)) tl
       (pr_vala pr_rto) rto
       (pr_vala (hlist (pr_attribute "@"))) alg_attrs)
  pc tl
]
;


value extension_constructor loc pc ec = match ec with [
  MLast.EcTuple _ gc -> cons_decl pc gc

| <:extension_constructor:< $uid:e$ = $longid:li$ $algattrs:alg_attrs$ >> ->
      pprintf pc "%p@;= %p%p" cons_escaped e longident li
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
  horiz_vertic_if (has_ecs_with_params vdl)
    (fun () ->
       pprintf pc "%p" (hlist2 (extension_constructor loc) (bar_before (extension_constructor loc)))
         vdl)
    (fun () ->
       pprintf pc "%p" (vlist2 (extension_constructor loc) (bar_before (extension_constructor loc)))
         vdl)
;

value type_extension loc pc te =
  let (tn, tp, pf, ecstrs, attrs) =
    (te.MLast.teNam, te.MLast.tePrm, te.MLast.tePrv,
     te.MLast.teECs, te.MLast.teAttributes)
  in
  horiz_vertic
    (fun () ->
       pprintf pc "%p%p += %p[ %p ]%p"
         (pr_vala longident_lident) tn
         (pr_vala (prepend_space_nelist (hlist type_param))) tp
         (pr_vala (pr_bool ("private ",""))) pf
         (pr_vala (extension_constructors loc)) ecstrs
         (pr_vala (hlist (pr_attribute "@@"))) attrs)
    (fun () ->
       if pc.aft = "" then
         pprintf pc "%p%p +=@;%p[ %p ]%p" (pr_vala longident_lident) tn
           (pr_vala (prepend_space_nelist (hlist type_param))) tp
           (pr_vala (pr_bool ("private ",""))) pf
           (pr_vala (extension_constructors loc)) ecstrs
           (pr_vala (hlist (pr_attribute "@@"))) attrs
       else
         pprintf pc "@[<a>%p%p +=@;%p[ %p ]%p@ @]" (pr_vala longident_lident) tn
           (pr_vala (prepend_space_nelist (hlist type_param))) tp
           (pr_vala (pr_bool ("private ",""))) pf
           (pr_vala (extension_constructors loc)) ecstrs
           (pr_vala (hlist (pr_attribute "@@"))) attrs)
;

value has_cons_with_params vdl =
  List.exists
    (fun (_, _, _, tl, _,_) ->
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

value external_decl pc (loc, n, tyvars, t, sl, attrs) =
  pprintf pc "external %p :@;%p%p = %s%p" (pr_vala var_escaped_noloc) n
    (pr_vala_with
       ~{vaant=(fun pc anti -> pprintf pc "%s" anti)}
       ~{vaval=typevars_binder}) tyvars
    ctyp t
    (pr_vala (hlist qstring) {(pc) with bef = ""; aft = ""} sl)
    (pr_vala (hlist (pr_attribute "@@"))) attrs
;

value external_decl_original pc (loc, n, tyvars, t, sl, attrs) =
  pprintf pc "external ( %p ) :@;%p%p = %s%p" (pr_vala pr_string) n
    (pr_vala_with
       ~{vaant=(fun pc anti -> pprintf pc "%s" anti)}
       ~{vaval=typevars_binder}) tyvars
    ctyp t
    (pr_vala (hlist qstring) {(pc) with bef = ""; aft = ""} sl)
    (pr_vala (hlist (pr_attribute "@@"))) attrs
;

value exception_decl pc (loc, e, tl, id, alg_attrs, item_attrs) =
  match id with
  [ [] ->
      match tl with
      [ [] -> pprintf pc "exception %p%p%p" cons_escaped e
            (hlist (pr_attribute "@")) alg_attrs
            (hlist (pr_attribute "@@")) item_attrs

      | tl ->
          let tl = List.map (fun t -> (t, " and")) tl in
          pprintf pc "exception %p of@;%p%p%p" cons_escaped e (plist ctyp_below_alg_attribute 0) tl
            (hlist (pr_attribute "@")) alg_attrs
            (hlist (pr_attribute "@@")) item_attrs
      ]
  | id ->
      match tl with
      [ [] ->
          pprintf pc "exception %p@;= %p%p%p" cons_escaped e mod_ident (loc, id)
            (hlist (pr_attribute "@")) alg_attrs
            (hlist (pr_attribute "@@")) item_attrs
      | tl ->
          let tl = List.map (fun t -> (t, " and")) tl in
          pprintf pc "exception %p of@;%p@;= %p%p%p" cons_escaped e
              (plist ctyp 0) tl mod_ident (loc, id)
            (hlist (pr_attribute "@")) alg_attrs
            (hlist (pr_attribute "@@")) item_attrs
      ] ]
;

value pr_opt somepr noneval pc x =
  match x with [
      None -> pprintf pc "%s" noneval
    | Some x -> pprintf pc "%p" somepr x
    ]
;

value str_module pref pc (m, me, item_attrs) =
  let (mal, me) =
    loop me where rec loop =
      fun
      [ <:module_expr< functor $_fp:arg$ -> $me$ >> ->
          let (mal, me) = loop me in
          ([arg :: mal], me)
      | me -> ([], me) ]
  in
  let module_arg pc x = match x with [
    Some (idopt, mt) ->
     pprintf pc "(%p :@;<1 1>%p)" (pr_vala (pr_opt (pr_vala pr_string) "_")) idopt module_type mt
  | None -> 
     pprintf pc "()"
  ] in
  let (me, mto) =
    match me with
    [ <:module_expr< ($me$ : $mt$) >> -> (me, Some mt)
    | _ -> (me, None) ]
  in
  if pc.aft = "" then
    match mto with
    [ Some mt ->
        pprintf pc "%s %p%s%p :@;%p =@;%p%p" pref (pr_vala (pr_opt (pr_vala pr_string) "_")) m
          (if mal = [] then "" else " ") (hlist (pr_vala module_arg)) mal
          module_type mt module_expr me
          (pr_vala (hlist (pr_attribute "@@"))) item_attrs
    | None ->
        let mal = List.map (fun ma -> (ma, "")) mal in
        pprintf pc "%s %p%p =@;%p%p" pref (pr_vala (pr_opt (pr_vala pr_string) "_")) m (plistb (pr_vala module_arg) 2) mal
          module_expr me
          (pr_vala (hlist (pr_attribute "@@"))) item_attrs
    ]
  else
    match mto with
    [ Some mt ->
        pprintf pc "%s %p%s%p :@;%p =@;%p%p@;<0 0>" pref (pr_vala (pr_opt (pr_vala pr_string) "_")) m
          (if mal = [] then "" else " ") (hlist (pr_vala module_arg)) mal
          module_type mt module_expr me
          (pr_vala (hlist (pr_attribute "@@"))) item_attrs
    | None ->
        let mal = List.map (fun ma -> (ma, "")) mal in
        pprintf pc "@[<a>%s %p%p =@;%p%p@;<0 0>@]" pref (pr_vala (pr_opt (pr_vala pr_string) "_")) m (plistb (pr_vala module_arg) 2)
          mal module_expr me
          (pr_vala (hlist (pr_attribute "@@"))) item_attrs
    ]
;

value sig_module_or_module_type pref defs pc ((m : Ploc.vala (option (Ploc.vala string))), mt, item_attrs) =
  let (mal, mt) =
    loop mt where rec loop =
      fun
      [ <:module_type< functor $_fp:arg$ -> $mt2$ >> ->
          let (mal, mt) = loop mt2 in
          ([arg :: mal], mt)
      | mt -> ([], mt) ]
  in
  let module_arg pc x = match x with [
    Some (idopt, mt) ->
     pprintf pc "(%p :@;<1 1>%p)" (pr_vala (pr_opt (pr_vala pr_string) "_")) idopt module_type mt
  | None -> 
     pprintf pc "()"
  ] in
  let mal = List.map (fun ma -> (ma, "")) mal in
  if pc.aft = "" then
    pprintf pc "%s %p%p %s@;%p%p" pref (pr_vala (pr_opt (pr_vala pr_string) "_")) m (plistb (pr_vala module_arg) 2) mal defs
      module_type_level_sig mt
      (pr_vala (hlist (pr_attribute "@@"))) item_attrs
  else
    pprintf pc "@[<a>%s %p%p %s@;%p%p@;<0 0>@]" pref (pr_vala (pr_opt (pr_vala pr_string) "_")) m (plistb (pr_vala module_arg) 2) mal
      defs module_type_level_sig mt
      (pr_vala (hlist (pr_attribute "@@"))) item_attrs
;

value str_or_sig_functor pc farg module_expr_or_type met =
  let pp_sopt pc sopt =
    pprintf pc "%p" (pr_vala (pr_opt (pr_vala pr_string)  "_")) sopt in
  let pp_farg1 pc (sopt, mt) =
    pprintf pc "(%p :@;<1 1>%p)" pp_sopt sopt module_type mt
  in
  pprintf pc "functor@;@[%p@]@ %s@;%p" (pr_vala (pr_opt pp_farg1 "()")) farg (arrow ()) module_expr_or_type met
(*
  match farg with [
    Some (sopt, mt) -> pprintf pc "functor@;@[%p@]@ %s@;%p" pp_farg1 (sopt,mt) 
      (arrow ()) module_expr_or_type met
  | None ->
    pprintf pc "functor@;@[()@]@ %s@;%p"
      (arrow ()) module_expr_or_type met
  ]
 *)
;

value con_typ_pat pc (loc, sl, tpl) =
  pprintf pc "%p%p" (pr_vala longident_lident) sl
    (pr_vala (prepend_space_nelist (hlist type_param))) tpl
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
  [ <:with_constr:< type $_lilongid:sl$ $_list:tpl$ = $_flag:pf$ $t$ >> ->
      pprintf pc "type %p =@;%p%p" con_typ_pat (loc, sl, tpl)
        (pr_vala (pr_bool ("private ",""))) pf ctyp t
  | <:with_constr:< type $_lilongid:sl$ $_list:tpl$ := $t$ >> ->
      pprintf pc "type %p :=@;%p" con_typ_pat (loc, sl, tpl) ctyp t
  | <:with_constr:< module $_longid:sl$ = $me$ >> ->
      pprintf pc "module %p =@;%p" (pr_vala longident) sl module_expr me
  | <:with_constr:< module $_longid:sl$ := $me$ >> ->
      pprintf pc "module %p :=@;%p" (pr_vala longident) sl module_expr me
  | <:with_constr:< module type $_longid:sl$ = $mt$ >> ->
      pprintf pc "module type %p =@;%p" (pr_vala longident) sl module_type mt
  | <:with_constr:< module type $_longid:sl$ := $mt$ >> ->
      pprintf pc "module type %p :=@;%p" (pr_vala longident) sl module_type mt
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

value unary op_pred expr pc x =
  match x with
  [ <:expr< $lid:f$ $_$ >> when op_pred f -> pprintf pc "(%p)" expr x
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
value map_option f =
  fun
  [ Some x -> Some (f x)
  | None -> None ]
;

value qs pc s = pprintf pc "\"%s\"" s ;

value pr_attrid pc (_,id) = qs pc id ;

EXTEND_PRINTER
  pr_attribute_body:
    [ "top"
      [ <:attribute_body< $_attrid:aid$ $_structure:st$ >> ->
        pprintf pc "%p%p" (pr_vala pr_attrid) aid (pr_vala (hlist (space_before (semi_after str_item)))) st
      | <:attribute_body< $_attrid:aid$ : $_signature:si$ >> ->
        pprintf pc "%p:%p" (pr_vala pr_attrid) aid (pr_vala (hlist (space_before (semi_after sig_item)))) si
      | <:attribute_body< $_attrid:aid$ : $_type:ty$ >> ->
        pprintf pc "%p:%p" (pr_vala pr_attrid) aid (pr_vala (space_before ctyp)) ty
      | <:attribute_body< $_attrid:aid$ ? $_patt:p$ >> ->
        pprintf pc "%p?%p" (pr_vala pr_attrid) aid (pr_vala (space_before patt)) p
      | <:attribute_body< $_attrid:aid$ ? $_patt:p$ when $_expr:e$ >> ->
        pprintf pc "%p?%p when %p" (pr_vala pr_attrid) aid (pr_vala (space_before patt)) p (pr_vala expr) e
      ]
    ]
    ;
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
      | <:expr< fun [ $_list:pwel$ ] >> ->
        pr_list_vala
          (fun pc () -> pprintf pc "fun []")
          (fun pc pwel -> 
            pr_vala_with
              ~{vaant=(fun pc anti -> pprintf pc "@[<b>fun@ %s@]" anti)}
              ~{vaval=(fun pc pwel ->
            match pwel with
              [ [ (p1, <:vala< None >>, e1)] when is_irrefut_patt p1 ->
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
              | pwel -> pprintf pc "@[<b>fun@ %p@]" match_assoc_list pwel ])}
           pc pwel
          )
        pc pwel

      | <:expr< try $e1$ with [ $_list:pwel$ ] >> |
        <:expr< match $e1$ with [ $_list:pwel$ ] >> as e ->
          let expr_wh =
            if flag_where_after_match.val then expr_wh else curr
          in
          let op =
            match e with
            [ <:expr< try $_$ with [ $_list:_$ ] >> -> "try"
            | _ -> "match" ]
          in
          pr_vala_with
            ~{vaant=(fun pc anti ->
                pprintf pc "%s %p with %s" op expr_wh e1 anti)}
            ~{vaval=(fun pc pwel ->
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
                         match_assoc_list pwel ]) ])} pc pwel

      | <:expr:< let $_flag:rf$ $_list:pel$ in $e$ >> as ge ->
          match flatten_sequence ge with
          [ Some se -> pprintf pc "do {@;%p@ }" hvseq se
          | None ->
              let expr_wh =
                if flag_where_after_in.val then expr_wh else curr
              in
              let pel = Pcaml.vala_map (List.map (fun x -> ("and",x))) pel in
              pprintf pc "%p@ %p" (letop_up_to_in "let") (rf, pel) (comm_expr expr_wh)
                e ]
      | <:expr< $lid:letop$ $arg$ (fun $bindpat$ -> $body$) >>
           when not Pcaml.flag_expand_letop_syntax.val && is_letop letop ->
        let rec deconstruct_ands acc = fun [
              (<:patt< ( $pat1$, $pat2$ ) >>, <:expr< $lid:andop$ $e1$ $e2$ >>) when is_andop andop ->
                deconstruct_ands [ (andop, (pat2, e2, <:vala< [] >>)) :: acc ] (pat1, e1)
            | (pat, exp) -> [ ("andop_unused", (pat, exp, <:vala< [] >>))::acc ]
        ] in
        let pel = deconstruct_ands [] (bindpat, arg) in
        pprintf pc "%p@ %p" (letop_up_to_in letop) (<:vala< False >>, <:vala< pel >>)
          curr body

      | <:expr< let $_stri:si$ in $e$ >> as ge ->
          match flatten_sequence ge with
          [ Some se -> pprintf pc "do {@;%p@ }" hvseq se
          | None -> pprintf pc "%p@ %p" (pr_vala let_str_item_up_to_in) si curr e ]
      | <:expr< do { $_list:el$ } >> ->
          pr_vala_with
            ~{vaant=(fun pc anti -> pprintf pc "do { %s }" anti)}
            ~{vaval=(fun pc el ->
          match el with
          [ [] -> pprintf pc "do {}"
          | [e :: el] ->
              let se = seq_of_expr_ne_list e el in
              pprintf pc "do {@;%p@ }" hvseq se ])}
            pc el
      | <:expr:< while $e1$ do { $_list:el$ } >> ->
          let bef pc () = pprintf pc "while@;%p@ " curr e1 in
          pr_vala_with
            ~{vaant=(fun pc anti -> pprintf pc "%pdo { %s }" bef () anti)}
            ~{vaval=(fun pc el ->
          match el with
          [ [] -> pprintf pc "%pdo {}" bef ()
          | [e :: el] ->
              let se = seq_of_expr_ne_list e el in
              pprintf pc "%pdo {@;%p@ }" bef () hvseq se ])}
            pc el
      | <:expr:< for $v$ = $e1$ $_to:d$ $e2$ do { $_list:el$ } >> ->
          let bef pc () =
            pprintf pc "@[<a>for %p = %p %p@;<1 4>%p@ @]" patt v curr e1
              (pr_vala (pr_bool ("to", "downto"))) d curr e2
          in
          pr_vala_with
            ~{vaant=(fun pc anti -> pprintf pc "%pdo { %s }" bef () anti)}
            ~{vaval=(fun pc el ->
          match el with
          [ [] -> pprintf pc "%pdo {}" bef ()
          | [e :: el] ->
              let se = seq_of_expr_ne_list e el in
              pprintf pc "@[<a>%pdo {@;%p@ }@]" bef () hvseq se ])}
            pc el
      ]
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
          let ops = ["!=" ; "<" ; "<=" ; "<>" ; "=" ; "==" ; ">" ; ">="] in
          if List.mem op ops || is_infixop0 op then
              operator pc next next 0 op x y
          else next pc z ]
    | "concat"
      [ z ->
          let unfold =
            fun
            [ <:expr< $lid:op$ $x$ $y$ >> ->
                if List.mem op ["^"; "@"] || is_infixop1 op then Some (x, " " ^ op, y) else None
            | _ -> None ]
          in
          right_operator pc 0 unfold next z ]
    | "alg_attribute"
      [ <:expr< $e$ [@ $_attribute:attr$] >> ->
        pprintf pc "%p[@%p]" curr e (pr_vala attribute_body) attr
      ]

    | "add"
      [ z ->
          let ops = ["+"; "+."; "-"; "-."] in
          let unfold =
            fun
            [ <:expr< $lid:op$ $x$ $y$ >> ->
                if List.mem op ops || is_infixop2 op then Some (x, " " ^ op, y) else None
            | _ -> None ]
          in
          left_operator pc 0 unfold next z ]
    | "mul"
      [ z ->
          let ops = ["*"; "*."; "/"; "/."; "land"; "lor"; "lxor"; "mod"] in
          let unfold =
            fun
            [ <:expr< $lid:op$ $x$ $y$ >> ->
                if List.mem op ops || is_infixop3 op then Some (x, " " ^ op, y) else None
            | _ -> None ]
          in
          left_operator pc 0 unfold next z ]
    | "pow"
      [ z ->
          let ops = ["**"; "asr"; "lsl"; "lsr"] in
          let unfold =
            fun
            [ <:expr< $lid:op$ $x$ $y$ >> ->
                if List.mem op ops || is_infixop4 op then Some (x, " " ^ op, y) else None
            | _ -> None ]
          in
          right_operator pc 0 unfold next z ]
    | "unary_minus"
      [ <:expr< $lid:op$ $x$ >> as z ->
        let ops = [("-","-") ; ("-.","-."); ("~+","+"); ("~+.","+.")] in
        let in_ops x = List.mem_assoc x ops in
        if in_ops op then
          pprintf pc "%s%p" (List.assoc op ops) (unary in_ops curr) x
        else next pc z ]
    | "apply"
      [ <:expr< assert $e$ >> ->
          pprintf pc "assert@;%p" next e
      | <:expr< lazy $e$ >> ->
          pprintf pc "lazy@;%p" next e
      | <:expr< $_$ $_$ >> as z ->
          let inf =
            match z with
            [ <:expr< $lid:n$ $_$ $_$ >> when is_infix n || is_infix_operator n -> True
            |  <:expr< $lid:n$ $_$ >> when is_unary n || is_prefixop n -> True
            | <:expr< [$_$ :: $_$] >> -> True
            | _ -> False ]
          in
          if inf then next pc z
          else
            let unfold =
              fun
              [ 
                <:expr< [$_$ :: $_$] >> -> None
              |  <:expr< $lid:n$ $_$ $_$ >> when is_infix n || is_infix_operator n -> None
              |  <:expr< $lid:n$ $_$ >> when is_unary n || is_prefixop n -> None
              | <:expr< $x$ $y$ >> -> Some (x, "", y)
              | e -> None ]
            in
            left_operator pc 2 unfold next z ]
    | "dot"
      [ 
        <:expr< $longid:li$ . ( $e$ ) >> ->
        match e with [
          <:expr< $uid:"[]"$ >> -> pprintf pc "%p.@;<0 0>@[<a>[]@]" longident li
        | <:expr< [ $_$ :: $_$ ] >> -> pprintf pc "%p.@;<0 0>%p" longident li curr e

        | <:expr< { $_list:_$ } >> -> pprintf pc "%p.@;<0 0>%p" longident li curr e
        | <:expr< {($_$) with $_list:_$ } >> -> pprintf pc "%p.@;<0 0>%p" longident li curr e
        | <:expr:< $_lid:v$ >> -> pprintf pc "%p.@;<0 0>%p" longident li (pr_vala var_escaped_noloc) v
        | <:expr< ($_list:el$) >> ->
          let el = Pcaml.vala_map (List.map (fun e -> (e, ","))) el in
          pprintf pc "%p.@;<0 0>@[<a>(%p)@]" longident li (pr_vala (plist expr 0)) el

        | e -> pprintf pc "%p.@;<0 0>@[<a>(%p)@]" longident li expr e
        ]

      | <:expr:< $e$ . $_lid:v$ >> -> pprintf pc "%p.@;<0 0>%p" curr e (pr_vala var_escaped_noloc) v
      | <:expr< $e$ . $_lilongid:lili$ >> -> pprintf pc "%p.@;<0 0>%p" curr e (pr_vala longident_lident) lili

      | <:expr< $longid:li$ >> -> longident pc li

      | <:expr< $x$ .( $y$ ) >> ->
          pprintf pc "%p.(%p)" curr x expr_short y
      | <:expr< $x$ $_dotop:op$ ( $list:el$ ) >> ->
          let el = List.map (fun e -> (e, ";")) el in
          pprintf pc "%p@;<0 0>%p(%p)" curr x (pr_vala pr_string) op (plist expr_short 0) el

      | <:expr< $x$ .[ $y$ ] >> ->
          pprintf pc "%p.[%p]" curr x expr_short y
      | <:expr< $x$ $_dotop:op$ [ $_list:el$ ] >> ->
          let el = Pcaml.vala_map (List.map (fun e -> (e, ";"))) el in
          pprintf pc "%p@;<0 0>%p[%p]" curr x (pr_vala pr_string) op (pr_vala (plist expr_short 0)) el

      | <:expr< $e$ .{ $_list:el$ } >> ->
          let el = Pcaml.vala_map (List.map (fun e -> (e, ","))) el in
          pprintf pc "%p.{%p}" curr e (pr_vala (plist expr_short 0)) el
      | <:expr< $x$ $_dotop:op$ { $_list:el$ } >> ->
          let el = Pcaml.vala_map (List.map (fun e -> (e, ";"))) el in
          pprintf pc "%p@;<0 0>%p{%p}" curr x (pr_vala pr_string) op (pr_vala (plist expr_short 0)) el
      ]
    | "~-"
      [ <:expr< $lid:op$ $x$ >> as z ->
        let in_ops x = is_prefixop x in
        if in_ops op then
          pprintf pc "%s%p" op (unary in_ops curr) x
        else next pc z ]
    | "simple"
      [ <:expr< ($_list:el$) >> ->
          let el = Pcaml.vala_map (List.map (fun e -> (e, ","))) el in
          pprintf pc "@[<1>(%p)@]" (pr_vala (plist expr 0)) el
      | <:expr< {$_list:lel$} >> ->
          let lxl = Pcaml.vala_map (List.map (fun lx -> (lx, ";"))) lel in
          pprintf pc "@[{%p}@]" (pr_vala (plist (comm_patt_any record_binding) 1))
            lxl
      | <:expr< {($e$) with $_list:lel$} >> ->
          let lxl = Pcaml.vala_map (List.map (fun lx -> (lx, ";"))) lel in
          pprintf pc "@[{(%p) with@ %p}@]" expr e
            (pr_vala (plist (comm_patt_any record_binding) 1)) lxl
      | <:expr< [| $_list:el$ |] >> ->
         pr_vala_with
           ~{vaant=(fun pc anti -> pprintf pc "[| %s |]" anti)}
           ~{vaval=(fun pc el ->
          if el = [] then pprintf pc "[| |]"
          else
            let el = List.map (fun e -> (e, ";")) el in
            pprintf pc "@[<3>[| %p |]@]" (plist expr 0) el)}
        pc el
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
      | <:expr< $_int:s$ >> | <:expr< $_flo:s$ >> ->
          pr_vala (fun pc s ->
          if String.length s > 0 && s.[0] = '-' then pprintf pc "(%s)" s
          else pprintf pc "%s" s)
            pc s
      | <:expr< $_int32:s$ >> ->
          pr_vala (fun pc s ->
          if String.length s > 0 && s.[0] = '-' then pprintf pc "(%sl)" s
          else pprintf pc "%sl" s)
            pc s
      | <:expr< $_int64:s$ >> ->
          pr_vala (fun pc s ->
          if String.length s > 0 && s.[0] = '-' then pprintf pc "(%sL)" s
          else pprintf pc "%sL" s)
            pc s
      | <:expr< $_nativeint:s$ >> ->
          pr_vala (fun pc s ->
          if String.length s > 0 && s.[0] = '-' then pprintf pc "(%sn)" s
          else pprintf pc "%sn" s)
            pc s
      | <:expr< . >> -> pprintf pc "."
      | <:expr:< $lid:s$ >> when is_special_op s ->
          pprintf pc "( %s )" s
      | <:expr:< $_lid:s$ >> ->
          (pr_vala var_escaped_noloc) pc s
      | <:expr< `$_:s$ >> ->
          failwith "variants not pretty printed (in expr); add pr_ro.cmo"
      | <:expr< $_str:s$ >> ->
          pr_vala (fun pc s -> pprintf pc "\"%s\"" s) pc s
      | <:expr< [% $_extension:e$ ] >> ->
          pprintf pc "%p" (pr_extension "%") e
      | <:expr< $_chr:s$ >> ->
          pr_vala (fun pc s -> pprintf pc "'%s'" s) pc s
      | MLast.ExOlb loc _ _ | MLast.ExLab loc _ _ ->
          error loc "labels not pretty printed (in expr); add pr_ro.cmo"
      | MLast.ExXtr _ s _ ->
         pprintf pc "%p" pr_xtr s

      | <:expr< $_$ $_$ >> | <:expr< assert $_$ >> | <:expr< lazy $_$ >> |
        <:expr< $_$ := $_$ >> |
        <:expr< fun [ $list:_$ ] >> | <:expr< if $_$ then $_$ else $_$ >> |
        <:expr< do { $list:_$ } >> |
        <:expr< for $lid:_$ = $_$ $to:_$ $_$ do { $list:_$ } >> |
        <:expr< while $_$ do { $list:_$ } >> |
        <:expr< let $flag:_$ $list:_$ in $_$ >> |
        <:expr< let $_stri:_$ in $_$ >> |
        <:expr< match $_$ with [ $list:_$ ] >> |
        <:expr< $_$ [@ $_attribute:_$] >> |
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
    | "alg_attribute"
      [ <:patt< $p$ [@ $_attribute:attr$] >> ->
        pprintf pc "%p[@%p]" curr p (pr_vala attribute_body) attr
      ]
    | [ <:patt< exception $p$ >> ->
          pprintf pc "exception %p" next p
      | <:patt< effect $p1$, $p2$ >> ->
          pprintf pc "effect %p, %p" next p1 simple_patt p2
      ]
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
      [ <:patt< $longid:li$ . $p$ >> -> pprintf pc "%p.%p" longident li curr p
      | <:patt< $longid:li$ >> -> pprintf pc "%p" longident li
      | <:patt< $longid:li$ (type $_list:l$) >> ->
        pprintf pc "%p (type %p)" longident li (pr_vala (hlist lident)) (Pcaml.vala_map (List.map snd) l)
      ]
    | "simple"
      [ <:patt< lazy $p$ >> -> pprintf pc "lazy@;%p" curr p
      | <:patt< ($x$ as $y$) >> ->
          pprintf pc "@[<1>(%p@ as %p)@]" patt x patt y
      | <:patt< ($_list:pl$, $_closed:clflag$) >> ->
          let pl = Pcaml.vala_map (List.map (fun p -> (p, ","))) pl in
          pprintf pc "@[<1>(%p%p)@]" (pr_vala (plist patt 0)) pl
            (pr_vala (pr_bool ("",", .."))) clflag

      | <:patt< {$_list:lpl$} >> ->
          let lxl = Pcaml.vala_map (List.map (fun lx -> (lx, ";"))) lpl in
          pprintf pc "@[<1>{%p}@]" (pr_vala (plist (binding patt) 0)) lxl
      | <:patt< [| $_list:pl$ |] >> ->
         pr_vala_with
           ~{vaant=(fun pc anti -> pprintf pc "[| %s |]" anti)}
           ~{vaval=(fun pc pl ->
          if pl = [] then pprintf pc "[| |]"
          else
            let pl = List.map (fun p -> (p, ";")) pl in
            pprintf pc "@[<3>[| %p |]@]" (plist patt 0) pl)}
           pc pl

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
      | <:patt:< (type $_lid:s$) >> ->
          pprintf pc "(type %p)" (pr_vala var_escaped_noloc) s
      | <:patt< (module $_uidopt:s$ : $mt$) >> ->
          pprintf pc "@[<1>(module %p :@ %p)@]" (pr_vala (pr_opt (pr_vala pr_string) "_")) s module_type mt
      | <:patt< (module $_uidopt:s$) >> ->
          pprintf pc "(module %p)" (pr_vala (pr_opt (pr_vala pr_string) "_")) s
      | <:patt< $_int:s$ >> | <:patt< $_flo:s$ >> ->
          pr_vala (fun pc s ->
          if String.length s > 0 && s.[0] = '-' then pprintf pc "(%s)" s
          else pprintf pc "%s" s)
            pc s
      | <:patt< $_int32:s$ >> ->
          pr_vala (fun pc s ->
          if String.length s > 0 && s.[0] = '-' then pprintf pc "(%sl)" s
          else pprintf pc "%sl" s)
            pc s
      | <:patt< $_int64:s$ >> ->
          pr_vala (fun pc s ->
          if String.length s > 0 && s.[0] = '-' then pprintf pc "(%sL)" s
          else pprintf pc "%sL" s)
            pc s
      | <:patt< $_nativeint:s$ >> ->
          pr_vala (fun pc s ->
          if String.length s > 0 && s.[0] = '-' then pprintf pc "(%sn)" s
          else pprintf pc "%sn" s)
            pc s
      | <:patt< [% $_extension:e$ ] >> ->
          pprintf pc "%p" (pr_extension "%") e
      | <:patt:< $lid:s$ >> when is_special_op s ->
          pprintf pc "( %s )" s
      | <:patt:< $_lid:s$ >> ->
          (pr_vala var_escaped_noloc) pc s
      | <:patt< $_chr:s$ >> ->
          pr_vala (fun pc s -> pprintf pc "'%s'" s) pc s
      | <:patt< $_str:s$ >> ->
          pr_vala (fun pc s -> pprintf pc "\"%s\"" s) pc s
      | <:patt< _ >> ->
          pprintf pc "_"
      | MLast.PaXtr _ s _ ->
         pprintf pc "%p" pr_xtr s
      | MLast.PaLab loc _ _ | MLast.PaOlb loc _ _ ->
          error loc "labels not pretty printed (in patt); add pr_ro.cmo"
      | <:patt< `$_:s$ >> ->
          failwith "variants not pretty printed (in patt); add pr_ro.cmo"
      | <:patt< $_$ $_$ >> | <:patt< $_$ | $_$ >> | <:patt< $_$ .. $_$ >>
      |  <:patt< exception $_$ >>
      | <:patt< $_$ [@ $attribute:_$] >>
(*
      | <:patt< [% $_extension:_$ ] >>
*)
        as z ->
          pprintf pc "@[<1>(%p)@]" patt z
      | z ->
          Ploc.raise (MLast.loc_of_patt z)
            (Failure (Format.asprintf "pr_patt %d: %a" (Obj.tag (Obj.repr z))
                        Pp_MLast.pp_patt z)) ] ]
  ;
  pr_ctyp:
    [ "top"
      [ <:ctyp< $x$ == $_priv:pf$ $y$ >> ->
       let spc = Pcaml.vala_mapa (fun [ False -> "" | True -> " " ]) (fun _ -> " ") pf in
       pprintf pc "%p ==%s%p@;%p"
         next x
         spc
         (pr_vala (pr_bool ("private",""))) pf
         next y ]
    | "alg_attribute"
      [ <:ctyp< $ct$ [@ $_attribute:attr$] >> ->
        pprintf pc "%p[@%p]" curr ct (pr_vala attribute_body) attr
      ]
    | "below_alg_attribute"
      [ z -> next pc z ]

    | "as"
      [ <:ctyp< $t1$ as $t2$ >> ->
          pprintf pc "%p@ as %p" curr t1 next t2 ]
    | "poly"
      [ <:ctyp< ! $_list:pl$ . $t$ >> ->
          pprintf pc "! %p .@;%p" (pr_vala (hlist typevar)) pl ctyp t
      | <:ctyp:< type $_list:pl$ . $t$ >> ->
          pprintf pc "type %p .@;%p" (pr_vala (hlist lident)) pl ctyp t ]
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
      [
        <:ctyp< $longid:me$ . $_lid:lid$ >> -> pprintf pc "%p.%p" longident me (pr_vala pr_string) lid
      | <:ctyp< $longid:me$ . ( $t$ ) >> -> pprintf pc "%p.( %p )" longident me ctyp t
      ]
    | "simple"
      [ <:ctyp< { $_list:ltl$ } >> ->
          horiz_vertic
            (fun () ->
               pprintf pc "{ %p }"
                 (pr_vala (hlistl (semi_after label_decl) label_decl)) ltl)
            (fun () ->
               pprintf pc "@[<2>{ %p }@]"
                 (pr_vala (vlistl (semi_after label_decl) label_decl)) ltl)
      | <:ctyp< [ $_list:vdl$ ] >> ->
         pr_vala_with
           ~{vaant=(fun pc anti -> pprintf pc "[ %s ]" anti)}
        ~{vaval=(fun pc vdl ->
          if vdl = [] then pprintf pc "[ | ]"
          else
            horiz_vertic_if (has_cons_with_params vdl)
              (fun () ->
                 pprintf pc "[ %p ]" (hlist2 cons_decl (bar_before cons_decl))
                   vdl)
              (fun () ->
                 pprintf pc "[ %p ]" (vlist2 cons_decl (bar_before cons_decl))
                   vdl))}
        pc vdl

      | <:ctyp< ($_list:tl$) >> ->
          let tl = Pcaml.vala_map (List.map (fun t -> (t, " *"))) tl in
          pprintf pc "@[<1>(%p)@]" (pr_vala (plist labeled_ctyp 0)) tl

      | <:ctyp< $_lidopt:lab$ : (module $_uid:s$ : $mt$) -> $ct$ >> ->
          let pr_lab pc s = pprintf pc "%s:" s in
          pprintf pc "@[<1>%p(module %p :@ %p) -> %p@]"
            (pr_vala (pr_opt (pr_vala pr_lab) "")) lab
            (pr_vala pr_string) s
            module_type mt
            ctyp_arrow ct

      | <:ctyp< ( module $mt$ ) >> ->
          pprintf pc "@[(module@ %p)@]" module_type mt
      | <:ctyp:< $_lid:t$ >> ->
          pr_vala (var_escaped_noloc) pc t
      | <:ctyp:< ' $s$ >> ->
          pprintf pc "%p" typevar s
      | <:ctyp< _ >> ->
          pprintf pc "_"
      | <:ctyp< .. >> -> pprintf pc ".."
      | <:ctyp< external $_str:s$ >> -> pprintf pc "external %p" (pr_vala qstring) s
      | <:ctyp< [% $_extension:e$ ] >> ->
          pprintf pc "%p" (pr_extension "%") e
      | <:ctyp< ?$i$: $t$ >> | <:ctyp< ~$_$: $t$ >> ->
          failwith "labels not pretty printed (in type); add pr_ro.cmo"
      | MLast.TyXtr _ s _ ->
         pprintf pc "%p" pr_xtr s
      | <:ctyp< [ = $_list:_$ ] >> | <:ctyp< [ > $_list:_$ ] >> |
       (* <:ctyp< [ < $_list:_$ ] >> | *) <:ctyp< [ < $_list:_$ > $_list:_$ ] >> ->
          failwith "variants not pretty printed (in type); add pr_ro.cmo"
      | <:ctyp< $_$ $_$ >> | <:ctyp< $_$ -> $_$ >>
      | <:ctyp< $_$ [@ $attribute:_$ ] >>
        as z ->
          pprintf pc "@[<1>(%p)@]" ctyp z
      | MLast.TyXtr _ s _ ->
         pprintf pc "%p" pr_xtr s
      ]
    ]
  ;
  pr_str_item:
    [ "top"
      [ <:str_item< # $_lid:s$ $e$ >> ->
          pprintf pc "#%p %p" (pr_vala pr_string) s expr e
      | <:str_item< declare $_list:sil$ end >> ->
        pr_vala_with
          ~{vaant=(fun pc anti -> pprintf pc "declare %s end" anti)}
          ~{vaval=(fun pc sil ->
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
                   (vlist (semi_after str_item)) sil))}
        pc sil

      | <:str_item:< exception $_excon:ec$ $_itemattrs:item_attrs$ >> ->
          pprintf pc "exception %p%p" (pr_vala (extension_constructor loc)) ec
            (pr_vala (hlist (pr_attribute "@@"))) item_attrs

      | <:str_item:< external $_lid:n$ : $_list:tyvars$ . $t$ = $_list:sl$ $_itemattrs:attrs$ >> ->
          if Pcaml.vala_mapa is_special_op (fun _ -> False) n then
            external_decl_original pc (loc, n, tyvars, t, sl, attrs)
          else
            external_decl pc (loc, n, tyvars, t, sl, attrs)
      | <:str_item< include $me$ $_itemattrs:attrs$ >> ->
          pprintf pc "include %p%p" module_expr me (pr_vala (hlist (pr_attribute "@@"))) attrs
      | <:str_item< module $_flag:rf$ $_list:mdl$ >> ->
          let rf = pr_vala (pr_bool (" rec","")) Pprintf.empty_pc rf in
          pr_vala_with
            ~{vaant=(fun pc anti -> pprintf pc "module %s %s" rf anti)}
            ~{vaval=(fun pc mdl ->
          (vlist2 (str_module ("module"^rf)) (str_module "and")) pc mdl)}
            pc mdl
      | <:str_item< module type $_:m$ = $mt$ $_itemattrs:item_attrs$ >> ->
          sig_module_or_module_type "module type" "=" pc (<:vala< Some m >>, mt, item_attrs)
      | <:str_item< open $_!:ovf$ $me$ $_itemattrs:attrs$ >> ->
          pprintf pc "open%p %p%p"
            (pr_vala (pr_bool ("!",""))) ovf
            module_expr me (pr_vala (hlist (pr_attribute "@@"))) attrs
      | <:str_item< type $_flag:nonrf$ $_list:tdl$ >> ->
          pprintf pc "type%p %p"
        (pr_vala (pr_bool (" nonrec", ""))) nonrf
            (pr_vala (vlist2 type_decl (and_before type_decl))) tdl
      | MLast.StTypExten loc te ->
          pprintf pc "type %p" (type_extension loc) te
      | <:str_item< value $_flag:rf$ $_list:pel$ >> ->
          horiz_vertic
            (fun () ->
               pprintf pc "value%p %p"
                 (pr_vala (pr_bool (" rec",""))) rf
                 (pr_vala (hlist2 value_binding (and_before value_binding))) pel)
            (fun () ->
               pprintf pc "value%p %p"
                 (pr_vala (pr_bool (" rec",""))) rf
                 (pr_vala (vlist2 value_binding (and_before value_binding))) pel)
      | <:str_item< $exp:e$ $_itemattrs:attrs$ >> ->
          pprintf pc "%p%p" expr e (pr_vala (hlist (pr_attribute "@@"))) attrs
      | <:str_item< class type $_list:_$ >> | <:str_item< class $_list:_$ >> ->
          failwith "classes and objects not pretty printed; add pr_ro.cmo"
      | MLast.StUse _ fn sl ->
          let pc = {(pc) with aft = ""} in
          pprintf pc ""
      | <:str_item< [@@@ $_attribute:attr$ ] >> ->
          pprintf pc "%p" (pr_attribute "@@@") attr
      | <:str_item< [%% $_extension:e$ ] $_itemattrs:attrs$ >> ->
          pprintf pc "%p%p" (pr_extension "%%") e (pr_vala (hlist (pr_attribute "@@"))) attrs
      | MLast.StXtr _ s _ ->
         pprintf pc "%p" pr_xtr s
      ] ]
  ;
  pr_sig_item:
    [ "top"
      [ <:sig_item< # $_lid:s$ $e$ >> ->
          let pc = {(pc) with aft = ""} in
          pprintf pc "(* #%p %p *)" (pr_vala pr_string) s expr e
      | <:sig_item< declare $_list:sil$ end >> ->
        pr_vala_with
          ~{vaant=(fun pc anti -> pprintf pc "declare %s end" anti)}
          ~{vaval=(fun pc sil ->
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
                   (vlist (semi_after sig_item)) sil))}
          pc sil
      | MLast.SgExc _ gc item_attrs -> pprintf pc "exception %p%p" cons_decl gc
            (pr_vala (hlist (pr_attribute "@@"))) item_attrs

      | <:sig_item:< external $_lid:n$ : $_list:tyvars$ . $t$ = $_list:sl$ $_itemattrs:attrs$ >> ->
          if Pcaml.vala_mapa is_special_op (fun _ -> False) n then
            external_decl_original pc (loc, n, tyvars, t, sl, attrs)
          else
            external_decl pc (loc, n, tyvars, t, sl, attrs)
      | <:sig_item< include $mt$ $_itemattrs:item_attrs$ >> ->
          pprintf pc "include %p%p" module_type mt (pr_vala (hlist (pr_attribute "@@"))) item_attrs
      | <:sig_item< module $_flag:rf$ $_list:mdl$ >> ->
          let rf = pr_vala (pr_bool (" rec","")) Pprintf.empty_pc rf in
          pr_vala_with
            ~{vaant=(fun pc anti ->  pprintf pc "module %s %s" rf anti)}
            ~{vaval=(fun pc mdl ->
            (vlist2
               (sig_module_or_module_type ("module" ^ rf) ":")
               (sig_module_or_module_type "and" ":")) pc mdl)}
            pc mdl
      | <:sig_item:< module $_uid:i$ := $longid:li$  $_itemattrs:item_attrs$ >> ->
          pprintf pc "module %p := %p%p" (pr_vala pr_string) i
            longident li (pr_vala (hlist (pr_attribute "@@"))) item_attrs
      | <:sig_item:< module alias $_uid:i$ = $longid:li$ $_itemattrs:item_attrs$ >> ->
          pprintf pc "module alias %p = %p%p" (pr_vala pr_string) i longident li (pr_vala (hlist (pr_attribute "@@"))) item_attrs
      | <:sig_item< module type $_:m$ = $mt$ $_itemattrs:item_attrs$ >> ->
          sig_module_or_module_type "module type" "=" pc (<:vala< Some m >>, mt, item_attrs)
      | <:sig_item< module type $_:m$ := $mt$ $_itemattrs:item_attrs$ >> ->
          sig_module_or_module_type "module type" ":=" pc (<:vala< Some m >>, mt, item_attrs)
      | <:sig_item< open $longid:i$ $_itemattrs:item_attrs$ >> ->
          pprintf pc "open %p%p" longident i (pr_vala (hlist (pr_attribute "@@"))) item_attrs
      | <:sig_item< type $_flag:nonrf$ $_list:tdl$ >> ->
          pprintf pc "type%p %p"
            (pr_vala (pr_bool (" nonrec", ""))) nonrf
            (pr_vala (vlist2 type_decl (and_before type_decl))) tdl
      | MLast.SgTypExten loc te ->
          pprintf pc "type %p" (type_extension loc) te

      | <:sig_item:< value $lid:s$ : ! $_list:ls$ . $t$ $_itemattrs:attrs$ >> when is_special_op s ->
          pprintf pc "value ( %s ) :@;%p%p%p" s (pr_vala typevars_binder) ls ctyp t (pr_vala (hlist (pr_attribute "@@"))) attrs

      | <:sig_item:< value $lid:s$ : $t$ $_itemattrs:attrs$ >> when is_special_op s ->
          pprintf pc "value ( %s ) :@;%p%p" s ctyp t (pr_vala (hlist (pr_attribute "@@"))) attrs

      | <:sig_item:< value $_lid:s$ : ! $_list:ls$ . $t$ $_itemattrs:attrs$ >> ->
          pprintf pc "value %p :@;%p%p%p" (pr_vala var_escaped_noloc) s (pr_vala typevars_binder) ls ctyp t (pr_vala (hlist (pr_attribute "@@"))) attrs

      | <:sig_item:< value $_lid:s$ : $t$ $_itemattrs:attrs$ >> ->
          pprintf pc "value %p :@;%p%p" (pr_vala var_escaped_noloc) s ctyp t (pr_vala (hlist (pr_attribute "@@"))) attrs

      | <:sig_item< class type $_list:_$ >> | <:sig_item< class $_list:_$ >> ->
          failwith "classes and objects not pretty printed; add pr_ro.cmo"
      | MLast.SgUse _ fn sl ->
          let pc = {(pc) with aft = ""} in
          pprintf pc ""
      | <:sig_item< [@@@ $_attribute:attr$ ] >> ->
          pprintf pc "%p" (pr_attribute "@@@") attr
      | <:sig_item< [%% $_extension:e$ ] $_itemattrs:attrs$ >> ->
          pprintf pc "%p%p" (pr_extension "%%") e (pr_vala (hlist (pr_attribute "@@"))) attrs
      | MLast.SgXtr _ s _ ->
         pprintf pc "%p" pr_xtr s
      ] ]
  ;
  pr_longident:
        [ "dot"
      [ <:extended_longident< $longid:x$ . $_uid:uid$ >> ->
          pprintf pc "%p.%p" curr x (pr_vala cons_escaped) uid
      | <:extended_longident< $longid:x$ ( $longid:y$ ) >> ->
          pprintf pc "%p(%p)" longident x longident y
      | <:extended_longident< $_uid:s$ >> ->
          pprintf pc "%p" (pr_vala cons_escaped) s
      | MLast.LiXtr _ s _ ->
         pprintf pc "%p" pr_xtr s
      ]
    | "bottom" [
        z -> pprintf pc "[INTERNAL ERROR(pr_module_longident): unexpected longident]"
      ]
    ]
  ;

  pr_module_expr:
    [ "top"
      [ <:module_expr< functor $_fp:arg$ -> $me$ >> ->
          str_or_sig_functor pc arg module_expr me ]
    | "alg_attribute"
      [ <:module_expr< $ct$ [@ $_attribute:attr$] >> ->
        pprintf pc "%p[@%p]" curr ct (pr_vala attribute_body) attr
      ]

    | [ <:module_expr< struct $_list:sil$ end >> ->
          (* Heuristic : I don't like to print structs horizontally
             when alone in a line. *)
        pr_vala_with
          ~{vaant=(fun pc anti -> pprintf pc "struct %s end" anti)}
          ~{vaval=(fun pc sil ->
          horiz_vertic_if (alone_in_line pc)
            (fun () ->
               pprintf pc "struct %p end" (hlist (semi_after str_item)) sil)
            (fun () ->
               pprintf pc "@[<b>struct@;%p@ end@]"
                 (vlist (semi_after str_item)) sil))}
          pc sil ]
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
      [ <:module_expr< $_uid:s$ >> ->
          pprintf pc "%p" (pr_vala pr_string) s
      | <:module_expr< (value $e$ : $mt1$ :> $mt2$) >> ->
          pprintf pc "@[<1>(value %p :@ %p :>@ %p)@]" expr e module_type mt1 module_type mt2
      | <:module_expr< (value $e$ : $mt$) >> ->
          pprintf pc "@[<1>(value %p :@ %p)@]" expr e module_type mt
      | <:module_expr< (value $e$) >> ->
          pprintf pc "(value %p)" expr e
      | <:module_expr< ($me$ : $mt$) >> ->
          pprintf pc "@[<1>(%p :@ %p)@]" module_expr me module_type mt
      | <:module_expr< [% $_extension:e$ ] >> ->
          pprintf pc "%p" (pr_extension "%") e
      | MLast.MeXtr _ s _ ->
         pprintf pc "%p" pr_xtr s
      | <:module_expr< functor $_fp:_$ -> $_$ >> |
        <:module_expr< struct $list:_$ end >> | <:module_expr< $_$ . $_$ >> |
        <:module_expr< $_$ $_$ >> |
        <:module_expr< $_$ [@ $attribute:_$] >>
        as z ->
          pprintf pc "@[<1>(%p)@]" module_expr z
      ] ]
  ;
  pr_module_type:
    [ "top"
      [ <:module_type< functor $_fp:arg$ -> $mt2$ >> ->
          str_or_sig_functor pc arg module_type mt2
      ]
    | [ <:module_type< module type of $me$ >> ->
          pprintf pc "@[module type of@ %p@]" module_expr me ]

    | "alg_attribute"
      [ <:module_type< $ct$ [@ $_attribute:attr$] >> ->
        pprintf pc "%p[@%p]" curr ct (pr_vala attribute_body) attr
      ]
    | "with" [ <:module_type< $mt$ with $_list:wcl$ >> ->
        pprintf pc "%p with@;%p" module_type mt
          (pr_vala (vlist2 with_constraint (and_before with_constraint))) wcl ]

    | "sig" [ <:module_type< sig $_list:sil$ end >> ->
         (* Heuristic : I don't like to print sigs horizontally
            when alone in a line. *)
        pr_vala_with
          ~{vaant=(fun pc anti -> pprintf pc "sig %s end" anti)}
          ~{vaval=(fun pc sil ->
          horiz_vertic_if (alone_in_line pc)
            (fun () ->
               pprintf pc "sig %p end" (hlist (semi_after sig_item)) sil)
            (fun () ->
               pprintf pc "@[<b>sig@;%p@ end@]"
                 (vlist (semi_after sig_item)) sil))}
          pc sil ]
    | "dot"
      [ <:module_type< $longid:li$ . $_lid:s$ >> ->
          pprintf pc "%p.%p" longident li (pr_vala pr_string) s
      | <:module_type< $longid:li$ >> ->
          pprintf pc "%p" longident li
      | <:module_type< $_lid:s$ >> ->
          pprintf pc "%p" (pr_vala pr_string) s
    ]
    | "simple"
      [ <:module_type< ' $_:s$ >> ->
          pprintf pc "'%p" (pr_vala pr_string) s
      | <:module_type< [% $_extension:e$ ] >> ->
          pprintf pc "%p" (pr_extension "%") e
      | MLast.MtXtr _ s _ ->
         pprintf pc "%p" pr_xtr s
    ]
    | "bottom"
      [ <:module_type< functor $fp:_$ -> $_$ >>
      | <:module_type< module type of $_$ >>
      | <:module_type< $_$ [@ $attribute:_$] >>
      | <:module_type< $_$ with $list:_$ >>
        as z -> pprintf pc "(%p)" module_type z
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

value print_interf = apply_printer sig_item;
value print_implem = apply_printer str_item;

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
          flag_expand_letop_syntax.val := v;
          flag_equilibrate_cases.val := v;
          flag_extensions_are_irrefutable.val := v;
          flag_horiz_let_in.val := v;
          flag_sequ_begin_at_eol.val := v;
        }
      | 'C' | 'c' -> flag_comments_in_phrases.val := is_uppercase s.[i]
      | 'D' | 'd' -> flag_expand_declare.val := is_uppercase s.[i]
      | 'E' | 'e' -> flag_equilibrate_cases.val := is_uppercase s.[i]
      | 'I' | 'i' -> flag_extensions_are_irrefutable.val := is_uppercase s.[i]
      | 'L' | 'l' -> flag_horiz_let_in.val := is_uppercase s.[i]
      | 'O' | 'o' -> flag_add_locations.val := is_uppercase s.[i]
      | 'S' | 's' -> flag_sequ_begin_at_eol.val := is_uppercase s.[i]
      | 'X' | 'x' -> flag_expand_letop_syntax.val := is_uppercase s.[i]
      | c -> failwith ("bad flag " ^ String.make 1 c) ];
      loop (i + 1)
    }
;

value default_flag () =
  let flag_on b t f = if b then t else "" in
  let flag_off b t f = if b then "" else f in
  let on_off flag =
    Printf.sprintf "%s%s%s%s%s%s%s%s"
      (flag flag_comments_in_phrases.val "C" "c")
      (flag flag_expand_declare.val "D" "d")
      (flag flag_equilibrate_cases.val "E" "e")
      (flag flag_extensions_are_irrefutable.val "I" "i")
      (flag flag_horiz_let_in.val "L" "l")
      (flag flag_add_locations.val "O" "o")
      (flag flag_sequ_begin_at_eol.val "S" "s")
      (flag flag_expand_letop_syntax.val "X" "x")
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

add_option "-flag" (Arg.String set_flags)
  ("<str> Change pretty printing behaviour according to <str>:
       A/a enable/disable all flags
       C/c enable/disable comments in phrases
       D/d enable/disable allowing expanding 'declare'
       E/e enable/disable equilibrate cases
       I/i enable/disable extensions in patterns treated as irrefutable
       L/l enable/disable allowing printing 'let..in' horizontally
       O/o enable/disable adding location comments
       S/s enable/disable printing sequences beginners at end of lines
       default setting is \"" ^ default_flag () ^ "\".");

add_option "-wflag" (Arg.String set_wflags)
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

add_option "-l" (Arg.Int (fun x -> Pretty.line_length.val := x))
  ("<length> Maximum line length for pretty printing (default " ^
     string_of_int Pretty.line_length.val ^ ")");

add_option "-sep_src" (Arg.Unit (fun () -> sep.val := None))
  "Read source file for text between phrases (default).";

add_option "-sep" (Arg.String (fun x -> sep.val := Some x))
  "<string> Use this string between phrases instead of reading source.";

add_option "-no_where" (Arg.Unit (fun () -> set_wflags "a"))
  "(obsolete since version 4.02; use rather \"-wflag a\")";

add_option "-cip" (Arg.Unit (fun x -> x))
  "(obsolete since version 4.02; use rather \"-flag C\")";

add_option "-ncip" (Arg.Unit (fun x -> x))
  "(obsolete since version 4.02; use rather \"-flag c\")";

add_option "-exp_dcl" (Arg.Unit (fun () -> set_flags "D"))
  "(obsolete since version 4.02; use rather \"-flag D\")";
end
;
