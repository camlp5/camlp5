(* camlp5r *)
(* pr_ro.ml,v *)
(* Copyright (c) INRIA 2007-2017 *)

#directory ".";
#load "pa_macro.cmo";
#load "q_MLast.cmo";
#load "pa_extfun.cmo";
#load "pa_extprint.cmo";
#load "pa_pprintf.cmo";

(* Pretty printing extension for objects and labels *)

open Pcaml;
open Prtools;
open Printf;
open Pretty;
open Mlsyntax.Revised;

value not_impl name pc x =
  let desc =
    if Obj.tag (Obj.repr x) = Obj.tag (Obj.repr "") then
      "\"" ^ Obj.magic x ^ "\""
    else if Obj.is_block (Obj.repr x) then
      "tag = " ^ string_of_int (Obj.tag (Obj.repr x))
    else "int_val = " ^ string_of_int (Obj.magic x)
  in
  pprintf pc "\"pr_ro, not impl: %s; %s\"" name (String.escaped desc)
;

value error loc msg = Ploc.raise loc (Failure msg);

value is_infix = do {
  let infixes = Hashtbl.create 73 in
  List.iter (fun s -> Hashtbl.add infixes s True)
    ["!="; "&&"; "*"; "**"; "*."; "+"; "+."; "-"; "-."; "/"; "/."; "<"; "<=";
     "<>"; "="; "=="; ">"; ">="; "@"; "^"; "asr"; "land"; "lor"; "lsl"; "lsr";
     "lxor"; "mod"; "or"; "||"; "~-"; "~-."];
  fun s -> try Hashtbl.find infixes s with [ Not_found -> False ]
};

value alone_in_line pc =
  (pc.aft = "" || pc.aft = ";") && pc.bef <> "" &&
  loop 0 where rec loop i =
    if i >= String.length pc.bef then True
    else if pc.bef.[i] = ' ' then loop (i + 1)
    else False
;

value expr = Eprinter.apply pr_expr;
value patt = Eprinter.apply pr_patt;
value ctyp = Eprinter.apply pr_ctyp;
value class_expr = Eprinter.apply pr_class_expr;
value class_type = Eprinter.apply pr_class_type;
value class_str_item = Eprinter.apply pr_class_str_item;
value class_sig_item = Eprinter.apply pr_class_sig_item;
value expr_fun_args ge = Extfun.apply pr_expr_fun_args.val ge;

value rec mod_ident pc sl =
  match sl with
  [ [] -> pprintf pc ""
  | [s] -> pprintf pc "%s" s
  | [s :: sl] -> pprintf pc "%s.%p" s mod_ident sl ]
;

value semi_after elem pc x = pprintf pc "%p;" elem x;
value amp_before elem pc x = pprintf pc "& %p" elem x;
value and_before elem pc x = pprintf pc "and %p" elem x;
value bar_before elem pc x = pprintf pc "| %p" elem x;

value type_var pc (tv, (vari, inj)) =
  let tv = Pcaml.unvala tv in
  pprintf pc "%s%s%s"
    (match vari with
     [ Some True -> "+"
     | Some False -> "-"
     | None -> "" ])
    (match inj with
       [ True -> "!"
       | False -> ""
       ])
    (match tv with
     [ Some v -> "'" ^ v
     | None -> "_" ])
;

value class_type_params pc ctp =
  if ctp = [] then pprintf pc ""
  else
    let ctp = List.map (fun ct -> (ct, ",")) ctp in
    pprintf pc "@;[%p]" (plist type_var 1) ctp
;

value class_def_or_type_decl char pc ci =
  pprintf pc "%s%p%p %c@;%p%p"
    (if Pcaml.unvala ci.MLast.ciVir then "virtual " else "")
    Pr_r.var_escaped_noloc (Pcaml.unvala ci.MLast.ciNam)
    class_type_params (Pcaml.unvala (snd ci.MLast.ciPrm)) char
    class_type ci.MLast.ciExp
    (hlist (Pr_r.pr_attribute "@@")) (Pcaml.unvala ci.MLast.ciAttributes)
;
value class_def = class_def_or_type_decl ':';
value class_type_decl = class_def_or_type_decl '=';

value class_type_decl_list pc cd =
  Pretty.horiz_vertic
    (fun () ->
       pprintf pc "class type %p"
         (hlist2 class_type_decl (and_before class_type_decl)) cd)
    (fun () ->
       pprintf pc "class type %p"
         (vlist2 class_type_decl (and_before class_type_decl)) cd)
;

value rec is_irrefut_patt =
  fun
  [ <:patt< $lid:_$ >> -> True
  | <:patt< ($p$ : $_$) >> -> is_irrefut_patt p
  | <:patt< ~{$_$} >> -> True
  | <:patt< ~{$_$ = $_$} >> -> True
  | <:patt< ?{$_$} >> -> True
  | <:patt< ?{$_$ = $_$} >> -> True
  | <:patt< () >> -> True
  | _ -> False ]
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
         pprintf pc "%s%p%p%s%p%p ="
           (if Pcaml.unvala ci.MLast.ciVir then "virtual " else "")
           Pr_r.var_escaped (ci.MLast.ciLoc, Pcaml.unvala ci.MLast.ciNam)
           class_type_params (Pcaml.unvala (snd ci.MLast.ciPrm))
           (if pl = [] then "" else " ") (hlist patt) pl
           class_type_opt ct_opt)
      (fun () ->
         let pl = List.map (fun p -> (p, "")) pl in
         let pc =
           {(pc) with
            bef =
              sprintf "%s%s%s%s " pc.bef
                (if Pcaml.unvala ci.MLast.ciVir then "virtual " else "")
                (Pcaml.unvala ci.MLast.ciNam)
                (class_type_params Pprintf.empty_pc
                   (Pcaml.unvala (snd ci.MLast.ciPrm)))}
         in
         pprintf pc "%p%p =" (plistl patt patt 4) pl class_type_opt ct_opt)
  in
  pprintf pc "@[%p@;%p%p@]" cdef () class_expr ce
    (hlist (Pr_r.pr_attribute "@@")) (Pcaml.unvala ci.MLast.ciAttributes)
;

value variant_decl pc pv =
  match pv with
  [ <:poly_variant:< `$c$ $_algattrs:alg_attrs$ >> ->
       pprintf pc "`%p%p" Pr_r.var_escaped (loc, c) (hlist (Pr_r.pr_attribute "@")) (Pcaml.unvala alg_attrs)
  | <:poly_variant:< `$c$ of $flag:ao$ $list:tl$ $_algattrs:alg_attrs$ >> ->
       pprintf pc "`%p of%s@;<1 5>%p%p" Pr_r.var_escaped (loc, c) (if ao then "& " else "")
         (hlist2 ctyp (amp_before ctyp)) tl (hlist (Pr_r.pr_attribute "@")) (Pcaml.unvala alg_attrs)
  | <:poly_variant< $t$ >> ->
       ctyp pc t
  | IFDEF STRICT THEN
      _ -> failwith "Pr_ro.variant_decl"
    END ]
;

value bquote_ident pc s = pprintf pc "`%s" s;

value variant_decl_list char pc pvl sl =
  if pvl = [] then pprintf pc "[ %c ]" char
  else
    Pretty.horiz_vertic
      (fun () ->
         pprintf pc "[ %c %p%p ]" char
           (hlist2 variant_decl (bar_before variant_decl)) pvl
           (fun pc → fun
            | [] → pprintf pc ""
            | sl → pprintf pc " > %p" (hlist bquote_ident) sl
            end) sl)
      (fun () ->
         pprintf pc "[ %c@   %p%p ]" char
           (vlist2 variant_decl (bar_before variant_decl)) pvl
           (fun pc → fun
            | [] → pprintf pc ""
            | sl → pprintf pc " > %p" (hlist bquote_ident) sl
            end) sl)
;

value ipatt_tcon_fun_binding pc (p, eo) =
  match Pcaml.unvala eo with
  [ Some e -> pprintf pc "%p =@;%p" patt p expr e
  | None -> patt pc p ]
;

value ipatt_tcon_opt_eq_patt pc (p, po) =
  match Pcaml.unvala po with
  [ Some p2 -> pprintf pc "%p =@;%p" patt p patt p2
  | None -> patt pc p ]
;

value binding elem pc (p, e, item_attrs) =
  pprintf pc "%p =@;%p%p" patt p expr e
    (hlist (Pr_r.pr_attribute "@@")) (Pcaml.unvala item_attrs);
value field pc = fun [
  (Some s, t, attrs) -> pprintf pc "%s :@;%p%p" s ctyp t
    (hlist (Pr_r.pr_attribute "@")) (Pcaml.unvala attrs)
| (None, t, attrs) -> pprintf pc "@;%p%p" ctyp t
    (hlist (Pr_r.pr_attribute "@")) (Pcaml.unvala attrs)
]
;

value field_expr pc (s, e) = pprintf pc "%s =@;%p" s expr e;

value patt_tcon pc p =
  match p with
  [ <:patt< ($p$ : $t$) >> -> pprintf pc "%p :@ %p" patt p ctyp t
  | p -> patt pc p ]
;

value class_object pc (csp, csl) =
  Pretty.horiz_vertic
    (fun () ->
       pprintf pc "object%p %p end"
         (fun pc ->
            fun
            [ Some (<:patt< ($_$ : $_$) >> as p) -> pprintf pc " %p" patt p
            | Some p -> pprintf pc " (%p)" patt p
            | None -> pprintf pc "" ])
         csp (hlist (semi_after class_str_item)) csl)
    (fun () ->
       pprintf pc "@[<a>object%p@;%p@ end@]"
         (fun pc ->
            fun
            [ Some (<:patt< ($_$ : $_$) >> as p) -> pprintf pc " %p" patt p
            | Some p -> pprintf pc " (%p)" patt p
            | None -> pprintf pc "" ])
         csp (vlist (semi_after class_str_item)) csl)
;

value sig_method_or_method_virtual pc virt priv s t item_attrs =
  pprintf pc "method%s%s %p :@;%p%p" virt (if priv then " private" else "") Pr_r.var_escaped_noloc s
    ctyp t (hlist (Pr_r.pr_attribute "@@")) (Pcaml.unvala item_attrs)
;

(* *)

EXTEND_PRINTER
  pr_patt: LEVEL "simple"
    [ [ <:patt< ~{$list:lpop$} >> ->
          let lpoe = List.map (fun pop -> (pop, ";")) lpop in
          pprintf pc "@[~{%p}@]" (plist ipatt_tcon_opt_eq_patt 1) lpoe
      | <:patt< ~{$p$} >> ->
          pprintf pc "~{%p}" patt p

      | <:patt< ?{$p$ : $t$ = $e$} >> ->
          pprintf pc "?{%p :@;%p =@;%p}" patt p ctyp t expr e
      | <:patt< ?{$p$ : $t$} >> ->
          pprintf pc "?{%p :@;%p}" patt p ctyp t
      | <:patt< ?{$p$ = $e$} >> ->
          pprintf pc "?{%p =@;%p}" patt p expr e
      | <:patt< ?{$p$} >> ->
          pprintf pc "?{%p}" patt p

      | <:patt:< `$s$ >> ->
          pprintf pc "`%p" Pr_r.var_escaped (loc, s)
      | <:patt< # $lilongid:lili$ >> ->
          pprintf pc "#%p" Pr_r.longident_lident lili
      | z ->
          Ploc.raise (MLast.loc_of_patt z)
            (Failure (sprintf "pr_patt %d" (Obj.tag (Obj.repr z)))) ] ]
  ;
  pr_expr: LEVEL "apply"
    [ [ <:expr< new $lilongid:lili$ >> ->
          pprintf pc "new@;%p" Pr_r.longident_lident lili
      | <:expr< object $opt:csp$ $list:csl$ end >> ->
          class_object pc (csp, csl) ]
    | "label"
      [ <:expr< ~{$list:lpoe$} >> ->
          let lpoe = List.map (fun poe -> (poe, ";")) lpoe in
          pprintf pc "@[~{%p}@]" (plist ipatt_tcon_fun_binding 1) lpoe
      | <:expr< ?{$p$ = $e$} >> ->
          pprintf pc "@[<2>?{%p =@;%p}@]" patt p curr e
      | <:expr< ?{$p$} >> ->
          pprintf pc "?{%p}" patt p ] ]
  ;
  pr_expr: LEVEL "dot"
    [ [ <:expr< $e$ # $lid:s$ >> -> pprintf pc "%p#@;<0 0>%s" curr e s
      | <:expr< $lid:op$ $e1$ $e2$ >> when is_hashop op ->
          pprintf pc "%p %s@;<1 0>%p" curr e1 op next e2
      ] ]
  ;
  pr_expr: LEVEL "simple"
    [ [ <:expr< ( $e$ : $t$ :> $t2$ ) >> ->
          pprintf pc "@[<1>@[<a>(%p :@ %p :>@ %p)@]@]" expr e ctyp t ctyp t2
      | <:expr< ( $e$ :> $t$ ) >> ->
          pprintf pc "@[<1>(%p :>@ %p)@]" expr e ctyp t
      | <:expr< {< $list:fel$ >} >> ->
          if fel = [] then pprintf pc "{< >}"
          else
            let fel = List.map (fun fe -> (fe, ";")) fel in
            pprintf pc "{< %p >}" (plist field_expr 3) fel
      | <:expr:< `$s$ >> ->
          pprintf pc "`%p" Pr_r.var_escaped (loc, s)
      | <:expr< new $longid:_$ . $lid:_$ >> | <:expr< new $lid:_$ >> | <:expr< object $list:_$ end >> as z ->
          pprintf pc "@[<1>(%p)@]" expr z
      | z ->
          not_impl "expr" pc z ] ]
  ;
  pr_ctyp: AFTER "arrow"
    [ "label"
      [ <:ctyp< ?$i$: $t$ >> -> pprintf pc "?%s:%p" i curr t
      | <:ctyp< ~$i$: $t$ >> -> pprintf pc "~%s:%p" i curr t ] ]
  ;
  pr_ctyp: LEVEL "simple"
    [ [ <:ctyp< < $list:ml$ $flag:v$ > >> ->
          if ml = [] then pprintf pc "<%s >@;<1 0>" (if v then " .." else "")
          else
            let ml = List.map (fun e -> (e, ";")) ml in
            pprintf pc "< %p%s >@;<1 0>" (plist field 0) ml (if v then " .." else "")
      | <:ctyp< # $lilongid:lili$ >> ->
          pprintf pc "#%p" Pr_r.longident_lident lili
      | <:ctyp< [ = $list:pvl$ ] >> ->
          variant_decl_list '=' pc pvl []
      | <:ctyp< [ > $list:pvl$ ] >> ->
          variant_decl_list '>' pc pvl []
      | <:ctyp< [ < $list:pvl$ ] >> ->
          variant_decl_list '<' pc pvl []
      | <:ctyp< [ < $list:pvl$ > $list:sl$ ] >> ->
          variant_decl_list '<' pc pvl sl
      | <:ctyp< $_$ as $_$ >> as z ->
          pprintf pc "@[<1>(%p)@]" ctyp z
      | z ->
          error (MLast.loc_of_ctyp z)
            (sprintf "pr_ctyp %d" (Obj.tag (Obj.repr z))) ] ]
  ;
  pr_sig_item: LEVEL "top"
    [ [ <:sig_item< class $list:cd$ >> ->
          Pretty.horiz_vertic
            (fun () ->
               pprintf pc "class %p" (hlist2 class_def (and_before class_def))
                 cd)
            (fun () ->
               pprintf pc "class %p" (vlist2 class_def (and_before class_def))
                 cd)
    | <:sig_item< class type $list:cd$ >> ->
        class_type_decl_list pc cd ] ]
  ;
  pr_str_item: LEVEL "top"
    [ [ <:str_item< class $list:cd$ >> ->
          Pretty.horiz_vertic
            (fun () ->
               pprintf pc "class %p"
                 (hlist2 class_decl (and_before class_decl)) cd)
            (fun () ->
               pprintf pc "class %p"
                 (vlist2 class_decl (and_before class_decl)) cd)
      | <:str_item< class type $list:cd$ >> ->
          class_type_decl_list pc cd ] ]
  ;
  pr_class_expr:
    [ "top"
      [ <:class_expr< fun $p$ -> $ce$ >> ->
          pprintf pc "fun %p ->@;%p" patt p curr ce
      | <:class_expr< let $flag:rf$ $list:pel$ in $ce$ >> ->
          pprintf pc "let%s %p in@ %p" (if rf then " rec" else "")
            (vlist2 (binding expr) (and_before (binding expr))) pel
            class_expr ce
      | <:class_expr< let open $_!:ovf$ $longid:li$ in $ce$ >> ->
          let ovf = if (Pcaml.unvala ovf) then "!" else "" in
          if pc.dang = ";" then
            pprintf pc "(@[<a>let open%s %p@ in@]@ %p)" ovf Pr_r.longident li curr ce
          else
            pprintf pc "@[<a>let open%s %p@ in@]@ %p" ovf Pr_r.longident li curr ce
      ]
    | "alg_attribute"
      [ <:class_expr< $ct$ [@ $attribute:attr$] >> ->
        pprintf pc "%p[@%p]" curr ct Pr_r.attribute_body attr
      ]

    | [ <:class_expr< [% $_extension:e$ ] >> ->
          pprintf pc "%p" (Pr_r.pr_extension "%") e
      ]

    | "apply"
      [ <:class_expr< $ce$ $e$ >> ->
          let (ce, el) =
            loop [e] ce where rec loop el =
              fun
              [ <:class_expr< $ce$ $e$ >> -> loop [e :: el] ce
              | ce -> (ce, el) ]
          in
          plistf 0 {(pc) with ind = pc.ind + 2}
            [(fun pc -> curr pc ce, "") ::
             List.map
               (fun e ->
                  (fun pc -> Eprinter.apply_level pr_expr "label" pc e, ""))
               el] ]
    | "simple"
      [ <:class_expr< $lilongid:lili$ >> ->
          Pr_r.longident_lident pc lili
      | <:class_expr< [ $list:ctcl$ ] $lilongid:lili$ >> ->
          let ctcl = List.map (fun ct -> (ct, ",")) ctcl in
          pprintf pc "@[<1>[%p]@;%p@]" (plist ctyp 0) ctcl Pr_r.longident_lident lili
      | <:class_expr< object $opt:csp$ $list:csl$ end >> ->
          class_object pc (csp, csl)
      | <:class_expr< ($ce$ : $ct$) >> ->
          pprintf pc "@[<1>(%p :@ %p)@]" class_expr ce class_type ct
      | <:class_expr< $_$ $_$ >> | <:class_expr< fun $_$ -> $_$ >>
        | <:class_expr< [% $_extension:_$ ] >>
        | <:class_expr< let $flag:_$ $list:_$ in $_$ >>
        | <:class_expr< let open $_!:_$ $longid:_$ in $_$ >>
        as z ->
          pprintf pc "@[<1>(%p)@]" class_expr z
      | z ->
          error (MLast.loc_of_class_expr z)
            (sprintf "pr_class_expr %d" (Obj.tag (Obj.repr z))) ] ]
  ;
  pr_class_type:
    [ "top"
      [ <:class_type< [ $t$ ] -> $ct$ >> ->
          match t with
          [ <:ctyp< < $list:_$ $flag:_$ > >> ->
              pprintf pc "[ %p ] ->@;%p" ctyp t curr ct
          | _ ->
              pprintf pc "[%p] ->@;%p" ctyp t curr ct ]
      | <:class_type< let open $_!:ovf$ $longid:li$ in $ce$ >> ->
          let ovf = if (Pcaml.unvala ovf) then "!" else "" in
          if pc.dang = ";" then
            pprintf pc "(@[<a>let open%s %p@ in@]@ %p)" ovf Pr_r.longident li curr ce
          else
            pprintf pc "@[<a>let open%s %p@ in@]@ %p" ovf Pr_r.longident li curr ce
      ]
    | "alg_attribute"
      [ <:class_type< $ct$ [@ $attribute:attr$] >> ->
        pprintf pc "%p[@%p]" curr ct Pr_r.attribute_body attr
      ]

    | [ <:class_type< object $opt:cst$ $list:csi$ end >> ->
          Pretty.horiz_vertic
            (fun () ->
               if alone_in_line pc then
                 (* Heuristic : I don't like to print it horizontally
                    when alone in a line. *)
                 Pretty.sprintf "\n"
               else
                 pprintf pc "object%p %p end"
                   (fun pc ->
                      fun
                      [ Some t -> pprintf pc " (%p)" ctyp t
                      | None -> pprintf pc "" ])
                   cst
                   (hlist (semi_after class_sig_item)) csi)
            (fun () ->
               pprintf pc "@[<b>%p@;%p@ end@]"
                 (fun pc ->
                    fun
                    [ Some t -> pprintf pc "object@;(%p)" ctyp t
                    | None -> pprintf pc "object" ])
                 cst
                 (vlist (semi_after class_sig_item)) csi)
      | <:class_type< $ct$ [ $list:ctcl$ ] >> ->
          let ctcl = List.map (fun ct -> (ct, ",")) ctcl in
          pprintf pc "%p@;@[<1>[%p]@]" curr ct (plist ctyp 0) ctcl ]
    | "dot"
      [
        <:class_type< $longid:li$ . $lid:s$ >> ->
          pprintf pc "%p.%s" Pr_r.longident li s
      | <:class_type< $lid:s$ >> ->
          pprintf pc "%s" s
    ]
    | "simple"
      [ <:class_type< [% $_extension:e$ ] >> ->
          pprintf pc "%p" (Pr_r.pr_extension "%") e
      | z ->
          Ploc.raise (MLast.loc_of_class_type z)
            (Failure (sprintf "pr_class_type %d" (Obj.tag (Obj.repr z)))) ] ]
  ;
  pr_class_sig_item:
    [ "top"
      [ <:class_sig_item< inherit $ct$ $_itemattrs:item_attrs$ >> ->
          pprintf pc "inherit@;%p%p" class_type ct
            (hlist (Pr_r.pr_attribute "@@")) (Pcaml.unvala item_attrs)
      | <:class_sig_item< method $flag:priv$ $lid:s$ : $t$ $_itemattrs:attrs$ >> ->
          sig_method_or_method_virtual pc "" priv s t attrs
      | <:class_sig_item< method virtual $flag:priv$ $lid:s$ : $t$ $_itemattrs:attrs$ >> ->
          sig_method_or_method_virtual pc " virtual" priv s t attrs
      | <:class_sig_item< type $t1$ = $t2$ $_itemattrs:item_attrs$ >> ->
          pprintf pc "type %p =@;%p%p" ctyp t1 ctyp t2
            (hlist (Pr_r.pr_attribute "@@")) (Pcaml.unvala item_attrs)
      | <:class_sig_item< value $flag:mf$ $flag:vf$ $lid:s$ : $t$ $_itemattrs:item_attrs$ >> ->
          pprintf pc "value%s%s %p :@;%p%p"
            (if mf then " mutable" else "")
            (if vf then " virtual" else "")
            Pr_r.var_escaped_noloc s ctyp t
            (hlist (Pr_r.pr_attribute "@@")) (Pcaml.unvala item_attrs)
      | <:class_sig_item< [@@@ $_attribute:attr$ ] >> ->
          pprintf pc "%p" (Pr_r.pr_attribute "@@@") attr
      | <:class_sig_item< [%% $_extension:e$ ] >> ->
          pprintf pc "%p" (Pr_r.pr_extension "%%") e
      | z ->
          error (MLast.loc_of_class_sig_item z)
            (sprintf "pr_class_sig_item %d" (Obj.tag (Obj.repr z)))
      ] ]
  ;
  pr_class_str_item:
    [ "top"
      [ <:class_str_item:< inherit $!:ovf$ $ce$ $opt:pb$ $_itemattrs:item_attrs$ >> ->
          pprintf pc "inherit%s@;%p%p%p" (if ovf then "!" else "") class_expr ce
            (fun pc ->
               fun
               [ Some s -> pprintf pc " as %p" Pr_r.var_escaped (loc, s)
               | None -> pprintf pc "" ])
            pb
            (hlist (Pr_r.pr_attribute "@@")) (Pcaml.unvala item_attrs)
      | <:class_str_item< initializer $e$ $_itemattrs:item_attrs$ >> ->
          pprintf pc "initializer@;%p%p" expr e (hlist (Pr_r.pr_attribute "@@")) (Pcaml.unvala item_attrs)
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
          let pl = List.map (fun p -> (p, "")) pl in
          pprintf pc "method%s%s %p%s%p%p =@;%p%p"
            (if ov then "!" else "") (if priv then " private" else "") Pr_r.var_escaped_noloc s
            (if pl = [] then "" else " ") (plist patt 2) pl
            (fun pc ->
               fun
               [ Some t -> pprintf pc " : %p" ctyp t
               | None -> pprintf pc "" ])
            topt expr e (hlist (Pr_r.pr_attribute "@@")) (Pcaml.unvala item_attrs)
      | <:class_str_item< type $t1$ = $t2$ $_itemattrs:item_attrs$ >> ->
          pprintf pc "type %p =@;%p%p" ctyp t1 ctyp t2
            (hlist (Pr_r.pr_attribute "@@")) (Pcaml.unvala item_attrs)
      | <:class_str_item< value $!:ovf$ $flag:mf$ $lid:s$ = $e$ $_itemattrs:item_attrs$ >> ->
          pprintf pc "value%s%s %p =@;%p%p" (if ovf then "!" else "")
            (if mf then " mutable" else "") Pr_r.var_escaped_noloc s expr e
            (hlist (Pr_r.pr_attribute "@@")) (Pcaml.unvala item_attrs)
      | <:class_str_item< value virtual $flag:mf$ $lid:s$ : $t$ $_itemattrs:item_attrs$ >> ->
          pprintf pc "value virtual%s %p :@;%p%p"
            (if mf then " mutable" else "") Pr_r.var_escaped_noloc s ctyp t
            (hlist (Pr_r.pr_attribute "@@")) (Pcaml.unvala item_attrs)
      | <:class_str_item< [@@@ $_attribute:attr$ ] >> ->
          pprintf pc "%p" (Pr_r.pr_attribute "@@@") attr
      | <:class_str_item< [%% $_extension:e$ ] >> ->
          pprintf pc "%p" (Pr_r.pr_extension "%%") e
      | z ->
          Ploc.raise (MLast.loc_of_class_str_item z)
            (Failure
               (sprintf "pr_class_str_item %d" (Obj.tag (Obj.repr z))))
      ] ]
  ;
END;
