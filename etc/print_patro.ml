(* camlp5r *)
(* pr_ro.ml,v *)
(* Copyright (c) INRIA 2007-2017 *)

#directory ".";
#load "pa_macro.cmo";
#load "parse_q_MLast.cmo";
#load "q_MLast.cmo";
#load "pa_extfun.cmo";
#load "pa_extprint.cmo";
#load "pa_pprintf.cmo";

(* Pretty printing extension for objects and labels *)

open Prtools;
open Printf;
open Pretty;
open Mlsyntax.Revised;

module PP(Base : Mlsyntax.PRINTBASESIG)(Pr_r : module type of Print_patr.PP(Base)) = struct
open Base.Printers ;
open Base ;
open Pr_r ;

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

value type_var pc (tv, vastr) =
  let tv = Pcaml.vala_map (fun [ Some v -> "'" ^ v | None -> "_" ]) tv in
  pprintf pc "%p%p" (pr_vala pr_string) vastr (pr_vala pr_string) tv
;

value class_type_params pc ctp =
  if ctp = [] then pprintf pc ""
  else
    let ctp = List.map (fun ct -> (ct, ",")) ctp in
    pprintf pc "@;[%p]" (plist type_var 1) ctp
;

value class_def_or_type_decl char pc ci =
  pprintf pc "%p%p%p %c@;%p%p"
    (pr_vala (pr_bool ("virtual ",""))) ci.MLast.ciVir
    (pr_vala var_escaped_noloc) ci.MLast.ciNam
    (pr_vala class_type_params) (snd ci.MLast.ciPrm) char
    class_type ci.MLast.ciExp
    (pr_vala (hlist (Pr_r.pr_attribute "@@"))) ci.MLast.ciAttributes
;
value class_def = class_def_or_type_decl ':';
value class_type_decl = class_def_or_type_decl '=';

value class_type_decl_list pc cd =
  Pretty.horiz_vertic
    (fun () ->
       pprintf pc "class type %p"
         (pr_vala (hlist2 class_type_decl (and_before class_type_decl))) cd)
    (fun () ->
       pprintf pc "class type %p"
         (pr_vala (vlist2 class_type_decl (and_before class_type_decl))) cd)
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
         pprintf pc "%p%p%p%p%p ="
           (pr_vala (pr_bool ("virtual ",""))) ci.MLast.ciVir
           (pr_vala var_escaped_noloc) ci.MLast.ciNam
           (pr_vala class_type_params) (snd ci.MLast.ciPrm)
           (prepend_space_nelist (hlist patt)) pl
           class_type_opt ct_opt)
      (fun () ->
         let pl = List.map (fun p -> (p, "")) pl in
         let pc =
           {(pc) with
            bef =
              sprintf "%s%s%s%s " pc.bef
                ((pr_vala (pr_bool ("virtual ",""))) Pprintf.empty_pc ci.MLast.ciVir)
                ((pr_vala pr_string) Pprintf.empty_pc ci.MLast.ciNam)
                ((pr_vala class_type_params) Pprintf.empty_pc
                   (snd ci.MLast.ciPrm))}
         in
         pprintf pc "%p%p =" (plistl patt patt 4) pl class_type_opt ct_opt)
  in
  pprintf pc "@[%p@;%p%p@]" cdef () class_expr ce
    (pr_vala (hlist (Pr_r.pr_attribute "@@"))) ci.MLast.ciAttributes
;

value variant_decl pc pv =
  match pv with
  [ <:poly_variant:< `$_:c$ $_algattrs:alg_attrs$ >> ->
       pprintf pc "`%p%p" (pr_vala var_escaped_noloc) c (pr_vala (hlist (Pr_r.pr_attribute "@"))) alg_attrs
  | <:poly_variant:< `$_:c$ of $_flag:ao$ $_list:tl$ $_algattrs:alg_attrs$ >> ->
       pprintf pc "`%p of%p@;<1 5>%p%p" (pr_vala var_escaped_noloc) c
         (pr_vala (pr_bool ("& ",""))) ao
         (pr_vala (hlist2 ctyp (amp_before ctyp))) tl
         (pr_vala (hlist (Pr_r.pr_attribute "@"))) alg_attrs
  | <:poly_variant< $t$ >> ->
       ctyp pc t
  | IFDEF STRICT THEN
      _ -> failwith "Pr_ro.variant_decl"
    END ]
;

value bquote_ident pc s = pprintf pc "`%s" s;

value variant_decl_list char pc pvl sl =
  Pretty.horiz_vertic
    (fun () ->
      pprintf pc "[ %c %p%p ]" char
        (pr_vala (hlist2 variant_decl (bar_before variant_decl))) pvl
        (pr_vala (prepend_nelist " > " (hlist bquote_ident))) sl)
    (fun () ->
      pprintf pc "[ %c@   %p%p ]" char
        (pr_vala (vlist2 variant_decl (bar_before variant_decl))) pvl
        (pr_vala (prepend_nelist " > " (hlist bquote_ident))) sl)
;

value ipatt_tcon_fun_binding pc (p, eo) =
  let pr_expr pc eo =
    pprintf pc " =@;%p" expr eo in
  pprintf pc "%p%p" patt p (pr_vala (pr_opt pr_expr "")) eo
;

value ipatt_tcon_opt_eq_patt pc (p, po) =
  let pr_patt pc po =
    pprintf pc " =@;%p" patt po in
  pprintf pc "%p%p" patt p (pr_vala (pr_opt pr_patt "")) po
;

value binding elem pc (p, e, item_attrs) =
  pprintf pc "%p =@;%p%p" patt p expr e
    (pr_vala (hlist (Pr_r.pr_attribute "@@"))) item_attrs;

value field pc = fun [
  (Some s, t, attrs) -> pprintf pc "%s :@;%p%p" s ctyp t
    (pr_vala (hlist (Pr_r.pr_attribute "@"))) attrs
| (None, t, attrs) -> pprintf pc "@;%p%p" ctyp t
    (pr_vala (hlist (Pr_r.pr_attribute "@"))) attrs
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
         (pr_vala (fun pc ->
            fun
            [ Some (<:patt< ($_$ : $_$) >> as p) -> pprintf pc " %p" patt p
            | Some p -> pprintf pc " (%p)" patt p
            | None -> pprintf pc "" ]))
         csp (pr_vala (hlist (semi_after class_str_item))) csl)
    (fun () ->
       pprintf pc "@[<a>object%p@;%p@ end@]"
         (pr_vala (fun pc ->
            fun
            [ Some (<:patt< ($_$ : $_$) >> as p) -> pprintf pc " %p" patt p
            | Some p -> pprintf pc " (%p)" patt p
            | None -> pprintf pc "" ]))
         csp (pr_vala (vlist (semi_after class_str_item))) csl)
;

value sig_method_or_method_virtual pc virt priv s t item_attrs =
  pprintf pc "method%s%p %p :@;%p%p"
    virt
    (pr_vala (pr_bool (" private", ""))) priv
    (pr_vala var_escaped_noloc) s
    ctyp t
    (pr_vala (hlist (Pr_r.pr_attribute "@@"))) item_attrs
;

(* *)

EXTEND_PRINTER
  pr_patt: LEVEL "simple"
    [ [ <:patt< ~{$p$ = $p2$} >> ->
          pprintf pc "@[~{%p}@]" ipatt_tcon_opt_eq_patt (p,<:vala< Some p2 >>)
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

      | <:patt:< `$_:s$ >> ->
          pprintf pc "`%p" (pr_vala var_escaped_noloc) s
      | <:patt< # $_lilongid:lili$ >> ->
          pprintf pc "#%p" (pr_vala longident_lident) lili
      | z ->
          Ploc.raise (MLast.loc_of_patt z)
            (Failure (sprintf "pr_patt %d" (Obj.tag (Obj.repr z)))) ] ]
  ;
  pr_expr: LEVEL "apply"
    [ [ <:expr< new $_lilongid:lili$ >> ->
          pprintf pc "new@;%p" (pr_vala longident_lident) lili
      | <:expr< object $_opt:csp$ $_list:csl$ end >> ->
          class_object pc (csp, csl) ]
    | "label"
      [ <:expr< ~{$p$ $_opt:oe$} >> ->
          pprintf pc "@[~{%p}@]" ipatt_tcon_fun_binding (p,oe)
      | <:expr< ?{$p$ = $e$} >> ->
          pprintf pc "@[<2>?{%p =@;%p}@]" patt p curr e
      | <:expr< ?{$p$} >> ->
          pprintf pc "?{%p}" patt p ] ]
  ;
  pr_expr: LEVEL "dot"
    [ [ <:expr< $e$ # $_lid:s$ >> -> pprintf pc "%p#@;<0 0>%p" curr e (pr_vala pr_string) s
      | <:expr< $lid:op$ $e1$ $e2$ >> when is_hashop op ->
          pprintf pc "%p %s@;<1 0>%p" curr e1 op next e2
      ] ]
  ;
  pr_expr: LEVEL "simple"
    [ [ <:expr< ( $e$ : $t$ :> $t2$ ) >> ->
          pprintf pc "@[<1>@[<a>(%p :@ %p :>@ %p)@]@]" expr e ctyp t ctyp t2
      | <:expr< ( $e$ :> $t$ ) >> ->
          pprintf pc "@[<1>(%p :>@ %p)@]" expr e ctyp t
      | <:expr< {< $_list:fel$ >} >> ->
         pr_vala_with
           ~{vaant=(fun pc anti -> pprintf pc "{< %s >}" anti)}
           ~{vaval=(fun pc fel ->
          if fel = [] then pprintf pc "{< >}"
          else
            let fel = List.map (fun fe -> (fe, ";")) fel in
            pprintf pc "{< %p >}" (plist field_expr 3) fel)}
           pc fel
      | <:expr:< `$_:s$ >> ->
          pprintf pc "`%p" (pr_vala var_escaped_noloc) s
      | <:expr< new $_longid:_$ . $_lid:_$ >> | <:expr< new $_lid:_$ >> | <:expr< object $_list:_$ end >> as z ->
          pprintf pc "@[<1>(%p)@]" expr z
      | z ->
          not_impl "expr" pc z ] ]
  ;
  pr_ctyp: AFTER "arrow"
    [ "label"
      [ <:ctyp< ?$_:i$: $t$ >> -> pprintf pc "?%p:%p" (pr_vala pr_string) i curr t
      | <:ctyp< ~$_:i$: $t$ >> -> pprintf pc "~%p:%p" (pr_vala pr_string) i curr t ] ]
  ;
  pr_ctyp: LEVEL "simple"
    [ [ <:ctyp< < $_list:ml$ $_flag:v$ > >> ->
          let ml = Pcaml.vala_map (List.map (fun e -> (e, ";"))) ml in
          pprintf pc "< %p%p >@;<1 0>" (pr_vala (plist field 0)) ml 
            (pr_vala (pr_bool (" ..", ""))) v
      | <:ctyp< # $_lilongid:lili$ >> ->
          pprintf pc "#%p" (pr_vala longident_lident) lili
      | <:ctyp< [ = $_list:pvl$ ] >> ->
          variant_decl_list '=' pc pvl <:vala< [] >>
      | <:ctyp< [ > $_list:pvl$ ] >> ->
          variant_decl_list '>' pc pvl <:vala< [] >>
      | <:ctyp< [ < $_list:pvl$ ] >> ->
          variant_decl_list '<' pc pvl <:vala< [] >>
      | <:ctyp< [ < $_list:pvl$ > $_list:sl$ ] >> ->
          variant_decl_list '<' pc pvl sl
      | <:ctyp< $_$ as $_$ >> as z ->
          pprintf pc "@[<1>(%p)@]" ctyp z
      | z ->
          error (MLast.loc_of_ctyp z)
            (sprintf "pr_ctyp %d" (Obj.tag (Obj.repr z))) ] ]
  ;
  pr_sig_item: LEVEL "top"
    [ [ <:sig_item< class $_list:cd$ >> ->
          Pretty.horiz_vertic
            (fun () ->
               pprintf pc "class %p" (pr_vala (hlist2 class_def (and_before class_def)))
                 cd)
            (fun () ->
               pprintf pc "class %p" (pr_vala (vlist2 class_def (and_before class_def)))
                 cd)
    | <:sig_item< class type $_list:cd$ >> ->
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
      | <:str_item< class type $_list:cd$ >> ->
          class_type_decl_list pc cd ] ]
  ;
  pr_class_expr:
    [ "top"
      [ <:class_expr< fun $p$ -> $ce$ >> ->
          pprintf pc "fun %p ->@;%p" patt p curr ce
      | <:class_expr< let $_flag:rf$ $_list:pel$ in $ce$ >> ->
          pprintf pc "let%p %p in@ %p"
            (pr_vala (pr_bool (" rec", ""))) rf
            (pr_vala (vlist2 (binding expr) (and_before (binding expr)))) pel
            class_expr ce
      | <:class_expr< let open $_!:ovf$ $longid:li$ in $ce$ >> ->
          if pc.dang = ";" then
            pprintf pc "(@[<a>let open%p %p@ in@]@ %p)"
              (pr_vala (pr_bool ("!",""))) ovf
              Pr_r.longident li curr ce
          else
            pprintf pc "@[<a>let open%p %p@ in@]@ %p"
              (pr_vala (pr_bool ("!",""))) ovf
              Pr_r.longident li curr ce
      ]
    | "alg_attribute"
      [ <:class_expr< $ct$ [@ $_attribute:attr$] >> ->
        pprintf pc "%p[@%p]" curr ct (pr_vala attribute_body) attr
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
      [ <:class_expr< $_lilongid:lili$ >> ->
          (pr_vala longident_lident) pc lili
      | <:class_expr< [ $_list:ctcl$ ] $_lilongid:lili$ >> ->
          let ctcl = Pcaml.vala_map (List.map (fun ct -> (ct, ","))) ctcl in
          pprintf pc "@[<1>[%p]@;%p@]" (pr_vala (plist ctyp 0)) ctcl (pr_vala longident_lident) lili
      | <:class_expr< object $_opt:csp$ $_list:csl$ end >> ->
          class_object pc (csp, csl)
      | <:class_expr< ($ce$ : $ct$) >> ->
          pprintf pc "@[<1>(%p :@ %p)@]" class_expr ce class_type ct
      | MLast.CeXtr _ s _ ->
         pprintf pc "%p" pr_xtr s
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
          [ <:ctyp< < $_list:_$ $_flag:_$ > >> ->
              pprintf pc "[ %p ] ->@;%p" ctyp t curr ct
          | _ ->
              pprintf pc "[%p] ->@;%p" ctyp t curr ct ]
      | <:class_type< let open $_!:ovf$ $longid:li$ in $ce$ >> ->
          if pc.dang = ";" then
            pprintf pc "(@[<a>let open%p %p@ in@]@ %p)"
              (pr_vala (pr_bool ("!",""))) ovf
              Pr_r.longident li curr ce
          else
            pprintf pc "@[<a>let open%p %p@ in@]@ %p"
              (pr_vala (pr_bool ("!",""))) ovf
              Pr_r.longident li curr ce
      ]
    | "alg_attribute"
      [ <:class_type< $ct$ [@ $_attribute:attr$] >> ->
        pprintf pc "%p[@%p]" curr ct (pr_vala attribute_body) attr
      ]

    | [ <:class_type< object $_opt:cst$ $_list:csi$ end >> ->
          Pretty.horiz_vertic
            (fun () ->
               if alone_in_line pc then
                 (* Heuristic : I don't like to print it horizontally
                    when alone in a line. *)
                 Pretty.sprintf "\n"
               else
                 pprintf pc "object%p %p end"
                   (pr_vala (pr_opt (fun pc t -> pprintf pc " (%p)" ctyp t) "")) cst
                   (pr_vala (hlist (semi_after class_sig_item))) csi)
            (fun () ->
               pprintf pc "@[<b>object%p@;%p@ end@]"
                 (pr_vala (pr_opt (fun pc t -> pprintf pc "@;(%p)" ctyp t) "")) cst
                 (pr_vala (vlist (semi_after class_sig_item))) csi)
      | <:class_type< $ct$ [ $_list:ctcl$ ] >> ->
          let ctcl = Pcaml.vala_map (List.map (fun ct -> (ct, ","))) ctcl in
          pprintf pc "%p@;@[<1>[%p]@]" curr ct (pr_vala (plist ctyp 0)) ctcl ]
    | "dot"
      [
        <:class_type< $longid:li$ . $_lid:s$ >> ->
          pprintf pc "%p.%p" longident li (pr_vala pr_string) s
      | <:class_type< $_lid:s$ >> ->
          pprintf pc "%p" (pr_vala pr_string) s
    ]
    | "simple"
      [ <:class_type< [% $_extension:e$ ] >> ->
          pprintf pc "%p" (Pr_r.pr_extension "%") e
      | MLast.CtXtr _ s _ ->
         pprintf pc "%p" pr_xtr s
      | z ->
          Ploc.raise (MLast.loc_of_class_type z)
            (Failure (sprintf "pr_class_type %d" (Obj.tag (Obj.repr z)))) ] ]
  ;
  pr_class_sig_item:
    [ "top"
      [ <:class_sig_item< inherit $ct$ $_itemattrs:item_attrs$ >> ->
          pprintf pc "inherit@;%p%p" class_type ct
            (pr_vala (hlist (Pr_r.pr_attribute "@@"))) item_attrs
      | <:class_sig_item< method $_flag:priv$ $_lid:s$ : $t$ $_itemattrs:attrs$ >> ->
          sig_method_or_method_virtual pc "" priv s t attrs
      | <:class_sig_item< method virtual $_flag:priv$ $_lid:s$ : $t$ $_itemattrs:attrs$ >> ->
          sig_method_or_method_virtual pc " virtual" priv s t attrs
      | <:class_sig_item< type $t1$ = $t2$ $_itemattrs:item_attrs$ >> ->
          pprintf pc "type %p =@;%p%p" ctyp t1 ctyp t2
            (pr_vala (hlist (Pr_r.pr_attribute "@@"))) item_attrs
      | <:class_sig_item< value $_flag:mf$ $_flag:vf$ $_lid:s$ : $t$ $_itemattrs:item_attrs$ >> ->
          pprintf pc "value%p%p %p :@;%p%p"
            (pr_vala (pr_bool (" mutable", ""))) mf
            (pr_vala (pr_bool (" virtual", ""))) vf
            (pr_vala var_escaped_noloc) s ctyp t
            (pr_vala (hlist (Pr_r.pr_attribute "@@"))) item_attrs
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
      [ <:class_str_item:< inherit $_!:ovf$ $ce$ $_opt:pb$ $_itemattrs:item_attrs$ >> ->
          pprintf pc "inherit%p@;%p%p%p"
            (pr_vala (pr_bool ("!",""))) ovf
            class_expr ce
            (pr_vala (pr_opt (fun pc s -> pprintf pc " as %p" var_escaped_noloc s) "")) pb
            (pr_vala (hlist (Pr_r.pr_attribute "@@"))) item_attrs
      | <:class_str_item< initializer $e$ $_itemattrs:item_attrs$ >> ->
          pprintf pc "initializer@;%p%p" expr e
            (pr_vala (hlist (Pr_r.pr_attribute "@@"))) item_attrs
      | <:class_str_item< method virtual $_flag:priv$ $_lid:s$ : $t$ $_itemattrs:item_attrs$ >> ->
          sig_method_or_method_virtual pc " virtual" priv s t item_attrs
      | <:class_str_item<
          method $_!:ov$ $_priv:priv$ $_lid:s$ $_opt:topt$ = $e$ $_itemattrs:item_attrs$
        >> ->
          let (pl, e) =
            Pcaml.vala_mapa
              (fun
            [ Some _ -> ([], e)
            | None -> expr_fun_args e ])
              (fun _ -> ([], e))
              topt
          in
          let pl = List.map (fun p -> (p, "")) pl in
          pprintf pc "method%p%p %p%p%p =@;%p%p"
            (pr_vala (pr_bool ("!",""))) ov
            (pr_vala (pr_bool (" private",""))) priv
            (pr_vala var_escaped_noloc) s
            (prepend_space_nelist (plist patt 2)) pl
            (pr_vala (pr_opt (fun pc t -> pprintf pc " : %p" ctyp t) "")) topt
            expr e
            (pr_vala (hlist (Pr_r.pr_attribute "@@"))) item_attrs
      | <:class_str_item< type $t1$ = $t2$ $_itemattrs:item_attrs$ >> ->
          pprintf pc "type %p =@;%p%p" ctyp t1 ctyp t2
            (pr_vala (hlist (Pr_r.pr_attribute "@@"))) item_attrs
      | <:class_str_item< value $_!:ovf$ $_flag:mf$ $_lid:s$ = $e$ $_itemattrs:item_attrs$ >> ->
          pprintf pc "value%p%p %p =@;%p%p"
            (pr_vala (pr_bool ("!",""))) ovf
            (pr_vala (pr_bool (" mutable", ""))) mf
            (pr_vala var_escaped_noloc) s
            expr e
            (pr_vala (hlist (Pr_r.pr_attribute "@@"))) item_attrs
      | <:class_str_item< value virtual $_flag:mf$ $_lid:s$ : $t$ $_itemattrs:item_attrs$ >> ->
          pprintf pc "value virtual%p %p :@;%p%p"
            (pr_vala (pr_bool (" mutable", ""))) mf
            (pr_vala var_escaped_noloc) s
 ctyp t
            (pr_vala (hlist (Pr_r.pr_attribute "@@"))) item_attrs
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
end
;
