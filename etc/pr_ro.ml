(* camlp5r pa_macro.cmo q_MLast.cmo ./pa_extfun.cmo ./pa_extprint.cmo *)
(* $Id: pr_ro.ml,v 1.49 2007/09/26 07:10:43 deraugla Exp $ *)
(* Copyright (c) INRIA 2007 *)

(* Pretty printing extension for objects and labels *)

open Pretty;
open Pcaml;
open Prtools;

value not_impl name pc x =
  let desc =
    if Obj.tag (Obj.repr x) = Obj.tag (Obj.repr "") then
      sprintf "\"%s\"" (Obj.magic x)
    else if Obj.is_block (Obj.repr x) then
      "tag = " ^ string_of_int (Obj.tag (Obj.repr x))
    else "int_val = " ^ string_of_int (Obj.magic x)
  in
  sprintf "%s\"pr_ro, not impl: %s; %s\"%s" pc.bef name (String.escaped desc)
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
  [ [] -> sprintf "%s%s" pc.bef pc.aft
  | [s] -> sprintf "%s%s%s" pc.bef s pc.aft
  | [s :: sl] -> mod_ident {(pc) with bef = sprintf "%s%s." pc.bef s} sl ]
;

value semi_after elem pc x = elem {(pc) with aft = sprintf ";%s" pc.aft} x;
value amp_before elem pc x = elem {(pc) with bef = sprintf "%s& " pc.bef} x;
value and_before elem pc x = elem {(pc) with bef = sprintf "%sand " pc.bef} x;
value bar_before elem pc x = elem {(pc) with bef = sprintf "%s| " pc.bef} x;

value type_var pc (tv, (p, m)) =
  sprintf "%s%s'%s%s" pc.bef (if p then "+" else if m then "-" else "")
    (Pcaml.unvala tv) pc.aft
;

value class_type_params pc ctp =
  if ctp = [] then sprintf "%s%s" pc.bef pc.aft
  else
    let ctp = List.map (fun ct -> (ct, ",")) ctp in
    plist type_var 1
      {(pc) with bef = sprintf "%s [" pc.bef; aft = sprintf "]%s" pc.aft}
      ctp
;

value class_def_or_type_decl char pc ci =
  horiz_vertic
    (fun () ->
       sprintf "%s%s%s%s %c %s%s" pc.bef
         (if Pcaml.unvala ci.MLast.ciVir then " virtual" else "")
            (Pcaml.unvala ci.MLast.ciNam)
         (class_type_params {(pc) with bef = ""; aft = ""}
            (Pcaml.unvala (snd ci.MLast.ciPrm)))
         char
         (class_type {(pc) with bef = ""; aft = ""} ci.MLast.ciExp) pc.aft)
    (fun () ->
       let s1 =
         sprintf "%s%s%s%s %c" pc.bef
           (if Pcaml.unvala ci.MLast.ciVir then "virtual " else "")
           (Pcaml.unvala ci.MLast.ciNam)
           (class_type_params {(pc) with bef = ""; aft = ""}
              (Pcaml.unvala (snd ci.MLast.ciPrm)))
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
            {(pc) with bef = ""; aft = ""} cd)
         pc.aft)
    (fun () ->
       vlist2 class_type_decl (and_before class_type_decl)
         {(pc) with bef = sprintf "%sclass type " pc.bef} cd)
;

value rec is_irrefut_patt =
  fun
  [ <:patt< $lid:_$ >> -> True
  | <:patt< ($p$ : $_$) >> -> is_irrefut_patt p
  | <:patt< ~$_$ >> -> True
  | _ -> False ]
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
            (Pcaml.unvala ci.MLast.ciNam)
         (class_type_params {(pc) with bef = ""; aft = ""}
            (Pcaml.unvala (snd ci.MLast.ciPrm)))
         (if pl = [] then "" else
          hlist patt {(pc) with bef = " "; aft = ""} pl)
         (class_expr {(pc) with bef = ""; aft = ""} ce) pc.aft)
    (fun () ->
       let s1 =
         sprintf "%s%s%s%s%s =" pc.bef
           (if Pcaml.unvala ci.MLast.ciVir then "virtual " else "")
           (Pcaml.unvala ci.MLast.ciNam)
           (class_type_params {(pc) with bef = ""; aft = ""}
              (Pcaml.unvala (snd ci.MLast.ciPrm)))
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
  horiz_vertic
    (fun () ->
       hlist2 variant_decl (bar_before variant_decl)
         {(pc) with bef = sprintf "%s[ %c " pc.bef char;
          aft = sprintf " ]%s" pc.aft}
         pvl)
    (fun () ->
       let s1 = sprintf "%s[ %c" pc.bef char in
       let s2 =
         vlist2 variant_decl (bar_before variant_decl)
           {(pc) with bef = tab (pc.ind + 2); aft = sprintf " ]%s" pc.aft}
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

value class_object pc (csp, csl) =
  horiz_vertic
    (fun () ->
       sprintf "%sobject%s %s end%s" pc.bef
         (match csp with
          [ Some (<:patt< ($_$ : $_$) >> as p) ->
              patt {(pc) with bef = " "; aft = ""} p
          | Some p -> patt {(pc) with bef = " ("; aft = ")"} p
          | None -> "" ])
         (hlist (semi_after class_str_item)
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
         vlist (semi_after class_str_item)
           {(pc) with ind = pc.ind + 2; bef = tab (pc.ind + 2);
            aft = ""}
           csl
       in
       let s3 = sprintf "%send%s" (tab pc.ind) pc.aft in
       sprintf "%s\n%s\n%s" s1 s2 s3)
;

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

(* *)

EXTEND_PRINTER
  pr_patt: LEVEL "simple"
    [ [ <:patt< ?$s$ >> ->
          sprintf "%s?%s%s" pc.bef s pc.aft
      | <:patt< ? ($p$ $opt:eo$) >> ->
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
      | <:patt< ?$i$: ($p$ $opt:eo$) >> ->
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
          horiz_vertic
            (fun () ->
               sprintf "%snew %s%s" pc.bef
                 (class_longident {(pc) with bef = ""; aft = ""} cl) pc.aft)
            (fun () -> not_impl "new vertic" pc cl)
      | <:expr< object $opt:csp$ $list:csl$ end >> ->
          class_object pc (csp, csl) ]
    | "label"
      [ <:expr< ?$s$ >> ->
          sprintf "%s?%s%s" pc.bef s pc.aft
      | <:expr< ?$i$: $e$ >> ->
          curr {(pc) with bef = sprintf "%s?%s:" pc.bef i} e
      | <:expr< ~$s$ >> ->
          sprintf "%s~%s%s" pc.bef s pc.aft
      | <:expr< ~$s$: $e$ >> ->
          Eprinter.apply_level pr_expr "dot"
            {(pc) with bef = sprintf "%s~%s:" pc.bef s} e ] ]
  ;
  pr_expr: LEVEL "dot"
    [ [ <:expr< $e$ # $lid:s$ >> ->
          horiz_vertic
            (fun () ->
               sprintf "%s%s#%s%s" pc.bef
                 (curr {(pc) with bef = ""; aft = ""} e) s pc.aft)
            (fun () -> not_impl "# vertic" pc e) ] ]
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
    [ [ <:ctyp< ?$i$: $t$ >> ->
          curr {(pc) with bef = sprintf "%s?%s:" pc.bef i} t
      | <:ctyp< ~$i$: $t$ >> ->
          curr {(pc) with bef = sprintf "%s~%s:" pc.bef i} t
      | <:ctyp< < $list:ml$ $flag:v$ > >> ->
          if ml = [] then
            sprintf "%s<%s >%s" pc.bef (if v then " .." else "") pc.aft
          else
            let ml = List.map (fun e -> (e, ";")) ml in
            plist field 0
              {(pc) with ind = pc.ind + 2; bef = sprintf "%s< " pc.bef;
               aft = sprintf "%s >%s" (if v then " .." else "") pc.aft}
              ml
      | <:ctyp< # $list:id$ >> ->
          class_longident {(pc) with bef = sprintf "%s#" pc.bef}  id
      | <:ctyp< [ = $list:pvl$ ] >> ->
          variant_decl_list '=' pc pvl
      | <:ctyp< [ > $list:pvl$ ] >> ->
          variant_decl_list '>' pc pvl
      | <:ctyp< [ < $list:pvl$ ] >> ->
          variant_decl_list '<' pc pvl
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
                 {(pc) with bef = sprintf "%sclass " pc.bef}
                 cd)
      | <:str_item< class type $list:cd$ >> ->
          class_type_decl_list pc cd ] ]
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
          horiz_vertic
            (fun () ->
               sprintf "%s%s %s%s" pc.bef
                 (curr {(pc) with bef = ""; aft = ""} ce)
                 (Eprinter.apply_level pr_expr "label"
                    {(pc) with bef = ""; aft = ""} e)
                 pc.aft)
            (fun () -> not_impl "class_expr_apply" pc ce) ]
    | "simple"
      [ <:class_expr< $list:cl$ >> ->
          class_longident pc cl
      | <:class_expr< $list:cl$ [ $list:ctcl$ ] >> ->
          let ctcl = List.map (fun ct -> (ct, ",")) ctcl in
          horiz_vertic
            (fun  () ->
               sprintf "%s%s [%s]%s" pc.bef
                 (class_longident {(pc) with bef = ""; aft = ""} cl)
                 (plist ctyp 0 {(pc) with bef = ""; aft = ""} ctcl)
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
          class_longident pc cl
      | <:class_type< $list:cl$ [ $list:ctcl$ ] >> ->
          let ctcl = List.map (fun ct -> (ct, ",")) ctcl in
          horiz_vertic
            (fun  () ->
               sprintf "%s%s [%s]%s" pc.bef
                 (class_longident {(pc) with bef = ""; aft = ""} cl)
                 (plist ctyp 0 {(pc) with bef = ""; aft = ""} ctcl)
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
               sprintf "%svalue%s %s : %s%s" pc.bef
                 (if mf then " mutable" else "")
                 (var_escaped {(pc) with bef = ""; aft = ""} s)
                 (ctyp {(pc) with bef = ""; aft = ""} t) pc.aft)
            (fun () ->
               let s1 =
                 sprintf "%svalue%s %s :" pc.bef
                   (if mf then " mutable" else "")
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
            (fun () -> not_impl "inherit vertic" pc ce)
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
          let args =
            if pl = [] then ""
            else hlist patt {(pc) with bef = " "; aft = ""} pl
          in
          horiz_vertic
            (fun () ->
               sprintf "%smethod%s %s%s%s = %s%s" pc.bef
                 (if priv then " private" else "") s args
                 (match topt with
                  [ Some t ->
                      sprintf " : %s" (ctyp {(pc) with bef = ""; aft = ""} t)
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
                            (ctyp {(pc) with bef = ""; aft = ""} t))
                       (fun () ->
                          let s1 =
                            sprintf "%smethod%s %s%s :" pc.bef
                              (if priv then " private" else "") s args
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
          horiz_vertic
            (fun () ->
               sprintf "%stype %s = %s%s" pc.bef
                 (ctyp {(pc) with bef = ""; aft = ""} t1)
                 (ctyp {(pc) with bef = ""; aft = ""} t2) pc.aft)
            (fun () -> not_impl "class_str_item type vertic" pc t1)
      | <:class_str_item< value $flag:mf$ $lid:s$ = $e$ >> ->
          horiz_vertic
            (fun () ->
               sprintf "%svalue%s %s = %s%s" pc.bef
                 (if mf then " mutable" else "") s
                 (expr {(pc) with bef = ""; aft = ""} e) pc.aft)
            (fun () ->
               let s1 =
                 sprintf "%svalue%s %s =" pc.bef
                   (if mf then " mutable" else "") s
               in
               let s2 =
                 expr {(pc) with ind = pc.ind + 2; bef = tab (pc.ind + 2)} e
               in
               sprintf "%s\n%s" s1 s2) ] ]
  ;
END;
