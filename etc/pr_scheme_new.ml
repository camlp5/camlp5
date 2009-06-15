(* camlp5r q_MLast.cmo ./pa_extprint.cmo ./pa_extfun.cmo *)
(* $Id$ *)
(* Copyright (c) INRIA 2007 *)

open Pretty;
open Pcaml;
open Prtools;

do {
  Eprinter.clear pr_expr;
  Eprinter.clear pr_patt;
  Eprinter.clear pr_ctyp;
  Eprinter.clear pr_str_item;
  Eprinter.clear pr_sig_item;
  Eprinter.clear pr_module_expr;
  Eprinter.clear pr_module_type;
(*
  Eprinter.clear pr_class_sig_item;
  Eprinter.clear pr_class_str_item;
  Eprinter.clear pr_class_expr;
  Eprinter.clear pr_class_type;
*)
};

(* general functions *)

value not_impl name pc x =
  let desc =
    if Obj.tag (Obj.repr x) = Obj.tag (Obj.repr "") then
      sprintf "\"%s\"" (Obj.magic x)
    else if Obj.is_block (Obj.repr x) then
      "tag = " ^ string_of_int (Obj.tag (Obj.repr x))
    else "int_val = " ^ string_of_int (Obj.magic x)
  in
  sprintf "%s\"pr_scheme_new, not impl: %s; %s\"%s" pc.bef name
    (String.escaped desc) pc.aft
;

value rec mod_ident pc sl =
  match sl with
  [ [] -> sprintf "%s%s" pc.bef pc.aft
  | [s] -> sprintf "%s%s%s" pc.bef s pc.aft
  | [s :: sl] -> mod_ident {(pc) with bef = sprintf "%s%s." pc.bef s} sl ]
;

value rec cons_ident pc sl =
  match sl with
  [ [] -> sprintf "%s%s" pc.bef pc.aft
  | [s] -> sprintf "%s%s%s" pc.bef s pc.aft
  | [s :: sl] -> cons_ident {(pc) with bef = sprintf "%s%s." pc.bef s} sl ]
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

pr_expr_fun_args.val :=
  extfun Extfun.empty with
  [ <:expr< fun [$p$ -> $e$] >> as ge ->
      if is_irrefut_patt p then
        let (pl, e) = expr_fun_args e in
        ([p :: pl], e)
      else ([], ge)
  | ge -> ([], ge) ];

value has_cons_with_params vdl =
  List.exists
    (fun (_, _, tl) ->
       match tl with
       [ <:vala< [] >> -> False
       | _ -> True ])
    vdl
;

value type_param pc (s, vari) =
  sprintf "%s'%s%s" pc.bef (Pcaml.unvala s) pc.aft
;

value type_decl b pc td =
  let n = Pcaml.unvala (snd td.MLast.tdNam) in
  horiz_vertic
    (fun () ->
       sprintf "%s(%s%s %s)%s" pc.bef b
         (match Pcaml.unvala td.MLast.tdPrm with
          [ [] -> n
          | tp ->
              sprintf "(%s %s)" n
                (hlist type_param {(pc) with bef = ""; aft = ""} tp) ])
         (ctyp {(pc) with bef = ""; aft = ""} td.MLast.tdDef) pc.aft)
    (fun () ->
       let s1 =
         sprintf "%s(%s%s" pc.bef b
           (match Pcaml.unvala td.MLast.tdPrm with
            [ [] -> n
            | tp ->
                sprintf "(%s %s)" n
                  (hlist type_param {(pc) with bef = ""; aft = ""} tp) ])
       in
       let s2 =
         ctyp
           {(pc) with ind = pc.ind + 1; bef = tab (pc.ind + 1);
            aft = sprintf ")%s" pc.aft}
           td.MLast.tdDef
       in
       sprintf "%s\n%s" s1 s2)
;

value type_decl_list pc =
  fun
  [ [td] -> type_decl "type " pc td
  | tdl ->
      horiz_vertic
        (fun () ->
           sprintf "%s(type* %s)%s" pc.bef
             (hlist (type_decl "") {(pc) with bef = ""; aft = ""} tdl)
             pc.aft)
        (fun () ->
           let s1 = sprintf "%s(type*" pc.bef in
           let s2 =
             vlist (type_decl "")
               {(pc) with ind = pc.ind + 1; bef = tab (pc.ind + 1);
                aft = sprintf ")%s" pc.aft}
               tdl
           in
           sprintf "%s\n%s" s1 s2) ]
;

value exception_decl pc (c, tl) =
  plistbf 0
    {(pc) with ind = pc.ind + 1; bef = sprintf "%s(exception" pc.bef;
     aft = sprintf ")%s" pc.aft}
    [(fun pc -> sprintf "%s%s%s" pc.bef c pc.aft, "") ::
     List.map (fun t -> (fun pc -> ctyp pc t, "")) tl]
;

value value_binding b pc (p, e) =
  let (pl, e) = expr_fun_args e in
  horiz_vertic
    (fun () ->
       let s =
         match pl with
         [ [] -> patt {(pc) with bef = ""; aft = ""} p
         | _ -> hlist patt {(pc) with bef = "("; aft = ")"} [p :: pl] ]
       in
       sprintf "%s(%s%s %s)%s" pc.bef b s
         (expr {(pc) with bef = ""; aft = ""} e) pc.aft)
    (fun () ->
       let s1 =
         let pc = {(pc) with bef = sprintf "%s(%s" pc.bef b; aft = ""} in
         match pl with
         [ [] -> patt pc p
         | _ ->
             hlist patt
               {(pc) with bef = sprintf "%s(" pc.bef;
                aft = sprintf ")%s" pc.aft}
               [p :: pl] ]
       in
       let s2 =
         expr
           {(pc) with ind = pc.ind + 1; bef = tab (pc.ind + 1);
            aft = sprintf ")%s" pc.aft}
           e
       in
       sprintf "%s\n%s" s1 s2)
;

value value_binding_list pc (rf, pel) =
  let b = if rf then "definerec" else "define" in
  match pel with
  [ [(p, e)] -> value_binding (b ^ " ") pc (p, e)
  | _ ->
      horiz_vertic
        (fun () ->
           sprintf "%s(%s* %s)%s" pc.bef b
             (hlist (value_binding "") {(pc) with bef = ""; aft = ""} pel)
             pc.aft)
        (fun () ->
           let s1 = sprintf "%s(%s*" pc.bef b in
           let s2 =
             vlist (value_binding "")
               {(pc) with ind = pc.ind + 1; bef = tab (pc.ind + 1);
                aft = sprintf ")%s" pc.aft}
               pel
           in
           sprintf "%s\n%s" s1 s2) ]
;

value let_binding pc (p, e) =
  let (pl, e) = expr_fun_args e in
  plistf 0
    {(pc) with ind = pc.ind + 1; bef = sprintf "%s(" pc.bef;
     aft = sprintf ")%s" pc.aft}
    [(fun pc ->
        match pl with
        [ [] -> patt pc p
        | _ ->
            hlist patt
              {(pc) with bef = sprintf "%s(" pc.bef;
               aft = sprintf ")%s" pc.aft}
              [p :: pl] ],
      "");
     (fun pc -> expr pc e, "")]
;

value let_binding_list pc (b, pel, e) =
  plistbf 0
    {(pc) with ind = pc.ind + 1; bef = sprintf "%s(%s" pc.bef b;
     aft = sprintf ")%s" pc.aft}
    [(fun pc ->
        let pc =
          {(pc) with ind = pc.ind + 1; bef = sprintf "%s(" pc.bef;
           aft = sprintf ")%s" pc.aft}
        in
        horiz_vertic
          (fun () -> hlist let_binding pc pel)
          (fun () -> vlist let_binding pc pel),
      "");
     (fun pc -> expr pc e, "")]
;

value match_assoc pc (p, we, e) =
  let list = [(fun pc -> expr pc e, "")] in
  let list =
    match we with
    [ <:vala< Some e >> ->
        [(fun pc ->
            plistbf 0
              {(pc) with ind = pc.ind + 1; bef = sprintf "%s(when" pc.bef;
               aft = sprintf ")%s" pc.aft}
              [(fun pc -> patt pc p, ""); (fun pc -> expr pc e, "")],
          "") ::
         list]
    | _ -> [(fun pc -> patt pc p, "") :: list] ]
  in
  plistf 0
    {(pc) with ind = pc.ind + 1; bef = sprintf "%s(" pc.bef;
     aft = sprintf ")%s" pc.aft}
    list
;

value constr_decl pc (_, c, tl) =
  let c = Pcaml.unvala c in
  let tl = Pcaml.unvala tl in
  match tl with
  [ [] -> sprintf "%s(%s)%s" pc.bef c pc.aft
  | _ ->
      plistf 0
        {(pc) with ind = pc.ind + 1; bef = sprintf "%s(" pc.bef;
         aft = sprintf ")%s" pc.aft}
        [(fun pc -> sprintf "%s%s%s" pc.bef c pc.aft, "") ::
         List.map (fun t -> (fun pc -> ctyp pc t, "")) tl] ]
;

value label_decl pc (_, l, m, t) =
  let list = [(fun pc -> ctyp pc t, "")] in
  plistf 0
    {(pc) with ind = pc.ind + 1; bef = sprintf "%s(" pc.bef;
     aft = sprintf ")%s" pc.aft}
    [(fun pc -> sprintf "%s%s%s" pc.bef l pc.aft, "") ::
     if m then [(fun pc -> sprintf "%smutable%s" pc.bef pc.aft, "") :: list]
     else list]
;

value module_type_decl pc (s, mt) =
  plistbf 0
    {(pc) with ind = pc.ind + 1; bef = sprintf "%s(moduletype" pc.bef;
     aft = sprintf ")%s" pc.aft}
    [(fun pc -> sprintf "%s%s%s" pc.bef s pc.aft, "");
     (fun pc -> module_type pc mt, "")]
;

value string pc s = sprintf "%s\"%s\"%s" pc.bef s pc.aft;

value int_repr s =
  if String.length s > 2 && s.[0] = '0' then
    match s.[1] with
    [ 'b' | 'o' | 'x' | 'B' | 'O' | 'X' ->
        "#" ^ String.sub s 1 (String.length s - 1)
    | _ -> s ]
  else s
;

value with_constraint pc =
  fun
  [ <:with_constr< type $sl$ $list:tvl$ = $flag:pf$ $t$ >> ->
      horiz_vertic
        (fun () ->
           let n = mod_ident {(pc) with bef = ""; aft = ""} sl in
           sprintf "%s(type%s %s %s)%s" pc.bef (if pf then "private" else "")
             (match tvl with
              [ [] -> n
              | tvl ->
                  sprintf "(%s %s)" n
                    (hlist type_param {(pc) with bef = ""; aft = ""} tvl) ])
             (ctyp {(pc) with bef = ""; aft = ""} t) pc.aft)
        (fun () -> not_impl "with_constraint type vertic" pc 0)
  | wc -> not_impl "with_constraint" pc wc ]
;

EXTEND_PRINTER
  pr_ctyp:
    [ "top"
      [ <:ctyp< [ $list:cdl$ ] >> ->
          horiz_vertic
            (fun () ->
               if has_cons_with_params cdl then sprintf "\n"
               else
                 sprintf "%s[%s]%s" pc.bef
                   (hlist constr_decl {(pc) with bef = ""; aft = ""} cdl)
                   pc.aft)
            (fun () ->
               vlist constr_decl
                 {(pc) with ind = pc.ind + 1; bef = sprintf "%s[" pc.bef;
                  aft = sprintf "]%s" pc.aft}
                 cdl)
      | <:ctyp< { $list:cdl$ } >> ->
          let cdl = List.map (fun cd -> (cd, "")) cdl in
          plist label_decl 0
            {(pc) with ind = pc.ind + 1; bef = sprintf "%s{" pc.bef;
             aft = sprintf "}%s" pc.aft}
            cdl
      | <:ctyp< ( $list:tl$ ) >> ->
          let tl = List.map (fun t -> (t, "")) tl in
          plistb curr 0
            {(pc) with ind = pc.ind + 1; bef = sprintf "%s(*" pc.bef;
             aft = sprintf ")%s" pc.aft}
            tl
      | <:ctyp< $t1$ -> $t2$ >> ->
          let tl =
            loop t2 where rec loop =
              fun
              [ <:ctyp< $t1$ -> $t2$ >> -> [(t1, "") :: loop t2]
              | t -> [(t, "")] ]
          in
          plistb ctyp 1
            {(pc) with bef = sprintf "%s(->" pc.bef;
             aft = sprintf ")%s" pc.aft}
            [(t1, "") :: tl]
      | <:ctyp< $t1$ $t2$ >> ->
          let tl =
            loop [t2] t1 where rec loop tl =
              fun
              [ <:ctyp< $t1$ $t2$ >> -> loop [t2 :: tl] t1
              | t1 -> [t1 :: tl] ]
          in
          let tl = List.map (fun p -> (p, "")) tl in
          plist curr 1
            {(pc) with ind = pc.ind + 1; bef = sprintf "%s(" pc.bef;
             aft = sprintf ")%s" pc.aft}
            tl
      | <:ctyp< $t1$ == $t2$ >> ->
          plistb curr 0
            {(pc) with ind = pc.ind + 1; bef = sprintf "%s(==" pc.bef;
             aft = sprintf ")%s" pc.aft}
            [(t1, ""); (t2, "")]
      | <:ctyp< $t1$ . $t2$ >> ->
           sprintf "%s.%s"
             (curr {(pc) with aft = ""} t1)
             (curr {(pc) with bef = ""} t2)
      | <:ctyp< $lid:s$ >> | <:ctyp< $uid:s$ >> ->
          sprintf "%s%s%s" pc.bef s pc.aft
      | <:ctyp< ' $s$ >> ->
          sprintf "%s'%s%s" pc.bef s pc.aft
      | <:ctyp< _ >> ->
          sprintf "%s_%s" pc.bef pc.aft
      | x ->
          not_impl "ctyp" pc x ] ]
  ;
  pr_expr:
    [ "top"
      [ <:expr< fun [] >> ->
          sprintf "%s(lambda)%s" pc.bef pc.aft
      | <:expr< fun $lid:s$ -> $e$ >> ->
          plistbf 0
            {(pc) with ind = pc.ind + 1; bef = sprintf "%s(lambda" pc.bef;
             aft = sprintf ")%s" pc.aft}
            [(fun pc -> sprintf "%s%s%s" pc.bef s pc.aft, "");
             (fun pc -> curr pc e, "")]
      | <:expr< fun [ $list:pwel$ ] >> ->
          horiz_vertic (fun () -> sprintf "\n")
            (fun () ->
               let s1 = sprintf "%s(lambda_match" pc.bef in
               let s2 =
                 vlist match_assoc
                   {(pc) with ind = pc.ind + 1; bef = tab (pc.ind + 1);
                    aft = sprintf ")%s" pc.aft}
                   pwel
               in
               sprintf "%s\n%s" s1 s2)
      | <:expr< match $e$ with [ $list:pwel$ ] >> |
        <:expr< try $e$ with [ $list:pwel$ ] >> as x ->
          let op =
            match x with
            [ <:expr< match $e$ with [ $list:pwel$ ] >> -> "match"
            | _ -> "try" ]
          in
          horiz_vertic
            (fun () ->
               sprintf "%s(%s %s %s)%s" pc.bef op
                 (curr {(pc) with bef = ""; aft = ""} e)
                 (hlist match_assoc {(pc) with bef = ""; aft = ""} pwel)
                 pc.aft)
            (fun () ->
               let s1 =
                 let pc = {(pc) with bef = sprintf "%s(" pc.bef} in
                 horiz_vertic
                   (fun () ->
                      sprintf "%s%s %s" pc.bef op
                        (curr {(pc) with bef = ""; aft = ""} e))
                   (fun () ->
                      let s1 = sprintf "%s%s" pc.bef op in
                      let s2 =
                        curr
                          {(pc) with ind = pc.ind + 1; bef = tab (pc.ind + 1);
                           aft = ""}
                        e
                      in
                      sprintf "%s\n%s" s1 s2)
               in
               let s2 =
                 let pc =
                   {(pc) with ind = pc.ind + 1; bef = tab (pc.ind + 1)}
                 in
                 vlist match_assoc {(pc) with aft = sprintf ")%s" pc.aft} pwel
               in
               sprintf "%s\n%s" s1 s2)
      | <:expr< let $p1$ = $e1$ in $e2$ >> ->
          let (pel, e) =
            loop [(p1, e1)] e2 where rec loop pel =
              fun
              [ <:expr< let $p1$ = $e1$ in $e2$ >> ->
                  loop [(p1, e1) :: pel] e2
              | e -> (List.rev pel, e) ]
          in
          let b =
            match pel with
            [ [_] -> "let"
            | _ -> "let*" ]
          in
          let_binding_list pc (b, pel, e)
      | <:expr< let $flag:rf$ $list:pel$ in $e$ >> ->
          let b = if rf then "letrec" else "let" in
          let_binding_list pc (b, pel, e)
      | <:expr< let module $s$ = $me$ in $e$  >> ->
          plistbf 0
            {(pc) with ind = pc.ind + 1; bef = sprintf "%s(letmodule" pc.bef;
             aft = sprintf ")%s" pc.aft}
            [(fun pc -> sprintf "%s%s%s" pc.bef s pc.aft, "");
             (fun pc -> module_expr pc me, "");
             (fun pc -> curr pc e, "")]
      | <:expr< if $e1$ then $e2$ else () >> ->
          plistb curr 0
            {(pc) with ind = pc.ind + 1; bef = sprintf "%s(if" pc.bef;
             aft = sprintf ")%s" pc.aft}
            [(e1, ""); (e2, "")]
      | <:expr< if $e1$ then $e2$ else $e3$ >> ->
          horiz_vertic
            (fun () ->
               let pc1 = {(pc) with bef = ""; aft = ""} in
               sprintf "%s(if %s %s %s)%s" pc.bef (curr pc1 e1) (curr pc1 e2)
                 (curr pc1 e3) pc.aft)
            (fun () ->
               let s1 =
                 horiz_vertic
                   (fun () ->
                      sprintf "%s(if %s" pc.bef
                        (curr {(pc) with bef = ""; aft = ""} e1))
                    (fun () ->
                       let s1 = sprintf "%s(if" pc.bef in
                       let s2 =
                         curr
                           {(pc) with ind = pc.ind + 1;
                            bef = tab (pc.ind + 1); aft = ""} e1
                       in
                       sprintf "%s\n%s" s1 s2)
               in
               let s2 =
                 curr
                   {(pc) with ind = pc.ind + 1; bef = tab (pc.ind + 1);
                    aft = ""}
                   e2
               in
               let s3 =
                 curr
                   {(pc) with ind = pc.ind + 1; bef = tab (pc.ind + 1);
                    aft = sprintf ")%s" pc.aft}
                   e3
               in
               sprintf "%s\n%s\n%s" s1 s2 s3) 
     | <:expr< do { $list:el$ } >> ->
          horiz_vertic
            (fun () ->
               sprintf "%s(begin %s)%s" pc.bef
                 (hlist curr {(pc) with bef = ""; aft = ""} el) pc.aft)
            (fun () ->
               let s1 = sprintf "%s(begin" pc.bef in
               let s2 =
                 vlist curr
                   {(pc) with ind = pc.ind + 1; bef = tab (pc.ind + 1);
                    aft = sprintf ")%s" pc.aft}
                   el
               in
               sprintf "%s\n%s" s1 s2)
      | <:expr< for $lid:i$ = $e1$ $to:tf$ $e2$ do { $list:el$ } >> ->
          let b = if tf then "for" else "fordown" in
          plistbf 0
            {(pc) with ind = pc.ind + 1; bef = sprintf "%s(%s" pc.bef b;
             aft = sprintf ")%s" pc.aft}
            [(fun pc -> sprintf "%s%s%s" pc.bef i pc.aft, "");
             (fun pc -> curr pc e1, ""); (fun pc -> curr pc e2, "");
             (fun pc -> plist curr 0 pc (List.map (fun e -> (e, "")) el), "")]
      | <:expr< while $e$ do { $list:el$ } >> ->
          plistbf 0
            {(pc) with ind = pc.ind + 1; bef = sprintf "%s(while" pc.bef;
             aft = sprintf ")%s" pc.aft}
            [(fun pc -> curr pc e, "");
             (fun pc -> plist curr 0 pc (List.map (fun e -> (e, "")) el), "")]
      | <:expr< ($e$ : $t$) >> ->
          plistbf 0
            {(pc) with ind = pc.ind + 1; bef = sprintf "%s(:" pc.bef;
             aft = sprintf ")%s" pc.aft}
            [(fun pc -> curr pc e, ""); (fun pc -> ctyp pc t, "")]
      | <:expr< ($list:el$) >> ->
          let el = List.map (fun e -> (e, "")) el in
          plistb curr 1
            {(pc) with bef = sprintf "%s(values" pc.bef;
             aft = sprintf ")%s" pc.aft}
            el
      | <:expr< { $list:fel$ } >> ->
          let record_binding pc (p, e) =
            plistf 0
              {(pc) with ind = pc.ind + 1; bef = sprintf "%s(" pc.bef;
               aft = sprintf ")%s" pc.aft}
              [(fun pc -> patt pc p, ""); (fun pc -> curr pc e, "")]
          in
          plist record_binding 0
            {(pc) with ind = pc.ind + 1; bef = sprintf "%s{" pc.bef;
             aft = sprintf "}%s" pc.aft}
            (List.map (fun fe -> (fe, "")) fel)
      | <:expr< { ($e$) with $list:fel$ } >> ->
          let record_binding pc (p, e) =
            plistf 0
              {(pc) with ind = pc.ind + 1; bef = sprintf "%s(" pc.bef;
               aft = sprintf ")%s" pc.aft}
              [(fun pc -> patt pc p, ""); (fun pc -> curr pc e, "")]
          in
          plistbf 0
            {(pc) with ind = pc.ind + 1; bef = sprintf "%s{with" pc.bef;
             aft = sprintf "}%s" pc.aft}
            [(fun pc -> curr pc e, "") ::
             List.map (fun fe -> (fun pc -> record_binding pc fe, "")) fel]
      | <:expr< $e1$ := $e2$ >> ->
          plistb curr 1
            {(pc) with bef = sprintf "%s(:=" pc.bef;
             aft = sprintf ")%s" pc.aft}
            [(e1, ""); (e2, "")]
      | <:expr< [$_$ :: $_$] >> as e ->
          let (el, c) =
            make_list e where rec make_list e =
              match e with
              [ <:expr< [$e$ :: $y$] >> ->
                  let (el, c) = make_list y in
                  ([e :: el], c)
              | <:expr< [] >> -> ([], None)
              | x -> ([], Some e) ]
          in
          let pc =
            {(pc) with ind = pc.ind + 1; bef = sprintf "%s[" pc.bef;
             aft = sprintf "]%s" pc.aft}
          in
          match c with
          [ None ->
              let el = List.map (fun e -> (e, "")) el in
              plist curr 0 pc el
          | Some x ->
              let dot_expr pc e =
                curr {(pc) with bef = sprintf "%s. " pc.bef} e
              in
              horiz_vertic
                (fun () -> hlistl curr dot_expr pc (el @ [x]))
                (fun () ->
                   let el =
                     List.rev_map (fun e -> (e, "")) [x :: List.rev el]
                   in
                   plistl curr dot_expr 0 pc el) ]
      | <:expr< [| $list:el$ |] >> ->
          plist curr 0
            {(pc) with ind = pc.ind + 2; bef = sprintf "%s#(" pc.bef;
             aft = sprintf ")%s" pc.aft}
            (List.map (fun e -> (e, "")) el)
      | <:expr< assert $x$ >> ->
          plistf 0
            {(pc) with ind = pc.ind + 1; bef = sprintf "%s(" pc.bef;
             aft = sprintf ")%s" pc.aft}
            [(fun pc -> sprintf "%sassert%s" pc.bef pc.aft, "");
             (fun pc -> curr pc x, "")]
      | <:expr< lazy $x$ >> ->
          plistf 0
            {(pc) with ind = pc.ind + 1; bef = sprintf "%s(" pc.bef;
             aft = sprintf ")%s" pc.aft}
            [(fun pc -> sprintf "%slazy%s" pc.bef pc.aft, "");
             (fun pc -> curr pc x, "")]
(*
      | <:expr< $lid:s$ $e1$ $e2$ >>
        when List.mem s assoc_right_parsed_op_list ->
          fun ppf curr next dg k ->
            let el =
              loop [e1] e2 where rec loop el =
                fun
                [ <:expr< $lid:s1$ $e1$ $e2$ >> when s1 = s ->
                    loop [e1 :: el] e2
                | e -> List.rev [e :: el] ]
            in
            fprintf ppf "(@[%s %a@]" s (list expr) (el, ks ")" k)
*)
      | <:expr< $e1$ $e2$ >> ->
          let el =
            loop [e2] e1 where rec loop el =
              fun
              [ <:expr< $e1$ $e2$ >> -> loop [e2 :: el] e1
              | e1 -> [e1 :: el] ]
          in
          let el = List.map (fun e -> (e, "")) el in
          plist curr 0
            {(pc) with ind = pc.ind + 1; bef = sprintf "%s(" pc.bef;
             aft = sprintf ")%s" pc.aft}
            el
(*
      | <:expr< ~$s$: ($e$) >> ->
          fun ppf curr next dg k ->
            fprintf ppf "(~%s@ %a" s expr (e, ks ")" k)
*)
      | <:expr< $e1$ .[ $e2$ ] >> ->
          sprintf "%s%s.[%s]%s" pc.bef
            (curr {(pc) with bef = ""; aft = ""} e1)
            (curr {(pc) with bef = ""; aft = ""} e2) pc.aft
      | <:expr< $e1$ .( $e2$ ) >> ->
          sprintf "%s%s.(%s)%s" pc.bef
            (curr {(pc) with bef = ""; aft = ""} e1)
            (curr {(pc) with bef = ""; aft = ""} e2) pc.aft
      | <:expr< $e1$ . $e2$ >> ->
           sprintf "%s.%s"
             (curr {(pc) with aft = ""} e1)
             (curr {(pc) with bef = ""} e2)
      | <:expr< $int:s$ >> ->
          sprintf "%s%s%s" pc.bef (int_repr s) pc.aft
      | <:expr< $flo:s$ >> ->
          sprintf "%s%s%s" pc.bef s pc.aft
      | <:expr< $lid:s$ >> ->
          let s =
            match s with
            [ "~-" -> "-"
            | s -> s ]
          in
          sprintf "%s%s%s" pc.bef s pc.aft
      | <:expr< $uid:s$ >> ->
          sprintf "%s%s%s" pc.bef s pc.aft
(*
      | <:expr< ` $s$ >> ->
          fun ppf curr next dg k -> fprintf ppf "`%s%t" s k
*)
      | <:expr< $str:s$ >> ->
          sprintf "%s\"%s\"%s" pc.bef s pc.aft
      | <:expr< $chr:s$ >> ->
          sprintf "%s'%s'%s" pc.bef s pc.aft
      | x ->
          not_impl "expr" pc x ] ]
  ;
  pr_patt:
    [ "top"
      [ <:patt< $p1$ | $p2$ >> ->
          let pl =
            loop [p2] p1 where rec loop pl =
              fun
              [ <:patt< $p1$ | $p2$ >> -> loop [p2 :: pl] p1
              | p1 -> [p1 :: pl] ]
          in
          let pl = List.map (fun p -> (p, "")) pl in
          plistb curr 1
            {(pc) with bef = sprintf "%s(or" pc.bef;
             aft = sprintf ")%s" pc.aft}
            pl
      | <:patt< ($p1$ as $p2$) >> ->
          plistb curr 0
            {(pc) with ind = pc.ind + 1; bef = sprintf "%s(as" pc.bef;
             aft = sprintf ")%s" pc.aft}
            [(p1, ""); (p2, "")]
      | <:patt< $p1$ .. $p2$ >> ->
          plistb curr 0
            {(pc) with ind = pc.ind + 1; bef = sprintf "%s(range" pc.bef;
             aft = sprintf ")%s" pc.aft}
            [(p1, ""); (p2, "")]
      | <:patt< [$_$ :: $_$] >> as p ->
          let (pl, c) =
            make_list p where rec make_list p =
              match p with
              [ <:patt< [$p$ :: $y$] >> ->
                  let (pl, c) = make_list y in
                  ([p :: pl], c)
              | <:patt< [] >> -> ([], None)
              | x -> ([], Some p) ]
          in
          let pc =
            {(pc) with ind = pc.ind + 1; bef = sprintf "%s[" pc.bef;
             aft = sprintf "]%s" pc.aft}
          in
          match c with
          [ None ->
              let pl = List.map (fun p -> (p, "")) pl in
              plist curr 0 pc pl
          | Some x ->
              let dot_patt pc p =
                curr {(pc) with bef = sprintf "%s. " pc.bef} p
              in
              horiz_vertic
                (fun () -> hlistl curr dot_patt pc (pl @ [x]))
                (fun () ->
                   let pl =
                     List.rev_map (fun p -> (p, "")) [x :: List.rev pl]
                   in
                   plistl curr dot_patt 0 pc pl) ]
      | <:patt< $p1$ $p2$ >> ->
          let pl =
            loop [p2] p1 where rec loop pl =
              fun
              [ <:patt< $p1$ $p2$ >> -> loop [p2 :: pl] p1
              | p1 -> [p1 :: pl] ]
          in
          let pl = List.map (fun p -> (p, "")) pl in
          plist curr 1
            {(pc) with ind = pc.ind + 1; bef = sprintf "%s(" pc.bef;
             aft = sprintf ")%s" pc.aft}
            pl
      | <:patt< ($p$ : $t$) >> ->
          plistbf 0
            {(pc) with ind = pc.ind + 1; bef = sprintf "%s(:" pc.bef;
             aft = sprintf ")%s" pc.aft}
            [(fun pc -> curr pc p, ""); (fun pc -> ctyp pc t, "")]
      | <:patt< ($list:pl$) >> ->
          let pl = List.map (fun p -> (p, "")) pl in
          plistb curr 1
            {(pc) with bef = sprintf "%s(values" pc.bef;
             aft = sprintf ")%s" pc.aft}
            pl
      | <:patt< { $list:fpl$ } >> ->
          let record_binding pc (p1, p2) =
            horiz_vertic
              (fun () ->
                 sprintf "%s(%s %s)%s" pc.bef
                   (curr {(pc) with bef = ""; aft = ""} p1)
                   (curr {(pc) with bef = ""; aft = ""} p2) pc.aft)
              (fun () -> not_impl "record_binding vertic" pc 0)
          in
          let fpl = List.map (fun fp -> (fp, "")) fpl in
          plist record_binding 0
            {(pc) with ind = pc.ind + 1; bef = sprintf "%s{" pc.bef;
             aft = sprintf "}%s" pc.aft}
            fpl
(*
      | <:patt< ?$x$ >> ->
          fun ppf curr next dg k -> fprintf ppf "?%s%t" x k
      |  <:patt< ? ($lid:x$ = $e$) >> ->
          fun ppf curr next dg k ->
            fprintf ppf "(?%s@ %a" x expr (e, ks ")" k)
*)
      | <:patt< $p1$ . $p2$ >> ->
           sprintf "%s.%s"
             (curr {(pc) with aft = ""} p1)
             (curr {(pc) with bef = ""} p2)
      | <:patt< $lid:s$ >> | <:patt< $uid:s$ >> ->
          sprintf "%s%s%s" pc.bef s pc.aft
      | <:patt< $str:s$ >> ->
          sprintf "%s\"%s\"%s" pc.bef s pc.aft
      | <:patt< $chr:s$ >> ->
          sprintf "%s'%s'%s" pc.bef s pc.aft
      | <:patt< $int:s$ >> ->
          sprintf "%s%s%s" pc.bef (int_repr s) pc.aft
(*
      | <:patt< $flo:s$ >> ->
          fun ppf curr next dg k -> fprintf ppf "%s%t" s k
*)
      | <:patt< _ >> ->
          sprintf "%s_%s" pc.bef pc.aft
      | x ->
          not_impl "patt" pc x ] ]
  ;
  pr_str_item:
    [ "top"
      [ <:str_item< open $i$ >> ->
          plistb mod_ident 0
            {(pc) with ind = pc.ind + 1; bef = sprintf "%s(open" pc.bef;
             aft = sprintf ")%s" pc.aft}
            [(i, "")]
      | <:str_item< type $list:tdl$ >> ->
          type_decl_list pc tdl
      | <:str_item< exception $uid:c$ of $list:tl$ >> ->
          exception_decl pc (c, tl)
      | <:str_item< exception $uid:c$ of $list:_$ = $id$ >> ->
          plistbf 0
            {(pc) with ind = pc.ind + 1;
             bef = sprintf "%s(exceptionrebind" pc.bef;
             aft = sprintf ")%s" pc.aft}
            [(fun pc -> sprintf "%s%s%s" pc.bef c pc.aft, "");
             (fun pc -> cons_ident pc id, "")]
      | <:str_item< value $flag:rf$ $list:pel$ >> ->
          value_binding_list pc (rf, pel)
      | <:str_item< module $uid:s$ = $me$ >> ->
          plistbf 0
            {(pc) with ind = pc.ind + 1; bef = sprintf "%s(module" pc.bef;
             aft = sprintf ")%s" pc.aft}
            [(fun pc -> sprintf "%s%s%s" pc.bef s pc.aft, "");
             (fun pc -> module_expr pc me, "")]
      | <:str_item< module type $uid:s$ = $mt$ >> ->
          module_type_decl pc (s, mt)
      | <:str_item< external $lid:i$ : $t$ = $list:pd$ >> ->
          plistbf 0
            {(pc) with ind = pc.ind + 1; bef = sprintf "%s(external" pc.bef;
             aft = sprintf ")%s" pc.aft}
            [(fun pc -> sprintf "%s%s%s" pc.bef i pc.aft, "");
             (fun pc -> ctyp pc t, "") ::
             List.map (fun s -> (fun pc -> string pc s, "")) pd]
      | <:str_item< $exp:e$ >> ->
          expr pc e
      | <:str_item< # $lid:s$ $opt:x$ >> ->
          plistbf 0
            {(pc) with ind = pc.ind + 1; bef = sprintf "%s(#" pc.bef;
             aft = sprintf ")%s" pc.aft}
            [(fun pc -> sprintf "%s%s%s" pc.bef s pc.aft, "") ::
             match x with
             [ Some e -> [(fun pc -> expr pc e, "")]
             | None -> [] ]]
      | <:str_item< declare $list:sil$ end >> ->
          if sil = [] then sprintf "%s%s" pc.bef pc.aft
          else vlist str_item pc sil
(*
      | MLast.StUse _ _ _ ->
          fun ppf curr next dg k -> ()
*)
      | x ->
          not_impl "str_item" pc x ] ]
  ;
  pr_sig_item:
    [ "top"
      [ <:sig_item< open $i$ >> ->
          plistb mod_ident 0
            {(pc) with ind = pc.ind + 1; bef = sprintf "%s(open" pc.bef;
             aft = sprintf ")%s" pc.aft}
            [(i, "")]
      | <:sig_item< type $list:tdl$ >> ->
          type_decl_list pc tdl
      | <:sig_item< exception $uid:c$ of $list:tl$ >> ->
          exception_decl pc (c, tl)
      | <:sig_item< value $lid:i$ : $t$ >> ->
          plistbf 0
            {(pc) with ind = pc.ind + 1; bef = sprintf "%s(value" pc.bef;
             aft = sprintf ")%s" pc.aft}
            [(fun pc -> sprintf "%s%s%s" pc.bef i pc.aft, "");
             (fun pc -> ctyp pc t, "")]
      | <:sig_item< external $lid:i$ : $t$ = $list:pd$ >> ->
          plistbf 0
            {(pc) with ind = pc.ind + 1; bef = sprintf "%s(external" pc.bef;
             aft = sprintf ")%s" pc.aft}
            [(fun pc -> sprintf "%s%s%s" pc.bef i pc.aft, "");
             (fun pc -> ctyp pc t, "") ::
             List.map (fun s -> (fun pc -> string pc s, "")) pd]
      | <:sig_item< module $uid:s$ : $mt$ >> ->
          plistbf 0
            {(pc) with ind = pc.ind + 1; bef = sprintf "%s(module" pc.bef;
             aft = sprintf ")%s" pc.aft}
            [(fun pc -> sprintf "%s%s%s" pc.bef s pc.aft, "");
             (fun pc -> module_type pc mt, "")]
      | <:sig_item< module type $uid:s$ = $mt$ >> ->
          module_type_decl pc (s, mt)
      | <:sig_item< declare $list:sil$ end >> ->
          if sil = [] then sprintf "%s%s" pc.bef pc.aft
          else vlist sig_item pc sil
(*
      | MLast.SgUse _ _ _ ->
          fun ppf curr next dg k -> ()
*)
      | x ->
          not_impl "sig_item" pc x ] ]
  ;
  pr_module_expr:
    [ "top"
      [ <:module_expr< functor ($uid:i$ : $mt$) -> $me$ >> ->
          plistbf 0
            {(pc) with ind = pc.ind + 1; bef = sprintf "%s(functor" pc.bef;
             aft = sprintf ")%s" pc.aft}
            [(fun pc -> sprintf "%s%s%s" pc.bef i pc.aft, "");
             (fun pc -> module_type pc mt, "");
             (fun pc -> module_expr pc me, "")]
      | <:module_expr< struct $list:sil$ end >> ->
          horiz_vertic
            (fun () ->
               sprintf "%s(struct %s)%s" pc.bef
                 (hlist str_item {(pc) with bef = ""; aft = ""} sil) pc.aft)
            (fun () ->
               let s1 = sprintf "%s(struct" pc.bef in
               let s2 =
                 vlist str_item
                   {(pc) with ind = pc.ind + 1; bef = tab (pc.ind + 1);
                    aft = sprintf ")%s" pc.aft}
                   sil
               in
               sprintf "%s\n%s" s1 s2)
      | <:module_expr< $me1$ $me2$ >> ->
          plist curr 0
            {(pc) with ind = pc.ind + 1; bef = sprintf "%s(" pc.bef;
             aft = sprintf ")%s" pc.aft}
            [(me1, ""); (me2, "")]
      | <:module_expr< ($me$ : $mt$) >> ->
          plistbf 0
            {(pc) with ind = pc.ind + 1; bef = sprintf "%s(:" pc.bef;
             aft = sprintf ")%s" pc.aft}
            [(fun pc -> curr pc me, ""); (fun pc -> module_type pc mt, "")]
      | <:module_expr< $me1$ . $me2$ >> ->
           sprintf "%s.%s"
             (curr {(pc) with aft = ""} me1)
             (curr {(pc) with bef = ""} me2)
      | <:module_expr< $uid:s$ >> ->
          sprintf "%s%s%s" pc.bef s pc.aft
      | x ->
          not_impl "module_expr" pc x ] ]
  ;
  pr_module_type:
    [ "top"
      [ <:module_type< functor ($uid:i$ : $mt1$) -> $mt2$ >> ->
          plistbf 0
            {(pc) with ind = pc.ind + 1; bef = sprintf "%s(functor" pc.bef;
             aft = sprintf ")%s" pc.aft}
            [(fun pc -> sprintf "%s%s%s" pc.bef i pc.aft, "");
             (fun pc -> curr pc mt1, "");
             (fun pc -> curr pc mt2, "")]
      | <:module_type< sig $list:sil$ end >> ->
          horiz_vertic
            (fun () ->
               sprintf "%s(sig %s)%s" pc.bef
                 (hlist sig_item {(pc) with bef = ""; aft = ""} sil) pc.aft)
            (fun () ->
               let s1 = sprintf "%s(sig" pc.bef in
               let s2 =
                 vlist sig_item
                   {(pc) with ind = pc.ind + 1; bef = tab (pc.ind + 1);
                    aft = sprintf ")%s" pc.aft}
                   sil
               in
               sprintf "%s\n%s" s1 s2)
      | <:module_type< $mt$ with $list:wcl$ >> ->
          horiz_vertic
            (fun () ->
               sprintf "%s(with %s %s)%s" pc.bef
                 (curr {(pc) with bef = ""; aft = ""} mt)
                 (hlist with_constraint {(pc) with bef = ""; aft = ""} wcl)
                 pc.aft)
            (fun () -> not_impl "module_type with vertic" pc 0)
      | <:module_type< $me1$ . $me2$ >> ->
           sprintf "%s.%s"
             (curr {(pc) with aft = ""} me1)
             (curr {(pc) with bef = ""} me2)
      | <:module_type< $uid:s$ >> ->
          sprintf "%s%s%s" pc.bef s pc.aft
      | x ->
          not_impl "module_type" pc x ] ]
  ;
END;

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
    | None -> stdout ]
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
           output_string oc (f {ind = 0; bef = ""; aft = ""; dang = ""} si);
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

Pcaml.add_option "-l" (Arg.Int (fun x -> Pretty.line_length.val := x))
  ("<length> Maximum line length for pretty printing (default " ^
     string_of_int Pretty.line_length.val ^ ")");

Pcaml.add_option "-sep_src" (Arg.Unit (fun () -> sep.val := None))
  "Read source file for text between phrases (default).";

Pcaml.add_option "-sep" (Arg.String (fun x -> sep.val := Some x))
  "<string> Use this string between phrases instead of reading source.";
