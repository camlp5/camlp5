(* camlp5r *)
(* q_MLast.ml,v *)
(* Copyright (c) INRIA 2007-2017 *)

(* #load "pa_extend.cmo" *)
(* #load "pa_extend_m.cmo" *)
(* #load "q_MLast.cmo" *)
(* #load "pa_macro.cmo" *)

(* *)

let gram = Grammar.gcreate (Plexer.gmake ());;

let antiquot k loc s f =
  let shift_bp =
    if k = "" then String.length "$"
    else String.length "$" + String.length k + String.length ":"
  in
  let shift_ep = String.length "$" in
  let loc =
    Ploc.make_loc (Ploc.file_name loc) (Ploc.line_nb loc) (Ploc.bol_pos loc)
      (Ploc.first_pos loc + shift_bp, Ploc.last_pos loc - shift_ep) ""
  in
  try loc, Grammar.Entry.parse f (Stream.of_string s) with
    Ploc.Exc (loc1, exc) ->
      let shift = Ploc.first_pos loc in
      let loc =
        Ploc.make_loc (Ploc.file_name loc)
          (Ploc.line_nb loc + Ploc.line_nb loc1 - 1)
          (if Ploc.line_nb loc1 = 1 then Ploc.bol_pos loc
           else shift + Ploc.bol_pos loc1)
          (shift + Ploc.first_pos loc1, shift + Ploc.last_pos loc1) ""
      in
      raise (Ploc.Exc (loc, exc))
;;

module Qast =
  struct
    type t =
        Node of string * t list
      | List of t list
      | Tuple of t list
      | Option of t option
      | Int of string
      | Str of string
      | Bool of bool
      | Cons of t * t
      | Apply of string * t list
      | Record of (string * t) list
      | Loc
      | TrueLoc
      | VaAnt of string * MLast.loc * string
      | VaVal of t
    ;;
    let loc = Ploc.dummy;;
    let expr_node m n =
      if m = "" then MLast.ExUid (loc, n)
      else MLast.ExAcc (loc, MLast.ExUid (loc, m), MLast.ExUid (loc, n))
    ;;
    let patt_node m n =
      if m = "" then MLast.PaUid (loc, n)
      else MLast.PaAcc (loc, MLast.PaUid (loc, m), MLast.PaUid (loc, n))
    ;;
    let patt_label m n =
      if m = "" then MLast.PaLid (loc, n)
      else MLast.PaAcc (loc, MLast.PaUid (loc, m), MLast.PaLid (loc, n))
    ;;
    let rec to_expr m =
      function
        Node (n, al) ->
          List.fold_left (fun e a -> MLast.ExApp (loc, e, to_expr m a))
            (expr_node m n) al
      | List al ->
          List.fold_right
            (fun a e ->
               MLast.ExApp
                 (loc,
                  MLast.ExApp (loc, MLast.ExUid (loc, "::"), to_expr m a), e))
            al (MLast.ExUid (loc, "[]"))
      | Tuple al -> MLast.ExTup (loc, List.map (to_expr m) al)
      | Option None -> MLast.ExUid (loc, "None")
      | Option (Some a) ->
          MLast.ExApp (loc, MLast.ExUid (loc, "Some"), to_expr m a)
      | Int s -> MLast.ExInt (loc, s, "")
      | Str s -> MLast.ExStr (loc, s)
      | Bool true -> MLast.ExUid (loc, "True")
      | Bool false -> MLast.ExUid (loc, "False")
      | Cons (a1, a2) ->
          MLast.ExApp
            (loc, MLast.ExApp (loc, MLast.ExUid (loc, "::"), to_expr m a1),
             to_expr m a2)
      | Apply (f, al) ->
          List.fold_left (fun e a -> MLast.ExApp (loc, e, to_expr m a))
            (MLast.ExLid (loc, f)) al
      | Record lal -> MLast.ExRec (loc, List.map (to_expr_label m) lal, None)
      | Loc | TrueLoc -> MLast.ExLid (loc, !(Ploc.name))
      | VaAnt (k, loc, x) ->
          let (loc, e) = antiquot k loc x Pcaml.expr_eoi in
          MLast.ExAnt (loc, e)
      | VaVal a ->
          let e = to_expr m a in
          if !(Pcaml.strict_mode) then
            match e with
              MLast.ExAnt (_, ee) ->
                let loc = MLast.loc_of_expr ee in
                let ee =
                  MLast.ExApp
                    (loc,
                     MLast.ExAcc
                       (loc, MLast.ExUid (loc, "Ploc"),
                        MLast.ExUid (loc, "VaVal")),
                     ee)
                in
                let loc = MLast.loc_of_expr e in MLast.ExAnt (loc, ee)
            | _ ->
                MLast.ExApp
                  (loc,
                   MLast.ExAcc
                     (loc, MLast.ExUid (loc, "Ploc"),
                      MLast.ExUid (loc, "VaVal")),
                   e)
          else e
    and to_expr_label m (l, e) = patt_label m l, to_expr m e;;
    let rec to_patt m =
      function
        Node (n, al) ->
          List.fold_left (fun e a -> MLast.PaApp (loc, e, to_patt m a))
            (patt_node m n) al
      | List al ->
          List.fold_right
            (fun a p ->
               MLast.PaApp
                 (loc,
                  MLast.PaApp (loc, MLast.PaUid (loc, "::"), to_patt m a), p))
            al (MLast.PaUid (loc, "[]"))
      | Tuple al -> MLast.PaTup (loc, List.map (to_patt m) al)
      | Option None -> MLast.PaUid (loc, "None")
      | Option (Some a) ->
          MLast.PaApp (loc, MLast.PaUid (loc, "Some"), to_patt m a)
      | Int s -> MLast.PaInt (loc, s, "")
      | Str s -> MLast.PaStr (loc, s)
      | Bool true -> MLast.PaUid (loc, "True")
      | Bool false -> MLast.PaUid (loc, "False")
      | Cons (a1, a2) ->
          MLast.PaApp
            (loc, MLast.PaApp (loc, MLast.PaUid (loc, "::"), to_patt m a1),
             to_patt m a2)
      | Apply (_, _) -> failwith "bad pattern"
      | Record lal -> MLast.PaRec (loc, List.map (to_patt_label m) lal)
      | Loc -> MLast.PaAny loc
      | TrueLoc -> MLast.PaLid (loc, !(Ploc.name))
      | VaAnt (k, loc, x) ->
          let (loc, e) = antiquot k loc x Pcaml.patt_eoi in
          MLast.PaAnt (loc, e)
      | VaVal a ->
          let p = to_patt m a in
          if !(Pcaml.strict_mode) then
            match p with
              MLast.PaAnt (_, pp) ->
                let loc = MLast.loc_of_patt pp in
                let pp =
                  MLast.PaApp
                    (loc,
                     MLast.PaAcc
                       (loc, MLast.PaUid (loc, "Ploc"),
                        MLast.PaUid (loc, "VaVal")),
                     pp)
                in
                let loc = MLast.loc_of_patt p in MLast.PaAnt (loc, pp)
            | _ ->
                MLast.PaApp
                  (loc,
                   MLast.PaAcc
                     (loc, MLast.PaUid (loc, "Ploc"),
                      MLast.PaUid (loc, "VaVal")),
                   p)
          else p
    and to_patt_label m (l, a) = patt_label m l, to_patt m a;;
  end
;;

let sig_item = Grammar.Entry.create gram "sig_item";;
let str_item = Grammar.Entry.create gram "str_item";;
let ctyp = Grammar.Entry.create gram "type";;
let patt = Grammar.Entry.create gram "patt";;
let expr = Grammar.Entry.create gram "expr";;

let functor_parameter = Grammar.Entry.create gram "functor_parameter";;
let module_type = Grammar.Entry.create gram "module_type";;
let module_expr = Grammar.Entry.create gram "module_expr";;

let structure = Grammar.Entry.create gram "structure";;
let signature = Grammar.Entry.create gram "signature";;

let class_type = Grammar.Entry.create gram "class_type";;
let class_expr = Grammar.Entry.create gram "class_expr";;
let class_sig_item = Grammar.Entry.create gram "class_sig_item";;
let class_str_item = Grammar.Entry.create gram "class_str_item";;

let ipatt = Grammar.Entry.create gram "ipatt";;
let let_binding = Grammar.Entry.create gram "let_binding";;
let type_decl = Grammar.Entry.create gram "type_decl";;
let match_case = Grammar.Entry.create gram "match_case";;
let constructor_declaration =
  Grammar.Entry.create gram "constructor_declaration"
;;
let label_declaration = Grammar.Entry.create gram "label_declaration";;

let with_constr = Grammar.Entry.create gram "with_constr";;
let poly_variant = Grammar.Entry.create gram "poly_variant";;
let attribute_body = Grammar.Entry.create gram "attribute_body";;

let mksequence2 _ =
  function
    Qast.VaVal (Qast.List [e]) -> e
  | el -> Qast.Node ("ExSeq", [Qast.Loc; el])
;;

let mksequence _ =
  function
    Qast.List [e] -> e
  | el -> Qast.Node ("ExSeq", [Qast.Loc; Qast.VaVal el])
;;

let mkmatchcase _ p aso w e =
  let p =
    match aso with
      Qast.Option (Some p2) -> Qast.Node ("PaAli", [Qast.Loc; p; p2])
    | Qast.Option None -> p
    | _ -> Qast.Node ("PaAli", [Qast.Loc; p; aso])
  in
  Qast.Tuple [p; w; e]
;;

let neg_string n =
  let x =
    let len = String.length n in
    if len > 0 && n.[0] = '-' then String.sub n 1 (len - 1) else "-" ^ n
  in
  Qast.Str x
;;

let mklistexp _ last =
  let rec loop top =
    function
      [] ->
        begin match last with
          Qast.Option (Some e) -> e
        | Qast.Option None ->
            Qast.Node ("ExUid", [Qast.Loc; Qast.VaVal (Qast.Str "[]")])
        | a -> a
        end
    | e1 :: el ->
        Qast.Node
          ("ExApp",
           [Qast.Loc;
            Qast.Node
              ("ExApp",
               [Qast.Loc;
                Qast.Node ("ExUid", [Qast.Loc; Qast.VaVal (Qast.Str "::")]);
                e1]);
            loop false el])
  in
  loop true
;;

let mklistpat _ last =
  let rec loop top =
    function
      [] ->
        begin match last with
          Qast.Option (Some p) -> p
        | Qast.Option None ->
            Qast.Node ("PaUid", [Qast.Loc; Qast.VaVal (Qast.Str "[]")])
        | a -> a
        end
    | p1 :: pl ->
        Qast.Node
          ("PaApp",
           [Qast.Loc;
            Qast.Node
              ("PaApp",
               [Qast.Loc;
                Qast.Node ("PaUid", [Qast.Loc; Qast.VaVal (Qast.Str "::")]);
                p1]);
            loop false pl])
  in
  loop true
;;

let mktupexp _ e el =
  Qast.Node ("ExTup", [Qast.Loc; Qast.VaVal (Qast.Cons (e, Qast.List el))])
;;

let mktuppat _ p pl =
  Qast.Node ("PaTup", [Qast.Loc; Qast.VaVal (Qast.Cons (p, Qast.List pl))])
;;

let mktuptyp _ t tl =
  Qast.Node ("TyTup", [Qast.Loc; Qast.VaVal (Qast.Cons (t, Qast.List tl))])
;;

let mklabdecl _ i mf t attrs =
  Qast.Tuple [Qast.Loc; Qast.Str i; Qast.Bool mf; t; attrs]
;;
let mkident i = Qast.Str i;;

let generalized_type_of_type t =
  let rec gen =
    function
      Qast.Node ("TyArr", [_; t1; t2]) ->
        let (tl, rt) = gen t2 in t1 :: tl, rt
    | t -> [], t
  in
  let (tl, rt) = gen t in Qast.List tl, rt
;;

let greek_ascii_equiv s = Qast.Str (Pcaml.greek_ascii_equiv s);;

let warned = ref false;;
let warning_deprecated_since_6_00 loc =
  if not !warned then
    begin
      !(Pcaml.warning) loc "syntax deprecated since version 6.00";
      warned := true
    end
;;

(* -- begin copy from pa_r to q_MLast -- *)

Grammar.safe_extend
  (let _ = (sig_item : 'sig_item Grammar.Entry.e)
   and _ = (str_item : 'str_item Grammar.Entry.e)
   and _ = (ctyp : 'ctyp Grammar.Entry.e)
   and _ = (patt : 'patt Grammar.Entry.e)
   and _ = (expr : 'expr Grammar.Entry.e)
   and _ = (functor_parameter : 'functor_parameter Grammar.Entry.e)
   and _ = (module_type : 'module_type Grammar.Entry.e)
   and _ = (module_expr : 'module_expr Grammar.Entry.e)
   and _ = (signature : 'signature Grammar.Entry.e)
   and _ = (structure : 'structure Grammar.Entry.e)
   and _ = (class_type : 'class_type Grammar.Entry.e)
   and _ = (class_expr : 'class_expr Grammar.Entry.e)
   and _ = (class_sig_item : 'class_sig_item Grammar.Entry.e)
   and _ = (class_str_item : 'class_str_item Grammar.Entry.e)
   and _ = (let_binding : 'let_binding Grammar.Entry.e)
   and _ = (type_decl : 'type_decl Grammar.Entry.e)
   and _ =
     (constructor_declaration : 'constructor_declaration Grammar.Entry.e)
   and _ = (label_declaration : 'label_declaration Grammar.Entry.e)
   and _ = (match_case : 'match_case Grammar.Entry.e)
   and _ = (ipatt : 'ipatt Grammar.Entry.e)
   and _ = (with_constr : 'with_constr Grammar.Entry.e)
   and _ = (poly_variant : 'poly_variant Grammar.Entry.e)
   and _ = (attribute_body : 'attribute_body Grammar.Entry.e) in
   let grammar_entry_create s =
     Grammar.create_local_entry (Grammar.of_entry sig_item) s
   in
   let attribute_id : 'attribute_id Grammar.Entry.e =
     grammar_entry_create "attribute_id"
   and attribute_structure : 'attribute_structure Grammar.Entry.e =
     grammar_entry_create "attribute_structure"
   and attribute_signature : 'attribute_signature Grammar.Entry.e =
     grammar_entry_create "attribute_signature"
   and rebind_exn : 'rebind_exn Grammar.Entry.e =
     grammar_entry_create "rebind_exn"
   and mod_binding : 'mod_binding Grammar.Entry.e =
     grammar_entry_create "mod_binding"
   and mod_fun_binding : 'mod_fun_binding Grammar.Entry.e =
     grammar_entry_create "mod_fun_binding"
   and mod_decl_binding : 'mod_decl_binding Grammar.Entry.e =
     grammar_entry_create "mod_decl_binding"
   and module_declaration : 'module_declaration Grammar.Entry.e =
     grammar_entry_create "module_declaration"
   and uidopt : 'uidopt Grammar.Entry.e = grammar_entry_create "uidopt"
   and closed_case_list : 'closed_case_list Grammar.Entry.e =
     grammar_entry_create "closed_case_list"
   and cons_expr_opt : 'cons_expr_opt Grammar.Entry.e =
     grammar_entry_create "cons_expr_opt"
   and dummy : 'dummy Grammar.Entry.e = grammar_entry_create "dummy"
   and sequence : 'sequence Grammar.Entry.e = grammar_entry_create "sequence"
   and fun_binding : 'fun_binding Grammar.Entry.e =
     grammar_entry_create "fun_binding"
   and as_patt_opt : 'as_patt_opt Grammar.Entry.e =
     grammar_entry_create "as_patt_opt"
   and when_expr : 'when_expr Grammar.Entry.e =
     grammar_entry_create "when_expr"
   and label_expr : 'label_expr Grammar.Entry.e =
     grammar_entry_create "label_expr"
   and fun_def : 'fun_def Grammar.Entry.e = grammar_entry_create "fun_def"
   and paren_patt : 'paren_patt Grammar.Entry.e =
     grammar_entry_create "paren_patt"
   and cons_patt_opt : 'cons_patt_opt Grammar.Entry.e =
     grammar_entry_create "cons_patt_opt"
   and label_patt : 'label_patt Grammar.Entry.e =
     grammar_entry_create "label_patt"
   and patt_label_ident : 'patt_label_ident Grammar.Entry.e =
     grammar_entry_create "patt_label_ident"
   and paren_ipatt : 'paren_ipatt Grammar.Entry.e =
     grammar_entry_create "paren_ipatt"
   and label_ipatt : 'label_ipatt Grammar.Entry.e =
     grammar_entry_create "label_ipatt"
   and item_attribute : 'item_attribute Grammar.Entry.e =
     grammar_entry_create "item_attribute"
   and alg_attribute : 'alg_attribute Grammar.Entry.e =
     grammar_entry_create "alg_attribute"
   and type_patt : 'type_patt Grammar.Entry.e =
     grammar_entry_create "type_patt"
   and constrain : 'constrain Grammar.Entry.e =
     grammar_entry_create "constrain"
   and type_parameter : 'type_parameter Grammar.Entry.e =
     grammar_entry_create "type_parameter"
   and simple_type_parameter : 'simple_type_parameter Grammar.Entry.e =
     grammar_entry_create "simple_type_parameter"
   and constructor_declaration_sans_alg_attrs : 'constructor_declaration_sans_alg_attrs Grammar.Entry.e =
     grammar_entry_create "constructor_declaration_sans_alg_attrs"
   and ident : 'ident Grammar.Entry.e = grammar_entry_create "ident"
   and mod_ident : 'mod_ident Grammar.Entry.e =
     grammar_entry_create "mod_ident"
   and direction_flag : 'direction_flag Grammar.Entry.e =
     grammar_entry_create "direction_flag"
   and typevar : 'typevar Grammar.Entry.e = grammar_entry_create "typevar"
   and class_declaration : 'class_declaration Grammar.Entry.e =
     grammar_entry_create "class_declaration"
   and class_fun_binding : 'class_fun_binding Grammar.Entry.e =
     grammar_entry_create "class_fun_binding"
   and class_type_parameters : 'class_type_parameters Grammar.Entry.e =
     grammar_entry_create "class_type_parameters"
   and class_fun_def : 'class_fun_def Grammar.Entry.e =
     grammar_entry_create "class_fun_def"
   and class_structure : 'class_structure Grammar.Entry.e =
     grammar_entry_create "class_structure"
   and class_self_patt : 'class_self_patt Grammar.Entry.e =
     grammar_entry_create "class_self_patt"
   and as_lident : 'as_lident Grammar.Entry.e =
     grammar_entry_create "as_lident"
   and polyt : 'polyt Grammar.Entry.e = grammar_entry_create "polyt"
   and cvalue_binding : 'cvalue_binding Grammar.Entry.e =
     grammar_entry_create "cvalue_binding"
   and lident : 'lident Grammar.Entry.e = grammar_entry_create "lident"
   and class_self_type : 'class_self_type Grammar.Entry.e =
     grammar_entry_create "class_self_type"
   and class_description : 'class_description Grammar.Entry.e =
     grammar_entry_create "class_description"
   and class_type_declaration : 'class_type_declaration Grammar.Entry.e =
     grammar_entry_create "class_type_declaration"
   and field_expr : 'field_expr Grammar.Entry.e =
     grammar_entry_create "field_expr"
   and field : 'field Grammar.Entry.e = grammar_entry_create "field"
   and class_longident : 'class_longident Grammar.Entry.e =
     grammar_entry_create "class_longident"
   and poly_variant_list : 'poly_variant_list Grammar.Entry.e =
     grammar_entry_create "poly_variant_list"
   and name_tag : 'name_tag Grammar.Entry.e = grammar_entry_create "name_tag"
   and patt_tcon_opt_eq_patt : 'patt_tcon_opt_eq_patt Grammar.Entry.e =
     grammar_entry_create "patt_tcon_opt_eq_patt"
   and patt_tcon : 'patt_tcon Grammar.Entry.e =
     grammar_entry_create "patt_tcon"
   and ipatt_tcon_opt_eq_patt : 'ipatt_tcon_opt_eq_patt Grammar.Entry.e =
     grammar_entry_create "ipatt_tcon_opt_eq_patt"
   and ipatt_tcon : 'ipatt_tcon Grammar.Entry.e =
     grammar_entry_create "ipatt_tcon"
   and patt_option_label : 'patt_option_label Grammar.Entry.e =
     grammar_entry_create "patt_option_label"
   and ipatt_tcon_fun_binding : 'ipatt_tcon_fun_binding Grammar.Entry.e =
     grammar_entry_create "ipatt_tcon_fun_binding"
   and joinautomaton : 'joinautomaton Grammar.Entry.e =
     grammar_entry_create "joinautomaton"
   and joinclause : 'joinclause Grammar.Entry.e =
     grammar_entry_create "joinclause"
   and joinpattern : 'joinpattern Grammar.Entry.e =
     grammar_entry_create "joinpattern"
   and joinident : 'joinident Grammar.Entry.e =
     grammar_entry_create "joinident"
   and a_ti : 'a_ti Grammar.Entry.e =
     (* -- end copy from pa_r to q_MLast -- *)
     grammar_entry_create "a_ti"
   and a_tic : 'a_tic Grammar.Entry.e = grammar_entry_create "a_tic"
   and a_qi : 'a_qi Grammar.Entry.e = grammar_entry_create "a_qi"
   and a_qic : 'a_qic Grammar.Entry.e = grammar_entry_create "a_qic" in
   [Grammar.extension (attribute_id : 'attribute_id Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_list1sep
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("UIDENT", "")),
                       (fun (i : string) (loc : Ploc.t) -> (i : 'e__1)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("LIDENT", "")),
                       (fun (i : string) (loc : Ploc.t) -> (i : 'e__1)))])
                (Grammar.s_token ("", ".")) false),
           (fun (l : 'e__1 list) (loc : Ploc.t) ->
              (Qast.VaVal (Qast.Str (String.concat "." l)) :
               'attribute_id)))]];
    Grammar.extension
      (attribute_structure : 'attribute_structure Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_list1
                            (Grammar.s_rules
                               [Grammar.production
                                  (Grammar.r_next
                                     (Grammar.r_next Grammar.r_stop
                                        (Grammar.s_nterm
                                           (str_item :
                                            'str_item Grammar.Entry.e)))
                                     (Grammar.s_token ("", ";")),
                                   (fun _ (s : 'str_item) (loc : Ploc.t) ->
                                      (s : 'e__2)))])),
                       (fun (a : 'e__2 list) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.List a) : 'e__3)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_structure")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_structure", loc, a) : 'e__3)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "structure")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("structure", loc, a)) :
                           'e__3)))])),
           (fun (st : 'e__3) (loc : Ploc.t) ->
              (st : 'attribute_structure)))]];
    Grammar.extension
      (attribute_signature : 'attribute_signature Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_list1
                            (Grammar.s_rules
                               [Grammar.production
                                  (Grammar.r_next
                                     (Grammar.r_next Grammar.r_stop
                                        (Grammar.s_nterm
                                           (sig_item :
                                            'sig_item Grammar.Entry.e)))
                                     (Grammar.s_token ("", ";")),
                                   (fun _ (s : 'sig_item) (loc : Ploc.t) ->
                                      (s : 'e__4)))])),
                       (fun (a : 'e__4 list) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.List a) : 'e__5)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_signature")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_signature", loc, a) : 'e__5)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "signature")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("signature", loc, a)) :
                           'e__5)))])),
           (fun (st : 'e__5) (loc : Ploc.t) ->
              (st : 'attribute_signature)))]];
    Grammar.extension (attribute_body : 'attribute_body Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_facto
                            (Grammar.s_rules
                               [Grammar.production
                                  (Grammar.r_next Grammar.r_stop
                                     (Grammar.s_nterm
                                        (attribute_id :
                                         'attribute_id Grammar.Entry.e)),
                                   (fun (a : 'attribute_id) (loc : Ploc.t) ->
                                      (Qast.VaVal a : 'e__13)));
                                Grammar.production
                                  (Grammar.r_next Grammar.r_stop
                                     (Grammar.s_token
                                        ("ANTIQUOT", "_attrid")),
                                   (fun (a : string) (loc : Ploc.t) ->
                                      (Qast.VaAnt ("_attrid", loc, a) :
                                       'e__13)));
                                Grammar.production
                                  (Grammar.r_next Grammar.r_stop
                                     (Grammar.s_token ("ANTIQUOT", "attrid")),
                                   (fun (a : string) (loc : Ploc.t) ->
                                      (Qast.VaVal
                                         (Qast.VaAnt ("attrid", loc, a)) :
                                       'e__13)))])))
                      (Grammar.s_token ("", "?")))
                   (Grammar.s_facto
                      (Grammar.s_rules
                         [Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_nterm
                                  (patt : 'patt Grammar.Entry.e)),
                             (fun (a : 'patt) (loc : Ploc.t) ->
                                (Qast.VaVal a : 'e__14)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "_patt")),
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaAnt ("_patt", loc, a) : 'e__14)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "patt")),
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaVal (Qast.VaAnt ("patt", loc, a)) :
                                 'e__14)))])))
                (Grammar.s_token ("", "when")))
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_nterm (expr : 'expr Grammar.Entry.e)),
                       (fun (a : 'expr) (loc : Ploc.t) ->
                          (Qast.VaVal a : 'e__15)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_expr")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_expr", loc, a) : 'e__15)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "expr")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("expr", loc, a)) :
                           'e__15)))])),
           (fun (e : 'e__15) _ (p : 'e__14) _ (id : 'e__13) (loc : Ploc.t) ->
              (Qast.Tuple
                 [id;
                  Qast.Node ("PaAttr", [Qast.Loc; p; Qast.Option (Some e)])] :
               'attribute_body)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop
                   (Grammar.s_facto
                      (Grammar.s_rules
                         [Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_nterm
                                  (attribute_id :
                                   'attribute_id Grammar.Entry.e)),
                             (fun (a : 'attribute_id) (loc : Ploc.t) ->
                                (Qast.VaVal a : 'e__11)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "_attrid")),
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaAnt ("_attrid", loc, a) : 'e__11)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "attrid")),
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaVal (Qast.VaAnt ("attrid", loc, a)) :
                                 'e__11)))])))
                (Grammar.s_token ("", "?")))
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_nterm (patt : 'patt Grammar.Entry.e)),
                       (fun (a : 'patt) (loc : Ploc.t) ->
                          (Qast.VaVal a : 'e__12)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_patt")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_patt", loc, a) : 'e__12)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "patt")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("patt", loc, a)) :
                           'e__12)))])),
           (fun (p : 'e__12) _ (id : 'e__11) (loc : Ploc.t) ->
              (Qast.Tuple
                 [id; Qast.Node ("PaAttr", [Qast.Loc; p; Qast.Option None])] :
               'attribute_body)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop
                   (Grammar.s_facto
                      (Grammar.s_rules
                         [Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_nterm
                                  (attribute_id :
                                   'attribute_id Grammar.Entry.e)),
                             (fun (a : 'attribute_id) (loc : Ploc.t) ->
                                (Qast.VaVal a : 'e__9)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "_attrid")),
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaAnt ("_attrid", loc, a) : 'e__9)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "attrid")),
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaVal (Qast.VaAnt ("attrid", loc, a)) :
                                 'e__9)))])))
                (Grammar.s_token ("", ":")))
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_nterm (ctyp : 'ctyp Grammar.Entry.e)),
                       (fun (a : 'ctyp) (loc : Ploc.t) ->
                          (Qast.VaVal a : 'e__10)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_type")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_type", loc, a) : 'e__10)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "type")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("type", loc, a)) :
                           'e__10)))])),
           (fun (ty : 'e__10) _ (id : 'e__9) (loc : Ploc.t) ->
              (Qast.Tuple [id; Qast.Node ("TyAttr", [Qast.Loc; ty])] :
               'attribute_body)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop
                   (Grammar.s_facto
                      (Grammar.s_rules
                         [Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_nterm
                                  (attribute_id :
                                   'attribute_id Grammar.Entry.e)),
                             (fun (a : 'attribute_id) (loc : Ploc.t) ->
                                (Qast.VaVal a : 'e__8)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "_attrid")),
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaAnt ("_attrid", loc, a) : 'e__8)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "attrid")),
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaVal (Qast.VaAnt ("attrid", loc, a)) :
                                 'e__8)))])))
                (Grammar.s_token ("", ":")))
             (Grammar.s_nterm
                (attribute_signature : 'attribute_signature Grammar.Entry.e)),
           (fun (si : 'attribute_signature) _ (id : 'e__8) (loc : Ploc.t) ->
              (Qast.Tuple [id; Qast.Node ("SiAttr", [Qast.Loc; si])] :
               'attribute_body)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_nterm
                            (attribute_id : 'attribute_id Grammar.Entry.e)),
                       (fun (a : 'attribute_id) (loc : Ploc.t) ->
                          (Qast.VaVal a : 'e__7)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_attrid")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_attrid", loc, a) : 'e__7)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "attrid")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("attrid", loc, a)) :
                           'e__7)))])),
           (fun (id : 'e__7) (loc : Ploc.t) ->
              (Qast.Tuple
                 [id;
                  Qast.Node
                    ("StAttr", [Qast.Loc; Qast.VaVal (Qast.List [])])] :
               'attribute_body)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop
                (Grammar.s_facto
                   (Grammar.s_rules
                      [Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_nterm
                               (attribute_id :
                                'attribute_id Grammar.Entry.e)),
                          (fun (a : 'attribute_id) (loc : Ploc.t) ->
                             (Qast.VaVal a : 'e__6)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_attrid")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_attrid", loc, a) : 'e__6)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "attrid")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("attrid", loc, a)) :
                              'e__6)))])))
             (Grammar.s_nterm
                (attribute_structure : 'attribute_structure Grammar.Entry.e)),
           (fun (st : 'attribute_structure) (id : 'e__6) (loc : Ploc.t) ->
              (Qast.Tuple [id; Qast.Node ("StAttr", [Qast.Loc; st])] :
               'attribute_body)))]];
    Grammar.extension (functor_parameter : 'functor_parameter Grammar.Entry.e)
      None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "(")))
             (Grammar.s_token ("", ")")),
           (fun _ _ (loc : Ploc.t) ->
              (Qast.Option None : 'functor_parameter)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("", "(")))
                      (Grammar.s_facto
                         (Grammar.s_rules
                            [Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_nterm
                                     (uidopt : 'uidopt Grammar.Entry.e)),
                                (fun (a : 'uidopt) (loc : Ploc.t) ->
                                   (Qast.VaVal a : 'e__16)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "_uidopt")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaAnt ("_uidopt", loc, a) :
                                    'e__16)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "uidopt")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaVal
                                      (Qast.VaAnt ("uidopt", loc, a)) :
                                    'e__16)))])))
                   (Grammar.s_token ("", ":")))
                (Grammar.s_nterm
                   (module_type : 'module_type Grammar.Entry.e)))
             (Grammar.s_token ("", ")")),
           (fun _ (t : 'module_type) _ (i : 'e__16) _ (loc : Ploc.t) ->
              (Qast.Option (Some (Qast.Tuple [i; t])) :
               'functor_parameter)))]];
    Grammar.extension (module_expr : 'module_expr Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next Grammar.r_stop
                      (Grammar.s_token ("", "functor")))
                   (Grammar.s_facto
                      (Grammar.s_rules
                         [Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_nterm
                                  (functor_parameter :
                                   'functor_parameter Grammar.Entry.e)),
                             (fun (a : 'functor_parameter) (loc : Ploc.t) ->
                                (Qast.VaVal a : 'e__17)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "_fp")),
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaAnt ("_fp", loc, a) : 'e__17)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "fp")),
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaVal (Qast.VaAnt ("fp", loc, a)) :
                                 'e__17)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token
                                  ("ANTIQUOT", "_functor_parameter")),
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaAnt ("_functor_parameter", loc, a) :
                                 'e__17)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token
                                  ("ANTIQUOT", "functor_parameter")),
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaVal
                                   (Qast.VaAnt
                                      ("functor_parameter", loc, a)) :
                                 'e__17)))])))
                (Grammar.s_token ("", "->")))
             Grammar.s_self,
           (fun (me : 'module_expr) _ (arg : 'e__17) _ (loc : Ploc.t) ->
              (Qast.Node ("MeFun", [Qast.Loc; arg; me]) : 'module_expr)))];
       Some "alg_attribute", Some Gramext.LeftA,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                   (Grammar.s_token ("", "[@")))
                (Grammar.s_facto
                   (Grammar.s_rules
                      [Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_nterm
                               (attribute_body :
                                'attribute_body Grammar.Entry.e)),
                          (fun (a : 'attribute_body) (loc : Ploc.t) ->
                             (Qast.VaVal a : 'e__18)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_attribute")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_attribute", loc, a) : 'e__18)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "attribute")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("attribute", loc, a)) :
                              'e__18)))])))
             (Grammar.s_token ("", "]")),
           (fun _ (attr : 'e__18) _ (e : 'module_expr) (loc : Ploc.t) ->
              (Qast.Node ("MeAtt", [Qast.Loc; e; attr]) : 'module_expr)))];
       None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_cut
                (Grammar.r_next
                   (Grammar.r_next Grammar.r_stop
                      (Grammar.s_token ("", "struct")))
                   (Grammar.s_nterm
                      (structure : 'structure Grammar.Entry.e))))
             (Grammar.s_token ("", "end")),
           (fun _ (st : 'structure) _ (loc : Ploc.t) ->
              (Qast.Node ("MeStr", [Qast.Loc; st]) : 'module_expr)))];
       None, None,
       [Grammar.production
          (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
             Grammar.s_self,
           (fun (me2 : 'module_expr) (me1 : 'module_expr) (loc : Ploc.t) ->
              (Qast.Node ("MeApp", [Qast.Loc; me1; me2]) : 'module_expr)))];
       None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                (Grammar.s_token ("", ".")))
             Grammar.s_self,
           (fun (me2 : 'module_expr) _ (me1 : 'module_expr) (loc : Ploc.t) ->
              (Qast.Node ("MeAcc", [Qast.Loc; me1; me2]) : 'module_expr)))];
       Some "simple", None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "(")))
                Grammar.s_self)
             (Grammar.s_token ("", ")")),
           (fun _ (me : 'module_expr) _ (loc : Ploc.t) ->
              (me : 'module_expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("", "(")))
                      Grammar.s_self)
                   (Grammar.s_token ("", ":")))
                (Grammar.s_nterm
                   (module_type : 'module_type Grammar.Entry.e)))
             (Grammar.s_token ("", ")")),
           (fun _ (mt : 'module_type) _ (me : 'module_expr) _
                (loc : Ploc.t) ->
              (Qast.Node ("MeTyc", [Qast.Loc; me; mt]) : 'module_expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "(")))
                   (Grammar.s_token ("", "value")))
                (Grammar.s_nterm (expr : 'expr Grammar.Entry.e)))
             (Grammar.s_token ("", ")")),
           (fun _ (e : 'expr) _ _ (loc : Ploc.t) ->
              (Qast.Node ("MeUnp", [Qast.Loc; e; Qast.Option None]) :
               'module_expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("", "(")))
                         (Grammar.s_token ("", "value")))
                      (Grammar.s_nterm (expr : 'expr Grammar.Entry.e)))
                   (Grammar.s_token ("", ":")))
                (Grammar.s_nterm
                   (module_type : 'module_type Grammar.Entry.e)))
             (Grammar.s_token ("", ")")),
           (fun _ (mt : 'module_type) _ (e : 'expr) _ _ (loc : Ploc.t) ->
              (Qast.Node ("MeUnp", [Qast.Loc; e; Qast.Option (Some mt)]) :
               'module_expr)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("UIDENT", "")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.Str a) : 'e__19)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_", loc, a) : 'e__19)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("", loc, a)) : 'e__19)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_uid")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_uid", loc, a) : 'e__19)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "uid")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("uid", loc, a)) :
                           'e__19)))])),
           (fun (i : 'e__19) (loc : Ploc.t) ->
              (Qast.Node ("MeUid", [Qast.Loc; i]) : 'module_expr)))]];
    Grammar.extension (structure : 'structure Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_list0
                            (Grammar.s_rules
                               [Grammar.production
                                  (Grammar.r_next
                                     (Grammar.r_next Grammar.r_stop
                                        (Grammar.s_nterm
                                           (str_item :
                                            'str_item Grammar.Entry.e)))
                                     (Grammar.s_token ("", ";")),
                                   (fun _ (s : 'str_item) (loc : Ploc.t) ->
                                      (s : 'e__20)))])),
                       (fun (a : 'e__20 list) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.List a) : 'e__21)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_list")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_list", loc, a) : 'e__21)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "list")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                           'e__21)))])),
           (fun (st : 'e__21) (loc : Ploc.t) -> (st : 'structure)))]];
    Grammar.extension (str_item : 'str_item Grammar.Entry.e) None
      [Some "top", Some Gramext.LeftA,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                   (Grammar.s_token ("", "[@@")))
                (Grammar.s_facto
                   (Grammar.s_rules
                      [Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_nterm
                               (attribute_body :
                                'attribute_body Grammar.Entry.e)),
                          (fun (a : 'attribute_body) (loc : Ploc.t) ->
                             (Qast.VaVal a : 'e__22)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_attribute")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_attribute", loc, a) : 'e__22)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "attribute")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("attribute", loc, a)) :
                              'e__22)))])))
             (Grammar.s_token ("", "]")),
           (fun _ (attr : 'e__22) _ (si : 'str_item) (loc : Ploc.t) ->
              (Qast.Node ("StAtt", [Qast.Loc; si; attr]) : 'str_item)))];
       Some "simple", None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop
                (Grammar.s_nterm (expr : 'expr Grammar.Entry.e)))
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_list0
                            (Grammar.s_nterm
                               (item_attribute :
                                'item_attribute Grammar.Entry.e))),
                       (fun (a : 'item_attribute list) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.List a) : 'e__44)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_list")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_list", loc, a) : 'e__44)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "list")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                           'e__44)))])),
           (fun (attrs : 'e__44) (e : 'expr) (loc : Ploc.t) ->
              (Qast.Node ("StExp", [Qast.Loc; e; attrs]) : 'str_item)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "#")))
                (Grammar.s_facto
                   (Grammar.s_rules
                      [Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("STRING", "")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.Str a) : 'e__41)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_str")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_str", loc, a) : 'e__41)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "str")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("str", loc, a)) :
                              'e__41)))])))
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_list0
                            (Grammar.s_rules
                               [Grammar.production
                                  (Grammar.r_next Grammar.r_stop
                                     (Grammar.s_nterm
                                        (str_item :
                                         'str_item Grammar.Entry.e)),
                                   (fun (si : 'str_item) (loc : Ploc.t) ->
                                      (Qast.Tuple [si; Qast.Loc] :
                                       'e__42)))])),
                       (fun (a : 'e__42 list) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.List a) : 'e__43)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_list")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_list", loc, a) : 'e__43)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "list")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                           'e__43)))])),
           (fun (sil : 'e__43) (s : 'e__41) _ (loc : Ploc.t) ->
              (Qast.Node ("StUse", [Qast.Loc; s; sil]) : 'str_item)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "#")))
                (Grammar.s_facto
                   (Grammar.s_rules
                      [Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("LIDENT", "")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.Str a) : 'e__39)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_", loc, a) : 'e__39)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("", loc, a)) :
                              'e__39)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_lid")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_lid", loc, a) : 'e__39)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "lid")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("lid", loc, a)) :
                              'e__39)))])))
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_opt
                            (Grammar.s_nterm (expr : 'expr Grammar.Entry.e))),
                       (fun (a : 'expr option) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.Option a) : 'e__40)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_opt")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_opt", loc, a) : 'e__40)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "opt")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("opt", loc, a)) :
                           'e__40)))])),
           (fun (dp : 'e__40) (n : 'e__39) _ (loc : Ploc.t) ->
              (Qast.Node ("StDir", [Qast.Loc; n; dp]) : 'str_item)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop
                   (Grammar.s_token ("", "value")))
                (Grammar.s_facto
                   (Grammar.s_rules
                      [Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_flag (Grammar.s_token ("", "rec"))),
                          (fun (a : bool) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.Bool a) : 'e__37)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_opt")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_opt", loc, a) : 'e__37)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "opt")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("opt", loc, a)) :
                              'e__37)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_flag")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_flag", loc, a) : 'e__37)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "flag")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("flag", loc, a)) :
                              'e__37)))])))
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_list1sep
                            (Grammar.s_nterm
                               (let_binding : 'let_binding Grammar.Entry.e))
                            (Grammar.s_token ("", "and")) false),
                       (fun (a : 'let_binding list) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.List a) : 'e__38)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_list")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_list", loc, a) : 'e__38)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "list")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                           'e__38)))])),
           (fun (l : 'e__38) (r : 'e__37) _ (loc : Ploc.t) ->
              (Qast.Node ("StVal", [Qast.Loc; r; l]) : 'str_item)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "type")))
                (Grammar.s_facto
                   (Grammar.s_rules
                      [Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_flag (Grammar.s_token ("", "nonrec"))),
                          (fun (a : bool) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.Bool a) : 'e__35)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_opt")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_opt", loc, a) : 'e__35)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "opt")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("opt", loc, a)) :
                              'e__35)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_flag")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_flag", loc, a) : 'e__35)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "flag")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("flag", loc, a)) :
                              'e__35)))])))
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_list1sep
                            (Grammar.s_nterm
                               (type_decl : 'type_decl Grammar.Entry.e))
                            (Grammar.s_token ("", "and")) false),
                       (fun (a : 'type_decl list) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.List a) : 'e__36)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_list")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_list", loc, a) : 'e__36)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "list")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                           'e__36)))])),
           (fun (tdl : 'e__36) (nrfl : 'e__35) _ (loc : Ploc.t) ->
              (Qast.Node ("StTyp", [Qast.Loc; nrfl; tdl]) : 'str_item)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "open")))
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_nterm
                            (mod_ident : 'mod_ident Grammar.Entry.e)),
                       (fun (a : 'mod_ident) (loc : Ploc.t) ->
                          (Qast.VaVal a : 'e__34)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_", loc, a) : 'e__34)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("", loc, a)) : 'e__34)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_list")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_list", loc, a) : 'e__34)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "list")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                           'e__34)))])),
           (fun (i : 'e__34) _ (loc : Ploc.t) ->
              (Qast.Node ("StOpn", [Qast.Loc; i]) : 'str_item)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("", "module")))
                         (Grammar.s_token ("", "type")))
                      (Grammar.s_facto
                         (Grammar.s_rules
                            [Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_nterm
                                     (ident : 'ident Grammar.Entry.e)),
                                (fun (a : 'ident) (loc : Ploc.t) ->
                                   (Qast.VaVal a : 'e__32)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "_")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaAnt ("_", loc, a) : 'e__32)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaVal (Qast.VaAnt ("", loc, a)) :
                                    'e__32)))])))
                   (Grammar.s_token ("", "=")))
                (Grammar.s_nterm
                   (module_type : 'module_type Grammar.Entry.e)))
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_list0
                            (Grammar.s_nterm
                               (item_attribute :
                                'item_attribute Grammar.Entry.e))),
                       (fun (a : 'item_attribute list) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.List a) : 'e__33)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_list")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_list", loc, a) : 'e__33)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "list")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                           'e__33)))])),
           (fun (attrs : 'e__33) (mt : 'module_type) _ (i : 'e__32) _ _
                (loc : Ploc.t) ->
              (Qast.Node ("StMty", [Qast.Loc; i; mt; attrs]) : 'str_item)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop
                   (Grammar.s_token ("", "module")))
                (Grammar.s_facto
                   (Grammar.s_rules
                      [Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_flag (Grammar.s_token ("", "rec"))),
                          (fun (a : bool) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.Bool a) : 'e__30)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_opt")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_opt", loc, a) : 'e__30)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "opt")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("opt", loc, a)) :
                              'e__30)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_flag")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_flag", loc, a) : 'e__30)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "flag")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("flag", loc, a)) :
                              'e__30)))])))
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_list1sep
                            (Grammar.s_nterm
                               (mod_binding : 'mod_binding Grammar.Entry.e))
                            (Grammar.s_token ("", "and")) false),
                       (fun (a : 'mod_binding list) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.List a) : 'e__31)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_list")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_list", loc, a) : 'e__31)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "list")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                           'e__31)))])),
           (fun (l : 'e__31) (r : 'e__30) _ (loc : Ploc.t) ->
              (Qast.Node ("StMod", [Qast.Loc; r; l]) : 'str_item)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "include")))
             (Grammar.s_nterm (module_expr : 'module_expr Grammar.Entry.e)),
           (fun (me : 'module_expr) _ (loc : Ploc.t) ->
              (Qast.Node ("StInc", [Qast.Loc; me]) : 'str_item)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next
                         (Grammar.r_next
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("", "external")))
                            (Grammar.s_facto
                               (Grammar.s_rules
                                  [Grammar.production
                                     (Grammar.r_next Grammar.r_stop
                                        (Grammar.s_token ("LIDENT", "")),
                                      (fun (a : string) (loc : Ploc.t) ->
                                         (Qast.VaVal (Qast.Str a) : 'e__27)));
                                   Grammar.production
                                     (Grammar.r_next Grammar.r_stop
                                        (Grammar.s_token ("ANTIQUOT", "_")),
                                      (fun (a : string) (loc : Ploc.t) ->
                                         (Qast.VaAnt ("_", loc, a) :
                                          'e__27)));
                                   Grammar.production
                                     (Grammar.r_next Grammar.r_stop
                                        (Grammar.s_token ("ANTIQUOT", "")),
                                      (fun (a : string) (loc : Ploc.t) ->
                                         (Qast.VaVal
                                            (Qast.VaAnt ("", loc, a)) :
                                          'e__27)));
                                   Grammar.production
                                     (Grammar.r_next Grammar.r_stop
                                        (Grammar.s_token
                                           ("ANTIQUOT", "_lid")),
                                      (fun (a : string) (loc : Ploc.t) ->
                                         (Qast.VaAnt ("_lid", loc, a) :
                                          'e__27)));
                                   Grammar.production
                                     (Grammar.r_next Grammar.r_stop
                                        (Grammar.s_token ("ANTIQUOT", "lid")),
                                      (fun (a : string) (loc : Ploc.t) ->
                                         (Qast.VaVal
                                            (Qast.VaAnt ("lid", loc, a)) :
                                          'e__27)))])))
                         (Grammar.s_token ("", ":")))
                      (Grammar.s_nterm (ctyp : 'ctyp Grammar.Entry.e)))
                   (Grammar.s_token ("", "=")))
                (Grammar.s_facto
                   (Grammar.s_rules
                      [Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_list1
                               (Grammar.s_token ("STRING", ""))),
                          (fun (a : string list) (loc : Ploc.t) ->
                             (Qast.VaVal
                                (Qast.List
                                   (List.map (fun a -> Qast.Str a) a)) :
                              'e__28)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_list")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_list", loc, a) : 'e__28)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "list")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                              'e__28)))])))
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_list0
                            (Grammar.s_nterm
                               (item_attribute :
                                'item_attribute Grammar.Entry.e))),
                       (fun (a : 'item_attribute list) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.List a) : 'e__29)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_list")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_list", loc, a) : 'e__29)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "list")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                           'e__29)))])),
           (fun (attrs : 'e__29) (pd : 'e__28) _ (t : 'ctyp) _ (i : 'e__27) _
                (loc : Ploc.t) ->
              (Qast.Node ("StExt", [Qast.Loc; i; t; pd; attrs]) :
               'str_item)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("", "exception")))
                      (Grammar.s_nterm
                         (constructor_declaration_sans_alg_attrs :
                          'constructor_declaration_sans_alg_attrs
                            Grammar.Entry.e)))
                   (Grammar.s_nterm
                      (rebind_exn : 'rebind_exn Grammar.Entry.e)))
                (Grammar.s_facto
                   (Grammar.s_rules
                      [Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_list0
                               (Grammar.s_nterm
                                  (alg_attribute :
                                   'alg_attribute Grammar.Entry.e))),
                          (fun (a : 'alg_attribute list) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.List a) : 'e__25)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_list")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_list", loc, a) : 'e__25)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "list")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                              'e__25)))])))
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_list0
                            (Grammar.s_nterm
                               (item_attribute :
                                'item_attribute Grammar.Entry.e))),
                       (fun (a : 'item_attribute list) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.List a) : 'e__26)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_list")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_list", loc, a) : 'e__26)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "list")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                           'e__26)))])),
           (fun (item_attrs : 'e__26) (alg_attrs : 'e__25) (b : 'rebind_exn)
                (ctl : 'constructor_declaration_sans_alg_attrs) _
                (loc : Ploc.t) ->
              (let (_, c, tl, _) =
                 match ctl with
                   Qast.Tuple [xx1; xx2; xx3; xx4] -> xx1, xx2, xx3, xx4
                 | _ -> raise (Match_failure ("q_MLast.ml", 353, 20))
               in
               Qast.Node
                 ("StExc", [Qast.Loc; c; tl; b; alg_attrs; item_attrs]) :
               'str_item)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop
                   (Grammar.s_token ("", "declare")))
                (Grammar.s_facto
                   (Grammar.s_rules
                      [Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_list0
                               (Grammar.s_rules
                                  [Grammar.production
                                     (Grammar.r_next
                                        (Grammar.r_next Grammar.r_stop
                                           (Grammar.s_nterm
                                              (str_item :
                                               'str_item Grammar.Entry.e)))
                                        (Grammar.s_token ("", ";")),
                                      (fun _ (s : 'str_item) (loc : Ploc.t) ->
                                         (s : 'e__23)))])),
                          (fun (a : 'e__23 list) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.List a) : 'e__24)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_list")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_list", loc, a) : 'e__24)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "list")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                              'e__24)))])))
             (Grammar.s_token ("", "end")),
           (fun _ (st : 'e__24) _ (loc : Ploc.t) ->
              (Qast.Node ("StDcl", [Qast.Loc; st]) : 'str_item)))]];
    Grammar.extension (rebind_exn : 'rebind_exn Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_stop,
           (fun (loc : Ploc.t) -> (Qast.VaVal (Qast.List []) : 'rebind_exn)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "=")))
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_nterm
                            (mod_ident : 'mod_ident Grammar.Entry.e)),
                       (fun (a : 'mod_ident) (loc : Ploc.t) ->
                          (Qast.VaVal a : 'e__45)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_", loc, a) : 'e__45)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("", loc, a)) : 'e__45)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_list")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_list", loc, a) : 'e__45)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "list")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                           'e__45)))])),
           (fun (a : 'e__45) _ (loc : Ploc.t) -> (a : 'rebind_exn)))]];
    Grammar.extension (mod_binding : 'mod_binding Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop
                   (Grammar.s_facto
                      (Grammar.s_rules
                         [Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_nterm
                                  (uidopt : 'uidopt Grammar.Entry.e)),
                             (fun (a : 'uidopt) (loc : Ploc.t) ->
                                (Qast.VaVal a : 'e__46)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "_uidopt")),
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaAnt ("_uidopt", loc, a) : 'e__46)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "uidopt")),
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaVal (Qast.VaAnt ("uidopt", loc, a)) :
                                 'e__46)))])))
                (Grammar.s_nterm
                   (mod_fun_binding : 'mod_fun_binding Grammar.Entry.e)))
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_list0
                            (Grammar.s_nterm
                               (item_attribute :
                                'item_attribute Grammar.Entry.e))),
                       (fun (a : 'item_attribute list) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.List a) : 'e__47)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_list")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_list", loc, a) : 'e__47)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "list")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                           'e__47)))])),
           (fun (attrs : 'e__47) (me : 'mod_fun_binding) (i : 'e__46)
                (loc : Ploc.t) ->
              (Qast.Tuple [i; me; attrs] : 'mod_binding)))]];
    Grammar.extension (mod_fun_binding : 'mod_fun_binding Grammar.Entry.e)
      None
      [None, Some Gramext.RightA,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "=")))
             (Grammar.s_nterm (module_expr : 'module_expr Grammar.Entry.e)),
           (fun (me : 'module_expr) _ (loc : Ploc.t) ->
              (me : 'mod_fun_binding)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", ":")))
                   (Grammar.s_nterm
                      (module_type : 'module_type Grammar.Entry.e)))
                (Grammar.s_token ("", "=")))
             (Grammar.s_nterm (module_expr : 'module_expr Grammar.Entry.e)),
           (fun (me : 'module_expr) _ (mt : 'module_type) _ (loc : Ploc.t) ->
              (Qast.Node ("MeTyc", [Qast.Loc; me; mt]) : 'mod_fun_binding)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop
                (Grammar.s_facto
                   (Grammar.s_rules
                      [Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_nterm
                               (functor_parameter :
                                'functor_parameter Grammar.Entry.e)),
                          (fun (a : 'functor_parameter) (loc : Ploc.t) ->
                             (Qast.VaVal a : 'e__48)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_fp")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_fp", loc, a) : 'e__48)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "fp")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("fp", loc, a)) :
                              'e__48)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token
                               ("ANTIQUOT", "_functor_parameter")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_functor_parameter", loc, a) :
                              'e__48)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token
                               ("ANTIQUOT", "functor_parameter")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal
                                (Qast.VaAnt ("functor_parameter", loc, a)) :
                              'e__48)))])))
             Grammar.s_self,
           (fun (mb : 'mod_fun_binding) (arg : 'e__48) (loc : Ploc.t) ->
              (Qast.Node ("MeFun", [Qast.Loc; arg; mb]) :
               'mod_fun_binding)))]];
    Grammar.extension (module_type : 'module_type Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next Grammar.r_stop
                      (Grammar.s_token ("", "functor")))
                   (Grammar.s_facto
                      (Grammar.s_rules
                         [Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_nterm
                                  (functor_parameter :
                                   'functor_parameter Grammar.Entry.e)),
                             (fun (a : 'functor_parameter) (loc : Ploc.t) ->
                                (Qast.VaVal a : 'e__49)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "_fp")),
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaAnt ("_fp", loc, a) : 'e__49)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "fp")),
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaVal (Qast.VaAnt ("fp", loc, a)) :
                                 'e__49)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token
                                  ("ANTIQUOT", "_functor_parameter")),
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaAnt ("_functor_parameter", loc, a) :
                                 'e__49)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token
                                  ("ANTIQUOT", "functor_parameter")),
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaVal
                                   (Qast.VaAnt
                                      ("functor_parameter", loc, a)) :
                                 'e__49)))])))
                (Grammar.s_token ("", "->")))
             Grammar.s_self,
           (fun (mt : 'module_type) _ (arg : 'e__49) _ (loc : Ploc.t) ->
              (Qast.Node ("MtFun", [Qast.Loc; arg; mt]) : 'module_type)))];
       Some "->", Some Gramext.RightA,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                (Grammar.s_token ("", "->")))
             Grammar.s_self,
           (fun (mt2 : 'module_type) _ (mt1 : 'module_type) (loc : Ploc.t) ->
              (Qast.Node
                 ("MtFun",
                  [Qast.Loc;
                   Qast.VaVal
                     (Qast.Option
                        (Some
                           (Qast.Tuple
                              [Qast.VaVal (Qast.Option None); mt1])));
                   mt2]) :
               'module_type)))];
       Some "alg_attribute", Some Gramext.LeftA,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                   (Grammar.s_token ("", "[@")))
                (Grammar.s_facto
                   (Grammar.s_rules
                      [Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_nterm
                               (attribute_body :
                                'attribute_body Grammar.Entry.e)),
                          (fun (a : 'attribute_body) (loc : Ploc.t) ->
                             (Qast.VaVal a : 'e__50)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_attribute")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_attribute", loc, a) : 'e__50)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "attribute")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("attribute", loc, a)) :
                              'e__50)))])))
             (Grammar.s_token ("", "]")),
           (fun _ (attr : 'e__50) _ (e : 'module_type) (loc : Ploc.t) ->
              (Qast.Node ("MtAtt", [Qast.Loc; e; attr]) : 'module_type)))];
       None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                (Grammar.s_token ("", "with")))
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_list1sep
                            (Grammar.s_nterm
                               (with_constr : 'with_constr Grammar.Entry.e))
                            (Grammar.s_token ("", "and")) false),
                       (fun (a : 'with_constr list) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.List a) : 'e__51)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_list")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_list", loc, a) : 'e__51)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "list")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                           'e__51)))])),
           (fun (wcl : 'e__51) _ (mt : 'module_type) (loc : Ploc.t) ->
              (Qast.Node ("MtWit", [Qast.Loc; mt; wcl]) : 'module_type)))];
       None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next Grammar.r_stop
                      (Grammar.s_token ("", "module")))
                   (Grammar.s_token ("", "type")))
                (Grammar.s_token ("", "of")))
             (Grammar.s_nterm (module_expr : 'module_expr Grammar.Entry.e)),
           (fun (me : 'module_expr) _ _ _ (loc : Ploc.t) ->
              (Qast.Node ("MtTyo", [Qast.Loc; me]) : 'module_type)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_cut
                (Grammar.r_next
                   (Grammar.r_next Grammar.r_stop
                      (Grammar.s_token ("", "sig")))
                   (Grammar.s_nterm
                      (signature : 'signature Grammar.Entry.e))))
             (Grammar.s_token ("", "end")),
           (fun _ (sg : 'signature) _ (loc : Ploc.t) ->
              (Qast.Node ("MtSig", [Qast.Loc; sg]) : 'module_type)))];
       None, None,
       [Grammar.production
          (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
             Grammar.s_self,
           (fun (m2 : 'module_type) (m1 : 'module_type) (loc : Ploc.t) ->
              (Qast.Node ("MtApp", [Qast.Loc; m1; m2]) : 'module_type)))];
       None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                (Grammar.s_token ("", ".")))
             Grammar.s_self,
           (fun (m2 : 'module_type) _ (m1 : 'module_type) (loc : Ploc.t) ->
              (Qast.Node ("MtAcc", [Qast.Loc; m1; m2]) : 'module_type)))];
       Some "simple", None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "(")))
                Grammar.s_self)
             (Grammar.s_token ("", ")")),
           (fun _ (mt : 'module_type) _ (loc : Ploc.t) ->
              (mt : 'module_type)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "'")))
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_nterm (ident : 'ident Grammar.Entry.e)),
                       (fun (a : 'ident) (loc : Ploc.t) ->
                          (Qast.VaVal a : 'e__54)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_", loc, a) : 'e__54)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("", loc, a)) :
                           'e__54)))])),
           (fun (i : 'e__54) _ (loc : Ploc.t) ->
              (Qast.Node ("MtQuo", [Qast.Loc; i]) : 'module_type)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("LIDENT", "")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.Str a) : 'e__53)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_", loc, a) : 'e__53)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("", loc, a)) : 'e__53)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_lid")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_lid", loc, a) : 'e__53)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "lid")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("lid", loc, a)) :
                           'e__53)))])),
           (fun (i : 'e__53) (loc : Ploc.t) ->
              (Qast.Node ("MtLid", [Qast.Loc; i]) : 'module_type)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("UIDENT", "")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.Str a) : 'e__52)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_", loc, a) : 'e__52)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("", loc, a)) : 'e__52)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_uid")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_uid", loc, a) : 'e__52)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "uid")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("uid", loc, a)) :
                           'e__52)))])),
           (fun (i : 'e__52) (loc : Ploc.t) ->
              (Qast.Node ("MtUid", [Qast.Loc; i]) : 'module_type)))]];
    Grammar.extension (signature : 'signature Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_list0
                            (Grammar.s_rules
                               [Grammar.production
                                  (Grammar.r_next
                                     (Grammar.r_next Grammar.r_stop
                                        (Grammar.s_nterm
                                           (sig_item :
                                            'sig_item Grammar.Entry.e)))
                                     (Grammar.s_token ("", ";")),
                                   (fun _ (s : 'sig_item) (loc : Ploc.t) ->
                                      (s : 'e__55)))])),
                       (fun (a : 'e__55 list) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.List a) : 'e__56)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_list")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_list", loc, a) : 'e__56)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "list")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                           'e__56)))])),
           (fun (st : 'e__56) (loc : Ploc.t) -> (st : 'signature)))]];
    Grammar.extension (sig_item : 'sig_item Grammar.Entry.e) None
      [Some "top", Some Gramext.LeftA,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                   (Grammar.s_token ("", "[@@")))
                (Grammar.s_facto
                   (Grammar.s_rules
                      [Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_nterm
                               (attribute_body :
                                'attribute_body Grammar.Entry.e)),
                          (fun (a : 'attribute_body) (loc : Ploc.t) ->
                             (Qast.VaVal a : 'e__57)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_attribute")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_attribute", loc, a) : 'e__57)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "attribute")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("attribute", loc, a)) :
                              'e__57)))])))
             (Grammar.s_token ("", "]")),
           (fun _ (attr : 'e__57) _ (si : 'sig_item) (loc : Ploc.t) ->
              (Qast.Node ("SgAtt", [Qast.Loc; si; attr]) : 'sig_item)))];
       Some "simple", None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "#")))
                (Grammar.s_facto
                   (Grammar.s_rules
                      [Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("STRING", "")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.Str a) : 'e__75)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_str")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_str", loc, a) : 'e__75)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "str")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("str", loc, a)) :
                              'e__75)))])))
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_list0
                            (Grammar.s_rules
                               [Grammar.production
                                  (Grammar.r_next Grammar.r_stop
                                     (Grammar.s_nterm
                                        (sig_item :
                                         'sig_item Grammar.Entry.e)),
                                   (fun (si : 'sig_item) (loc : Ploc.t) ->
                                      (Qast.Tuple [si; Qast.Loc] :
                                       'e__76)))])),
                       (fun (a : 'e__76 list) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.List a) : 'e__77)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_list")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_list", loc, a) : 'e__77)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "list")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                           'e__77)))])),
           (fun (sil : 'e__77) (s : 'e__75) _ (loc : Ploc.t) ->
              (Qast.Node ("SgUse", [Qast.Loc; s; sil]) : 'sig_item)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "#")))
                (Grammar.s_facto
                   (Grammar.s_rules
                      [Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("LIDENT", "")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.Str a) : 'e__73)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_", loc, a) : 'e__73)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("", loc, a)) :
                              'e__73)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_lid")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_lid", loc, a) : 'e__73)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "lid")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("lid", loc, a)) :
                              'e__73)))])))
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_opt
                            (Grammar.s_nterm (expr : 'expr Grammar.Entry.e))),
                       (fun (a : 'expr option) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.Option a) : 'e__74)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_opt")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_opt", loc, a) : 'e__74)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "opt")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("opt", loc, a)) :
                           'e__74)))])),
           (fun (dp : 'e__74) (n : 'e__73) _ (loc : Ploc.t) ->
              (Qast.Node ("SgDir", [Qast.Loc; n; dp]) : 'sig_item)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("", "value")))
                      (Grammar.s_facto
                         (Grammar.s_rules
                            [Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("LIDENT", "")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaVal (Qast.Str a) : 'e__71)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "_")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaAnt ("_", loc, a) : 'e__71)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaVal (Qast.VaAnt ("", loc, a)) :
                                    'e__71)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "_lid")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaAnt ("_lid", loc, a) : 'e__71)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "lid")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaVal (Qast.VaAnt ("lid", loc, a)) :
                                    'e__71)))])))
                   (Grammar.s_token ("", ":")))
                (Grammar.s_nterm (ctyp : 'ctyp Grammar.Entry.e)))
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_list0
                            (Grammar.s_nterm
                               (item_attribute :
                                'item_attribute Grammar.Entry.e))),
                       (fun (a : 'item_attribute list) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.List a) : 'e__72)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_list")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_list", loc, a) : 'e__72)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "list")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                           'e__72)))])),
           (fun (attrs : 'e__72) (t : 'ctyp) _ (i : 'e__71) _
                (loc : Ploc.t) ->
              (Qast.Node ("SgVal", [Qast.Loc; i; t; attrs]) : 'sig_item)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "type")))
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_list1sep
                            (Grammar.s_nterm
                               (type_decl : 'type_decl Grammar.Entry.e))
                            (Grammar.s_token ("", "and")) false),
                       (fun (a : 'type_decl list) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.List a) : 'e__70)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_list")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_list", loc, a) : 'e__70)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "list")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                           'e__70)))])),
           (fun (tdl : 'e__70) _ (loc : Ploc.t) ->
              (Qast.Node ("SgTyp", [Qast.Loc; tdl]) : 'sig_item)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "open")))
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_nterm
                            (mod_ident : 'mod_ident Grammar.Entry.e)),
                       (fun (a : 'mod_ident) (loc : Ploc.t) ->
                          (Qast.VaVal a : 'e__69)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_", loc, a) : 'e__69)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("", loc, a)) : 'e__69)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_list")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_list", loc, a) : 'e__69)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "list")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                           'e__69)))])),
           (fun (i : 'e__69) _ (loc : Ploc.t) ->
              (Qast.Node ("SgOpn", [Qast.Loc; i]) : 'sig_item)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("", "module")))
                         (Grammar.s_token ("", "type")))
                      (Grammar.s_facto
                         (Grammar.s_rules
                            [Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_nterm
                                     (ident : 'ident Grammar.Entry.e)),
                                (fun (a : 'ident) (loc : Ploc.t) ->
                                   (Qast.VaVal a : 'e__67)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "_")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaAnt ("_", loc, a) : 'e__67)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaVal (Qast.VaAnt ("", loc, a)) :
                                    'e__67)))])))
                   (Grammar.s_token ("", "=")))
                (Grammar.s_nterm
                   (module_type : 'module_type Grammar.Entry.e)))
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_list0
                            (Grammar.s_nterm
                               (item_attribute :
                                'item_attribute Grammar.Entry.e))),
                       (fun (a : 'item_attribute list) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.List a) : 'e__68)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_list")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_list", loc, a) : 'e__68)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "list")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                           'e__68)))])),
           (fun (attrs : 'e__68) (mt : 'module_type) _ (i : 'e__67) _ _
                (loc : Ploc.t) ->
              (Qast.Node ("SgMty", [Qast.Loc; i; mt; attrs]) : 'sig_item)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop
                   (Grammar.s_token ("", "module")))
                (Grammar.s_facto
                   (Grammar.s_rules
                      [Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_flag (Grammar.s_token ("", "rec"))),
                          (fun (a : bool) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.Bool a) : 'e__65)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_opt")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_opt", loc, a) : 'e__65)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "opt")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("opt", loc, a)) :
                              'e__65)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_flag")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_flag", loc, a) : 'e__65)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "flag")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("flag", loc, a)) :
                              'e__65)))])))
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_list1sep
                            (Grammar.s_nterm
                               (mod_decl_binding :
                                'mod_decl_binding Grammar.Entry.e))
                            (Grammar.s_token ("", "and")) false),
                       (fun (a : 'mod_decl_binding list) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.List a) : 'e__66)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_list")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_list", loc, a) : 'e__66)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "list")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                           'e__66)))])),
           (fun (l : 'e__66) (rf : 'e__65) _ (loc : Ploc.t) ->
              (Qast.Node ("SgMod", [Qast.Loc; rf; l]) : 'sig_item)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "include")))
             (Grammar.s_nterm (module_type : 'module_type Grammar.Entry.e)),
           (fun (mt : 'module_type) _ (loc : Ploc.t) ->
              (Qast.Node ("SgInc", [Qast.Loc; mt]) : 'sig_item)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next
                         (Grammar.r_next
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("", "external")))
                            (Grammar.s_facto
                               (Grammar.s_rules
                                  [Grammar.production
                                     (Grammar.r_next Grammar.r_stop
                                        (Grammar.s_token ("LIDENT", "")),
                                      (fun (a : string) (loc : Ploc.t) ->
                                         (Qast.VaVal (Qast.Str a) : 'e__62)));
                                   Grammar.production
                                     (Grammar.r_next Grammar.r_stop
                                        (Grammar.s_token ("ANTIQUOT", "_")),
                                      (fun (a : string) (loc : Ploc.t) ->
                                         (Qast.VaAnt ("_", loc, a) :
                                          'e__62)));
                                   Grammar.production
                                     (Grammar.r_next Grammar.r_stop
                                        (Grammar.s_token ("ANTIQUOT", "")),
                                      (fun (a : string) (loc : Ploc.t) ->
                                         (Qast.VaVal
                                            (Qast.VaAnt ("", loc, a)) :
                                          'e__62)));
                                   Grammar.production
                                     (Grammar.r_next Grammar.r_stop
                                        (Grammar.s_token
                                           ("ANTIQUOT", "_lid")),
                                      (fun (a : string) (loc : Ploc.t) ->
                                         (Qast.VaAnt ("_lid", loc, a) :
                                          'e__62)));
                                   Grammar.production
                                     (Grammar.r_next Grammar.r_stop
                                        (Grammar.s_token ("ANTIQUOT", "lid")),
                                      (fun (a : string) (loc : Ploc.t) ->
                                         (Qast.VaVal
                                            (Qast.VaAnt ("lid", loc, a)) :
                                          'e__62)))])))
                         (Grammar.s_token ("", ":")))
                      (Grammar.s_nterm (ctyp : 'ctyp Grammar.Entry.e)))
                   (Grammar.s_token ("", "=")))
                (Grammar.s_facto
                   (Grammar.s_rules
                      [Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_list1
                               (Grammar.s_token ("STRING", ""))),
                          (fun (a : string list) (loc : Ploc.t) ->
                             (Qast.VaVal
                                (Qast.List
                                   (List.map (fun a -> Qast.Str a) a)) :
                              'e__63)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_list")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_list", loc, a) : 'e__63)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "list")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                              'e__63)))])))
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_list0
                            (Grammar.s_nterm
                               (item_attribute :
                                'item_attribute Grammar.Entry.e))),
                       (fun (a : 'item_attribute list) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.List a) : 'e__64)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_list")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_list", loc, a) : 'e__64)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "list")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                           'e__64)))])),
           (fun (attrs : 'e__64) (pd : 'e__63) _ (t : 'ctyp) _ (i : 'e__62) _
                (loc : Ploc.t) ->
              (Qast.Node ("SgExt", [Qast.Loc; i; t; pd; attrs]) :
               'sig_item)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next Grammar.r_stop
                      (Grammar.s_token ("", "exception")))
                   (Grammar.s_nterm
                      (constructor_declaration_sans_alg_attrs :
                       'constructor_declaration_sans_alg_attrs
                         Grammar.Entry.e)))
                (Grammar.s_facto
                   (Grammar.s_rules
                      [Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_list0
                               (Grammar.s_nterm
                                  (alg_attribute :
                                   'alg_attribute Grammar.Entry.e))),
                          (fun (a : 'alg_attribute list) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.List a) : 'e__60)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_list")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_list", loc, a) : 'e__60)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "list")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                              'e__60)))])))
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_list0
                            (Grammar.s_nterm
                               (item_attribute :
                                'item_attribute Grammar.Entry.e))),
                       (fun (a : 'item_attribute list) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.List a) : 'e__61)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_list")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_list", loc, a) : 'e__61)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "list")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                           'e__61)))])),
           (fun (item_attrs : 'e__61) (alg_attrs : 'e__60)
                (ctl : 'constructor_declaration_sans_alg_attrs) _
                (loc : Ploc.t) ->
              (let (_, c, tl, _) =
                 match ctl with
                   Qast.Tuple [xx1; xx2; xx3; xx4] -> xx1, xx2, xx3, xx4
                 | _ -> raise (Match_failure ("q_MLast.ml", 438, 20))
               in
               Qast.Node ("SgExc", [Qast.Loc; c; tl; alg_attrs; item_attrs]) :
               'sig_item)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop
                   (Grammar.s_token ("", "declare")))
                (Grammar.s_facto
                   (Grammar.s_rules
                      [Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_list0
                               (Grammar.s_rules
                                  [Grammar.production
                                     (Grammar.r_next
                                        (Grammar.r_next Grammar.r_stop
                                           (Grammar.s_nterm
                                              (sig_item :
                                               'sig_item Grammar.Entry.e)))
                                        (Grammar.s_token ("", ";")),
                                      (fun _ (s : 'sig_item) (loc : Ploc.t) ->
                                         (s : 'e__58)))])),
                          (fun (a : 'e__58 list) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.List a) : 'e__59)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_list")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_list", loc, a) : 'e__59)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "list")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                              'e__59)))])))
             (Grammar.s_token ("", "end")),
           (fun _ (st : 'e__59) _ (loc : Ploc.t) ->
              (Qast.Node ("SgDcl", [Qast.Loc; st]) : 'sig_item)))]];
    Grammar.extension (mod_decl_binding : 'mod_decl_binding Grammar.Entry.e)
      None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop
                   (Grammar.s_facto
                      (Grammar.s_rules
                         [Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_nterm
                                  (uidopt : 'uidopt Grammar.Entry.e)),
                             (fun (a : 'uidopt) (loc : Ploc.t) ->
                                (Qast.VaVal a : 'e__78)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "_uidopt")),
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaAnt ("_uidopt", loc, a) : 'e__78)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "uidopt")),
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaVal (Qast.VaAnt ("uidopt", loc, a)) :
                                 'e__78)))])))
                (Grammar.s_nterm
                   (module_declaration :
                    'module_declaration Grammar.Entry.e)))
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_list0
                            (Grammar.s_nterm
                               (item_attribute :
                                'item_attribute Grammar.Entry.e))),
                       (fun (a : 'item_attribute list) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.List a) : 'e__79)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_list")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_list", loc, a) : 'e__79)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "list")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                           'e__79)))])),
           (fun (attrs : 'e__79) (mt : 'module_declaration) (i : 'e__78)
                (loc : Ploc.t) ->
              (Qast.Tuple [i; mt; attrs] : 'mod_decl_binding)))]];
    Grammar.extension
      (module_declaration : 'module_declaration Grammar.Entry.e) None
      [None, Some Gramext.RightA,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop
                (Grammar.s_facto
                   (Grammar.s_rules
                      [Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_nterm
                               (functor_parameter :
                                'functor_parameter Grammar.Entry.e)),
                          (fun (a : 'functor_parameter) (loc : Ploc.t) ->
                             (Qast.VaVal a : 'e__80)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_fp")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_fp", loc, a) : 'e__80)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "fp")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("fp", loc, a)) :
                              'e__80)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token
                               ("ANTIQUOT", "_functor_parameter")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_functor_parameter", loc, a) :
                              'e__80)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token
                               ("ANTIQUOT", "functor_parameter")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal
                                (Qast.VaAnt ("functor_parameter", loc, a)) :
                              'e__80)))])))
             Grammar.s_self,
           (fun (mt : 'module_declaration) (arg : 'e__80) (loc : Ploc.t) ->
              (Qast.Node ("MtFun", [Qast.Loc; arg; mt]) :
               'module_declaration)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", ":")))
             (Grammar.s_nterm (module_type : 'module_type Grammar.Entry.e)),
           (fun (mt : 'module_type) _ (loc : Ploc.t) ->
              (mt : 'module_declaration)))]];
    Grammar.extension (with_constr : 'with_constr Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next Grammar.r_stop
                      (Grammar.s_token ("", "module")))
                   (Grammar.s_facto
                      (Grammar.s_rules
                         [Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_nterm
                                  (mod_ident : 'mod_ident Grammar.Entry.e)),
                             (fun (a : 'mod_ident) (loc : Ploc.t) ->
                                (Qast.VaVal a : 'e__87)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "_")),
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaAnt ("_", loc, a) : 'e__87)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "")),
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaVal (Qast.VaAnt ("", loc, a)) :
                                 'e__87)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "_list")),
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaAnt ("_list", loc, a) : 'e__87)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "list")),
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                                 'e__87)))])))
                (Grammar.s_token ("", ":=")))
             (Grammar.s_nterm (module_expr : 'module_expr Grammar.Entry.e)),
           (fun (me : 'module_expr) _ (i : 'e__87) _ (loc : Ploc.t) ->
              (Qast.Node ("WcMos", [Qast.Loc; i; me]) : 'with_constr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next Grammar.r_stop
                      (Grammar.s_token ("", "module")))
                   (Grammar.s_facto
                      (Grammar.s_rules
                         [Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_nterm
                                  (mod_ident : 'mod_ident Grammar.Entry.e)),
                             (fun (a : 'mod_ident) (loc : Ploc.t) ->
                                (Qast.VaVal a : 'e__86)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "_")),
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaAnt ("_", loc, a) : 'e__86)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "")),
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaVal (Qast.VaAnt ("", loc, a)) :
                                 'e__86)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "_list")),
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaAnt ("_list", loc, a) : 'e__86)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "list")),
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                                 'e__86)))])))
                (Grammar.s_token ("", "=")))
             (Grammar.s_nterm (module_expr : 'module_expr Grammar.Entry.e)),
           (fun (me : 'module_expr) _ (i : 'e__86) _ (loc : Ploc.t) ->
              (Qast.Node ("WcMod", [Qast.Loc; i; me]) : 'with_constr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("", "type")))
                      (Grammar.s_facto
                         (Grammar.s_rules
                            [Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_nterm
                                     (mod_ident :
                                      'mod_ident Grammar.Entry.e)),
                                (fun (a : 'mod_ident) (loc : Ploc.t) ->
                                   (Qast.VaVal a : 'e__84)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "_")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaAnt ("_", loc, a) : 'e__84)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaVal (Qast.VaAnt ("", loc, a)) :
                                    'e__84)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "_list")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaAnt ("_list", loc, a) : 'e__84)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "list")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                                    'e__84)))])))
                   (Grammar.s_facto
                      (Grammar.s_rules
                         [Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_list0
                                  (Grammar.s_nterm
                                     (type_parameter :
                                      'type_parameter Grammar.Entry.e))),
                             (fun (a : 'type_parameter list) (loc : Ploc.t) ->
                                (Qast.VaVal (Qast.List a) : 'e__85)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "_list")),
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaAnt ("_list", loc, a) : 'e__85)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "list")),
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                                 'e__85)))])))
                (Grammar.s_token ("", ":=")))
             (Grammar.s_nterm (ctyp : 'ctyp Grammar.Entry.e)),
           (fun (t : 'ctyp) _ (tpl : 'e__85) (i : 'e__84) _ (loc : Ploc.t) ->
              (Qast.Node ("WcTys", [Qast.Loc; i; tpl; t]) : 'with_constr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("", "type")))
                         (Grammar.s_facto
                            (Grammar.s_rules
                               [Grammar.production
                                  (Grammar.r_next Grammar.r_stop
                                     (Grammar.s_nterm
                                        (mod_ident :
                                         'mod_ident Grammar.Entry.e)),
                                   (fun (a : 'mod_ident) (loc : Ploc.t) ->
                                      (Qast.VaVal a : 'e__81)));
                                Grammar.production
                                  (Grammar.r_next Grammar.r_stop
                                     (Grammar.s_token ("ANTIQUOT", "_")),
                                   (fun (a : string) (loc : Ploc.t) ->
                                      (Qast.VaAnt ("_", loc, a) : 'e__81)));
                                Grammar.production
                                  (Grammar.r_next Grammar.r_stop
                                     (Grammar.s_token ("ANTIQUOT", "")),
                                   (fun (a : string) (loc : Ploc.t) ->
                                      (Qast.VaVal (Qast.VaAnt ("", loc, a)) :
                                       'e__81)));
                                Grammar.production
                                  (Grammar.r_next Grammar.r_stop
                                     (Grammar.s_token ("ANTIQUOT", "_list")),
                                   (fun (a : string) (loc : Ploc.t) ->
                                      (Qast.VaAnt ("_list", loc, a) :
                                       'e__81)));
                                Grammar.production
                                  (Grammar.r_next Grammar.r_stop
                                     (Grammar.s_token ("ANTIQUOT", "list")),
                                   (fun (a : string) (loc : Ploc.t) ->
                                      (Qast.VaVal
                                         (Qast.VaAnt ("list", loc, a)) :
                                       'e__81)))])))
                      (Grammar.s_facto
                         (Grammar.s_rules
                            [Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_list0
                                     (Grammar.s_nterm
                                        (type_parameter :
                                         'type_parameter Grammar.Entry.e))),
                                (fun (a : 'type_parameter list)
                                     (loc : Ploc.t) ->
                                   (Qast.VaVal (Qast.List a) : 'e__82)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "_list")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaAnt ("_list", loc, a) : 'e__82)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "list")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                                    'e__82)))])))
                   (Grammar.s_token ("", "=")))
                (Grammar.s_facto
                   (Grammar.s_rules
                      [Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_flag
                               (Grammar.s_token ("", "private"))),
                          (fun (a : bool) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.Bool a) : 'e__83)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_opt")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_opt", loc, a) : 'e__83)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "opt")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("opt", loc, a)) :
                              'e__83)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_flag")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_flag", loc, a) : 'e__83)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "flag")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("flag", loc, a)) :
                              'e__83)))])))
             (Grammar.s_nterm (ctyp : 'ctyp Grammar.Entry.e)),
           (fun (t : 'ctyp) (pf : 'e__83) _ (tpl : 'e__82) (i : 'e__81) _
                (loc : Ploc.t) ->
              (Qast.Node ("WcTyp", [Qast.Loc; i; tpl; pf; t]) :
               'with_constr)))]];
    Grammar.extension (uidopt : 'uidopt Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "_")),
           (fun _ (loc : Ploc.t) -> (Qast.Option None : 'uidopt)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("UIDENT", "")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.Str a) : 'e__88)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_", loc, a) : 'e__88)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("", loc, a)) : 'e__88)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_uid")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_uid", loc, a) : 'e__88)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "uid")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("uid", loc, a)) :
                           'e__88)))])),
           (fun (m : 'e__88) (loc : Ploc.t) ->
              (Qast.Option (Some m) : 'uidopt)))]];
    Grammar.extension (expr : 'expr Grammar.Entry.e) None
      [Some "top", Some Gramext.RightA,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("", "while")))
                         Grammar.s_self)
                      (Grammar.s_token ("", "do")))
                   (Grammar.s_token ("", "{")))
                (Grammar.s_facto
                   (Grammar.s_rules
                      [Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_nterm
                               (sequence : 'sequence Grammar.Entry.e)),
                          (fun (a : 'sequence) (loc : Ploc.t) ->
                             (Qast.VaVal a : 'e__96)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_list")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_list", loc, a) : 'e__96)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "list")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                              'e__96)))])))
             (Grammar.s_token ("", "}")),
           (fun _ (seq : 'e__96) _ _ (e : 'expr) _ (loc : Ploc.t) ->
              (Qast.Node ("ExWhi", [Qast.Loc; e; seq]) : 'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next
                         (Grammar.r_next
                            (Grammar.r_next
                               (Grammar.r_next
                                  (Grammar.r_next
                                     (Grammar.r_next Grammar.r_stop
                                        (Grammar.s_token ("", "for")))
                                     (Grammar.s_facto
                                        (Grammar.s_rules
                                           [Grammar.production
                                              (Grammar.r_next Grammar.r_stop
                                                 (Grammar.s_token
                                                    ("LIDENT", "")),
                                               (fun (a : string)
                                                    (loc : Ploc.t) ->
                                                  (Qast.VaVal (Qast.Str a) :
                                                   'e__93)));
                                            Grammar.production
                                              (Grammar.r_next Grammar.r_stop
                                                 (Grammar.s_token
                                                    ("ANTIQUOT", "_")),
                                               (fun (a : string)
                                                    (loc : Ploc.t) ->
                                                  (Qast.VaAnt ("_", loc, a) :
                                                   'e__93)));
                                            Grammar.production
                                              (Grammar.r_next Grammar.r_stop
                                                 (Grammar.s_token
                                                    ("ANTIQUOT", "")),
                                               (fun (a : string)
                                                    (loc : Ploc.t) ->
                                                  (Qast.VaVal
                                                     (Qast.VaAnt
                                                        ("", loc, a)) :
                                                   'e__93)));
                                            Grammar.production
                                              (Grammar.r_next Grammar.r_stop
                                                 (Grammar.s_token
                                                    ("ANTIQUOT", "_lid")),
                                               (fun (a : string)
                                                    (loc : Ploc.t) ->
                                                  (Qast.VaAnt
                                                     ("_lid", loc, a) :
                                                   'e__93)));
                                            Grammar.production
                                              (Grammar.r_next Grammar.r_stop
                                                 (Grammar.s_token
                                                    ("ANTIQUOT", "lid")),
                                               (fun (a : string)
                                                    (loc : Ploc.t) ->
                                                  (Qast.VaVal
                                                     (Qast.VaAnt
                                                        ("lid", loc, a)) :
                                                   'e__93)))])))
                                  (Grammar.s_token ("", "=")))
                               Grammar.s_self)
                            (Grammar.s_facto
                               (Grammar.s_rules
                                  [Grammar.production
                                     (Grammar.r_next Grammar.r_stop
                                        (Grammar.s_nterm
                                           (direction_flag :
                                            'direction_flag Grammar.Entry.e)),
                                      (fun (a : 'direction_flag)
                                           (loc : Ploc.t) ->
                                         (Qast.VaVal a : 'e__94)));
                                   Grammar.production
                                     (Grammar.r_next Grammar.r_stop
                                        (Grammar.s_token ("ANTIQUOT", "_to")),
                                      (fun (a : string) (loc : Ploc.t) ->
                                         (Qast.VaAnt ("_to", loc, a) :
                                          'e__94)));
                                   Grammar.production
                                     (Grammar.r_next Grammar.r_stop
                                        (Grammar.s_token ("ANTIQUOT", "to")),
                                      (fun (a : string) (loc : Ploc.t) ->
                                         (Qast.VaVal
                                            (Qast.VaAnt ("to", loc, a)) :
                                          'e__94)))])))
                         Grammar.s_self)
                      (Grammar.s_token ("", "do")))
                   (Grammar.s_token ("", "{")))
                (Grammar.s_facto
                   (Grammar.s_rules
                      [Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_nterm
                               (sequence : 'sequence Grammar.Entry.e)),
                          (fun (a : 'sequence) (loc : Ploc.t) ->
                             (Qast.VaVal a : 'e__95)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_list")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_list", loc, a) : 'e__95)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "list")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                              'e__95)))])))
             (Grammar.s_token ("", "}")),
           (fun _ (seq : 'e__95) _ _ (e2 : 'expr) (df : 'e__94) (e1 : 'expr) _
                (i : 'e__93) _ (loc : Ploc.t) ->
              (Qast.Node ("ExFor", [Qast.Loc; i; e1; e2; df; seq]) : 'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next Grammar.r_stop
                      (Grammar.s_token ("", "do")))
                   (Grammar.s_token ("", "{")))
                (Grammar.s_facto
                   (Grammar.s_rules
                      [Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_nterm
                               (sequence : 'sequence Grammar.Entry.e)),
                          (fun (a : 'sequence) (loc : Ploc.t) ->
                             (Qast.VaVal a : 'e__92)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_list")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_list", loc, a) : 'e__92)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "list")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                              'e__92)))])))
             (Grammar.s_token ("", "}")),
           (fun _ (seq : 'e__92) _ _ (loc : Ploc.t) ->
              (mksequence2 Qast.Loc seq : 'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("", "if")))
                         Grammar.s_self)
                      (Grammar.s_token ("", "then")))
                   Grammar.s_self)
                (Grammar.s_token ("", "else")))
             Grammar.s_self,
           (fun (e3 : 'expr) _ (e2 : 'expr) _ (e1 : 'expr) _ (loc : Ploc.t) ->
              (Qast.Node ("ExIfe", [Qast.Loc; e1; e2; e3]) : 'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next Grammar.r_stop
                      (Grammar.s_token ("", "try")))
                   Grammar.s_self)
                (Grammar.s_token ("", "with")))
             (Grammar.s_nterm (match_case : 'match_case Grammar.Entry.e)),
           (fun (mc : 'match_case) _ (e : 'expr) _ (loc : Ploc.t) ->
              (Qast.Node
                 ("ExTry", [Qast.Loc; e; Qast.VaVal (Qast.List [mc])]) :
               'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next Grammar.r_stop
                      (Grammar.s_token ("", "try")))
                   Grammar.s_self)
                (Grammar.s_token ("", "with")))
             (Grammar.s_nterm
                (closed_case_list : 'closed_case_list Grammar.Entry.e)),
           (fun (l : 'closed_case_list) _ (e : 'expr) _ (loc : Ploc.t) ->
              (Qast.Node ("ExTry", [Qast.Loc; e; l]) : 'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("", "match")))
                         Grammar.s_self)
                      (Grammar.s_token ("", "with")))
                   (Grammar.s_nterm (ipatt : 'ipatt Grammar.Entry.e)))
                (Grammar.s_token ("", "->")))
             Grammar.s_self,
           (fun (e1 : 'expr) _ (p1 : 'ipatt) _ (e : 'expr) _ (loc : Ploc.t) ->
              (Qast.Node
                 ("ExMat",
                  [Qast.Loc; e;
                   Qast.VaVal
                     (Qast.List
                        [Qast.Tuple
                           [p1; Qast.VaVal (Qast.Option None); e1]])]) :
               'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next Grammar.r_stop
                      (Grammar.s_token ("", "match")))
                   Grammar.s_self)
                (Grammar.s_token ("", "with")))
             (Grammar.s_nterm
                (closed_case_list : 'closed_case_list Grammar.Entry.e)),
           (fun (l : 'closed_case_list) _ (e : 'expr) _ (loc : Ploc.t) ->
              (Qast.Node ("ExMat", [Qast.Loc; e; l]) : 'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "fun")))
                (Grammar.s_nterm (ipatt : 'ipatt Grammar.Entry.e)))
             (Grammar.s_nterm (fun_def : 'fun_def Grammar.Entry.e)),
           (fun (e : 'fun_def) (p : 'ipatt) _ (loc : Ploc.t) ->
              (Qast.Node
                 ("ExFun",
                  [Qast.Loc;
                   Qast.VaVal
                     (Qast.List
                        [Qast.Tuple
                           [p; Qast.VaVal (Qast.Option None); e]])]) :
               'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "fun")))
             (Grammar.s_nterm
                (closed_case_list : 'closed_case_list Grammar.Entry.e)),
           (fun (l : 'closed_case_list) _ (loc : Ploc.t) ->
              (Qast.Node ("ExFun", [Qast.Loc; l]) : 'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("", "let")))
                      (Grammar.s_token ("", "open")))
                   (Grammar.s_nterm
                      (module_expr : 'module_expr Grammar.Entry.e)))
                (Grammar.s_token ("", "in")))
             Grammar.s_self,
           (fun (e : 'expr) _ (m : 'module_expr) _ _ (loc : Ploc.t) ->
              (Qast.Node ("ExLop", [Qast.Loc; m; e]) : 'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("", "let")))
                         (Grammar.s_token ("", "module")))
                      (Grammar.s_facto
                         (Grammar.s_rules
                            [Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_nterm
                                     (uidopt : 'uidopt Grammar.Entry.e)),
                                (fun (a : 'uidopt) (loc : Ploc.t) ->
                                   (Qast.VaVal a : 'e__91)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "_uidopt")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaAnt ("_uidopt", loc, a) :
                                    'e__91)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "uidopt")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaVal
                                      (Qast.VaAnt ("uidopt", loc, a)) :
                                    'e__91)))])))
                   (Grammar.s_nterm
                      (mod_fun_binding : 'mod_fun_binding Grammar.Entry.e)))
                (Grammar.s_token ("", "in")))
             Grammar.s_self,
           (fun (e : 'expr) _ (mb : 'mod_fun_binding) (m : 'e__91) _ _
                (loc : Ploc.t) ->
              (Qast.Node ("ExLmd", [Qast.Loc; m; mb; e]) : 'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("", "let")))
                      (Grammar.s_facto
                         (Grammar.s_rules
                            [Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_flag
                                     (Grammar.s_token ("", "rec"))),
                                (fun (a : bool) (loc : Ploc.t) ->
                                   (Qast.VaVal (Qast.Bool a) : 'e__89)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "_opt")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaAnt ("_opt", loc, a) : 'e__89)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "opt")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaVal (Qast.VaAnt ("opt", loc, a)) :
                                    'e__89)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "_flag")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaAnt ("_flag", loc, a) : 'e__89)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "flag")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaVal (Qast.VaAnt ("flag", loc, a)) :
                                    'e__89)))])))
                   (Grammar.s_facto
                      (Grammar.s_rules
                         [Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_list1sep
                                  (Grammar.s_nterm
                                     (let_binding :
                                      'let_binding Grammar.Entry.e))
                                  (Grammar.s_token ("", "and")) false),
                             (fun (a : 'let_binding list) (loc : Ploc.t) ->
                                (Qast.VaVal (Qast.List a) : 'e__90)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "_list")),
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaAnt ("_list", loc, a) : 'e__90)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "list")),
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                                 'e__90)))])))
                (Grammar.s_token ("", "in")))
             Grammar.s_self,
           (fun (x : 'expr) _ (l : 'e__90) (r : 'e__89) _ (loc : Ploc.t) ->
              (Qast.Node ("ExLet", [Qast.Loc; r; l; x]) : 'expr)))];
       Some "where", None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                   (Grammar.s_token ("", "where")))
                (Grammar.s_facto
                   (Grammar.s_rules
                      [Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_flag (Grammar.s_token ("", "rec"))),
                          (fun (a : bool) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.Bool a) : 'e__97)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_opt")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_opt", loc, a) : 'e__97)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "opt")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("opt", loc, a)) :
                              'e__97)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_flag")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_flag", loc, a) : 'e__97)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "flag")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("flag", loc, a)) :
                              'e__97)))])))
             (Grammar.s_nterm (let_binding : 'let_binding Grammar.Entry.e)),
           (fun (lb : 'let_binding) (rf : 'e__97) _ (e : 'expr)
                (loc : Ploc.t) ->
              (Qast.Node
                 ("ExLet", [Qast.Loc; rf; Qast.VaVal (Qast.List [lb]); e]) :
               'expr)))];
       Some ":=", Some Gramext.NonA,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                   (Grammar.s_token ("", ":=")))
                Grammar.s_self)
             (Grammar.s_nterm (dummy : 'dummy Grammar.Entry.e)),
           (fun _ (e2 : 'expr) _ (e1 : 'expr) (loc : Ploc.t) ->
              (Qast.Node ("ExAss", [Qast.Loc; e1; e2]) : 'expr)))];
       Some "||", Some Gramext.RightA,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                (Grammar.s_token ("", "||")))
             Grammar.s_self,
           (fun (e2 : 'expr) _ (e1 : 'expr) (loc : Ploc.t) ->
              (Qast.Node
                 ("ExApp",
                  [Qast.Loc;
                   Qast.Node
                     ("ExApp",
                      [Qast.Loc;
                       Qast.Node
                         ("ExLid", [Qast.Loc; Qast.VaVal (Qast.Str "||")]);
                       e1]);
                   e2]) :
               'expr)))];
       Some "&&", Some Gramext.RightA,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                (Grammar.s_token ("", "&&")))
             Grammar.s_self,
           (fun (e2 : 'expr) _ (e1 : 'expr) (loc : Ploc.t) ->
              (Qast.Node
                 ("ExApp",
                  [Qast.Loc;
                   Qast.Node
                     ("ExApp",
                      [Qast.Loc;
                       Qast.Node
                         ("ExLid", [Qast.Loc; Qast.VaVal (Qast.Str "&&")]);
                       e1]);
                   e2]) :
               'expr)))];
       Some "<", Some Gramext.LeftA,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                (Grammar.s_token ("", "!=")))
             Grammar.s_self,
           (fun (e2 : 'expr) _ (e1 : 'expr) (loc : Ploc.t) ->
              (Qast.Node
                 ("ExApp",
                  [Qast.Loc;
                   Qast.Node
                     ("ExApp",
                      [Qast.Loc;
                       Qast.Node
                         ("ExLid", [Qast.Loc; Qast.VaVal (Qast.Str "!=")]);
                       e1]);
                   e2]) :
               'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                (Grammar.s_token ("", "==")))
             Grammar.s_self,
           (fun (e2 : 'expr) _ (e1 : 'expr) (loc : Ploc.t) ->
              (Qast.Node
                 ("ExApp",
                  [Qast.Loc;
                   Qast.Node
                     ("ExApp",
                      [Qast.Loc;
                       Qast.Node
                         ("ExLid", [Qast.Loc; Qast.VaVal (Qast.Str "==")]);
                       e1]);
                   e2]) :
               'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                (Grammar.s_token ("", "<>")))
             Grammar.s_self,
           (fun (e2 : 'expr) _ (e1 : 'expr) (loc : Ploc.t) ->
              (Qast.Node
                 ("ExApp",
                  [Qast.Loc;
                   Qast.Node
                     ("ExApp",
                      [Qast.Loc;
                       Qast.Node
                         ("ExLid", [Qast.Loc; Qast.VaVal (Qast.Str "<>")]);
                       e1]);
                   e2]) :
               'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                (Grammar.s_token ("", "=")))
             Grammar.s_self,
           (fun (e2 : 'expr) _ (e1 : 'expr) (loc : Ploc.t) ->
              (Qast.Node
                 ("ExApp",
                  [Qast.Loc;
                   Qast.Node
                     ("ExApp",
                      [Qast.Loc;
                       Qast.Node
                         ("ExLid", [Qast.Loc; Qast.VaVal (Qast.Str "=")]);
                       e1]);
                   e2]) :
               'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                (Grammar.s_token ("", ">=")))
             Grammar.s_self,
           (fun (e2 : 'expr) _ (e1 : 'expr) (loc : Ploc.t) ->
              (Qast.Node
                 ("ExApp",
                  [Qast.Loc;
                   Qast.Node
                     ("ExApp",
                      [Qast.Loc;
                       Qast.Node
                         ("ExLid", [Qast.Loc; Qast.VaVal (Qast.Str ">=")]);
                       e1]);
                   e2]) :
               'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                (Grammar.s_token ("", "<=")))
             Grammar.s_self,
           (fun (e2 : 'expr) _ (e1 : 'expr) (loc : Ploc.t) ->
              (Qast.Node
                 ("ExApp",
                  [Qast.Loc;
                   Qast.Node
                     ("ExApp",
                      [Qast.Loc;
                       Qast.Node
                         ("ExLid", [Qast.Loc; Qast.VaVal (Qast.Str "<=")]);
                       e1]);
                   e2]) :
               'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                (Grammar.s_token ("", ">")))
             Grammar.s_self,
           (fun (e2 : 'expr) _ (e1 : 'expr) (loc : Ploc.t) ->
              (Qast.Node
                 ("ExApp",
                  [Qast.Loc;
                   Qast.Node
                     ("ExApp",
                      [Qast.Loc;
                       Qast.Node
                         ("ExLid", [Qast.Loc; Qast.VaVal (Qast.Str ">")]);
                       e1]);
                   e2]) :
               'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                (Grammar.s_token ("", "<")))
             Grammar.s_self,
           (fun (e2 : 'expr) _ (e1 : 'expr) (loc : Ploc.t) ->
              (Qast.Node
                 ("ExApp",
                  [Qast.Loc;
                   Qast.Node
                     ("ExApp",
                      [Qast.Loc;
                       Qast.Node
                         ("ExLid", [Qast.Loc; Qast.VaVal (Qast.Str "<")]);
                       e1]);
                   e2]) :
               'expr)))];
       Some "^", Some Gramext.RightA,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                (Grammar.s_token ("", "@")))
             Grammar.s_self,
           (fun (e2 : 'expr) _ (e1 : 'expr) (loc : Ploc.t) ->
              (Qast.Node
                 ("ExApp",
                  [Qast.Loc;
                   Qast.Node
                     ("ExApp",
                      [Qast.Loc;
                       Qast.Node
                         ("ExLid", [Qast.Loc; Qast.VaVal (Qast.Str "@")]);
                       e1]);
                   e2]) :
               'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                (Grammar.s_token ("", "^")))
             Grammar.s_self,
           (fun (e2 : 'expr) _ (e1 : 'expr) (loc : Ploc.t) ->
              (Qast.Node
                 ("ExApp",
                  [Qast.Loc;
                   Qast.Node
                     ("ExApp",
                      [Qast.Loc;
                       Qast.Node
                         ("ExLid", [Qast.Loc; Qast.VaVal (Qast.Str "^")]);
                       e1]);
                   e2]) :
               'expr)))];
       Some "alg_attribute", Some Gramext.LeftA,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                   (Grammar.s_token ("", "[@")))
                (Grammar.s_facto
                   (Grammar.s_rules
                      [Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_nterm
                               (attribute_body :
                                'attribute_body Grammar.Entry.e)),
                          (fun (a : 'attribute_body) (loc : Ploc.t) ->
                             (Qast.VaVal a : 'e__98)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_attribute")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_attribute", loc, a) : 'e__98)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "attribute")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("attribute", loc, a)) :
                              'e__98)))])))
             (Grammar.s_token ("", "]")),
           (fun _ (attr : 'e__98) _ (e : 'expr) (loc : Ploc.t) ->
              (Qast.Node ("ExAtt", [Qast.Loc; e; attr]) : 'expr)))];
       Some "+", Some Gramext.LeftA,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                (Grammar.s_token ("", "-.")))
             Grammar.s_self,
           (fun (e2 : 'expr) _ (e1 : 'expr) (loc : Ploc.t) ->
              (Qast.Node
                 ("ExApp",
                  [Qast.Loc;
                   Qast.Node
                     ("ExApp",
                      [Qast.Loc;
                       Qast.Node
                         ("ExLid", [Qast.Loc; Qast.VaVal (Qast.Str "-.")]);
                       e1]);
                   e2]) :
               'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                (Grammar.s_token ("", "+.")))
             Grammar.s_self,
           (fun (e2 : 'expr) _ (e1 : 'expr) (loc : Ploc.t) ->
              (Qast.Node
                 ("ExApp",
                  [Qast.Loc;
                   Qast.Node
                     ("ExApp",
                      [Qast.Loc;
                       Qast.Node
                         ("ExLid", [Qast.Loc; Qast.VaVal (Qast.Str "+.")]);
                       e1]);
                   e2]) :
               'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                (Grammar.s_token ("", "-")))
             Grammar.s_self,
           (fun (e2 : 'expr) _ (e1 : 'expr) (loc : Ploc.t) ->
              (Qast.Node
                 ("ExApp",
                  [Qast.Loc;
                   Qast.Node
                     ("ExApp",
                      [Qast.Loc;
                       Qast.Node
                         ("ExLid", [Qast.Loc; Qast.VaVal (Qast.Str "-")]);
                       e1]);
                   e2]) :
               'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                (Grammar.s_token ("", "+")))
             Grammar.s_self,
           (fun (e2 : 'expr) _ (e1 : 'expr) (loc : Ploc.t) ->
              (Qast.Node
                 ("ExApp",
                  [Qast.Loc;
                   Qast.Node
                     ("ExApp",
                      [Qast.Loc;
                       Qast.Node
                         ("ExLid", [Qast.Loc; Qast.VaVal (Qast.Str "+")]);
                       e1]);
                   e2]) :
               'expr)))];
       Some "*", Some Gramext.LeftA,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                (Grammar.s_token ("", "mod")))
             Grammar.s_self,
           (fun (e2 : 'expr) _ (e1 : 'expr) (loc : Ploc.t) ->
              (Qast.Node
                 ("ExApp",
                  [Qast.Loc;
                   Qast.Node
                     ("ExApp",
                      [Qast.Loc;
                       Qast.Node
                         ("ExLid", [Qast.Loc; Qast.VaVal (Qast.Str "mod")]);
                       e1]);
                   e2]) :
               'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                (Grammar.s_token ("", "lxor")))
             Grammar.s_self,
           (fun (e2 : 'expr) _ (e1 : 'expr) (loc : Ploc.t) ->
              (Qast.Node
                 ("ExApp",
                  [Qast.Loc;
                   Qast.Node
                     ("ExApp",
                      [Qast.Loc;
                       Qast.Node
                         ("ExLid", [Qast.Loc; Qast.VaVal (Qast.Str "lxor")]);
                       e1]);
                   e2]) :
               'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                (Grammar.s_token ("", "lor")))
             Grammar.s_self,
           (fun (e2 : 'expr) _ (e1 : 'expr) (loc : Ploc.t) ->
              (Qast.Node
                 ("ExApp",
                  [Qast.Loc;
                   Qast.Node
                     ("ExApp",
                      [Qast.Loc;
                       Qast.Node
                         ("ExLid", [Qast.Loc; Qast.VaVal (Qast.Str "lor")]);
                       e1]);
                   e2]) :
               'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                (Grammar.s_token ("", "land")))
             Grammar.s_self,
           (fun (e2 : 'expr) _ (e1 : 'expr) (loc : Ploc.t) ->
              (Qast.Node
                 ("ExApp",
                  [Qast.Loc;
                   Qast.Node
                     ("ExApp",
                      [Qast.Loc;
                       Qast.Node
                         ("ExLid", [Qast.Loc; Qast.VaVal (Qast.Str "land")]);
                       e1]);
                   e2]) :
               'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                (Grammar.s_token ("", "/.")))
             Grammar.s_self,
           (fun (e2 : 'expr) _ (e1 : 'expr) (loc : Ploc.t) ->
              (Qast.Node
                 ("ExApp",
                  [Qast.Loc;
                   Qast.Node
                     ("ExApp",
                      [Qast.Loc;
                       Qast.Node
                         ("ExLid", [Qast.Loc; Qast.VaVal (Qast.Str "/.")]);
                       e1]);
                   e2]) :
               'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                (Grammar.s_token ("", "*.")))
             Grammar.s_self,
           (fun (e2 : 'expr) _ (e1 : 'expr) (loc : Ploc.t) ->
              (Qast.Node
                 ("ExApp",
                  [Qast.Loc;
                   Qast.Node
                     ("ExApp",
                      [Qast.Loc;
                       Qast.Node
                         ("ExLid", [Qast.Loc; Qast.VaVal (Qast.Str "*.")]);
                       e1]);
                   e2]) :
               'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                (Grammar.s_token ("", "/")))
             Grammar.s_self,
           (fun (e2 : 'expr) _ (e1 : 'expr) (loc : Ploc.t) ->
              (Qast.Node
                 ("ExApp",
                  [Qast.Loc;
                   Qast.Node
                     ("ExApp",
                      [Qast.Loc;
                       Qast.Node
                         ("ExLid", [Qast.Loc; Qast.VaVal (Qast.Str "/")]);
                       e1]);
                   e2]) :
               'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                (Grammar.s_token ("", "*")))
             Grammar.s_self,
           (fun (e2 : 'expr) _ (e1 : 'expr) (loc : Ploc.t) ->
              (Qast.Node
                 ("ExApp",
                  [Qast.Loc;
                   Qast.Node
                     ("ExApp",
                      [Qast.Loc;
                       Qast.Node
                         ("ExLid", [Qast.Loc; Qast.VaVal (Qast.Str "*")]);
                       e1]);
                   e2]) :
               'expr)))];
       Some "**", Some Gramext.RightA,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                (Grammar.s_token ("", "lsr")))
             Grammar.s_self,
           (fun (e2 : 'expr) _ (e1 : 'expr) (loc : Ploc.t) ->
              (Qast.Node
                 ("ExApp",
                  [Qast.Loc;
                   Qast.Node
                     ("ExApp",
                      [Qast.Loc;
                       Qast.Node
                         ("ExLid", [Qast.Loc; Qast.VaVal (Qast.Str "lsr")]);
                       e1]);
                   e2]) :
               'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                (Grammar.s_token ("", "lsl")))
             Grammar.s_self,
           (fun (e2 : 'expr) _ (e1 : 'expr) (loc : Ploc.t) ->
              (Qast.Node
                 ("ExApp",
                  [Qast.Loc;
                   Qast.Node
                     ("ExApp",
                      [Qast.Loc;
                       Qast.Node
                         ("ExLid", [Qast.Loc; Qast.VaVal (Qast.Str "lsl")]);
                       e1]);
                   e2]) :
               'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                (Grammar.s_token ("", "asr")))
             Grammar.s_self,
           (fun (e2 : 'expr) _ (e1 : 'expr) (loc : Ploc.t) ->
              (Qast.Node
                 ("ExApp",
                  [Qast.Loc;
                   Qast.Node
                     ("ExApp",
                      [Qast.Loc;
                       Qast.Node
                         ("ExLid", [Qast.Loc; Qast.VaVal (Qast.Str "asr")]);
                       e1]);
                   e2]) :
               'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                (Grammar.s_token ("", "**")))
             Grammar.s_self,
           (fun (e2 : 'expr) _ (e1 : 'expr) (loc : Ploc.t) ->
              (Qast.Node
                 ("ExApp",
                  [Qast.Loc;
                   Qast.Node
                     ("ExApp",
                      [Qast.Loc;
                       Qast.Node
                         ("ExLid", [Qast.Loc; Qast.VaVal (Qast.Str "**")]);
                       e1]);
                   e2]) :
               'expr)))];
       Some "unary minus", Some Gramext.NonA,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "-.")))
             Grammar.s_self,
           (fun (e : 'expr) _ (loc : Ploc.t) ->
              (Qast.Node
                 ("ExApp",
                  [Qast.Loc;
                   Qast.Node
                     ("ExLid", [Qast.Loc; Qast.VaVal (Qast.Str "-.")]);
                   e]) :
               'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "-")))
             Grammar.s_self,
           (fun (e : 'expr) _ (loc : Ploc.t) ->
              (Qast.Node
                 ("ExApp",
                  [Qast.Loc;
                   Qast.Node ("ExLid", [Qast.Loc; Qast.VaVal (Qast.Str "-")]);
                   e]) :
               'expr)))];
       Some "apply", Some Gramext.LeftA,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "lazy")))
             Grammar.s_self,
           (fun (e : 'expr) _ (loc : Ploc.t) ->
              (Qast.Node ("ExLaz", [Qast.Loc; e]) : 'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "assert")))
             Grammar.s_self,
           (fun (e : 'expr) _ (loc : Ploc.t) ->
              (Qast.Node ("ExAsr", [Qast.Loc; e]) : 'expr)));
        Grammar.production
          (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
             Grammar.s_self,
           (fun (e2 : 'expr) (e1 : 'expr) (loc : Ploc.t) ->
              (Qast.Node ("ExApp", [Qast.Loc; e1; e2]) : 'expr)))];
       Some ".", Some Gramext.LeftA,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                (Grammar.s_token ("", ".")))
             Grammar.s_self,
           (fun (e2 : 'expr) _ (e1 : 'expr) (loc : Ploc.t) ->
              (Qast.Node ("ExAcc", [Qast.Loc; e1; e2]) : 'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next Grammar.r_stop Grammar.s_self)
                      (Grammar.s_token ("", ".")))
                   (Grammar.s_token ("", "{")))
                (Grammar.s_facto
                   (Grammar.s_rules
                      [Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_list1sep
                               (Grammar.s_nterm
                                  (expr : 'expr Grammar.Entry.e))
                               (Grammar.s_token ("", ",")) false),
                          (fun (a : 'expr list) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.List a) : 'e__99)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_list")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_list", loc, a) : 'e__99)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "list")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                              'e__99)))])))
             (Grammar.s_token ("", "}")),
           (fun _ (el : 'e__99) _ _ (e : 'expr) (loc : Ploc.t) ->
              (Qast.Node ("ExBae", [Qast.Loc; e; el]) : 'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next Grammar.r_stop Grammar.s_self)
                      (Grammar.s_token ("", ".")))
                   (Grammar.s_token ("", "[")))
                Grammar.s_self)
             (Grammar.s_token ("", "]")),
           (fun _ (e2 : 'expr) _ _ (e1 : 'expr) (loc : Ploc.t) ->
              (Qast.Node ("ExSte", [Qast.Loc; e1; e2]) : 'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next Grammar.r_stop Grammar.s_self)
                      (Grammar.s_token ("", ".")))
                   (Grammar.s_token ("", "(")))
                Grammar.s_self)
             (Grammar.s_token ("", ")")),
           (fun _ (e2 : 'expr) _ _ (e1 : 'expr) (loc : Ploc.t) ->
              (Qast.Node ("ExAre", [Qast.Loc; e1; e2]) : 'expr)))];
       Some "~-", Some Gramext.NonA,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "~-.")))
             Grammar.s_self,
           (fun (e : 'expr) _ (loc : Ploc.t) ->
              (Qast.Node
                 ("ExApp",
                  [Qast.Loc;
                   Qast.Node
                     ("ExLid", [Qast.Loc; Qast.VaVal (Qast.Str "~-.")]);
                   e]) :
               'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "~-")))
             Grammar.s_self,
           (fun (e : 'expr) _ (loc : Ploc.t) ->
              (Qast.Node
                 ("ExApp",
                  [Qast.Loc;
                   Qast.Node
                     ("ExLid", [Qast.Loc; Qast.VaVal (Qast.Str "~-")]);
                   e]) :
               'expr)))];
       Some "simple", None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "(")))
                (Grammar.s_facto
                   (Grammar.s_rules
                      [Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_list1sep
                               (Grammar.s_nterm
                                  (expr : 'expr Grammar.Entry.e))
                               (Grammar.s_token ("", ",")) false),
                          (fun (a : 'expr list) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.List a) : 'e__113)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_list")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_list", loc, a) : 'e__113)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "list")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                              'e__113)))])))
             (Grammar.s_token ("", ")")),
           (fun _ (el : 'e__113) _ (loc : Ploc.t) ->
              (Qast.Node ("ExTup", [Qast.Loc; el]) : 'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "(")))
                Grammar.s_self)
             (Grammar.s_token ("", ")")),
           (fun _ (e : 'expr) _ (loc : Ploc.t) -> (e : 'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("", "(")))
                      Grammar.s_self)
                   (Grammar.s_token ("", ",")))
                (Grammar.s_list1sep
                   (Grammar.s_nterm (expr : 'expr Grammar.Entry.e))
                   (Grammar.s_token ("", ",")) false))
             (Grammar.s_token ("", ")")),
           (fun _ (el : 'expr list) _ (e : 'expr) _ (loc : Ploc.t) ->
              (mktupexp Qast.Loc e el : 'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("", "(")))
                      Grammar.s_self)
                   (Grammar.s_token ("", ":")))
                (Grammar.s_nterm (ctyp : 'ctyp Grammar.Entry.e)))
             (Grammar.s_token ("", ")")),
           (fun _ (t : 'ctyp) _ (e : 'expr) _ (loc : Ploc.t) ->
              (Qast.Node ("ExTyc", [Qast.Loc; e; t]) : 'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "(")))
                   (Grammar.s_token ("", "module")))
                (Grammar.s_nterm
                   (module_expr : 'module_expr Grammar.Entry.e)))
             (Grammar.s_token ("", ")")),
           (fun _ (me : 'module_expr) _ _ (loc : Ploc.t) ->
              (Qast.Node ("ExPck", [Qast.Loc; me; Qast.Option None]) :
               'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("", "(")))
                         (Grammar.s_token ("", "module")))
                      (Grammar.s_nterm
                         (module_expr : 'module_expr Grammar.Entry.e)))
                   (Grammar.s_token ("", ":")))
                (Grammar.s_nterm
                   (module_type : 'module_type Grammar.Entry.e)))
             (Grammar.s_token ("", ")")),
           (fun _ (mt : 'module_type) _ (me : 'module_expr) _ _
                (loc : Ploc.t) ->
              (Qast.Node ("ExPck", [Qast.Loc; me; Qast.Option (Some mt)]) :
               'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "(")))
             (Grammar.s_token ("", ")")),
           (fun _ _ (loc : Ploc.t) ->
              (Qast.Node ("ExUid", [Qast.Loc; Qast.VaVal (Qast.Str "()")]) :
               'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next
                         (Grammar.r_next
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("", "{")))
                            (Grammar.s_token ("", "(")))
                         Grammar.s_self)
                      (Grammar.s_token ("", ")")))
                   (Grammar.s_token ("", "with")))
                (Grammar.s_facto
                   (Grammar.s_rules
                      [Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_list1sep
                               (Grammar.s_nterm
                                  (label_expr : 'label_expr Grammar.Entry.e))
                               (Grammar.s_token ("", ";")) false),
                          (fun (a : 'label_expr list) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.List a) : 'e__112)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_list")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_list", loc, a) : 'e__112)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "list")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                              'e__112)))])))
             (Grammar.s_token ("", "}")),
           (fun _ (lel : 'e__112) _ _ (e : 'expr) _ _ (loc : Ploc.t) ->
              (Qast.Node ("ExRec", [Qast.Loc; lel; Qast.Option (Some e)]) :
               'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "{")))
                (Grammar.s_facto
                   (Grammar.s_rules
                      [Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_list1sep
                               (Grammar.s_nterm
                                  (label_expr : 'label_expr Grammar.Entry.e))
                               (Grammar.s_token ("", ";")) false),
                          (fun (a : 'label_expr list) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.List a) : 'e__111)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_list")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_list", loc, a) : 'e__111)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "list")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                              'e__111)))])))
             (Grammar.s_token ("", "}")),
           (fun _ (lel : 'e__111) _ (loc : Ploc.t) ->
              (Qast.Node ("ExRec", [Qast.Loc; lel; Qast.Option None]) :
               'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "[|")))
                (Grammar.s_facto
                   (Grammar.s_rules
                      [Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_list0sep
                               (Grammar.s_nterm
                                  (expr : 'expr Grammar.Entry.e))
                               (Grammar.s_token ("", ";")) false),
                          (fun (a : 'expr list) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.List a) : 'e__110)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_list")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_list", loc, a) : 'e__110)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "list")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                              'e__110)))])))
             (Grammar.s_token ("", "|]")),
           (fun _ (el : 'e__110) _ (loc : Ploc.t) ->
              (Qast.Node ("ExArr", [Qast.Loc; el]) : 'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "[")))
                   (Grammar.s_list1sep
                      (Grammar.s_nterm (expr : 'expr Grammar.Entry.e))
                      (Grammar.s_token ("", ";")) false))
                (Grammar.s_nterm
                   (cons_expr_opt : 'cons_expr_opt Grammar.Entry.e)))
             (Grammar.s_token ("", "]")),
           (fun _ (last : 'cons_expr_opt) (el : 'expr list) _
                (loc : Ploc.t) ->
              (mklistexp Qast.Loc last el : 'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "[")))
             (Grammar.s_token ("", "]")),
           (fun _ _ (loc : Ploc.t) ->
              (Qast.Node ("ExUid", [Qast.Loc; Qast.VaVal (Qast.Str "[]")]) :
               'expr)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("UIDENT", "")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.Str a) : 'e__109)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_", loc, a) : 'e__109)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("", loc, a)) : 'e__109)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_uid")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_uid", loc, a) : 'e__109)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "uid")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("uid", loc, a)) :
                           'e__109)))])),
           (fun (i : 'e__109) (loc : Ploc.t) ->
              (Qast.Node ("ExUid", [Qast.Loc; i]) : 'expr)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("GIDENT", "")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.Str a) : 'e__108)))])),
           (fun (i : 'e__108) (loc : Ploc.t) ->
              (Qast.Node ("ExLid", [Qast.Loc; i]) : 'expr)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("LIDENT", "")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.Str a) : 'e__107)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_", loc, a) : 'e__107)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("", loc, a)) : 'e__107)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_lid")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_lid", loc, a) : 'e__107)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "lid")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("lid", loc, a)) :
                           'e__107)))])),
           (fun (i : 'e__107) (loc : Ploc.t) ->
              (Qast.Node ("ExLid", [Qast.Loc; i]) : 'expr)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("CHAR", "")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.Str a) : 'e__106)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_chr")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_chr", loc, a) : 'e__106)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "chr")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("chr", loc, a)) :
                           'e__106)))])),
           (fun (s : 'e__106) (loc : Ploc.t) ->
              (Qast.Node ("ExChr", [Qast.Loc; s]) : 'expr)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("STRING", "")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.Str a) : 'e__105)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_str")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_str", loc, a) : 'e__105)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "str")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("str", loc, a)) :
                           'e__105)))])),
           (fun (s : 'e__105) (loc : Ploc.t) ->
              (Qast.Node ("ExStr", [Qast.Loc; s]) : 'expr)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("FLOAT", "")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.Str a) : 'e__104)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_flo")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_flo", loc, a) : 'e__104)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "flo")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("flo", loc, a)) :
                           'e__104)))])),
           (fun (s : 'e__104) (loc : Ploc.t) ->
              (Qast.Node ("ExFlo", [Qast.Loc; s]) : 'expr)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("INT_n", "")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.Str a) : 'e__103)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_nativeint")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_nativeint", loc, a) : 'e__103)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "nativeint")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("nativeint", loc, a)) :
                           'e__103)))])),
           (fun (s : 'e__103) (loc : Ploc.t) ->
              (Qast.Node ("ExInt", [Qast.Loc; s; Qast.Str "n"]) : 'expr)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("INT_L", "")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.Str a) : 'e__102)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_int64")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_int64", loc, a) : 'e__102)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "int64")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("int64", loc, a)) :
                           'e__102)))])),
           (fun (s : 'e__102) (loc : Ploc.t) ->
              (Qast.Node ("ExInt", [Qast.Loc; s; Qast.Str "L"]) : 'expr)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("INT_l", "")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.Str a) : 'e__101)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_int32")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_int32", loc, a) : 'e__101)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "int32")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("int32", loc, a)) :
                           'e__101)))])),
           (fun (s : 'e__101) (loc : Ploc.t) ->
              (Qast.Node ("ExInt", [Qast.Loc; s; Qast.Str "l"]) : 'expr)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("INT", "")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.Str a) : 'e__100)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_int")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_int", loc, a) : 'e__100)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "int")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("int", loc, a)) :
                           'e__100)))])),
           (fun (s : 'e__100) (loc : Ploc.t) ->
              (Qast.Node ("ExInt", [Qast.Loc; s; Qast.Str ""]) : 'expr)))]];
    Grammar.extension (closed_case_list : 'closed_case_list Grammar.Entry.e)
      None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "|")))
                (Grammar.s_facto
                   (Grammar.s_rules
                      [Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_list0sep
                               (Grammar.s_nterm
                                  (match_case : 'match_case Grammar.Entry.e))
                               (Grammar.s_token ("", "|")) false),
                          (fun (a : 'match_case list) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.List a) : 'e__115)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_list")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_list", loc, a) : 'e__115)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "list")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                              'e__115)))])))
             (Grammar.s_token ("", "end")),
           (fun _ (l : 'e__115) _ (loc : Ploc.t) -> (l : 'closed_case_list)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "[")))
                (Grammar.s_facto
                   (Grammar.s_rules
                      [Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_list0sep
                               (Grammar.s_nterm
                                  (match_case : 'match_case Grammar.Entry.e))
                               (Grammar.s_token ("", "|")) false),
                          (fun (a : 'match_case list) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.List a) : 'e__114)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_list")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_list", loc, a) : 'e__114)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "list")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                              'e__114)))])))
             (Grammar.s_token ("", "]")),
           (fun _ (l : 'e__114) _ (loc : Ploc.t) ->
              (l : 'closed_case_list)))]];
    Grammar.extension (cons_expr_opt : 'cons_expr_opt Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_stop,
           (fun (loc : Ploc.t) -> (Qast.Option None : 'cons_expr_opt)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "::")))
             (Grammar.s_nterm (expr : 'expr Grammar.Entry.e)),
           (fun (e : 'expr) _ (loc : Ploc.t) ->
              (Qast.Option (Some e) : 'cons_expr_opt)))]];
    Grammar.extension (dummy : 'dummy Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_stop, (fun (loc : Ploc.t) -> (() : 'dummy)))]];
    Grammar.extension (sequence : 'sequence Grammar.Entry.e) None
      [None, Some Gramext.RightA,
       [Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_nterm (expr : 'expr Grammar.Entry.e)),
           (fun (e : 'expr) (loc : Ploc.t) -> (Qast.List [e] : 'sequence)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop
                (Grammar.s_nterm (expr : 'expr Grammar.Entry.e)))
             (Grammar.s_token ("", ";")),
           (fun _ (e : 'expr) (loc : Ploc.t) -> (Qast.List [e] : 'sequence)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop
                   (Grammar.s_nterm (expr : 'expr Grammar.Entry.e)))
                (Grammar.s_token ("", ";")))
             Grammar.s_self,
           (fun (el : 'sequence) _ (e : 'expr) (loc : Ploc.t) ->
              (Qast.Cons (e, el) : 'sequence)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("", "let")))
                      (Grammar.s_token ("", "open")))
                   (Grammar.s_nterm
                      (module_expr : 'module_expr Grammar.Entry.e)))
                (Grammar.s_token ("", "in")))
             Grammar.s_self,
           (fun (el : 'sequence) _ (m : 'module_expr) _ _ (loc : Ploc.t) ->
              (Qast.List
                 [Qast.Node
                    ("ExLop", [Qast.Loc; m; mksequence Qast.Loc el])] :
               'sequence)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("", "let")))
                         (Grammar.s_token ("", "module")))
                      (Grammar.s_facto
                         (Grammar.s_rules
                            [Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_nterm
                                     (uidopt : 'uidopt Grammar.Entry.e)),
                                (fun (a : 'uidopt) (loc : Ploc.t) ->
                                   (Qast.VaVal a : 'e__118)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "_uidopt")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaAnt ("_uidopt", loc, a) :
                                    'e__118)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "uidopt")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaVal
                                      (Qast.VaAnt ("uidopt", loc, a)) :
                                    'e__118)))])))
                   (Grammar.s_nterm
                      (mod_fun_binding : 'mod_fun_binding Grammar.Entry.e)))
                (Grammar.s_token ("", "in")))
             Grammar.s_self,
           (fun (el : 'sequence) _ (mb : 'mod_fun_binding) (m : 'e__118) _ _
                (loc : Ploc.t) ->
              (Qast.List
                 [Qast.Node
                    ("ExLmd", [Qast.Loc; m; mb; mksequence Qast.Loc el])] :
               'sequence)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("", "let")))
                      (Grammar.s_facto
                         (Grammar.s_rules
                            [Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_flag
                                     (Grammar.s_token ("", "rec"))),
                                (fun (a : bool) (loc : Ploc.t) ->
                                   (Qast.VaVal (Qast.Bool a) : 'e__116)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "_opt")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaAnt ("_opt", loc, a) : 'e__116)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "opt")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaVal (Qast.VaAnt ("opt", loc, a)) :
                                    'e__116)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "_flag")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaAnt ("_flag", loc, a) : 'e__116)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "flag")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaVal (Qast.VaAnt ("flag", loc, a)) :
                                    'e__116)))])))
                   (Grammar.s_facto
                      (Grammar.s_rules
                         [Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_list1sep
                                  (Grammar.s_nterm
                                     (let_binding :
                                      'let_binding Grammar.Entry.e))
                                  (Grammar.s_token ("", "and")) false),
                             (fun (a : 'let_binding list) (loc : Ploc.t) ->
                                (Qast.VaVal (Qast.List a) : 'e__117)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "_list")),
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaAnt ("_list", loc, a) : 'e__117)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "list")),
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                                 'e__117)))])))
                (Grammar.s_token ("", "in")))
             Grammar.s_self,
           (fun (el : 'sequence) _ (l : 'e__117) (rf : 'e__116) _
                (loc : Ploc.t) ->
              (Qast.List
                 [Qast.Node
                    ("ExLet", [Qast.Loc; rf; l; mksequence Qast.Loc el])] :
               'sequence)))]];
    Grammar.extension (let_binding : 'let_binding Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop
                (Grammar.s_nterm (ipatt : 'ipatt Grammar.Entry.e)))
             (Grammar.s_nterm (fun_binding : 'fun_binding Grammar.Entry.e)),
           (fun (e : 'fun_binding) (p : 'ipatt) (loc : Ploc.t) ->
              (Qast.Tuple [p; e] : 'let_binding)))]];
    Grammar.extension (fun_binding : 'fun_binding Grammar.Entry.e) None
      [None, Some Gramext.RightA,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", ":")))
                   (Grammar.s_nterm (ctyp : 'ctyp Grammar.Entry.e)))
                (Grammar.s_token ("", "=")))
             (Grammar.s_nterm (expr : 'expr Grammar.Entry.e)),
           (fun (e : 'expr) _ (t : 'ctyp) _ (loc : Ploc.t) ->
              (Qast.Node ("ExTyc", [Qast.Loc; e; t]) : 'fun_binding)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "=")))
             (Grammar.s_nterm (expr : 'expr Grammar.Entry.e)),
           (fun (e : 'expr) _ (loc : Ploc.t) -> (e : 'fun_binding)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop
                (Grammar.s_nterm (ipatt : 'ipatt Grammar.Entry.e)))
             Grammar.s_self,
           (fun (e : 'fun_binding) (p : 'ipatt) (loc : Ploc.t) ->
              (Qast.Node
                 ("ExFun",
                  [Qast.Loc;
                   Qast.VaVal
                     (Qast.List
                        [Qast.Tuple
                           [p; Qast.VaVal (Qast.Option None); e]])]) :
               'fun_binding)))]];
    Grammar.extension (match_case : 'match_case Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_nterm (patt : 'patt Grammar.Entry.e)))
                      (Grammar.s_nterm
                         (as_patt_opt : 'as_patt_opt Grammar.Entry.e)))
                   (Grammar.s_facto
                      (Grammar.s_rules
                         [Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_opt
                                  (Grammar.s_nterm
                                     (when_expr :
                                      'when_expr Grammar.Entry.e))),
                             (fun (a : 'when_expr option) (loc : Ploc.t) ->
                                (Qast.VaVal (Qast.Option a) : 'e__119)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "_opt")),
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaAnt ("_opt", loc, a) : 'e__119)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "opt")),
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaVal (Qast.VaAnt ("opt", loc, a)) :
                                 'e__119)))])))
                (Grammar.s_token ("", "->")))
             (Grammar.s_nterm (expr : 'expr Grammar.Entry.e)),
           (fun (e : 'expr) _ (w : 'e__119) (aso : 'as_patt_opt) (p : 'patt)
                (loc : Ploc.t) ->
              (mkmatchcase Qast.Loc p aso w e : 'match_case)))]];
    Grammar.extension (as_patt_opt : 'as_patt_opt Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_stop,
           (fun (loc : Ploc.t) -> (Qast.Option None : 'as_patt_opt)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "as")))
             (Grammar.s_nterm (patt : 'patt Grammar.Entry.e)),
           (fun (p : 'patt) _ (loc : Ploc.t) ->
              (Qast.Option (Some p) : 'as_patt_opt)))]];
    Grammar.extension (when_expr : 'when_expr Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "when")))
             (Grammar.s_nterm (expr : 'expr Grammar.Entry.e)),
           (fun (e : 'expr) _ (loc : Ploc.t) -> (e : 'when_expr)))]];
    Grammar.extension (label_expr : 'label_expr Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop
                (Grammar.s_nterm
                   (patt_label_ident : 'patt_label_ident Grammar.Entry.e)))
             (Grammar.s_nterm (fun_binding : 'fun_binding Grammar.Entry.e)),
           (fun (e : 'fun_binding) (i : 'patt_label_ident) (loc : Ploc.t) ->
              (Qast.Tuple [i; e] : 'label_expr)))]];
    Grammar.extension (fun_def : 'fun_def Grammar.Entry.e) None
      [None, Some Gramext.RightA,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "->")))
             (Grammar.s_nterm (expr : 'expr Grammar.Entry.e)),
           (fun (e : 'expr) _ (loc : Ploc.t) -> (e : 'fun_def)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop
                (Grammar.s_nterm (ipatt : 'ipatt Grammar.Entry.e)))
             Grammar.s_self,
           (fun (e : 'fun_def) (p : 'ipatt) (loc : Ploc.t) ->
              (Qast.Node
                 ("ExFun",
                  [Qast.Loc;
                   Qast.VaVal
                     (Qast.List
                        [Qast.Tuple
                           [p; Qast.VaVal (Qast.Option None); e]])]) :
               'fun_def)))]];
    Grammar.extension (patt : 'patt Grammar.Entry.e) None
      [None, Some Gramext.LeftA,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                (Grammar.s_token ("", "|")))
             Grammar.s_self,
           (fun (p2 : 'patt) _ (p1 : 'patt) (loc : Ploc.t) ->
              (Qast.Node ("PaOrp", [Qast.Loc; p1; p2]) : 'patt)))];
       Some "alg_attribute", Some Gramext.LeftA,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                   (Grammar.s_token ("", "[@")))
                (Grammar.s_facto
                   (Grammar.s_rules
                      [Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_nterm
                               (attribute_body :
                                'attribute_body Grammar.Entry.e)),
                          (fun (a : 'attribute_body) (loc : Ploc.t) ->
                             (Qast.VaVal a : 'e__120)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_attribute")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_attribute", loc, a) : 'e__120)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "attribute")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("attribute", loc, a)) :
                              'e__120)))])))
             (Grammar.s_token ("", "]")),
           (fun _ (attr : 'e__120) _ (p1 : 'patt) (loc : Ploc.t) ->
              (Qast.Node ("PaAtt", [Qast.Loc; p1; attr]) : 'patt)))];
       None, Some Gramext.NonA,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                (Grammar.s_token ("", "..")))
             Grammar.s_self,
           (fun (p2 : 'patt) _ (p1 : 'patt) (loc : Ploc.t) ->
              (Qast.Node ("PaRng", [Qast.Loc; p1; p2]) : 'patt)))];
       None, Some Gramext.LeftA,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "lazy")))
             Grammar.s_self,
           (fun (p : 'patt) _ (loc : Ploc.t) ->
              (Qast.Node ("PaLaz", [Qast.Loc; p]) : 'patt)));
        Grammar.production
          (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
             Grammar.s_self,
           (fun (p2 : 'patt) (p1 : 'patt) (loc : Ploc.t) ->
              (Qast.Node ("PaApp", [Qast.Loc; p1; p2]) : 'patt)))];
       None, Some Gramext.LeftA,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                (Grammar.s_token ("", ".")))
             Grammar.s_self,
           (fun (p2 : 'patt) _ (p1 : 'patt) (loc : Ploc.t) ->
              (Qast.Node ("PaAcc", [Qast.Loc; p1; p2]) : 'patt)))];
       Some "simple", None,
       [Grammar.production
          (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "_")),
           (fun _ (loc : Ploc.t) ->
              (Qast.Node ("PaAny", [Qast.Loc]) : 'patt)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "(")))
                (Grammar.s_nterm (paren_patt : 'paren_patt Grammar.Entry.e)))
             (Grammar.s_token ("", ")")),
           (fun _ (p : 'paren_patt) _ (loc : Ploc.t) -> (p : 'patt)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "{")))
                (Grammar.s_facto
                   (Grammar.s_rules
                      [Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_list1sep
                               (Grammar.s_nterm
                                  (label_patt : 'label_patt Grammar.Entry.e))
                               (Grammar.s_token ("", ";")) false),
                          (fun (a : 'label_patt list) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.List a) : 'e__132)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_list")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_list", loc, a) : 'e__132)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "list")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                              'e__132)))])))
             (Grammar.s_token ("", "}")),
           (fun _ (lpl : 'e__132) _ (loc : Ploc.t) ->
              (Qast.Node ("PaRec", [Qast.Loc; lpl]) : 'patt)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "[|")))
                (Grammar.s_facto
                   (Grammar.s_rules
                      [Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_list0sep
                               (Grammar.s_nterm
                                  (patt : 'patt Grammar.Entry.e))
                               (Grammar.s_token ("", ";")) false),
                          (fun (a : 'patt list) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.List a) : 'e__131)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_list")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_list", loc, a) : 'e__131)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "list")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                              'e__131)))])))
             (Grammar.s_token ("", "|]")),
           (fun _ (pl : 'e__131) _ (loc : Ploc.t) ->
              (Qast.Node ("PaArr", [Qast.Loc; pl]) : 'patt)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "[")))
                   (Grammar.s_list1sep
                      (Grammar.s_nterm (patt : 'patt Grammar.Entry.e))
                      (Grammar.s_token ("", ";")) false))
                (Grammar.s_nterm
                   (cons_patt_opt : 'cons_patt_opt Grammar.Entry.e)))
             (Grammar.s_token ("", "]")),
           (fun _ (last : 'cons_patt_opt) (pl : 'patt list) _
                (loc : Ploc.t) ->
              (mklistpat Qast.Loc last pl : 'patt)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "[")))
             (Grammar.s_token ("", "]")),
           (fun _ _ (loc : Ploc.t) ->
              (Qast.Node ("PaUid", [Qast.Loc; Qast.VaVal (Qast.Str "[]")]) :
               'patt)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "-")))
             (Grammar.s_token ("FLOAT", "")),
           (fun (s : string) _ (loc : Ploc.t) ->
              (Qast.Node ("PaFlo", [Qast.Loc; Qast.VaVal (neg_string s)]) :
               'patt)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "-")))
             (Grammar.s_token ("INT_n", "")),
           (fun (s : string) _ (loc : Ploc.t) ->
              (Qast.Node
                 ("PaInt",
                  [Qast.Loc; Qast.VaVal (neg_string s); Qast.Str "n"]) :
               'patt)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "-")))
             (Grammar.s_token ("INT_L", "")),
           (fun (s : string) _ (loc : Ploc.t) ->
              (Qast.Node
                 ("PaInt",
                  [Qast.Loc; Qast.VaVal (neg_string s); Qast.Str "L"]) :
               'patt)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "-")))
             (Grammar.s_token ("INT_l", "")),
           (fun (s : string) _ (loc : Ploc.t) ->
              (Qast.Node
                 ("PaInt",
                  [Qast.Loc; Qast.VaVal (neg_string s); Qast.Str "l"]) :
               'patt)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "-")))
             (Grammar.s_token ("INT", "")),
           (fun (s : string) _ (loc : Ploc.t) ->
              (Qast.Node
                 ("PaInt",
                  [Qast.Loc; Qast.VaVal (neg_string s); Qast.Str ""]) :
               'patt)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("CHAR", "")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.Str a) : 'e__130)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_chr")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_chr", loc, a) : 'e__130)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "chr")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("chr", loc, a)) :
                           'e__130)))])),
           (fun (s : 'e__130) (loc : Ploc.t) ->
              (Qast.Node ("PaChr", [Qast.Loc; s]) : 'patt)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("STRING", "")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.Str a) : 'e__129)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_str")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_str", loc, a) : 'e__129)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "str")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("str", loc, a)) :
                           'e__129)))])),
           (fun (s : 'e__129) (loc : Ploc.t) ->
              (Qast.Node ("PaStr", [Qast.Loc; s]) : 'patt)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("FLOAT", "")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.Str a) : 'e__128)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_flo")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_flo", loc, a) : 'e__128)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "flo")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("flo", loc, a)) :
                           'e__128)))])),
           (fun (s : 'e__128) (loc : Ploc.t) ->
              (Qast.Node ("PaFlo", [Qast.Loc; s]) : 'patt)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("INT_n", "")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.Str a) : 'e__127)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_nativeint")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_nativeint", loc, a) : 'e__127)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "nativeint")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("nativeint", loc, a)) :
                           'e__127)))])),
           (fun (s : 'e__127) (loc : Ploc.t) ->
              (Qast.Node ("PaInt", [Qast.Loc; s; Qast.Str "n"]) : 'patt)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("INT_L", "")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.Str a) : 'e__126)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_int64")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_int64", loc, a) : 'e__126)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "int64")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("int64", loc, a)) :
                           'e__126)))])),
           (fun (s : 'e__126) (loc : Ploc.t) ->
              (Qast.Node ("PaInt", [Qast.Loc; s; Qast.Str "L"]) : 'patt)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("INT_l", "")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.Str a) : 'e__125)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_int32")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_int32", loc, a) : 'e__125)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "int32")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("int32", loc, a)) :
                           'e__125)))])),
           (fun (s : 'e__125) (loc : Ploc.t) ->
              (Qast.Node ("PaInt", [Qast.Loc; s; Qast.Str "l"]) : 'patt)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("INT", "")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.Str a) : 'e__124)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_int")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_int", loc, a) : 'e__124)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "int")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("int", loc, a)) :
                           'e__124)))])),
           (fun (s : 'e__124) (loc : Ploc.t) ->
              (Qast.Node ("PaInt", [Qast.Loc; s; Qast.Str ""]) : 'patt)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("UIDENT", "")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.Str a) : 'e__123)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_", loc, a) : 'e__123)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("", loc, a)) : 'e__123)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_uid")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_uid", loc, a) : 'e__123)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "uid")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("uid", loc, a)) :
                           'e__123)))])),
           (fun (s : 'e__123) (loc : Ploc.t) ->
              (Qast.Node ("PaUid", [Qast.Loc; s]) : 'patt)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("GIDENT", "")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.Str a) : 'e__122)))])),
           (fun (s : 'e__122) (loc : Ploc.t) ->
              (Qast.Node ("PaLid", [Qast.Loc; s]) : 'patt)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("LIDENT", "")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.Str a) : 'e__121)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_", loc, a) : 'e__121)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("", loc, a)) : 'e__121)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_lid")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_lid", loc, a) : 'e__121)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "lid")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("lid", loc, a)) :
                           'e__121)))])),
           (fun (s : 'e__121) (loc : Ploc.t) ->
              (Qast.Node ("PaLid", [Qast.Loc; s]) : 'patt)))]];
    Grammar.extension (paren_patt : 'paren_patt Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_stop,
           (fun (loc : Ploc.t) ->
              (Qast.Node ("PaUid", [Qast.Loc; Qast.VaVal (Qast.Str "()")]) :
               'paren_patt)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "module")))
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_nterm (uidopt : 'uidopt Grammar.Entry.e)),
                       (fun (a : 'uidopt) (loc : Ploc.t) ->
                          (Qast.VaVal a : 'e__136)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_uidopt")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_uidopt", loc, a) : 'e__136)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "uidopt")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("uidopt", loc, a)) :
                           'e__136)))])),
           (fun (s : 'e__136) _ (loc : Ploc.t) ->
              (Qast.Node ("PaUnp", [Qast.Loc; s; Qast.Option None]) :
               'paren_patt)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next Grammar.r_stop
                      (Grammar.s_token ("", "module")))
                   (Grammar.s_facto
                      (Grammar.s_rules
                         [Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_nterm
                                  (uidopt : 'uidopt Grammar.Entry.e)),
                             (fun (a : 'uidopt) (loc : Ploc.t) ->
                                (Qast.VaVal a : 'e__135)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "_uidopt")),
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaAnt ("_uidopt", loc, a) : 'e__135)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "uidopt")),
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaVal (Qast.VaAnt ("uidopt", loc, a)) :
                                 'e__135)))])))
                (Grammar.s_token ("", ":")))
             (Grammar.s_nterm (module_type : 'module_type Grammar.Entry.e)),
           (fun (mt : 'module_type) _ (s : 'e__135) _ (loc : Ploc.t) ->
              (Qast.Node ("PaUnp", [Qast.Loc; s; Qast.Option (Some mt)]) :
               'paren_patt)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "type")))
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("LIDENT", "")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.Str a) : 'e__134)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_", loc, a) : 'e__134)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("", loc, a)) : 'e__134)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_lid")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_lid", loc, a) : 'e__134)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "lid")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("lid", loc, a)) :
                           'e__134)))])),
           (fun (s : 'e__134) _ (loc : Ploc.t) ->
              (Qast.Node ("PaNty", [Qast.Loc; s]) : 'paren_patt)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_list1sep
                            (Grammar.s_nterm (patt : 'patt Grammar.Entry.e))
                            (Grammar.s_token ("", ",")) false),
                       (fun (a : 'patt list) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.List a) : 'e__133)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_list")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_list", loc, a) : 'e__133)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "list")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                           'e__133)))])),
           (fun (pl : 'e__133) (loc : Ploc.t) ->
              (Qast.Node ("PaTup", [Qast.Loc; pl]) : 'paren_patt)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_nterm (patt : 'patt Grammar.Entry.e)),
           (fun (p : 'patt) (loc : Ploc.t) -> (p : 'paren_patt)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop
                   (Grammar.s_nterm (patt : 'patt Grammar.Entry.e)))
                (Grammar.s_token ("", ",")))
             (Grammar.s_list1sep
                (Grammar.s_nterm (patt : 'patt Grammar.Entry.e))
                (Grammar.s_token ("", ",")) false),
           (fun (pl : 'patt list) _ (p : 'patt) (loc : Ploc.t) ->
              (mktuppat Qast.Loc p pl : 'paren_patt)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop
                   (Grammar.s_nterm (patt : 'patt Grammar.Entry.e)))
                (Grammar.s_token ("", "as")))
             (Grammar.s_nterm (patt : 'patt Grammar.Entry.e)),
           (fun (p2 : 'patt) _ (p : 'patt) (loc : Ploc.t) ->
              (Qast.Node ("PaAli", [Qast.Loc; p; p2]) : 'paren_patt)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop
                   (Grammar.s_nterm (patt : 'patt Grammar.Entry.e)))
                (Grammar.s_token ("", ":")))
             (Grammar.s_nterm (ctyp : 'ctyp Grammar.Entry.e)),
           (fun (t : 'ctyp) _ (p : 'patt) (loc : Ploc.t) ->
              (Qast.Node ("PaTyc", [Qast.Loc; p; t]) : 'paren_patt)))]];
    Grammar.extension (cons_patt_opt : 'cons_patt_opt Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_stop,
           (fun (loc : Ploc.t) -> (Qast.Option None : 'cons_patt_opt)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "::")))
             (Grammar.s_nterm (patt : 'patt Grammar.Entry.e)),
           (fun (p : 'patt) _ (loc : Ploc.t) ->
              (Qast.Option (Some p) : 'cons_patt_opt)))]];
    Grammar.extension (label_patt : 'label_patt Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop
                   (Grammar.s_nterm
                      (patt_label_ident : 'patt_label_ident Grammar.Entry.e)))
                (Grammar.s_token ("", "=")))
             (Grammar.s_nterm (patt : 'patt Grammar.Entry.e)),
           (fun (p : 'patt) _ (i : 'patt_label_ident) (loc : Ploc.t) ->
              (Qast.Tuple [i; p] : 'label_patt)))]];
    Grammar.extension (patt_label_ident : 'patt_label_ident Grammar.Entry.e)
      None
      [None, Some Gramext.LeftA,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                (Grammar.s_token ("", ".")))
             Grammar.s_self,
           (fun (p2 : 'patt_label_ident) _ (p1 : 'patt_label_ident)
                (loc : Ploc.t) ->
              (Qast.Node ("PaAcc", [Qast.Loc; p1; p2]) :
               'patt_label_ident)))];
       Some "simple", Some Gramext.RightA,
       [Grammar.production
          (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "_")),
           (fun _ (loc : Ploc.t) ->
              (Qast.Node ("PaAny", [Qast.Loc]) : 'patt_label_ident)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("LIDENT", "")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.Str a) : 'e__138)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_", loc, a) : 'e__138)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("", loc, a)) : 'e__138)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_lid")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_lid", loc, a) : 'e__138)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "lid")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("lid", loc, a)) :
                           'e__138)))])),
           (fun (i : 'e__138) (loc : Ploc.t) ->
              (Qast.Node ("PaLid", [Qast.Loc; i]) : 'patt_label_ident)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("UIDENT", "")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.Str a) : 'e__137)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_", loc, a) : 'e__137)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("", loc, a)) : 'e__137)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_uid")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_uid", loc, a) : 'e__137)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "uid")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("uid", loc, a)) :
                           'e__137)))])),
           (fun (i : 'e__137) (loc : Ploc.t) ->
              (Qast.Node ("PaUid", [Qast.Loc; i]) : 'patt_label_ident)))]];
    Grammar.extension (ipatt : 'ipatt Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "_")),
           (fun _ (loc : Ploc.t) ->
              (Qast.Node ("PaAny", [Qast.Loc]) : 'ipatt)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("GIDENT", "")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.Str a) : 'e__141)))])),
           (fun (s : 'e__141) (loc : Ploc.t) ->
              (Qast.Node ("PaLid", [Qast.Loc; s]) : 'ipatt)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("LIDENT", "")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.Str a) : 'e__140)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_", loc, a) : 'e__140)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("", loc, a)) : 'e__140)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_lid")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_lid", loc, a) : 'e__140)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "lid")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("lid", loc, a)) :
                           'e__140)))])),
           (fun (s : 'e__140) (loc : Ploc.t) ->
              (Qast.Node ("PaLid", [Qast.Loc; s]) : 'ipatt)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "(")))
                (Grammar.s_nterm
                   (paren_ipatt : 'paren_ipatt Grammar.Entry.e)))
             (Grammar.s_token ("", ")")),
           (fun _ (p : 'paren_ipatt) _ (loc : Ploc.t) -> (p : 'ipatt)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "{")))
                (Grammar.s_facto
                   (Grammar.s_rules
                      [Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_list1sep
                               (Grammar.s_nterm
                                  (label_ipatt :
                                   'label_ipatt Grammar.Entry.e))
                               (Grammar.s_token ("", ";")) false),
                          (fun (a : 'label_ipatt list) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.List a) : 'e__139)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_list")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_list", loc, a) : 'e__139)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "list")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                              'e__139)))])))
             (Grammar.s_token ("", "}")),
           (fun _ (lpl : 'e__139) _ (loc : Ploc.t) ->
              (Qast.Node ("PaRec", [Qast.Loc; lpl]) : 'ipatt)))]];
    Grammar.extension (paren_ipatt : 'paren_ipatt Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_stop,
           (fun (loc : Ploc.t) ->
              (Qast.Node ("PaUid", [Qast.Loc; Qast.VaVal (Qast.Str "()")]) :
               'paren_ipatt)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "module")))
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_nterm (uidopt : 'uidopt Grammar.Entry.e)),
                       (fun (a : 'uidopt) (loc : Ploc.t) ->
                          (Qast.VaVal a : 'e__145)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_uidopt")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_uidopt", loc, a) : 'e__145)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "uidopt")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("uidopt", loc, a)) :
                           'e__145)))])),
           (fun (s : 'e__145) _ (loc : Ploc.t) ->
              (Qast.Node ("PaUnp", [Qast.Loc; s; Qast.Option None]) :
               'paren_ipatt)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next Grammar.r_stop
                      (Grammar.s_token ("", "module")))
                   (Grammar.s_facto
                      (Grammar.s_rules
                         [Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_nterm
                                  (uidopt : 'uidopt Grammar.Entry.e)),
                             (fun (a : 'uidopt) (loc : Ploc.t) ->
                                (Qast.VaVal a : 'e__144)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "_uidopt")),
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaAnt ("_uidopt", loc, a) : 'e__144)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "uidopt")),
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaVal (Qast.VaAnt ("uidopt", loc, a)) :
                                 'e__144)))])))
                (Grammar.s_token ("", ":")))
             (Grammar.s_nterm (module_type : 'module_type Grammar.Entry.e)),
           (fun (mt : 'module_type) _ (s : 'e__144) _ (loc : Ploc.t) ->
              (Qast.Node ("PaUnp", [Qast.Loc; s; Qast.Option (Some mt)]) :
               'paren_ipatt)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "type")))
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("LIDENT", "")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.Str a) : 'e__143)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_", loc, a) : 'e__143)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("", loc, a)) : 'e__143)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_lid")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_lid", loc, a) : 'e__143)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "lid")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("lid", loc, a)) :
                           'e__143)))])),
           (fun (s : 'e__143) _ (loc : Ploc.t) ->
              (Qast.Node ("PaNty", [Qast.Loc; s]) : 'paren_ipatt)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_list1sep
                            (Grammar.s_nterm (ipatt : 'ipatt Grammar.Entry.e))
                            (Grammar.s_token ("", ",")) false),
                       (fun (a : 'ipatt list) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.List a) : 'e__142)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_list")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_list", loc, a) : 'e__142)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "list")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                           'e__142)))])),
           (fun (pl : 'e__142) (loc : Ploc.t) ->
              (Qast.Node ("PaTup", [Qast.Loc; pl]) : 'paren_ipatt)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_nterm (ipatt : 'ipatt Grammar.Entry.e)),
           (fun (p : 'ipatt) (loc : Ploc.t) -> (p : 'paren_ipatt)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop
                   (Grammar.s_nterm (ipatt : 'ipatt Grammar.Entry.e)))
                (Grammar.s_token ("", ",")))
             (Grammar.s_list1sep
                (Grammar.s_nterm (ipatt : 'ipatt Grammar.Entry.e))
                (Grammar.s_token ("", ",")) false),
           (fun (pl : 'ipatt list) _ (p : 'ipatt) (loc : Ploc.t) ->
              (mktuppat Qast.Loc p pl : 'paren_ipatt)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop
                   (Grammar.s_nterm (ipatt : 'ipatt Grammar.Entry.e)))
                (Grammar.s_token ("", "as")))
             (Grammar.s_nterm (ipatt : 'ipatt Grammar.Entry.e)),
           (fun (p2 : 'ipatt) _ (p : 'ipatt) (loc : Ploc.t) ->
              (Qast.Node ("PaAli", [Qast.Loc; p; p2]) : 'paren_ipatt)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop
                   (Grammar.s_nterm (ipatt : 'ipatt Grammar.Entry.e)))
                (Grammar.s_token ("", ":")))
             (Grammar.s_nterm (ctyp : 'ctyp Grammar.Entry.e)),
           (fun (t : 'ctyp) _ (p : 'ipatt) (loc : Ploc.t) ->
              (Qast.Node ("PaTyc", [Qast.Loc; p; t]) : 'paren_ipatt)))]];
    Grammar.extension (label_ipatt : 'label_ipatt Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop
                   (Grammar.s_nterm
                      (patt_label_ident : 'patt_label_ident Grammar.Entry.e)))
                (Grammar.s_token ("", "=")))
             (Grammar.s_nterm (ipatt : 'ipatt Grammar.Entry.e)),
           (fun (p : 'ipatt) _ (i : 'patt_label_ident) (loc : Ploc.t) ->
              (Qast.Tuple [i; p] : 'label_ipatt)))]];
    Grammar.extension (item_attribute : 'item_attribute Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "[@@")))
                (Grammar.s_facto
                   (Grammar.s_rules
                      [Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_nterm
                               (attribute_body :
                                'attribute_body Grammar.Entry.e)),
                          (fun (a : 'attribute_body) (loc : Ploc.t) ->
                             (Qast.VaVal a : 'e__146)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_attribute")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_attribute", loc, a) : 'e__146)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "attribute")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("attribute", loc, a)) :
                              'e__146)))])))
             (Grammar.s_token ("", "]")),
           (fun _ (attr : 'e__146) _ (loc : Ploc.t) ->
              (attr : 'item_attribute)))]];
    Grammar.extension (alg_attribute : 'alg_attribute Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "[@")))
                (Grammar.s_facto
                   (Grammar.s_rules
                      [Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_nterm
                               (attribute_body :
                                'attribute_body Grammar.Entry.e)),
                          (fun (a : 'attribute_body) (loc : Ploc.t) ->
                             (Qast.VaVal a : 'e__147)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_attribute")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_attribute", loc, a) : 'e__147)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "attribute")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("attribute", loc, a)) :
                              'e__147)))])))
             (Grammar.s_token ("", "]")),
           (fun _ (attr : 'e__147) _ (loc : Ploc.t) ->
              (attr : 'alg_attribute)))]];
    Grammar.extension (type_decl : 'type_decl Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next
                         (Grammar.r_next
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_facto
                                  (Grammar.s_rules
                                     [Grammar.production
                                        (Grammar.r_next Grammar.r_stop
                                           (Grammar.s_nterm
                                              (type_patt :
                                               'type_patt Grammar.Entry.e)),
                                         (fun (a : 'type_patt)
                                              (loc : Ploc.t) ->
                                            (Qast.VaVal a : 'e__148)));
                                      Grammar.production
                                        (Grammar.r_next Grammar.r_stop
                                           (Grammar.s_token
                                              ("ANTIQUOT", "_tp")),
                                         (fun (a : string) (loc : Ploc.t) ->
                                            (Qast.VaAnt ("_tp", loc, a) :
                                             'e__148)));
                                      Grammar.production
                                        (Grammar.r_next Grammar.r_stop
                                           (Grammar.s_token
                                              ("ANTIQUOT", "tp")),
                                         (fun (a : string) (loc : Ploc.t) ->
                                            (Qast.VaVal
                                               (Qast.VaAnt ("tp", loc, a)) :
                                             'e__148)))])))
                            (Grammar.s_facto
                               (Grammar.s_rules
                                  [Grammar.production
                                     (Grammar.r_next Grammar.r_stop
                                        (Grammar.s_list0
                                           (Grammar.s_nterm
                                              (type_parameter :
                                               'type_parameter
                                                 Grammar.Entry.e))),
                                      (fun (a : 'type_parameter list)
                                           (loc : Ploc.t) ->
                                         (Qast.VaVal (Qast.List a) :
                                          'e__149)));
                                   Grammar.production
                                     (Grammar.r_next Grammar.r_stop
                                        (Grammar.s_token
                                           ("ANTIQUOT", "_list")),
                                      (fun (a : string) (loc : Ploc.t) ->
                                         (Qast.VaAnt ("_list", loc, a) :
                                          'e__149)));
                                   Grammar.production
                                     (Grammar.r_next Grammar.r_stop
                                        (Grammar.s_token
                                           ("ANTIQUOT", "list")),
                                      (fun (a : string) (loc : Ploc.t) ->
                                         (Qast.VaVal
                                            (Qast.VaAnt ("list", loc, a)) :
                                          'e__149)))])))
                         (Grammar.s_token ("", "=")))
                      (Grammar.s_facto
                         (Grammar.s_rules
                            [Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_flag
                                     (Grammar.s_token ("", "private"))),
                                (fun (a : bool) (loc : Ploc.t) ->
                                   (Qast.VaVal (Qast.Bool a) : 'e__150)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "_priv")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaAnt ("_priv", loc, a) : 'e__150)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "priv")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaVal (Qast.VaAnt ("priv", loc, a)) :
                                    'e__150)))])))
                   (Grammar.s_nterm (ctyp : 'ctyp Grammar.Entry.e)))
                (Grammar.s_facto
                   (Grammar.s_rules
                      [Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_list0
                               (Grammar.s_nterm
                                  (constrain : 'constrain Grammar.Entry.e))),
                          (fun (a : 'constrain list) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.List a) : 'e__151)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_list")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_list", loc, a) : 'e__151)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "list")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                              'e__151)))])))
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_list0
                            (Grammar.s_nterm
                               (item_attribute :
                                'item_attribute Grammar.Entry.e))),
                       (fun (a : 'item_attribute list) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.List a) : 'e__152)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_list")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_list", loc, a) : 'e__152)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "list")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                           'e__152)))])),
           (fun (attrs : 'e__152) (cl : 'e__151) (tk : 'ctyp) (pf : 'e__150) _
                (tpl : 'e__149) (n : 'e__148) (loc : Ploc.t) ->
              (Qast.Record
                 ["tdNam", n; "tdPrm", tpl; "tdPrv", pf; "tdDef", tk;
                  "tdCon", cl; "tdAttributes", attrs] :
               'type_decl)))]];
    Grammar.extension (type_patt : 'type_patt Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("LIDENT", "")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.Str a) : 'e__153)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_", loc, a) : 'e__153)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("", loc, a)) : 'e__153)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_lid")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_lid", loc, a) : 'e__153)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "lid")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("lid", loc, a)) :
                           'e__153)))])),
           (fun (n : 'e__153) (loc : Ploc.t) ->
              (Qast.Tuple [Qast.Loc; n] : 'type_patt)))]];
    Grammar.extension (constrain : 'constrain Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next Grammar.r_stop
                      (Grammar.s_token ("", "constraint")))
                   (Grammar.s_nterm (ctyp : 'ctyp Grammar.Entry.e)))
                (Grammar.s_token ("", "=")))
             (Grammar.s_nterm (ctyp : 'ctyp Grammar.Entry.e)),
           (fun (t2 : 'ctyp) _ (t1 : 'ctyp) _ (loc : Ploc.t) ->
              (Qast.Tuple [t1; t2] : 'constrain)))]];
    Grammar.extension (type_parameter : 'type_parameter Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_nterm
                            (simple_type_parameter :
                             'simple_type_parameter Grammar.Entry.e)),
                       (fun (a : 'simple_type_parameter) (loc : Ploc.t) ->
                          (Qast.VaVal a : 'e__156)))])),
           (fun (p : 'e__156) (loc : Ploc.t) ->
              (Qast.Tuple [p; Qast.Option None] : 'type_parameter)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "-")))
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_nterm
                            (simple_type_parameter :
                             'simple_type_parameter Grammar.Entry.e)),
                       (fun (a : 'simple_type_parameter) (loc : Ploc.t) ->
                          (Qast.VaVal a : 'e__155)))])),
           (fun (p : 'e__155) _ (loc : Ploc.t) ->
              (Qast.Tuple [p; Qast.Option (Some (Qast.Bool false))] :
               'type_parameter)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "+")))
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_nterm
                            (simple_type_parameter :
                             'simple_type_parameter Grammar.Entry.e)),
                       (fun (a : 'simple_type_parameter) (loc : Ploc.t) ->
                          (Qast.VaVal a : 'e__154)))])),
           (fun (p : 'e__154) _ (loc : Ploc.t) ->
              (Qast.Tuple [p; Qast.Option (Some (Qast.Bool true))] :
               'type_parameter)))]];
    Grammar.extension
      (simple_type_parameter : 'simple_type_parameter Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "_")),
           (fun _ (loc : Ploc.t) ->
              (Qast.Option None : 'simple_type_parameter)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop (Grammar.s_token ("GIDENT", "")),
           (fun (i : string) (loc : Ploc.t) ->
              (Qast.Option (Some (greek_ascii_equiv i)) :
               'simple_type_parameter)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "'")))
             (Grammar.s_nterm (ident : 'ident Grammar.Entry.e)),
           (fun (i : 'ident) _ (loc : Ploc.t) ->
              (Qast.Option (Some i) : 'simple_type_parameter)))]];
    Grammar.extension (ctyp : 'ctyp Grammar.Entry.e) None
      [Some "top", Some Gramext.LeftA,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                   (Grammar.s_token ("", "==")))
                (Grammar.s_facto
                   (Grammar.s_rules
                      [Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_flag
                               (Grammar.s_token ("", "private"))),
                          (fun (a : bool) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.Bool a) : 'e__157)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_priv")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_priv", loc, a) : 'e__157)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "priv")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("priv", loc, a)) :
                              'e__157)))])))
             Grammar.s_self,
           (fun (t2 : 'ctyp) (pf : 'e__157) _ (t1 : 'ctyp) (loc : Ploc.t) ->
              (Qast.Node ("TyMan", [Qast.Loc; t1; pf; t2]) : 'ctyp)))];
       Some "alg_attribute", Some Gramext.LeftA,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                   (Grammar.s_token ("", "[@")))
                (Grammar.s_facto
                   (Grammar.s_rules
                      [Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_nterm
                               (attribute_body :
                                'attribute_body Grammar.Entry.e)),
                          (fun (a : 'attribute_body) (loc : Ploc.t) ->
                             (Qast.VaVal a : 'e__158)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_attribute")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_attribute", loc, a) : 'e__158)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "attribute")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("attribute", loc, a)) :
                              'e__158)))])))
             (Grammar.s_token ("", "]")),
           (fun _ (attr : 'e__158) _ (t1 : 'ctyp) (loc : Ploc.t) ->
              (Qast.Node ("TyAtt", [Qast.Loc; t1; attr]) : 'ctyp)))];
       Some "below_alg_attribute", None,
       [Grammar.production
          (Grammar.r_next Grammar.r_stop Grammar.s_next,
           (fun (t : 'ctyp) (loc : Ploc.t) -> (t : 'ctyp)))];
       Some "as", Some Gramext.LeftA,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                (Grammar.s_token ("", "as")))
             Grammar.s_self,
           (fun (t2 : 'ctyp) _ (t1 : 'ctyp) (loc : Ploc.t) ->
              (Qast.Node ("TyAli", [Qast.Loc; t1; t2]) : 'ctyp)))];
       None, Some Gramext.LeftA,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next Grammar.r_stop
                      (Grammar.s_token ("", "type")))
                   (Grammar.s_facto
                      (Grammar.s_rules
                         [Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_list1
                                  (Grammar.s_token ("LIDENT", ""))),
                             (fun (a : string list) (loc : Ploc.t) ->
                                (Qast.VaVal
                                   (Qast.List
                                      (List.map (fun a -> Qast.Str a) a)) :
                                 'e__160)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "_list")),
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaAnt ("_list", loc, a) : 'e__160)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "list")),
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                                 'e__160)))])))
                (Grammar.s_token ("", ".")))
             Grammar.s_self,
           (fun (t : 'ctyp) _ (pl : 'e__160) _ (loc : Ploc.t) ->
              (Qast.Node ("TyPot", [Qast.Loc; pl; t]) : 'ctyp)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "!")))
                   (Grammar.s_facto
                      (Grammar.s_rules
                         [Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_list1
                                  (Grammar.s_nterm
                                     (typevar : 'typevar Grammar.Entry.e))),
                             (fun (a : 'typevar list) (loc : Ploc.t) ->
                                (Qast.VaVal (Qast.List a) : 'e__159)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "_list")),
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaAnt ("_list", loc, a) : 'e__159)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "list")),
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                                 'e__159)))])))
                (Grammar.s_token ("", ".")))
             Grammar.s_self,
           (fun (t : 'ctyp) _ (pl : 'e__159) _ (loc : Ploc.t) ->
              (Qast.Node ("TyPol", [Qast.Loc; pl; t]) : 'ctyp)))];
       Some "arrow", Some Gramext.RightA,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                (Grammar.s_token ("", "->")))
             Grammar.s_self,
           (fun (t2 : 'ctyp) _ (t1 : 'ctyp) (loc : Ploc.t) ->
              (Qast.Node ("TyArr", [Qast.Loc; t1; t2]) : 'ctyp)))];
       Some "apply", Some Gramext.LeftA,
       [Grammar.production
          (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
             Grammar.s_self,
           (fun (t2 : 'ctyp) (t1 : 'ctyp) (loc : Ploc.t) ->
              (Qast.Node ("TyApp", [Qast.Loc; t1; t2]) : 'ctyp)))];
       None, Some Gramext.LeftA,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                (Grammar.s_token ("", ".")))
             Grammar.s_self,
           (fun (t2 : 'ctyp) _ (t1 : 'ctyp) (loc : Ploc.t) ->
              (Qast.Node ("TyAcc", [Qast.Loc; t1; t2]) : 'ctyp)))];
       Some "simple", None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "{")))
                (Grammar.s_facto
                   (Grammar.s_rules
                      [Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_list1sep
                               (Grammar.s_nterm
                                  (label_declaration :
                                   'label_declaration Grammar.Entry.e))
                               (Grammar.s_token ("", ";")) false),
                          (fun (a : 'label_declaration list) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.List a) : 'e__166)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_list")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_list", loc, a) : 'e__166)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "list")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                              'e__166)))])))
             (Grammar.s_token ("", "}")),
           (fun _ (ldl : 'e__166) _ (loc : Ploc.t) ->
              (Qast.Node ("TyRec", [Qast.Loc; ldl]) : 'ctyp)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "[")))
                (Grammar.s_facto
                   (Grammar.s_rules
                      [Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_list0sep
                               (Grammar.s_nterm
                                  (constructor_declaration :
                                   'constructor_declaration Grammar.Entry.e))
                               (Grammar.s_token ("", "|")) false),
                          (fun (a : 'constructor_declaration list)
                               (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.List a) : 'e__165)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_list")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_list", loc, a) : 'e__165)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "list")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                              'e__165)))])))
             (Grammar.s_token ("", "]")),
           (fun _ (cdl : 'e__165) _ (loc : Ploc.t) ->
              (Qast.Node ("TySum", [Qast.Loc; cdl]) : 'ctyp)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "(")))
                (Grammar.s_facto
                   (Grammar.s_rules
                      [Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_list1sep
                               (Grammar.s_nterm
                                  (ctyp : 'ctyp Grammar.Entry.e))
                               (Grammar.s_token ("", "*")) false),
                          (fun (a : 'ctyp list) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.List a) : 'e__164)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_list")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_list", loc, a) : 'e__164)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "list")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                              'e__164)))])))
             (Grammar.s_token ("", ")")),
           (fun _ (tl : 'e__164) _ (loc : Ploc.t) ->
              (Qast.Node ("TyTup", [Qast.Loc; tl]) : 'ctyp)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "(")))
                Grammar.s_self)
             (Grammar.s_token ("", ")")),
           (fun _ (t : 'ctyp) _ (loc : Ploc.t) -> (t : 'ctyp)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("", "(")))
                      Grammar.s_self)
                   (Grammar.s_token ("", "*")))
                (Grammar.s_list1sep
                   (Grammar.s_nterm (ctyp : 'ctyp Grammar.Entry.e))
                   (Grammar.s_token ("", "*")) false))
             (Grammar.s_token ("", ")")),
           (fun _ (tl : 'ctyp list) _ (t : 'ctyp) _ (loc : Ploc.t) ->
              (mktuptyp Qast.Loc t tl : 'ctyp)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "module")))
             (Grammar.s_nterm (module_type : 'module_type Grammar.Entry.e)),
           (fun (mt : 'module_type) _ (loc : Ploc.t) ->
              (Qast.Node ("TyPck", [Qast.Loc; mt]) : 'ctyp)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("UIDENT", "")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.Str a) : 'e__163)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_", loc, a) : 'e__163)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("", loc, a)) : 'e__163)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_uid")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_uid", loc, a) : 'e__163)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "uid")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("uid", loc, a)) :
                           'e__163)))])),
           (fun (i : 'e__163) (loc : Ploc.t) ->
              (Qast.Node ("TyUid", [Qast.Loc; i]) : 'ctyp)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("LIDENT", "")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.Str a) : 'e__162)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_", loc, a) : 'e__162)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("", loc, a)) : 'e__162)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_lid")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_lid", loc, a) : 'e__162)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "lid")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("lid", loc, a)) :
                           'e__162)))])),
           (fun (i : 'e__162) (loc : Ploc.t) ->
              (Qast.Node ("TyLid", [Qast.Loc; i]) : 'ctyp)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "_")),
           (fun _ (loc : Ploc.t) ->
              (Qast.Node ("TyAny", [Qast.Loc]) : 'ctyp)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop (Grammar.s_token ("GIDENT", "")),
           (fun (i : string) (loc : Ploc.t) ->
              (Qast.Node
                 ("TyQuo", [Qast.Loc; Qast.VaVal (greek_ascii_equiv i)]) :
               'ctyp)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "'")))
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_nterm (ident : 'ident Grammar.Entry.e)),
                       (fun (a : 'ident) (loc : Ploc.t) ->
                          (Qast.VaVal a : 'e__161)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_", loc, a) : 'e__161)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("", loc, a)) :
                           'e__161)))])),
           (fun (i : 'e__161) _ (loc : Ploc.t) ->
              (Qast.Node ("TyQuo", [Qast.Loc; i]) : 'ctyp)))]];
    Grammar.extension
      (constructor_declaration : 'constructor_declaration Grammar.Entry.e)
      None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop
                (Grammar.s_facto
                   (Grammar.s_rules
                      [Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("UIDENT", "")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.Str a) : 'e__172)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_", loc, a) : 'e__172)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("", loc, a)) :
                              'e__172)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_uid")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_uid", loc, a) : 'e__172)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "uid")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("uid", loc, a)) :
                              'e__172)))])))
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_list0
                            (Grammar.s_nterm
                               (alg_attribute :
                                'alg_attribute Grammar.Entry.e))),
                       (fun (a : 'alg_attribute list) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.List a) : 'e__173)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_list")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_list", loc, a) : 'e__173)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "list")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                           'e__173)))])),
           (fun (alg_attrs : 'e__173) (ci : 'e__172) (loc : Ploc.t) ->
              (Qast.Tuple
                 [Qast.Loc; ci; Qast.VaVal (Qast.List []); Qast.Option None;
                  alg_attrs] :
               'constructor_declaration)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next Grammar.r_stop
                      (Grammar.s_facto
                         (Grammar.s_rules
                            [Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("UIDENT", "")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaVal (Qast.Str a) : 'e__170)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "_")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaAnt ("_", loc, a) : 'e__170)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaVal (Qast.VaAnt ("", loc, a)) :
                                    'e__170)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "_uid")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaAnt ("_uid", loc, a) : 'e__170)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "uid")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaVal (Qast.VaAnt ("uid", loc, a)) :
                                    'e__170)))])))
                   (Grammar.s_token ("", ":")))
                (Grammar.s_nterm (ctyp : 'ctyp Grammar.Entry.e)))
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_list0
                            (Grammar.s_nterm
                               (alg_attribute :
                                'alg_attribute Grammar.Entry.e))),
                       (fun (a : 'alg_attribute list) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.List a) : 'e__171)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_list")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_list", loc, a) : 'e__171)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "list")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                           'e__171)))])),
           (fun (alg_attrs : 'e__171) (t : 'ctyp) _ (ci : 'e__170)
                (loc : Ploc.t) ->
              (let (tl, rt) = generalized_type_of_type t in
               Qast.Tuple
                 [Qast.Loc; ci; Qast.VaVal tl; Qast.Option (Some rt);
                  alg_attrs] :
               'constructor_declaration)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next Grammar.r_stop
                      (Grammar.s_facto
                         (Grammar.s_rules
                            [Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("UIDENT", "")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaVal (Qast.Str a) : 'e__167)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "_")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaAnt ("_", loc, a) : 'e__167)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaVal (Qast.VaAnt ("", loc, a)) :
                                    'e__167)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "_uid")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaAnt ("_uid", loc, a) : 'e__167)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "uid")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaVal (Qast.VaAnt ("uid", loc, a)) :
                                    'e__167)))])))
                   (Grammar.s_token ("", "of")))
                (Grammar.s_facto
                   (Grammar.s_rules
                      [Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_list1sep
                               (Grammar.s_nterm
                                  (ctyp : 'ctyp Grammar.Entry.e))
                               (Grammar.s_token ("", "and")) false),
                          (fun (a : 'ctyp list) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.List a) : 'e__168)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_list")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_list", loc, a) : 'e__168)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "list")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                              'e__168)))])))
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_list0
                            (Grammar.s_nterm
                               (alg_attribute :
                                'alg_attribute Grammar.Entry.e))),
                       (fun (a : 'alg_attribute list) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.List a) : 'e__169)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_list")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_list", loc, a) : 'e__169)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "list")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                           'e__169)))])),
           (fun (alg_attrs : 'e__169) (cal : 'e__168) _ (ci : 'e__167)
                (loc : Ploc.t) ->
              (Qast.Tuple [Qast.Loc; ci; cal; Qast.Option None; alg_attrs] :
               'constructor_declaration)))]];
    Grammar.extension
      (constructor_declaration_sans_alg_attrs :
       'constructor_declaration_sans_alg_attrs Grammar.Entry.e)
      None
      [None, None,
       [Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("UIDENT", "")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.Str a) : 'e__177)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_", loc, a) : 'e__177)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("", loc, a)) : 'e__177)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_uid")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_uid", loc, a) : 'e__177)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "uid")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("uid", loc, a)) :
                           'e__177)))])),
           (fun (ci : 'e__177) (loc : Ploc.t) ->
              (Qast.Tuple
                 [Qast.Loc; ci; Qast.VaVal (Qast.List []); Qast.Option None] :
               'constructor_declaration_sans_alg_attrs)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop
                   (Grammar.s_facto
                      (Grammar.s_rules
                         [Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("UIDENT", "")),
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaVal (Qast.Str a) : 'e__176)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "_")),
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaAnt ("_", loc, a) : 'e__176)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "")),
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaVal (Qast.VaAnt ("", loc, a)) :
                                 'e__176)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "_uid")),
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaAnt ("_uid", loc, a) : 'e__176)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "uid")),
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaVal (Qast.VaAnt ("uid", loc, a)) :
                                 'e__176)))])))
                (Grammar.s_token ("", ":")))
             (Grammar.s_nterm (ctyp : 'ctyp Grammar.Entry.e)),
           (fun (t : 'ctyp) _ (ci : 'e__176) (loc : Ploc.t) ->
              (let (tl, rt) = generalized_type_of_type t in
               Qast.Tuple
                 [Qast.Loc; ci; Qast.VaVal tl; Qast.Option (Some rt)] :
               'constructor_declaration_sans_alg_attrs)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop
                   (Grammar.s_facto
                      (Grammar.s_rules
                         [Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("UIDENT", "")),
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaVal (Qast.Str a) : 'e__174)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "_")),
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaAnt ("_", loc, a) : 'e__174)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "")),
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaVal (Qast.VaAnt ("", loc, a)) :
                                 'e__174)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "_uid")),
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaAnt ("_uid", loc, a) : 'e__174)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "uid")),
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaVal (Qast.VaAnt ("uid", loc, a)) :
                                 'e__174)))])))
                (Grammar.s_token ("", "of")))
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_list1sep
                            (Grammar.s_nterm (ctyp : 'ctyp Grammar.Entry.e))
                            (Grammar.s_token ("", "and")) false),
                       (fun (a : 'ctyp list) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.List a) : 'e__175)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_list")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_list", loc, a) : 'e__175)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "list")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                           'e__175)))])),
           (fun (cal : 'e__175) _ (ci : 'e__174) (loc : Ploc.t) ->
              (Qast.Tuple [Qast.Loc; ci; cal; Qast.Option None] :
               'constructor_declaration_sans_alg_attrs)))]];
    Grammar.extension (label_declaration : 'label_declaration Grammar.Entry.e)
      None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("LIDENT", "")))
                      (Grammar.s_token ("", ":")))
                   (Grammar.s_flag (Grammar.s_token ("", "mutable"))))
                (Grammar.s_nterml (ctyp : 'ctyp Grammar.Entry.e)
                   "below_alg_attribute"))
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_list0
                            (Grammar.s_nterm
                               (alg_attribute :
                                'alg_attribute Grammar.Entry.e))),
                       (fun (a : 'alg_attribute list) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.List a) : 'e__178)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_list")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_list", loc, a) : 'e__178)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "list")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                           'e__178)))])),
           (fun (alg_attrs : 'e__178) (t : 'ctyp) (mf : bool) _ (i : string)
                (loc : Ploc.t) ->
              (mklabdecl Qast.Loc i mf t alg_attrs : 'label_declaration)))]];
    Grammar.extension (ident : 'ident Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next Grammar.r_stop (Grammar.s_token ("UIDENT", "")),
           (fun (i : string) (loc : Ploc.t) -> (mkident i : 'ident)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop (Grammar.s_token ("LIDENT", "")),
           (fun (i : string) (loc : Ploc.t) -> (mkident i : 'ident)))]];
    Grammar.extension (mod_ident : 'mod_ident Grammar.Entry.e) None
      [None, Some Gramext.RightA,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop
                   (Grammar.s_token ("UIDENT", "")))
                (Grammar.s_token ("", ".")))
             Grammar.s_self,
           (fun (j : 'mod_ident) _ (i : string) (loc : Ploc.t) ->
              (Qast.Cons (mkident i, j) : 'mod_ident)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop (Grammar.s_token ("LIDENT", "")),
           (fun (i : string) (loc : Ploc.t) ->
              (Qast.List [mkident i] : 'mod_ident)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop (Grammar.s_token ("UIDENT", "")),
           (fun (i : string) (loc : Ploc.t) ->
              (Qast.List [mkident i] : 'mod_ident)))]];
    Grammar.extension (direction_flag : 'direction_flag Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "downto")),
           (fun _ (loc : Ploc.t) -> (Qast.Bool false : 'direction_flag)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "to")),
           (fun _ (loc : Ploc.t) -> (Qast.Bool true : 'direction_flag)))]];
    Grammar.extension (typevar : 'typevar Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "'")))
             (Grammar.s_nterm (ident : 'ident Grammar.Entry.e)),
           (fun (i : 'ident) _ (loc : Ploc.t) -> (i : 'typevar)))]];
    (* Objects and Classes *)
    Grammar.extension (str_item : 'str_item Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop
                   (Grammar.s_token ("", "class")))
                (Grammar.s_token ("", "type")))
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_list1sep
                            (Grammar.s_nterm
                               (class_type_declaration :
                                'class_type_declaration Grammar.Entry.e))
                            (Grammar.s_token ("", "and")) false),
                       (fun (a : 'class_type_declaration list)
                            (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.List a) : 'e__180)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_list")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_list", loc, a) : 'e__180)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "list")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                           'e__180)))])),
           (fun (ctd : 'e__180) _ _ (loc : Ploc.t) ->
              (Qast.Node ("StClt", [Qast.Loc; ctd]) : 'str_item)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "class")))
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_list1sep
                            (Grammar.s_nterm
                               (class_declaration :
                                'class_declaration Grammar.Entry.e))
                            (Grammar.s_token ("", "and")) false),
                       (fun (a : 'class_declaration list) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.List a) : 'e__179)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_list")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_list", loc, a) : 'e__179)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "list")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                           'e__179)))])),
           (fun (cd : 'e__179) _ (loc : Ploc.t) ->
              (Qast.Node ("StCls", [Qast.Loc; cd]) : 'str_item)))]];
    Grammar.extension (sig_item : 'sig_item Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop
                   (Grammar.s_token ("", "class")))
                (Grammar.s_token ("", "type")))
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_list1sep
                            (Grammar.s_nterm
                               (class_type_declaration :
                                'class_type_declaration Grammar.Entry.e))
                            (Grammar.s_token ("", "and")) false),
                       (fun (a : 'class_type_declaration list)
                            (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.List a) : 'e__182)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_list")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_list", loc, a) : 'e__182)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "list")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                           'e__182)))])),
           (fun (ctd : 'e__182) _ _ (loc : Ploc.t) ->
              (Qast.Node ("SgClt", [Qast.Loc; ctd]) : 'sig_item)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "class")))
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_list1sep
                            (Grammar.s_nterm
                               (class_description :
                                'class_description Grammar.Entry.e))
                            (Grammar.s_token ("", "and")) false),
                       (fun (a : 'class_description list) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.List a) : 'e__181)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_list")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_list", loc, a) : 'e__181)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "list")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                           'e__181)))])),
           (fun (cd : 'e__181) _ (loc : Ploc.t) ->
              (Qast.Node ("SgCls", [Qast.Loc; cd]) : 'sig_item)))]];
    Grammar.extension (class_declaration : 'class_declaration Grammar.Entry.e)
      None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next Grammar.r_stop
                      (Grammar.s_facto
                         (Grammar.s_rules
                            [Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_flag
                                     (Grammar.s_token ("", "virtual"))),
                                (fun (a : bool) (loc : Ploc.t) ->
                                   (Qast.VaVal (Qast.Bool a) : 'e__183)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "_opt")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaAnt ("_opt", loc, a) : 'e__183)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "opt")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaVal (Qast.VaAnt ("opt", loc, a)) :
                                    'e__183)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "_flag")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaAnt ("_flag", loc, a) : 'e__183)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "flag")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaVal (Qast.VaAnt ("flag", loc, a)) :
                                    'e__183)))])))
                   (Grammar.s_facto
                      (Grammar.s_rules
                         [Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("LIDENT", "")),
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaVal (Qast.Str a) : 'e__184)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "_")),
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaAnt ("_", loc, a) : 'e__184)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "")),
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaVal (Qast.VaAnt ("", loc, a)) :
                                 'e__184)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "_lid")),
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaAnt ("_lid", loc, a) : 'e__184)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "lid")),
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaVal (Qast.VaAnt ("lid", loc, a)) :
                                 'e__184)))])))
                (Grammar.s_nterm
                   (class_type_parameters :
                    'class_type_parameters Grammar.Entry.e)))
             (Grammar.s_nterm
                (class_fun_binding : 'class_fun_binding Grammar.Entry.e)),
           (fun (cfb : 'class_fun_binding) (ctp : 'class_type_parameters)
                (i : 'e__184) (vf : 'e__183) (loc : Ploc.t) ->
              (Qast.Record
                 ["ciLoc", Qast.Loc; "ciVir", vf; "ciPrm", ctp; "ciNam", i;
                  "ciExp", cfb] :
               'class_declaration)))]];
    Grammar.extension (class_fun_binding : 'class_fun_binding Grammar.Entry.e)
      None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop
                (Grammar.s_nterm (ipatt : 'ipatt Grammar.Entry.e)))
             Grammar.s_self,
           (fun (cfb : 'class_fun_binding) (p : 'ipatt) (loc : Ploc.t) ->
              (Qast.Node ("CeFun", [Qast.Loc; p; cfb]) :
               'class_fun_binding)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", ":")))
                   (Grammar.s_nterm
                      (class_type : 'class_type Grammar.Entry.e)))
                (Grammar.s_token ("", "=")))
             (Grammar.s_nterm (class_expr : 'class_expr Grammar.Entry.e)),
           (fun (ce : 'class_expr) _ (ct : 'class_type) _ (loc : Ploc.t) ->
              (Qast.Node ("CeTyc", [Qast.Loc; ce; ct]) :
               'class_fun_binding)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "=")))
             (Grammar.s_nterm (class_expr : 'class_expr Grammar.Entry.e)),
           (fun (ce : 'class_expr) _ (loc : Ploc.t) ->
              (ce : 'class_fun_binding)))]];
    Grammar.extension
      (class_type_parameters : 'class_type_parameters Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "[")))
                (Grammar.s_facto
                   (Grammar.s_rules
                      [Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_list1sep
                               (Grammar.s_nterm
                                  (type_parameter :
                                   'type_parameter Grammar.Entry.e))
                               (Grammar.s_token ("", ",")) false),
                          (fun (a : 'type_parameter list) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.List a) : 'e__185)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_list")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_list", loc, a) : 'e__185)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "list")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                              'e__185)))])))
             (Grammar.s_token ("", "]")),
           (fun _ (tpl : 'e__185) _ (loc : Ploc.t) ->
              (Qast.Tuple [Qast.Loc; tpl] : 'class_type_parameters)));
        Grammar.production
          (Grammar.r_stop,
           (fun (loc : Ploc.t) ->
              (Qast.Tuple [Qast.Loc; Qast.VaVal (Qast.List [])] :
               'class_type_parameters)))]];
    Grammar.extension (class_fun_def : 'class_fun_def Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "->")))
             (Grammar.s_nterm (class_expr : 'class_expr Grammar.Entry.e)),
           (fun (ce : 'class_expr) _ (loc : Ploc.t) ->
              (ce : 'class_fun_def)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop
                (Grammar.s_nterm (ipatt : 'ipatt Grammar.Entry.e)))
             Grammar.s_self,
           (fun (ce : 'class_fun_def) (p : 'ipatt) (loc : Ploc.t) ->
              (Qast.Node ("CeFun", [Qast.Loc; p; ce]) : 'class_fun_def)))]];
    Grammar.extension (class_expr : 'class_expr Grammar.Entry.e) None
      [Some "top", None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("", "let")))
                      (Grammar.s_facto
                         (Grammar.s_rules
                            [Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_flag
                                     (Grammar.s_token ("", "rec"))),
                                (fun (a : bool) (loc : Ploc.t) ->
                                   (Qast.VaVal (Qast.Bool a) : 'e__186)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "_opt")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaAnt ("_opt", loc, a) : 'e__186)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "opt")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaVal (Qast.VaAnt ("opt", loc, a)) :
                                    'e__186)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "_flag")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaAnt ("_flag", loc, a) : 'e__186)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "flag")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaVal (Qast.VaAnt ("flag", loc, a)) :
                                    'e__186)))])))
                   (Grammar.s_facto
                      (Grammar.s_rules
                         [Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_list1sep
                                  (Grammar.s_nterm
                                     (let_binding :
                                      'let_binding Grammar.Entry.e))
                                  (Grammar.s_token ("", "and")) false),
                             (fun (a : 'let_binding list) (loc : Ploc.t) ->
                                (Qast.VaVal (Qast.List a) : 'e__187)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "_list")),
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaAnt ("_list", loc, a) : 'e__187)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "list")),
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                                 'e__187)))])))
                (Grammar.s_token ("", "in")))
             Grammar.s_self,
           (fun (ce : 'class_expr) _ (lb : 'e__187) (rf : 'e__186) _
                (loc : Ploc.t) ->
              (Qast.Node ("CeLet", [Qast.Loc; rf; lb; ce]) : 'class_expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "fun")))
                (Grammar.s_nterm (ipatt : 'ipatt Grammar.Entry.e)))
             (Grammar.s_nterm
                (class_fun_def : 'class_fun_def Grammar.Entry.e)),
           (fun (ce : 'class_fun_def) (p : 'ipatt) _ (loc : Ploc.t) ->
              (Qast.Node ("CeFun", [Qast.Loc; p; ce]) : 'class_expr)))];
       Some "alg_attribute", Some Gramext.LeftA,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                   (Grammar.s_token ("", "[@")))
                (Grammar.s_facto
                   (Grammar.s_rules
                      [Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_nterm
                               (attribute_body :
                                'attribute_body Grammar.Entry.e)),
                          (fun (a : 'attribute_body) (loc : Ploc.t) ->
                             (Qast.VaVal a : 'e__188)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_attribute")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_attribute", loc, a) : 'e__188)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "attribute")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("attribute", loc, a)) :
                              'e__188)))])))
             (Grammar.s_token ("", "]")),
           (fun _ (attr : 'e__188) _ (t1 : 'class_expr) (loc : Ploc.t) ->
              (Qast.Node ("CeAtt", [Qast.Loc; t1; attr]) : 'class_expr)))];
       Some "apply", Some Gramext.LeftA,
       [Grammar.production
          (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
             (Grammar.s_nterml (expr : 'expr Grammar.Entry.e) "label"),
           (fun (e : 'expr) (ce : 'class_expr) (loc : Ploc.t) ->
              (Qast.Node ("CeApp", [Qast.Loc; ce; e]) : 'class_expr)))];
       Some "alg_attribute", Some Gramext.LeftA,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                   (Grammar.s_token ("", "[@")))
                (Grammar.s_facto
                   (Grammar.s_rules
                      [Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_nterm
                               (attribute_body :
                                'attribute_body Grammar.Entry.e)),
                          (fun (a : 'attribute_body) (loc : Ploc.t) ->
                             (Qast.VaVal a : 'e__189)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_attribute")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_attribute", loc, a) : 'e__189)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "attribute")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("attribute", loc, a)) :
                              'e__189)))])))
             (Grammar.s_token ("", "]")),
           (fun _ (attr : 'e__189) _ (t1 : 'class_expr) (loc : Ploc.t) ->
              (Qast.Node ("CeAtt", [Qast.Loc; t1; attr]) : 'class_expr)))];
       Some "simple", None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "(")))
                Grammar.s_self)
             (Grammar.s_token ("", ")")),
           (fun _ (ce : 'class_expr) _ (loc : Ploc.t) -> (ce : 'class_expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("", "(")))
                      Grammar.s_self)
                   (Grammar.s_token ("", ":")))
                (Grammar.s_nterm (class_type : 'class_type Grammar.Entry.e)))
             (Grammar.s_token ("", ")")),
           (fun _ (ct : 'class_type) _ (ce : 'class_expr) _ (loc : Ploc.t) ->
              (Qast.Node ("CeTyc", [Qast.Loc; ce; ct]) : 'class_expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "[")))
                   (Grammar.s_facto
                      (Grammar.s_rules
                         [Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_list1sep
                                  (Grammar.s_nterm
                                     (ctyp : 'ctyp Grammar.Entry.e))
                                  (Grammar.s_token ("", ",")) false),
                             (fun (a : 'ctyp list) (loc : Ploc.t) ->
                                (Qast.VaVal (Qast.List a) : 'e__192)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "_list")),
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaAnt ("_list", loc, a) : 'e__192)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "list")),
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                                 'e__192)))])))
                (Grammar.s_token ("", "]")))
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_nterm
                            (class_longident :
                             'class_longident Grammar.Entry.e)),
                       (fun (a : 'class_longident) (loc : Ploc.t) ->
                          (Qast.VaVal a : 'e__193)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_list")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_list", loc, a) : 'e__193)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "list")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                           'e__193)))])),
           (fun (ci : 'e__193) _ (ctcl : 'e__192) _ (loc : Ploc.t) ->
              (Qast.Node ("CeCon", [Qast.Loc; ci; ctcl]) : 'class_expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next Grammar.r_stop
                      (Grammar.s_token ("", "object")))
                   (Grammar.s_facto
                      (Grammar.s_rules
                         [Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_opt
                                  (Grammar.s_nterm
                                     (class_self_patt :
                                      'class_self_patt Grammar.Entry.e))),
                             (fun (a : 'class_self_patt option)
                                  (loc : Ploc.t) ->
                                (Qast.VaVal (Qast.Option a) : 'e__191)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "_opt")),
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaAnt ("_opt", loc, a) : 'e__191)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "opt")),
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaVal (Qast.VaAnt ("opt", loc, a)) :
                                 'e__191)))])))
                (Grammar.s_nterm
                   (class_structure : 'class_structure Grammar.Entry.e)))
             (Grammar.s_token ("", "end")),
           (fun _ (cf : 'class_structure) (cspo : 'e__191) _ (loc : Ploc.t) ->
              (Qast.Node ("CeStr", [Qast.Loc; cspo; cf]) : 'class_expr)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_nterm
                            (class_longident :
                             'class_longident Grammar.Entry.e)),
                       (fun (a : 'class_longident) (loc : Ploc.t) ->
                          (Qast.VaVal a : 'e__190)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_list")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_list", loc, a) : 'e__190)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "list")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                           'e__190)))])),
           (fun (ci : 'e__190) (loc : Ploc.t) ->
              (Qast.Node
                 ("CeCon", [Qast.Loc; ci; Qast.VaVal (Qast.List [])]) :
               'class_expr)))]];
    Grammar.extension (class_structure : 'class_structure Grammar.Entry.e)
      None
      [None, None,
       [Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_list0
                            (Grammar.s_rules
                               [Grammar.production
                                  (Grammar.r_next
                                     (Grammar.r_next Grammar.r_stop
                                        (Grammar.s_nterm
                                           (class_str_item :
                                            'class_str_item Grammar.Entry.e)))
                                     (Grammar.s_token ("", ";")),
                                   (fun _ (cf : 'class_str_item)
                                        (loc : Ploc.t) ->
                                      (cf : 'e__194)))])),
                       (fun (a : 'e__194 list) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.List a) : 'e__195)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_list")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_list", loc, a) : 'e__195)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "list")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                           'e__195)))])),
           (fun (cf : 'e__195) (loc : Ploc.t) -> (cf : 'class_structure)))]];
    Grammar.extension (class_self_patt : 'class_self_patt Grammar.Entry.e)
      None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("", "(")))
                      (Grammar.s_nterm (patt : 'patt Grammar.Entry.e)))
                   (Grammar.s_token ("", ":")))
                (Grammar.s_nterm (ctyp : 'ctyp Grammar.Entry.e)))
             (Grammar.s_token ("", ")")),
           (fun _ (t : 'ctyp) _ (p : 'patt) _ (loc : Ploc.t) ->
              (Qast.Node ("PaTyc", [Qast.Loc; p; t]) : 'class_self_patt)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "(")))
                (Grammar.s_nterm (patt : 'patt Grammar.Entry.e)))
             (Grammar.s_token ("", ")")),
           (fun _ (p : 'patt) _ (loc : Ploc.t) -> (p : 'class_self_patt)))]];
    Grammar.extension (class_str_item : 'class_str_item Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop
                (Grammar.s_token ("", "initializer")))
             (Grammar.s_nterm (expr : 'expr Grammar.Entry.e)),
           (fun (se : 'expr) _ (loc : Ploc.t) ->
              (Qast.Node ("CrIni", [Qast.Loc; se]) : 'class_str_item)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next Grammar.r_stop
                      (Grammar.s_token ("", "type")))
                   (Grammar.s_nterm (ctyp : 'ctyp Grammar.Entry.e)))
                (Grammar.s_token ("", "=")))
             (Grammar.s_nterm (ctyp : 'ctyp Grammar.Entry.e)),
           (fun (t2 : 'ctyp) _ (t1 : 'ctyp) _ (loc : Ploc.t) ->
              (Qast.Node ("CrCtr", [Qast.Loc; t1; t2]) : 'class_str_item)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("", "method")))
                         (Grammar.s_facto
                            (Grammar.s_rules
                               [Grammar.production
                                  (Grammar.r_next Grammar.r_stop
                                     (Grammar.s_flag
                                        (Grammar.s_token ("", "!"))),
                                   (fun (a : bool) (loc : Ploc.t) ->
                                      (Qast.VaVal (Qast.Bool a) : 'e__207)));
                                Grammar.production
                                  (Grammar.r_next Grammar.r_stop
                                     (Grammar.s_token ("ANTIQUOT", "_!")),
                                   (fun (a : string) (loc : Ploc.t) ->
                                      (Qast.VaAnt ("_!", loc, a) : 'e__207)));
                                Grammar.production
                                  (Grammar.r_next Grammar.r_stop
                                     (Grammar.s_token ("ANTIQUOT", "!")),
                                   (fun (a : string) (loc : Ploc.t) ->
                                      (Qast.VaVal (Qast.VaAnt ("!", loc, a)) :
                                       'e__207)))])))
                      (Grammar.s_facto
                         (Grammar.s_rules
                            [Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_flag
                                     (Grammar.s_token ("", "private"))),
                                (fun (a : bool) (loc : Ploc.t) ->
                                   (Qast.VaVal (Qast.Bool a) : 'e__208)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "_priv")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaAnt ("_priv", loc, a) : 'e__208)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "priv")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaVal (Qast.VaAnt ("priv", loc, a)) :
                                    'e__208)))])))
                   (Grammar.s_facto
                      (Grammar.s_rules
                         [Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_nterm
                                  (lident : 'lident Grammar.Entry.e)),
                             (fun (a : 'lident) (loc : Ploc.t) ->
                                (Qast.VaVal a : 'e__209)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "_")),
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaAnt ("_", loc, a) : 'e__209)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "")),
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaVal (Qast.VaAnt ("", loc, a)) :
                                 'e__209)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "_lid")),
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaAnt ("_lid", loc, a) : 'e__209)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "lid")),
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaVal (Qast.VaAnt ("lid", loc, a)) :
                                 'e__209)))])))
                (Grammar.s_facto
                   (Grammar.s_rules
                      [Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_opt
                               (Grammar.s_nterm
                                  (polyt : 'polyt Grammar.Entry.e))),
                          (fun (a : 'polyt option) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.Option a) : 'e__210)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_opt")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_opt", loc, a) : 'e__210)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "opt")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("opt", loc, a)) :
                              'e__210)))])))
             (Grammar.s_nterm (fun_binding : 'fun_binding Grammar.Entry.e)),
           (fun (e : 'fun_binding) (topt : 'e__210) (l : 'e__209)
                (pf : 'e__208) (ovf : 'e__207) _ (loc : Ploc.t) ->
              (Qast.Node ("CrMth", [Qast.Loc; ovf; pf; l; topt; e]) :
               'class_str_item)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("", "method")))
                         (Grammar.s_token ("", "virtual")))
                      (Grammar.s_facto
                         (Grammar.s_rules
                            [Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_flag
                                     (Grammar.s_token ("", "private"))),
                                (fun (a : bool) (loc : Ploc.t) ->
                                   (Qast.VaVal (Qast.Bool a) : 'e__205)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "_opt")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaAnt ("_opt", loc, a) : 'e__205)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "opt")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaVal (Qast.VaAnt ("opt", loc, a)) :
                                    'e__205)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "_flag")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaAnt ("_flag", loc, a) : 'e__205)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "flag")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaVal (Qast.VaAnt ("flag", loc, a)) :
                                    'e__205)))])))
                   (Grammar.s_facto
                      (Grammar.s_rules
                         [Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_nterm
                                  (lident : 'lident Grammar.Entry.e)),
                             (fun (a : 'lident) (loc : Ploc.t) ->
                                (Qast.VaVal a : 'e__206)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "_")),
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaAnt ("_", loc, a) : 'e__206)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "")),
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaVal (Qast.VaAnt ("", loc, a)) :
                                 'e__206)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "_lid")),
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaAnt ("_lid", loc, a) : 'e__206)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "lid")),
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaVal (Qast.VaAnt ("lid", loc, a)) :
                                 'e__206)))])))
                (Grammar.s_token ("", ":")))
             (Grammar.s_nterm (ctyp : 'ctyp Grammar.Entry.e)),
           (fun (t : 'ctyp) _ (l : 'e__206) (pf : 'e__205) _ _
                (loc : Ploc.t) ->
              (Qast.Node ("CrVir", [Qast.Loc; pf; l; t]) : 'class_str_item)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("", "value")))
                         (Grammar.s_token ("", "virtual")))
                      (Grammar.s_facto
                         (Grammar.s_rules
                            [Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_flag
                                     (Grammar.s_token ("", "mutable"))),
                                (fun (a : bool) (loc : Ploc.t) ->
                                   (Qast.VaVal (Qast.Bool a) : 'e__203)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "_opt")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaAnt ("_opt", loc, a) : 'e__203)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "opt")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaVal (Qast.VaAnt ("opt", loc, a)) :
                                    'e__203)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "_flag")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaAnt ("_flag", loc, a) : 'e__203)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "flag")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaVal (Qast.VaAnt ("flag", loc, a)) :
                                    'e__203)))])))
                   (Grammar.s_facto
                      (Grammar.s_rules
                         [Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_nterm
                                  (lident : 'lident Grammar.Entry.e)),
                             (fun (a : 'lident) (loc : Ploc.t) ->
                                (Qast.VaVal a : 'e__204)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "_")),
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaAnt ("_", loc, a) : 'e__204)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "")),
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaVal (Qast.VaAnt ("", loc, a)) :
                                 'e__204)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "_lid")),
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaAnt ("_lid", loc, a) : 'e__204)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "lid")),
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaVal (Qast.VaAnt ("lid", loc, a)) :
                                 'e__204)))])))
                (Grammar.s_token ("", ":")))
             (Grammar.s_nterm (ctyp : 'ctyp Grammar.Entry.e)),
           (fun (t : 'ctyp) _ (lab : 'e__204) (mf : 'e__203) _ _
                (loc : Ploc.t) ->
              (Qast.Node ("CrVav", [Qast.Loc; mf; lab; t]) :
               'class_str_item)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("", "value")))
                      (Grammar.s_facto
                         (Grammar.s_rules
                            [Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_flag
                                     (Grammar.s_token ("", "!"))),
                                (fun (a : bool) (loc : Ploc.t) ->
                                   (Qast.VaVal (Qast.Bool a) : 'e__200)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "_!")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaAnt ("_!", loc, a) : 'e__200)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "!")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaVal (Qast.VaAnt ("!", loc, a)) :
                                    'e__200)))])))
                   (Grammar.s_facto
                      (Grammar.s_rules
                         [Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_flag
                                  (Grammar.s_token ("", "mutable"))),
                             (fun (a : bool) (loc : Ploc.t) ->
                                (Qast.VaVal (Qast.Bool a) : 'e__201)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "_opt")),
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaAnt ("_opt", loc, a) : 'e__201)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "opt")),
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaVal (Qast.VaAnt ("opt", loc, a)) :
                                 'e__201)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "_flag")),
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaAnt ("_flag", loc, a) : 'e__201)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "flag")),
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaVal (Qast.VaAnt ("flag", loc, a)) :
                                 'e__201)))])))
                (Grammar.s_facto
                   (Grammar.s_rules
                      [Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_nterm
                               (lident : 'lident Grammar.Entry.e)),
                          (fun (a : 'lident) (loc : Ploc.t) ->
                             (Qast.VaVal a : 'e__202)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_", loc, a) : 'e__202)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("", loc, a)) :
                              'e__202)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_lid")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_lid", loc, a) : 'e__202)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "lid")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("lid", loc, a)) :
                              'e__202)))])))
             (Grammar.s_nterm
                (cvalue_binding : 'cvalue_binding Grammar.Entry.e)),
           (fun (e : 'cvalue_binding) (lab : 'e__202) (mf : 'e__201)
                (ovf : 'e__200) _ (loc : Ploc.t) ->
              (Qast.Node ("CrVal", [Qast.Loc; ovf; mf; lab; e]) :
               'class_str_item)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next Grammar.r_stop
                      (Grammar.s_token ("", "inherit")))
                   (Grammar.s_token ("", "!")))
                (Grammar.s_nterm (class_expr : 'class_expr Grammar.Entry.e)))
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_opt
                            (Grammar.s_nterm
                               (as_lident : 'as_lident Grammar.Entry.e))),
                       (fun (a : 'as_lident option) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.Option a) : 'e__199)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_opt")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_opt", loc, a) : 'e__199)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "opt")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("opt", loc, a)) :
                           'e__199)))])),
           (fun (pb : 'e__199) (ce : 'class_expr) _ _ (loc : Ploc.t) ->
              (Qast.Node
                 ("CrInh", [Qast.Loc; Qast.Node ("Override", []); ce; pb]) :
               'class_str_item)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop
                   (Grammar.s_token ("", "inherit")))
                (Grammar.s_nterm (class_expr : 'class_expr Grammar.Entry.e)))
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_opt
                            (Grammar.s_nterm
                               (as_lident : 'as_lident Grammar.Entry.e))),
                       (fun (a : 'as_lident option) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.Option a) : 'e__198)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_opt")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_opt", loc, a) : 'e__198)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "opt")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("opt", loc, a)) :
                           'e__198)))])),
           (fun (pb : 'e__198) (ce : 'class_expr) _ (loc : Ploc.t) ->
              (Qast.Node
                 ("CrInh", [Qast.Loc; Qast.Node ("Fresh", []); ce; pb]) :
               'class_str_item)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop
                   (Grammar.s_token ("", "declare")))
                (Grammar.s_facto
                   (Grammar.s_rules
                      [Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_list0
                               (Grammar.s_rules
                                  [Grammar.production
                                     (Grammar.r_next
                                        (Grammar.r_next Grammar.r_stop
                                           (Grammar.s_nterm
                                              (class_str_item :
                                               'class_str_item
                                                 Grammar.Entry.e)))
                                        (Grammar.s_token ("", ";")),
                                      (fun _ (s : 'class_str_item)
                                           (loc : Ploc.t) ->
                                         (s : 'e__196)))])),
                          (fun (a : 'e__196 list) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.List a) : 'e__197)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_list")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_list", loc, a) : 'e__197)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "list")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                              'e__197)))])))
             (Grammar.s_token ("", "end")),
           (fun _ (st : 'e__197) _ (loc : Ploc.t) ->
              (Qast.Node ("CrDcl", [Qast.Loc; st]) : 'class_str_item)))]];
    Grammar.extension (as_lident : 'as_lident Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "as")))
             (Grammar.s_token ("LIDENT", "")),
           (fun (i : string) _ (loc : Ploc.t) -> (mkident i : 'as_lident)))]];
    Grammar.extension (polyt : 'polyt Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", ":")))
             (Grammar.s_nterm (ctyp : 'ctyp Grammar.Entry.e)),
           (fun (t : 'ctyp) _ (loc : Ploc.t) -> (t : 'polyt)))]];
    Grammar.extension (cvalue_binding : 'cvalue_binding Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next Grammar.r_stop
                      (Grammar.s_token ("", ":>")))
                   (Grammar.s_nterm (ctyp : 'ctyp Grammar.Entry.e)))
                (Grammar.s_token ("", "=")))
             (Grammar.s_nterm (expr : 'expr Grammar.Entry.e)),
           (fun (e : 'expr) _ (t : 'ctyp) _ (loc : Ploc.t) ->
              (Qast.Node ("ExCoe", [Qast.Loc; e; Qast.Option None; t]) :
               'cvalue_binding)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("", ":")))
                         (Grammar.s_nterm (ctyp : 'ctyp Grammar.Entry.e)))
                      (Grammar.s_token ("", ":>")))
                   (Grammar.s_nterm (ctyp : 'ctyp Grammar.Entry.e)))
                (Grammar.s_token ("", "=")))
             (Grammar.s_nterm (expr : 'expr Grammar.Entry.e)),
           (fun (e : 'expr) _ (t2 : 'ctyp) _ (t : 'ctyp) _ (loc : Ploc.t) ->
              (Qast.Node ("ExCoe", [Qast.Loc; e; Qast.Option (Some t); t2]) :
               'cvalue_binding)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", ":")))
                   (Grammar.s_nterm (ctyp : 'ctyp Grammar.Entry.e)))
                (Grammar.s_token ("", "=")))
             (Grammar.s_nterm (expr : 'expr Grammar.Entry.e)),
           (fun (e : 'expr) _ (t : 'ctyp) _ (loc : Ploc.t) ->
              (Qast.Node ("ExTyc", [Qast.Loc; e; t]) : 'cvalue_binding)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "=")))
             (Grammar.s_nterm (expr : 'expr Grammar.Entry.e)),
           (fun (e : 'expr) _ (loc : Ploc.t) -> (e : 'cvalue_binding)))]];
    Grammar.extension (lident : 'lident Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next Grammar.r_stop (Grammar.s_token ("LIDENT", "")),
           (fun (i : string) (loc : Ploc.t) -> (mkident i : 'lident)))]];
    Grammar.extension (class_type : 'class_type Grammar.Entry.e) None
      [Some "top", Some Gramext.RightA,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("", "[")))
                      (Grammar.s_nterm (ctyp : 'ctyp Grammar.Entry.e)))
                   (Grammar.s_token ("", "]")))
                (Grammar.s_token ("", "->")))
             Grammar.s_self,
           (fun (ct : 'class_type) _ _ (t : 'ctyp) _ (loc : Ploc.t) ->
              (Qast.Node ("CtFun", [Qast.Loc; t; ct]) : 'class_type)))];
       Some "alg_attribute", Some Gramext.LeftA,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                   (Grammar.s_token ("", "[@")))
                (Grammar.s_facto
                   (Grammar.s_rules
                      [Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_nterm
                               (attribute_body :
                                'attribute_body Grammar.Entry.e)),
                          (fun (a : 'attribute_body) (loc : Ploc.t) ->
                             (Qast.VaVal a : 'e__211)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_attribute")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_attribute", loc, a) : 'e__211)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "attribute")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("attribute", loc, a)) :
                              'e__211)))])))
             (Grammar.s_token ("", "]")),
           (fun _ (attr : 'e__211) _ (t1 : 'class_type) (loc : Ploc.t) ->
              (Qast.Node ("CtAtt", [Qast.Loc; t1; attr]) : 'class_type)))];
       None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                   (Grammar.s_token ("", "[")))
                (Grammar.s_facto
                   (Grammar.s_rules
                      [Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_list1sep
                               (Grammar.s_nterm
                                  (ctyp : 'ctyp Grammar.Entry.e))
                               (Grammar.s_token ("", ",")) false),
                          (fun (a : 'ctyp list) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.List a) : 'e__215)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_list")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_list", loc, a) : 'e__215)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "list")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                              'e__215)))])))
             (Grammar.s_token ("", "]")),
           (fun _ (tl : 'e__215) _ (ct : 'class_type) (loc : Ploc.t) ->
              (Qast.Node ("CtCon", [Qast.Loc; ct; tl]) : 'class_type)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next Grammar.r_stop
                      (Grammar.s_token ("", "object")))
                   (Grammar.s_facto
                      (Grammar.s_rules
                         [Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_opt
                                  (Grammar.s_nterm
                                     (class_self_type :
                                      'class_self_type Grammar.Entry.e))),
                             (fun (a : 'class_self_type option)
                                  (loc : Ploc.t) ->
                                (Qast.VaVal (Qast.Option a) : 'e__212)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "_opt")),
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaAnt ("_opt", loc, a) : 'e__212)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "opt")),
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaVal (Qast.VaAnt ("opt", loc, a)) :
                                 'e__212)))])))
                (Grammar.s_facto
                   (Grammar.s_rules
                      [Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_list0
                               (Grammar.s_rules
                                  [Grammar.production
                                     (Grammar.r_next
                                        (Grammar.r_next Grammar.r_stop
                                           (Grammar.s_nterm
                                              (class_sig_item :
                                               'class_sig_item
                                                 Grammar.Entry.e)))
                                        (Grammar.s_token ("", ";")),
                                      (fun _ (csf : 'class_sig_item)
                                           (loc : Ploc.t) ->
                                         (csf : 'e__213)))])),
                          (fun (a : 'e__213 list) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.List a) : 'e__214)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_list")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_list", loc, a) : 'e__214)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "list")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                              'e__214)))])))
             (Grammar.s_token ("", "end")),
           (fun _ (csf : 'e__214) (cst : 'e__212) _ (loc : Ploc.t) ->
              (Qast.Node ("CtSig", [Qast.Loc; cst; csf]) : 'class_type)))];
       Some "apply", None,
       [Grammar.production
          (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
             Grammar.s_self,
           (fun (ct2 : 'class_type) (ct1 : 'class_type) (loc : Ploc.t) ->
              (Qast.Node ("CtApp", [Qast.Loc; ct1; ct2]) : 'class_type)))];
       Some "dot", None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                (Grammar.s_token ("", ".")))
             Grammar.s_self,
           (fun (ct2 : 'class_type) _ (ct1 : 'class_type) (loc : Ploc.t) ->
              (Qast.Node ("CtAcc", [Qast.Loc; ct1; ct2]) : 'class_type)))];
       Some "simple", None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "(")))
                Grammar.s_self)
             (Grammar.s_token ("", ")")),
           (fun _ (ct : 'class_type) _ (loc : Ploc.t) -> (ct : 'class_type)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("UIDENT", "")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.Str a) : 'e__217)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_id")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_id", loc, a) : 'e__217)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "id")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("id", loc, a)) :
                           'e__217)))])),
           (fun (i : 'e__217) (loc : Ploc.t) ->
              (Qast.Node ("CtIde", [Qast.Loc; i]) : 'class_type)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("LIDENT", "")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.Str a) : 'e__216)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_id")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_id", loc, a) : 'e__216)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "id")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("id", loc, a)) :
                           'e__216)))])),
           (fun (i : 'e__216) (loc : Ploc.t) ->
              (Qast.Node ("CtIde", [Qast.Loc; i]) : 'class_type)))]];
    Grammar.extension (class_self_type : 'class_self_type Grammar.Entry.e)
      None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "(")))
                (Grammar.s_nterm (ctyp : 'ctyp Grammar.Entry.e)))
             (Grammar.s_token ("", ")")),
           (fun _ (t : 'ctyp) _ (loc : Ploc.t) -> (t : 'class_self_type)))]];
    Grammar.extension (class_sig_item : 'class_sig_item Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next Grammar.r_stop
                      (Grammar.s_token ("", "type")))
                   (Grammar.s_nterm (ctyp : 'ctyp Grammar.Entry.e)))
                (Grammar.s_token ("", "=")))
             (Grammar.s_nterm (ctyp : 'ctyp Grammar.Entry.e)),
           (fun (t2 : 'ctyp) _ (t1 : 'ctyp) _ (loc : Ploc.t) ->
              (Qast.Node ("CgCtr", [Qast.Loc; t1; t2]) : 'class_sig_item)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("", "method")))
                      (Grammar.s_facto
                         (Grammar.s_rules
                            [Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_flag
                                     (Grammar.s_token ("", "private"))),
                                (fun (a : bool) (loc : Ploc.t) ->
                                   (Qast.VaVal (Qast.Bool a) : 'e__225)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "_opt")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaAnt ("_opt", loc, a) : 'e__225)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "opt")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaVal (Qast.VaAnt ("opt", loc, a)) :
                                    'e__225)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "_flag")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaAnt ("_flag", loc, a) : 'e__225)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "flag")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaVal (Qast.VaAnt ("flag", loc, a)) :
                                    'e__225)))])))
                   (Grammar.s_facto
                      (Grammar.s_rules
                         [Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_nterm
                                  (lident : 'lident Grammar.Entry.e)),
                             (fun (a : 'lident) (loc : Ploc.t) ->
                                (Qast.VaVal a : 'e__226)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "_")),
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaAnt ("_", loc, a) : 'e__226)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "")),
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaVal (Qast.VaAnt ("", loc, a)) :
                                 'e__226)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "_lid")),
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaAnt ("_lid", loc, a) : 'e__226)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "lid")),
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaVal (Qast.VaAnt ("lid", loc, a)) :
                                 'e__226)))])))
                (Grammar.s_token ("", ":")))
             (Grammar.s_nterm (ctyp : 'ctyp Grammar.Entry.e)),
           (fun (t : 'ctyp) _ (l : 'e__226) (pf : 'e__225) _ (loc : Ploc.t) ->
              (Qast.Node ("CgMth", [Qast.Loc; pf; l; t]) : 'class_sig_item)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("", "method")))
                         (Grammar.s_token ("", "virtual")))
                      (Grammar.s_facto
                         (Grammar.s_rules
                            [Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_flag
                                     (Grammar.s_token ("", "private"))),
                                (fun (a : bool) (loc : Ploc.t) ->
                                   (Qast.VaVal (Qast.Bool a) : 'e__223)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "_opt")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaAnt ("_opt", loc, a) : 'e__223)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "opt")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaVal (Qast.VaAnt ("opt", loc, a)) :
                                    'e__223)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "_flag")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaAnt ("_flag", loc, a) : 'e__223)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "flag")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaVal (Qast.VaAnt ("flag", loc, a)) :
                                    'e__223)))])))
                   (Grammar.s_facto
                      (Grammar.s_rules
                         [Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_nterm
                                  (lident : 'lident Grammar.Entry.e)),
                             (fun (a : 'lident) (loc : Ploc.t) ->
                                (Qast.VaVal a : 'e__224)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "_")),
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaAnt ("_", loc, a) : 'e__224)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "")),
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaVal (Qast.VaAnt ("", loc, a)) :
                                 'e__224)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "_lid")),
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaAnt ("_lid", loc, a) : 'e__224)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "lid")),
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaVal (Qast.VaAnt ("lid", loc, a)) :
                                 'e__224)))])))
                (Grammar.s_token ("", ":")))
             (Grammar.s_nterm (ctyp : 'ctyp Grammar.Entry.e)),
           (fun (t : 'ctyp) _ (l : 'e__224) (pf : 'e__223) _ _
                (loc : Ploc.t) ->
              (Qast.Node ("CgVir", [Qast.Loc; pf; l; t]) : 'class_sig_item)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("", "value")))
                         (Grammar.s_facto
                            (Grammar.s_rules
                               [Grammar.production
                                  (Grammar.r_next Grammar.r_stop
                                     (Grammar.s_flag
                                        (Grammar.s_token ("", "mutable"))),
                                   (fun (a : bool) (loc : Ploc.t) ->
                                      (Qast.VaVal (Qast.Bool a) : 'e__220)));
                                Grammar.production
                                  (Grammar.r_next Grammar.r_stop
                                     (Grammar.s_token ("ANTIQUOT", "_opt")),
                                   (fun (a : string) (loc : Ploc.t) ->
                                      (Qast.VaAnt ("_opt", loc, a) :
                                       'e__220)));
                                Grammar.production
                                  (Grammar.r_next Grammar.r_stop
                                     (Grammar.s_token ("ANTIQUOT", "opt")),
                                   (fun (a : string) (loc : Ploc.t) ->
                                      (Qast.VaVal
                                         (Qast.VaAnt ("opt", loc, a)) :
                                       'e__220)));
                                Grammar.production
                                  (Grammar.r_next Grammar.r_stop
                                     (Grammar.s_token ("ANTIQUOT", "_flag")),
                                   (fun (a : string) (loc : Ploc.t) ->
                                      (Qast.VaAnt ("_flag", loc, a) :
                                       'e__220)));
                                Grammar.production
                                  (Grammar.r_next Grammar.r_stop
                                     (Grammar.s_token ("ANTIQUOT", "flag")),
                                   (fun (a : string) (loc : Ploc.t) ->
                                      (Qast.VaVal
                                         (Qast.VaAnt ("flag", loc, a)) :
                                       'e__220)))])))
                      (Grammar.s_facto
                         (Grammar.s_rules
                            [Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_flag
                                     (Grammar.s_token ("", "virtual"))),
                                (fun (a : bool) (loc : Ploc.t) ->
                                   (Qast.VaVal (Qast.Bool a) : 'e__221)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "_opt")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaAnt ("_opt", loc, a) : 'e__221)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "opt")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaVal (Qast.VaAnt ("opt", loc, a)) :
                                    'e__221)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "_flag")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaAnt ("_flag", loc, a) : 'e__221)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "flag")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaVal (Qast.VaAnt ("flag", loc, a)) :
                                    'e__221)))])))
                   (Grammar.s_facto
                      (Grammar.s_rules
                         [Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_nterm
                                  (lident : 'lident Grammar.Entry.e)),
                             (fun (a : 'lident) (loc : Ploc.t) ->
                                (Qast.VaVal a : 'e__222)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "_")),
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaAnt ("_", loc, a) : 'e__222)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "")),
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaVal (Qast.VaAnt ("", loc, a)) :
                                 'e__222)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "_lid")),
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaAnt ("_lid", loc, a) : 'e__222)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "lid")),
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaVal (Qast.VaAnt ("lid", loc, a)) :
                                 'e__222)))])))
                (Grammar.s_token ("", ":")))
             (Grammar.s_nterm (ctyp : 'ctyp Grammar.Entry.e)),
           (fun (t : 'ctyp) _ (l : 'e__222) (vf : 'e__221) (mf : 'e__220) _
                (loc : Ploc.t) ->
              (Qast.Node ("CgVal", [Qast.Loc; mf; vf; l; t]) :
               'class_sig_item)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "inherit")))
             (Grammar.s_nterm (class_type : 'class_type Grammar.Entry.e)),
           (fun (cs : 'class_type) _ (loc : Ploc.t) ->
              (Qast.Node ("CgInh", [Qast.Loc; cs]) : 'class_sig_item)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop
                   (Grammar.s_token ("", "declare")))
                (Grammar.s_facto
                   (Grammar.s_rules
                      [Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_list0
                               (Grammar.s_rules
                                  [Grammar.production
                                     (Grammar.r_next
                                        (Grammar.r_next Grammar.r_stop
                                           (Grammar.s_nterm
                                              (class_sig_item :
                                               'class_sig_item
                                                 Grammar.Entry.e)))
                                        (Grammar.s_token ("", ";")),
                                      (fun _ (s : 'class_sig_item)
                                           (loc : Ploc.t) ->
                                         (s : 'e__218)))])),
                          (fun (a : 'e__218 list) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.List a) : 'e__219)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_list")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_list", loc, a) : 'e__219)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "list")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                              'e__219)))])))
             (Grammar.s_token ("", "end")),
           (fun _ (st : 'e__219) _ (loc : Ploc.t) ->
              (Qast.Node ("CgDcl", [Qast.Loc; st]) : 'class_sig_item)))]];
    Grammar.extension (class_description : 'class_description Grammar.Entry.e)
      None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_facto
                            (Grammar.s_rules
                               [Grammar.production
                                  (Grammar.r_next Grammar.r_stop
                                     (Grammar.s_flag
                                        (Grammar.s_token ("", "virtual"))),
                                   (fun (a : bool) (loc : Ploc.t) ->
                                      (Qast.VaVal (Qast.Bool a) : 'e__227)));
                                Grammar.production
                                  (Grammar.r_next Grammar.r_stop
                                     (Grammar.s_token ("ANTIQUOT", "_opt")),
                                   (fun (a : string) (loc : Ploc.t) ->
                                      (Qast.VaAnt ("_opt", loc, a) :
                                       'e__227)));
                                Grammar.production
                                  (Grammar.r_next Grammar.r_stop
                                     (Grammar.s_token ("ANTIQUOT", "opt")),
                                   (fun (a : string) (loc : Ploc.t) ->
                                      (Qast.VaVal
                                         (Qast.VaAnt ("opt", loc, a)) :
                                       'e__227)));
                                Grammar.production
                                  (Grammar.r_next Grammar.r_stop
                                     (Grammar.s_token ("ANTIQUOT", "_flag")),
                                   (fun (a : string) (loc : Ploc.t) ->
                                      (Qast.VaAnt ("_flag", loc, a) :
                                       'e__227)));
                                Grammar.production
                                  (Grammar.r_next Grammar.r_stop
                                     (Grammar.s_token ("ANTIQUOT", "flag")),
                                   (fun (a : string) (loc : Ploc.t) ->
                                      (Qast.VaVal
                                         (Qast.VaAnt ("flag", loc, a)) :
                                       'e__227)))])))
                      (Grammar.s_facto
                         (Grammar.s_rules
                            [Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("LIDENT", "")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaVal (Qast.Str a) : 'e__228)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "_")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaAnt ("_", loc, a) : 'e__228)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaVal (Qast.VaAnt ("", loc, a)) :
                                    'e__228)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "_lid")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaAnt ("_lid", loc, a) : 'e__228)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "lid")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaVal (Qast.VaAnt ("lid", loc, a)) :
                                    'e__228)))])))
                   (Grammar.s_nterm
                      (class_type_parameters :
                       'class_type_parameters Grammar.Entry.e)))
                (Grammar.s_token ("", ":")))
             (Grammar.s_nterm (class_type : 'class_type Grammar.Entry.e)),
           (fun (ct : 'class_type) _ (ctp : 'class_type_parameters)
                (n : 'e__228) (vf : 'e__227) (loc : Ploc.t) ->
              (Qast.Record
                 ["ciLoc", Qast.Loc; "ciVir", vf; "ciPrm", ctp; "ciNam", n;
                  "ciExp", ct] :
               'class_description)))]];
    Grammar.extension
      (class_type_declaration : 'class_type_declaration Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_facto
                            (Grammar.s_rules
                               [Grammar.production
                                  (Grammar.r_next Grammar.r_stop
                                     (Grammar.s_flag
                                        (Grammar.s_token ("", "virtual"))),
                                   (fun (a : bool) (loc : Ploc.t) ->
                                      (Qast.VaVal (Qast.Bool a) : 'e__229)));
                                Grammar.production
                                  (Grammar.r_next Grammar.r_stop
                                     (Grammar.s_token ("ANTIQUOT", "_opt")),
                                   (fun (a : string) (loc : Ploc.t) ->
                                      (Qast.VaAnt ("_opt", loc, a) :
                                       'e__229)));
                                Grammar.production
                                  (Grammar.r_next Grammar.r_stop
                                     (Grammar.s_token ("ANTIQUOT", "opt")),
                                   (fun (a : string) (loc : Ploc.t) ->
                                      (Qast.VaVal
                                         (Qast.VaAnt ("opt", loc, a)) :
                                       'e__229)));
                                Grammar.production
                                  (Grammar.r_next Grammar.r_stop
                                     (Grammar.s_token ("ANTIQUOT", "_flag")),
                                   (fun (a : string) (loc : Ploc.t) ->
                                      (Qast.VaAnt ("_flag", loc, a) :
                                       'e__229)));
                                Grammar.production
                                  (Grammar.r_next Grammar.r_stop
                                     (Grammar.s_token ("ANTIQUOT", "flag")),
                                   (fun (a : string) (loc : Ploc.t) ->
                                      (Qast.VaVal
                                         (Qast.VaAnt ("flag", loc, a)) :
                                       'e__229)))])))
                      (Grammar.s_facto
                         (Grammar.s_rules
                            [Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("LIDENT", "")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaVal (Qast.Str a) : 'e__230)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "_")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaAnt ("_", loc, a) : 'e__230)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaVal (Qast.VaAnt ("", loc, a)) :
                                    'e__230)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "_lid")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaAnt ("_lid", loc, a) : 'e__230)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "lid")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaVal (Qast.VaAnt ("lid", loc, a)) :
                                    'e__230)))])))
                   (Grammar.s_nterm
                      (class_type_parameters :
                       'class_type_parameters Grammar.Entry.e)))
                (Grammar.s_token ("", "=")))
             (Grammar.s_nterm (class_type : 'class_type Grammar.Entry.e)),
           (fun (cs : 'class_type) _ (ctp : 'class_type_parameters)
                (n : 'e__230) (vf : 'e__229) (loc : Ploc.t) ->
              (Qast.Record
                 ["ciLoc", Qast.Loc; "ciVir", vf; "ciPrm", ctp; "ciNam", n;
                  "ciExp", cs] :
               'class_type_declaration)))]];
    Grammar.extension (expr : 'expr Grammar.Entry.e)
      (Some (Gramext.Level "apply"))
      [None, Some Gramext.LeftA,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next Grammar.r_stop
                      (Grammar.s_token ("", "object")))
                   (Grammar.s_facto
                      (Grammar.s_rules
                         [Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_opt
                                  (Grammar.s_nterm
                                     (class_self_patt :
                                      'class_self_patt Grammar.Entry.e))),
                             (fun (a : 'class_self_patt option)
                                  (loc : Ploc.t) ->
                                (Qast.VaVal (Qast.Option a) : 'e__232)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "_opt")),
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaAnt ("_opt", loc, a) : 'e__232)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "opt")),
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaVal (Qast.VaAnt ("opt", loc, a)) :
                                 'e__232)))])))
                (Grammar.s_nterm
                   (class_structure : 'class_structure Grammar.Entry.e)))
             (Grammar.s_token ("", "end")),
           (fun _ (cf : 'class_structure) (cspo : 'e__232) _ (loc : Ploc.t) ->
              (Qast.Node ("ExObj", [Qast.Loc; cspo; cf]) : 'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "new")))
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_nterm
                            (class_longident :
                             'class_longident Grammar.Entry.e)),
                       (fun (a : 'class_longident) (loc : Ploc.t) ->
                          (Qast.VaVal a : 'e__231)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_list")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_list", loc, a) : 'e__231)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "list")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                           'e__231)))])),
           (fun (i : 'e__231) _ (loc : Ploc.t) ->
              (Qast.Node ("ExNew", [Qast.Loc; i]) : 'expr)))]];
    Grammar.extension (expr : 'expr Grammar.Entry.e)
      (Some (Gramext.Level "."))
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                (Grammar.s_token ("", "#")))
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_nterm (lident : 'lident Grammar.Entry.e)),
                       (fun (a : 'lident) (loc : Ploc.t) ->
                          (Qast.VaVal a : 'e__233)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_", loc, a) : 'e__233)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("", loc, a)) : 'e__233)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_lid")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_lid", loc, a) : 'e__233)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "lid")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("lid", loc, a)) :
                           'e__233)))])),
           (fun (lab : 'e__233) _ (e : 'expr) (loc : Ploc.t) ->
              (Qast.Node ("ExSnd", [Qast.Loc; e; lab]) : 'expr)))]];
    Grammar.extension (expr : 'expr Grammar.Entry.e)
      (Some (Gramext.Level "simple"))
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "{<")))
                (Grammar.s_facto
                   (Grammar.s_rules
                      [Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_list0sep
                               (Grammar.s_nterm
                                  (field_expr : 'field_expr Grammar.Entry.e))
                               (Grammar.s_token ("", ";")) false),
                          (fun (a : 'field_expr list) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.List a) : 'e__234)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_list")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_list", loc, a) : 'e__234)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "list")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                              'e__234)))])))
             (Grammar.s_token ("", ">}")),
           (fun _ (fel : 'e__234) _ (loc : Ploc.t) ->
              (Qast.Node ("ExOvr", [Qast.Loc; fel]) : 'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("", "(")))
                      Grammar.s_self)
                   (Grammar.s_token ("", ":>")))
                (Grammar.s_nterm (ctyp : 'ctyp Grammar.Entry.e)))
             (Grammar.s_token ("", ")")),
           (fun _ (t : 'ctyp) _ (e : 'expr) _ (loc : Ploc.t) ->
              (Qast.Node ("ExCoe", [Qast.Loc; e; Qast.Option None; t]) :
               'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next
                         (Grammar.r_next
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("", "(")))
                            Grammar.s_self)
                         (Grammar.s_token ("", ":")))
                      (Grammar.s_nterm (ctyp : 'ctyp Grammar.Entry.e)))
                   (Grammar.s_token ("", ":>")))
                (Grammar.s_nterm (ctyp : 'ctyp Grammar.Entry.e)))
             (Grammar.s_token ("", ")")),
           (fun _ (t2 : 'ctyp) _ (t : 'ctyp) _ (e : 'expr) _ (loc : Ploc.t) ->
              (Qast.Node ("ExCoe", [Qast.Loc; e; Qast.Option (Some t); t2]) :
               'expr)))]];
    Grammar.extension (field_expr : 'field_expr Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop
                   (Grammar.s_nterm (lident : 'lident Grammar.Entry.e)))
                (Grammar.s_token ("", "=")))
             (Grammar.s_nterm (expr : 'expr Grammar.Entry.e)),
           (fun (e : 'expr) _ (l : 'lident) (loc : Ploc.t) ->
              (Qast.Tuple [l; e] : 'field_expr)))]];
    Grammar.extension (ctyp : 'ctyp Grammar.Entry.e)
      (Some (Gramext.Level "simple"))
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "<")))
                   (Grammar.s_facto
                      (Grammar.s_rules
                         [Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_list0sep
                                  (Grammar.s_nterm
                                     (field : 'field Grammar.Entry.e))
                                  (Grammar.s_token ("", ";")) false),
                             (fun (a : 'field list) (loc : Ploc.t) ->
                                (Qast.VaVal (Qast.List a) : 'e__236)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "_list")),
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaAnt ("_list", loc, a) : 'e__236)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "list")),
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                                 'e__236)))])))
                (Grammar.s_facto
                   (Grammar.s_rules
                      [Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_flag (Grammar.s_token ("", ".."))),
                          (fun (a : bool) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.Bool a) : 'e__237)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_opt")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_opt", loc, a) : 'e__237)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "opt")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("opt", loc, a)) :
                              'e__237)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_flag")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_flag", loc, a) : 'e__237)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "flag")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("flag", loc, a)) :
                              'e__237)))])))
             (Grammar.s_token ("", ">")),
           (fun _ (v : 'e__237) (ml : 'e__236) _ (loc : Ploc.t) ->
              (Qast.Node ("TyObj", [Qast.Loc; ml; v]) : 'ctyp)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "#")))
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_nterm
                            (class_longident :
                             'class_longident Grammar.Entry.e)),
                       (fun (a : 'class_longident) (loc : Ploc.t) ->
                          (Qast.VaVal a : 'e__235)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_list")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_list", loc, a) : 'e__235)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "list")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                           'e__235)))])),
           (fun (id : 'e__235) _ (loc : Ploc.t) ->
              (Qast.Node ("TyCls", [Qast.Loc; id]) : 'ctyp)))]];
    Grammar.extension (field : 'field Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop
                   (Grammar.s_token ("LIDENT", "")))
                (Grammar.s_token ("", ":")))
             (Grammar.s_nterm (ctyp : 'ctyp Grammar.Entry.e)),
           (fun (t : 'ctyp) _ (lab : string) (loc : Ploc.t) ->
              (Qast.Tuple [mkident lab; t] : 'field)))]];
    Grammar.extension (class_longident : 'class_longident Grammar.Entry.e)
      None
      [None, None,
       [Grammar.production
          (Grammar.r_next Grammar.r_stop (Grammar.s_token ("LIDENT", "")),
           (fun (i : string) (loc : Ploc.t) ->
              (Qast.List [mkident i] : 'class_longident)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop
                   (Grammar.s_token ("UIDENT", "")))
                (Grammar.s_token ("", ".")))
             Grammar.s_self,
           (fun (l : 'class_longident) _ (m : string) (loc : Ploc.t) ->
              (Qast.Cons (mkident m, l) : 'class_longident)))]];
    (* Labels *)
    Grammar.extension (ctyp : 'ctyp Grammar.Entry.e)
      (Some (Gramext.After "arrow"))
      [None, Some Gramext.NonA,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop
                (Grammar.s_facto
                   (Grammar.s_rules
                      [Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_nterm
                               (a_qic : 'a_qic Grammar.Entry.e)),
                          (fun (a : 'a_qic) (loc : Ploc.t) -> (a : 'e__239)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("QUESTIONIDENTCOLON", "")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.Str a) : 'e__239)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "?_:")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("?_:", loc, a) : 'e__239)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "?:")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("?:", loc, a)) :
                              'e__239)))])))
             Grammar.s_self,
           (fun (t : 'ctyp) (i : 'e__239) (loc : Ploc.t) ->
              (Qast.Node ("TyOlb", [Qast.Loc; i; t]) : 'ctyp)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop
                (Grammar.s_facto
                   (Grammar.s_rules
                      [Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_nterm
                               (a_tic : 'a_tic Grammar.Entry.e)),
                          (fun (a : 'a_tic) (loc : Ploc.t) -> (a : 'e__238)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("TILDEIDENTCOLON", "")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.Str a) : 'e__238)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "~_:")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("~_:", loc, a) : 'e__238)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "~:")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("~:", loc, a)) :
                              'e__238)))])))
             Grammar.s_self,
           (fun (t : 'ctyp) (i : 'e__238) (loc : Ploc.t) ->
              (Qast.Node ("TyLab", [Qast.Loc; i; t]) : 'ctyp)))]];
    Grammar.extension (ctyp : 'ctyp Grammar.Entry.e)
      (Some (Gramext.Level "simple"))
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("", "[")))
                         (Grammar.s_token ("", "<")))
                      (Grammar.s_nterm
                         (poly_variant_list :
                          'poly_variant_list Grammar.Entry.e)))
                   (Grammar.s_token ("", ">")))
                (Grammar.s_facto
                   (Grammar.s_rules
                      [Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_list1
                               (Grammar.s_nterm
                                  (name_tag : 'name_tag Grammar.Entry.e))),
                          (fun (a : 'name_tag list) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.List a) : 'e__240)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_list")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_list", loc, a) : 'e__240)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "list")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                              'e__240)))])))
             (Grammar.s_token ("", "]")),
           (fun _ (ntl : 'e__240) _ (rfl : 'poly_variant_list) _ _
                (loc : Ploc.t) ->
              (Qast.Node
                 ("TyVrn",
                  [Qast.Loc; rfl;
                   Qast.Option (Some (Qast.Option (Some ntl)))]) :
               'ctyp)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "[")))
                   (Grammar.s_token ("", "<")))
                (Grammar.s_nterm
                   (poly_variant_list : 'poly_variant_list Grammar.Entry.e)))
             (Grammar.s_token ("", "]")),
           (fun _ (rfl : 'poly_variant_list) _ _ (loc : Ploc.t) ->
              (Qast.Node
                 ("TyVrn",
                  [Qast.Loc; rfl;
                   Qast.Option
                     (Some
                        (Qast.Option (Some (Qast.VaVal (Qast.List [])))))]) :
               'ctyp)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "[")))
                   (Grammar.s_token ("", ">")))
                (Grammar.s_nterm
                   (poly_variant_list : 'poly_variant_list Grammar.Entry.e)))
             (Grammar.s_token ("", "]")),
           (fun _ (rfl : 'poly_variant_list) _ _ (loc : Ploc.t) ->
              (Qast.Node
                 ("TyVrn",
                  [Qast.Loc; rfl; Qast.Option (Some (Qast.Option None))]) :
               'ctyp)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "[")))
                   (Grammar.s_token ("", "=")))
                (Grammar.s_nterm
                   (poly_variant_list : 'poly_variant_list Grammar.Entry.e)))
             (Grammar.s_token ("", "]")),
           (fun _ (rfl : 'poly_variant_list) _ _ (loc : Ploc.t) ->
              (Qast.Node ("TyVrn", [Qast.Loc; rfl; Qast.Option None]) :
               'ctyp)))]];
    Grammar.extension (poly_variant_list : 'poly_variant_list Grammar.Entry.e)
      None
      [None, None,
       [Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_list0sep
                            (Grammar.s_nterm
                               (poly_variant : 'poly_variant Grammar.Entry.e))
                            (Grammar.s_token ("", "|")) false),
                       (fun (a : 'poly_variant list) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.List a) : 'e__241)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_list")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_list", loc, a) : 'e__241)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "list")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                           'e__241)))])),
           (fun (rfl : 'e__241) (loc : Ploc.t) ->
              (rfl : 'poly_variant_list)))]];
    Grammar.extension (poly_variant : 'poly_variant Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_nterm (ctyp : 'ctyp Grammar.Entry.e)),
           (fun (t : 'ctyp) (loc : Ploc.t) ->
              (Qast.Node ("PvInh", [Qast.Loc; t]) : 'poly_variant)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("", "`")))
                         (Grammar.s_facto
                            (Grammar.s_rules
                               [Grammar.production
                                  (Grammar.r_next Grammar.r_stop
                                     (Grammar.s_nterm
                                        (ident : 'ident Grammar.Entry.e)),
                                   (fun (a : 'ident) (loc : Ploc.t) ->
                                      (Qast.VaVal a : 'e__244)));
                                Grammar.production
                                  (Grammar.r_next Grammar.r_stop
                                     (Grammar.s_token ("ANTIQUOT", "_")),
                                   (fun (a : string) (loc : Ploc.t) ->
                                      (Qast.VaAnt ("_", loc, a) : 'e__244)));
                                Grammar.production
                                  (Grammar.r_next Grammar.r_stop
                                     (Grammar.s_token ("ANTIQUOT", "")),
                                   (fun (a : string) (loc : Ploc.t) ->
                                      (Qast.VaVal (Qast.VaAnt ("", loc, a)) :
                                       'e__244)))])))
                      (Grammar.s_token ("", "of")))
                   (Grammar.s_facto
                      (Grammar.s_rules
                         [Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_flag (Grammar.s_token ("", "&"))),
                             (fun (a : bool) (loc : Ploc.t) ->
                                (Qast.VaVal (Qast.Bool a) : 'e__245)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "_opt")),
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaAnt ("_opt", loc, a) : 'e__245)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "opt")),
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaVal (Qast.VaAnt ("opt", loc, a)) :
                                 'e__245)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "_flag")),
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaAnt ("_flag", loc, a) : 'e__245)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "flag")),
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaVal (Qast.VaAnt ("flag", loc, a)) :
                                 'e__245)))])))
                (Grammar.s_facto
                   (Grammar.s_rules
                      [Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_list1sep
                               (Grammar.s_nterml
                                  (ctyp : 'ctyp Grammar.Entry.e)
                                  "below_alg_attribute")
                               (Grammar.s_token ("", "&")) false),
                          (fun (a : 'ctyp list) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.List a) : 'e__246)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_list")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_list", loc, a) : 'e__246)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "list")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                              'e__246)))])))
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_list0
                            (Grammar.s_nterm
                               (alg_attribute :
                                'alg_attribute Grammar.Entry.e))),
                       (fun (a : 'alg_attribute list) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.List a) : 'e__247)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_list")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_list", loc, a) : 'e__247)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "list")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                           'e__247)))])),
           (fun (alg_attrs : 'e__247) (l : 'e__246) (ao : 'e__245) _
                (i : 'e__244) _ (loc : Ploc.t) ->
              (Qast.Node ("PvTag", [Qast.Loc; i; ao; l; alg_attrs]) :
               'poly_variant)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "`")))
                (Grammar.s_facto
                   (Grammar.s_rules
                      [Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_nterm
                               (ident : 'ident Grammar.Entry.e)),
                          (fun (a : 'ident) (loc : Ploc.t) ->
                             (Qast.VaVal a : 'e__242)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_", loc, a) : 'e__242)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("", loc, a)) :
                              'e__242)))])))
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_list0
                            (Grammar.s_nterm
                               (alg_attribute :
                                'alg_attribute Grammar.Entry.e))),
                       (fun (a : 'alg_attribute list) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.List a) : 'e__243)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_list")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_list", loc, a) : 'e__243)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "list")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                           'e__243)))])),
           (fun (alg_attrs : 'e__243) (i : 'e__242) _ (loc : Ploc.t) ->
              (Qast.Node
                 ("PvTag",
                  [Qast.Loc; i; Qast.VaVal (Qast.Bool true);
                   Qast.VaVal (Qast.List []); alg_attrs]) :
               'poly_variant)))]];
    Grammar.extension (name_tag : 'name_tag Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "`")))
             (Grammar.s_nterm (ident : 'ident Grammar.Entry.e)),
           (fun (i : 'ident) _ (loc : Ploc.t) -> (i : 'name_tag)))]];
    Grammar.extension (patt : 'patt Grammar.Entry.e)
      (Some (Gramext.Level "simple"))
      [None, None,
       [Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_nterm
                (patt_option_label : 'patt_option_label Grammar.Entry.e)),
           (fun (p : 'patt_option_label) (loc : Ploc.t) ->
              (let _ = warning_deprecated_since_6_00 loc in p : 'patt)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_nterm (a_ti : 'a_ti Grammar.Entry.e)),
                       (fun (a : 'a_ti) (loc : Ploc.t) -> (a : 'e__254)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("TILDEIDENT", "")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.Str a) : 'e__254)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "~_")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("~_", loc, a) : 'e__254)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "~")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("~", loc, a)) :
                           'e__254)))])),
           (fun (i : 'e__254) (loc : Ploc.t) ->
              (let _ = warning_deprecated_since_6_00 loc in
               Qast.Node
                 ("PaLab",
                  [Qast.Loc;
                   Qast.VaVal
                     (Qast.List
                        [Qast.Tuple
                           [Qast.Node ("PaLid", [Qast.Loc; i]);
                            Qast.VaVal (Qast.Option None)]])]) :
               'patt)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop
                (Grammar.s_facto
                   (Grammar.s_rules
                      [Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_nterm
                               (a_tic : 'a_tic Grammar.Entry.e)),
                          (fun (a : 'a_tic) (loc : Ploc.t) -> (a : 'e__253)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("TILDEIDENTCOLON", "")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.Str a) : 'e__253)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "~_:")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("~_:", loc, a) : 'e__253)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "~:")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("~:", loc, a)) :
                              'e__253)))])))
             Grammar.s_self,
           (fun (p : 'patt) (i : 'e__253) (loc : Ploc.t) ->
              (let _ = warning_deprecated_since_6_00 loc in
               Qast.Node
                 ("PaLab",
                  [Qast.Loc;
                   Qast.VaVal
                     (Qast.List
                        [Qast.Tuple
                           [Qast.Node ("PaLid", [Qast.Loc; i]);
                            Qast.VaVal (Qast.Option (Some p))]])]) :
               'patt)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("", "?")))
                      (Grammar.s_token ("", "{")))
                   (Grammar.s_nterm (patt_tcon : 'patt_tcon Grammar.Entry.e)))
                (Grammar.s_facto
                   (Grammar.s_rules
                      [Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_opt
                               (Grammar.s_rules
                                  [Grammar.production
                                     (Grammar.r_next
                                        (Grammar.r_next Grammar.r_stop
                                           (Grammar.s_token ("", "=")))
                                        (Grammar.s_nterm
                                           (expr : 'expr Grammar.Entry.e)),
                                      (fun (e : 'expr) _ (loc : Ploc.t) ->
                                         (e : 'e__251)))])),
                          (fun (a : 'e__251 option) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.Option a) : 'e__252)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_opt")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_opt", loc, a) : 'e__252)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "opt")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("opt", loc, a)) :
                              'e__252)))])))
             (Grammar.s_token ("", "}")),
           (fun _ (eo : 'e__252) (p : 'patt_tcon) _ _ (loc : Ploc.t) ->
              (Qast.Node ("PaOlb", [Qast.Loc; p; eo]) : 'patt)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "~")))
                   (Grammar.s_token ("", "{")))
                (Grammar.s_facto
                   (Grammar.s_rules
                      [Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_list1sep
                               (Grammar.s_nterm
                                  (patt_tcon_opt_eq_patt :
                                   'patt_tcon_opt_eq_patt Grammar.Entry.e))
                               (Grammar.s_token ("", ";")) false),
                          (fun (a : 'patt_tcon_opt_eq_patt list)
                               (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.List a) : 'e__250)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_list")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_list", loc, a) : 'e__250)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "list")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                              'e__250)))])))
             (Grammar.s_token ("", "}")),
           (fun _ (lppo : 'e__250) _ _ (loc : Ploc.t) ->
              (Qast.Node ("PaLab", [Qast.Loc; lppo]) : 'patt)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "#")))
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_nterm
                            (mod_ident : 'mod_ident Grammar.Entry.e)),
                       (fun (a : 'mod_ident) (loc : Ploc.t) ->
                          (Qast.VaVal a : 'e__249)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_", loc, a) : 'e__249)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("", loc, a)) : 'e__249)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_list")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_list", loc, a) : 'e__249)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "list")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                           'e__249)))])),
           (fun (sl : 'e__249) _ (loc : Ploc.t) ->
              (Qast.Node ("PaTyp", [Qast.Loc; sl]) : 'patt)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "`")))
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_nterm (ident : 'ident Grammar.Entry.e)),
                       (fun (a : 'ident) (loc : Ploc.t) ->
                          (Qast.VaVal a : 'e__248)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_", loc, a) : 'e__248)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("", loc, a)) :
                           'e__248)))])),
           (fun (s : 'e__248) _ (loc : Ploc.t) ->
              (Qast.Node ("PaVrn", [Qast.Loc; s]) : 'patt)))]];
    Grammar.extension
      (patt_tcon_opt_eq_patt : 'patt_tcon_opt_eq_patt Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop
                (Grammar.s_nterm (patt_tcon : 'patt_tcon Grammar.Entry.e)))
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_opt
                            (Grammar.s_rules
                               [Grammar.production
                                  (Grammar.r_next
                                     (Grammar.r_next Grammar.r_stop
                                        (Grammar.s_token ("", "=")))
                                     (Grammar.s_nterm
                                        (patt : 'patt Grammar.Entry.e)),
                                   (fun (p : 'patt) _ (loc : Ploc.t) ->
                                      (p : 'e__255)))])),
                       (fun (a : 'e__255 option) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.Option a) : 'e__256)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_opt")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_opt", loc, a) : 'e__256)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "opt")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("opt", loc, a)) :
                           'e__256)))])),
           (fun (po : 'e__256) (p : 'patt_tcon) (loc : Ploc.t) ->
              (Qast.Tuple [p; po] : 'patt_tcon_opt_eq_patt)))]];
    Grammar.extension (patt_tcon : 'patt_tcon Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop
                   (Grammar.s_nterm (patt : 'patt Grammar.Entry.e)))
                (Grammar.s_token ("", ":")))
             (Grammar.s_nterm (ctyp : 'ctyp Grammar.Entry.e)),
           (fun (t : 'ctyp) _ (p : 'patt) (loc : Ploc.t) ->
              (Qast.Node ("PaTyc", [Qast.Loc; p; t]) : 'patt_tcon)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_nterm (patt : 'patt Grammar.Entry.e)),
           (fun (p : 'patt) (loc : Ploc.t) -> (p : 'patt_tcon)))]];
    Grammar.extension (ipatt : 'ipatt Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_nterm
                (patt_option_label : 'patt_option_label Grammar.Entry.e)),
           (fun (p : 'patt_option_label) (loc : Ploc.t) ->
              (let _ = warning_deprecated_since_6_00 loc in p : 'ipatt)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_nterm (a_ti : 'a_ti Grammar.Entry.e)),
                       (fun (a : 'a_ti) (loc : Ploc.t) -> (a : 'e__261)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("TILDEIDENT", "")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.Str a) : 'e__261)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "~_")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("~_", loc, a) : 'e__261)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "~")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("~", loc, a)) :
                           'e__261)))])),
           (fun (i : 'e__261) (loc : Ploc.t) ->
              (let _ = warning_deprecated_since_6_00 loc in
               Qast.Node
                 ("PaLab",
                  [Qast.Loc;
                   Qast.VaVal
                     (Qast.List
                        [Qast.Tuple
                           [Qast.Node ("PaLid", [Qast.Loc; i]);
                            Qast.VaVal (Qast.Option None)]])]) :
               'ipatt)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop
                (Grammar.s_facto
                   (Grammar.s_rules
                      [Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_nterm
                               (a_tic : 'a_tic Grammar.Entry.e)),
                          (fun (a : 'a_tic) (loc : Ploc.t) -> (a : 'e__260)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("TILDEIDENTCOLON", "")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.Str a) : 'e__260)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "~_:")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("~_:", loc, a) : 'e__260)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "~:")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("~:", loc, a)) :
                              'e__260)))])))
             Grammar.s_self,
           (fun (p : 'ipatt) (i : 'e__260) (loc : Ploc.t) ->
              (let _ = warning_deprecated_since_6_00 loc in
               Qast.Node
                 ("PaLab",
                  [Qast.Loc;
                   Qast.VaVal
                     (Qast.List
                        [Qast.Tuple
                           [Qast.Node ("PaLid", [Qast.Loc; i]);
                            Qast.VaVal (Qast.Option (Some p))]])]) :
               'ipatt)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("", "?")))
                      (Grammar.s_token ("", "{")))
                   (Grammar.s_nterm
                      (ipatt_tcon : 'ipatt_tcon Grammar.Entry.e)))
                (Grammar.s_facto
                   (Grammar.s_rules
                      [Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_opt
                               (Grammar.s_rules
                                  [Grammar.production
                                     (Grammar.r_next
                                        (Grammar.r_next Grammar.r_stop
                                           (Grammar.s_token ("", "=")))
                                        (Grammar.s_nterm
                                           (expr : 'expr Grammar.Entry.e)),
                                      (fun (e : 'expr) _ (loc : Ploc.t) ->
                                         (e : 'e__258)))])),
                          (fun (a : 'e__258 option) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.Option a) : 'e__259)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_opt")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_opt", loc, a) : 'e__259)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "opt")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("opt", loc, a)) :
                              'e__259)))])))
             (Grammar.s_token ("", "}")),
           (fun _ (eo : 'e__259) (p : 'ipatt_tcon) _ _ (loc : Ploc.t) ->
              (Qast.Node ("PaOlb", [Qast.Loc; p; eo]) : 'ipatt)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "~")))
                   (Grammar.s_token ("", "{")))
                (Grammar.s_facto
                   (Grammar.s_rules
                      [Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_list1sep
                               (Grammar.s_nterm
                                  (ipatt_tcon_opt_eq_patt :
                                   'ipatt_tcon_opt_eq_patt Grammar.Entry.e))
                               (Grammar.s_token ("", ";")) false),
                          (fun (a : 'ipatt_tcon_opt_eq_patt list)
                               (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.List a) : 'e__257)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_list")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_list", loc, a) : 'e__257)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "list")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                              'e__257)))])))
             (Grammar.s_token ("", "}")),
           (fun _ (lppo : 'e__257) _ _ (loc : Ploc.t) ->
              (Qast.Node ("PaLab", [Qast.Loc; lppo]) : 'ipatt)))]];
    Grammar.extension
      (ipatt_tcon_opt_eq_patt : 'ipatt_tcon_opt_eq_patt Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop
                (Grammar.s_nterm (ipatt_tcon : 'ipatt_tcon Grammar.Entry.e)))
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_opt
                            (Grammar.s_rules
                               [Grammar.production
                                  (Grammar.r_next
                                     (Grammar.r_next Grammar.r_stop
                                        (Grammar.s_token ("", "=")))
                                     (Grammar.s_nterm
                                        (patt : 'patt Grammar.Entry.e)),
                                   (fun (p : 'patt) _ (loc : Ploc.t) ->
                                      (p : 'e__262)))])),
                       (fun (a : 'e__262 option) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.Option a) : 'e__263)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_opt")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_opt", loc, a) : 'e__263)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "opt")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("opt", loc, a)) :
                           'e__263)))])),
           (fun (po : 'e__263) (p : 'ipatt_tcon) (loc : Ploc.t) ->
              (Qast.Tuple [p; po] : 'ipatt_tcon_opt_eq_patt)))]];
    Grammar.extension (ipatt_tcon : 'ipatt_tcon Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop
                   (Grammar.s_nterm (ipatt : 'ipatt Grammar.Entry.e)))
                (Grammar.s_token ("", ":")))
             (Grammar.s_nterm (ctyp : 'ctyp Grammar.Entry.e)),
           (fun (t : 'ctyp) _ (p : 'ipatt) (loc : Ploc.t) ->
              (Qast.Node ("PaTyc", [Qast.Loc; p; t]) : 'ipatt_tcon)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_nterm (ipatt : 'ipatt Grammar.Entry.e)),
           (fun (p : 'ipatt) (loc : Ploc.t) -> (p : 'ipatt_tcon)))]];
    Grammar.extension (patt_option_label : 'patt_option_label Grammar.Entry.e)
      None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "?")))
                   (Grammar.s_token ("", "(")))
                (Grammar.s_facto
                   (Grammar.s_rules
                      [Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("LIDENT", "")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.Str a) : 'e__276)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_", loc, a) : 'e__276)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("", loc, a)) :
                              'e__276)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_lid")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_lid", loc, a) : 'e__276)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "lid")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("lid", loc, a)) :
                              'e__276)))])))
             (Grammar.s_token ("", ")")),
           (fun _ (i : 'e__276) _ _ (loc : Ploc.t) ->
              (Qast.Node
                 ("PaOlb",
                  [Qast.Loc; Qast.Node ("PaLid", [Qast.Loc; i]);
                   Qast.VaVal (Qast.Option None)]) :
               'patt_option_label)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("", "?")))
                         (Grammar.s_token ("", "(")))
                      (Grammar.s_facto
                         (Grammar.s_rules
                            [Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("LIDENT", "")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaVal (Qast.Str a) : 'e__275)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "_")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaAnt ("_", loc, a) : 'e__275)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaVal (Qast.VaAnt ("", loc, a)) :
                                    'e__275)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "_lid")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaAnt ("_lid", loc, a) : 'e__275)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "lid")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaVal (Qast.VaAnt ("lid", loc, a)) :
                                    'e__275)))])))
                   (Grammar.s_token ("", "=")))
                (Grammar.s_nterm (expr : 'expr Grammar.Entry.e)))
             (Grammar.s_token ("", ")")),
           (fun _ (e : 'expr) _ (i : 'e__275) _ _ (loc : Ploc.t) ->
              (Qast.Node
                 ("PaOlb",
                  [Qast.Loc; Qast.Node ("PaLid", [Qast.Loc; i]);
                   Qast.VaVal (Qast.Option (Some e))]) :
               'patt_option_label)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("", "?")))
                         (Grammar.s_token ("", "(")))
                      (Grammar.s_facto
                         (Grammar.s_rules
                            [Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("LIDENT", "")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaVal (Qast.Str a) : 'e__274)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "_")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaAnt ("_", loc, a) : 'e__274)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaVal (Qast.VaAnt ("", loc, a)) :
                                    'e__274)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "_lid")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaAnt ("_lid", loc, a) : 'e__274)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "lid")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaVal (Qast.VaAnt ("lid", loc, a)) :
                                    'e__274)))])))
                   (Grammar.s_token ("", ":")))
                (Grammar.s_nterm (ctyp : 'ctyp Grammar.Entry.e)))
             (Grammar.s_token ("", ")")),
           (fun _ (t : 'ctyp) _ (i : 'e__274) _ _ (loc : Ploc.t) ->
              (Qast.Node
                 ("PaOlb",
                  [Qast.Loc;
                   Qast.Node
                     ("PaTyc",
                      [Qast.Loc; Qast.Node ("PaLid", [Qast.Loc; i]); t]);
                   Qast.VaVal (Qast.Option None)]) :
               'patt_option_label)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next
                         (Grammar.r_next
                            (Grammar.r_next
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("", "?")))
                               (Grammar.s_token ("", "(")))
                            (Grammar.s_facto
                               (Grammar.s_rules
                                  [Grammar.production
                                     (Grammar.r_next Grammar.r_stop
                                        (Grammar.s_token ("LIDENT", "")),
                                      (fun (a : string) (loc : Ploc.t) ->
                                         (Qast.VaVal (Qast.Str a) :
                                          'e__273)));
                                   Grammar.production
                                     (Grammar.r_next Grammar.r_stop
                                        (Grammar.s_token ("ANTIQUOT", "_")),
                                      (fun (a : string) (loc : Ploc.t) ->
                                         (Qast.VaAnt ("_", loc, a) :
                                          'e__273)));
                                   Grammar.production
                                     (Grammar.r_next Grammar.r_stop
                                        (Grammar.s_token ("ANTIQUOT", "")),
                                      (fun (a : string) (loc : Ploc.t) ->
                                         (Qast.VaVal
                                            (Qast.VaAnt ("", loc, a)) :
                                          'e__273)));
                                   Grammar.production
                                     (Grammar.r_next Grammar.r_stop
                                        (Grammar.s_token
                                           ("ANTIQUOT", "_lid")),
                                      (fun (a : string) (loc : Ploc.t) ->
                                         (Qast.VaAnt ("_lid", loc, a) :
                                          'e__273)));
                                   Grammar.production
                                     (Grammar.r_next Grammar.r_stop
                                        (Grammar.s_token ("ANTIQUOT", "lid")),
                                      (fun (a : string) (loc : Ploc.t) ->
                                         (Qast.VaVal
                                            (Qast.VaAnt ("lid", loc, a)) :
                                          'e__273)))])))
                         (Grammar.s_token ("", ":")))
                      (Grammar.s_nterm (ctyp : 'ctyp Grammar.Entry.e)))
                   (Grammar.s_token ("", "=")))
                (Grammar.s_nterm (expr : 'expr Grammar.Entry.e)))
             (Grammar.s_token ("", ")")),
           (fun _ (e : 'expr) _ (t : 'ctyp) _ (i : 'e__273) _ _
                (loc : Ploc.t) ->
              (Qast.Node
                 ("PaOlb",
                  [Qast.Loc;
                   Qast.Node
                     ("PaTyc",
                      [Qast.Loc; Qast.Node ("PaLid", [Qast.Loc; i]); t]);
                   Qast.VaVal (Qast.Option (Some e))]) :
               'patt_option_label)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_nterm (a_qi : 'a_qi Grammar.Entry.e)),
                       (fun (a : 'a_qi) (loc : Ploc.t) -> (a : 'e__272)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("QUESTIONIDENT", "")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.Str a) : 'e__272)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "?_")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("?_", loc, a) : 'e__272)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "?")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("?", loc, a)) :
                           'e__272)))])),
           (fun (i : 'e__272) (loc : Ploc.t) ->
              (Qast.Node
                 ("PaOlb",
                  [Qast.Loc; Qast.Node ("PaLid", [Qast.Loc; i]);
                   Qast.VaVal (Qast.Option None)]) :
               'patt_option_label)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next Grammar.r_stop
                      (Grammar.s_facto
                         (Grammar.s_rules
                            [Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_nterm
                                     (a_qic : 'a_qic Grammar.Entry.e)),
                                (fun (a : 'a_qic) (loc : Ploc.t) ->
                                   (a : 'e__270)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token
                                     ("QUESTIONIDENTCOLON", "")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaVal (Qast.Str a) : 'e__270)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "?_:")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaAnt ("?_:", loc, a) : 'e__270)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "?:")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaVal (Qast.VaAnt ("?:", loc, a)) :
                                    'e__270)))])))
                   (Grammar.s_token ("", "(")))
                (Grammar.s_facto
                   (Grammar.s_rules
                      [Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("LIDENT", "")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.Str a) : 'e__271)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_", loc, a) : 'e__271)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("", loc, a)) :
                              'e__271)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_lid")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_lid", loc, a) : 'e__271)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "lid")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("lid", loc, a)) :
                              'e__271)))])))
             (Grammar.s_token ("", ")")),
           (fun _ (j : 'e__271) _ (i : 'e__270) (loc : Ploc.t) ->
              (Qast.Node
                 ("PaOlb",
                  [Qast.Loc; Qast.Node ("PaLid", [Qast.Loc; i]);
                   Qast.VaVal
                     (Qast.Option
                        (Some (Qast.Node ("ExLid", [Qast.Loc; j]))))]) :
               'patt_option_label)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_facto
                               (Grammar.s_rules
                                  [Grammar.production
                                     (Grammar.r_next Grammar.r_stop
                                        (Grammar.s_nterm
                                           (a_qic : 'a_qic Grammar.Entry.e)),
                                      (fun (a : 'a_qic) (loc : Ploc.t) ->
                                         (a : 'e__268)));
                                   Grammar.production
                                     (Grammar.r_next Grammar.r_stop
                                        (Grammar.s_token
                                           ("QUESTIONIDENTCOLON", "")),
                                      (fun (a : string) (loc : Ploc.t) ->
                                         (Qast.VaVal (Qast.Str a) :
                                          'e__268)));
                                   Grammar.production
                                     (Grammar.r_next Grammar.r_stop
                                        (Grammar.s_token ("ANTIQUOT", "?_:")),
                                      (fun (a : string) (loc : Ploc.t) ->
                                         (Qast.VaAnt ("?_:", loc, a) :
                                          'e__268)));
                                   Grammar.production
                                     (Grammar.r_next Grammar.r_stop
                                        (Grammar.s_token ("ANTIQUOT", "?:")),
                                      (fun (a : string) (loc : Ploc.t) ->
                                         (Qast.VaVal
                                            (Qast.VaAnt ("?:", loc, a)) :
                                          'e__268)))])))
                         (Grammar.s_token ("", "(")))
                      (Grammar.s_facto
                         (Grammar.s_rules
                            [Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("LIDENT", "")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaVal (Qast.Str a) : 'e__269)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "_")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaAnt ("_", loc, a) : 'e__269)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaVal (Qast.VaAnt ("", loc, a)) :
                                    'e__269)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "_lid")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaAnt ("_lid", loc, a) : 'e__269)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "lid")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaVal (Qast.VaAnt ("lid", loc, a)) :
                                    'e__269)))])))
                   (Grammar.s_token ("", "=")))
                (Grammar.s_nterm (expr : 'expr Grammar.Entry.e)))
             (Grammar.s_token ("", ")")),
           (fun _ (e : 'expr) _ (j : 'e__269) _ (i : 'e__268)
                (loc : Ploc.t) ->
              (Qast.Node
                 ("PaOlb",
                  [Qast.Loc; Qast.Node ("PaLid", [Qast.Loc; i]);
                   Qast.VaVal
                     (Qast.Option
                        (Some
                           (Qast.Node
                              ("ExOlb",
                               [Qast.Loc; Qast.Node ("PaLid", [Qast.Loc; j]);
                                Qast.VaVal (Qast.Option (Some e))]))))]) :
               'patt_option_label)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_facto
                               (Grammar.s_rules
                                  [Grammar.production
                                     (Grammar.r_next Grammar.r_stop
                                        (Grammar.s_nterm
                                           (a_qic : 'a_qic Grammar.Entry.e)),
                                      (fun (a : 'a_qic) (loc : Ploc.t) ->
                                         (a : 'e__266)));
                                   Grammar.production
                                     (Grammar.r_next Grammar.r_stop
                                        (Grammar.s_token
                                           ("QUESTIONIDENTCOLON", "")),
                                      (fun (a : string) (loc : Ploc.t) ->
                                         (Qast.VaVal (Qast.Str a) :
                                          'e__266)));
                                   Grammar.production
                                     (Grammar.r_next Grammar.r_stop
                                        (Grammar.s_token ("ANTIQUOT", "?_:")),
                                      (fun (a : string) (loc : Ploc.t) ->
                                         (Qast.VaAnt ("?_:", loc, a) :
                                          'e__266)));
                                   Grammar.production
                                     (Grammar.r_next Grammar.r_stop
                                        (Grammar.s_token ("ANTIQUOT", "?:")),
                                      (fun (a : string) (loc : Ploc.t) ->
                                         (Qast.VaVal
                                            (Qast.VaAnt ("?:", loc, a)) :
                                          'e__266)))])))
                         (Grammar.s_token ("", "(")))
                      (Grammar.s_facto
                         (Grammar.s_rules
                            [Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("LIDENT", "")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaVal (Qast.Str a) : 'e__267)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "_")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaAnt ("_", loc, a) : 'e__267)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaVal (Qast.VaAnt ("", loc, a)) :
                                    'e__267)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "_lid")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaAnt ("_lid", loc, a) : 'e__267)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("ANTIQUOT", "lid")),
                                (fun (a : string) (loc : Ploc.t) ->
                                   (Qast.VaVal (Qast.VaAnt ("lid", loc, a)) :
                                    'e__267)))])))
                   (Grammar.s_token ("", ":")))
                (Grammar.s_nterm (ctyp : 'ctyp Grammar.Entry.e)))
             (Grammar.s_token ("", ")")),
           (fun _ (t : 'ctyp) _ (j : 'e__267) _ (i : 'e__266)
                (loc : Ploc.t) ->
              (Qast.Node
                 ("PaOlb",
                  [Qast.Loc;
                   Qast.Node
                     ("PaTyc",
                      [Qast.Loc; Qast.Node ("PaLid", [Qast.Loc; i]); t]);
                   Qast.VaVal
                     (Qast.Option
                        (Some
                           (Qast.Node
                              ("ExOlb",
                               [Qast.Loc; Qast.Node ("PaLid", [Qast.Loc; j]);
                                Qast.VaVal (Qast.Option None)]))))]) :
               'patt_option_label)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next
                         (Grammar.r_next
                            (Grammar.r_next
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_facto
                                     (Grammar.s_rules
                                        [Grammar.production
                                           (Grammar.r_next Grammar.r_stop
                                              (Grammar.s_nterm
                                                 (a_qic :
                                                  'a_qic Grammar.Entry.e)),
                                            (fun (a : 'a_qic)
                                                 (loc : Ploc.t) ->
                                               (a : 'e__264)));
                                         Grammar.production
                                           (Grammar.r_next Grammar.r_stop
                                              (Grammar.s_token
                                                 ("QUESTIONIDENTCOLON", "")),
                                            (fun (a : string)
                                                 (loc : Ploc.t) ->
                                               (Qast.VaVal (Qast.Str a) :
                                                'e__264)));
                                         Grammar.production
                                           (Grammar.r_next Grammar.r_stop
                                              (Grammar.s_token
                                                 ("ANTIQUOT", "?_:")),
                                            (fun (a : string)
                                                 (loc : Ploc.t) ->
                                               (Qast.VaAnt ("?_:", loc, a) :
                                                'e__264)));
                                         Grammar.production
                                           (Grammar.r_next Grammar.r_stop
                                              (Grammar.s_token
                                                 ("ANTIQUOT", "?:")),
                                            (fun (a : string)
                                                 (loc : Ploc.t) ->
                                               (Qast.VaVal
                                                  (Qast.VaAnt
                                                     ("?:", loc, a)) :
                                                'e__264)))])))
                               (Grammar.s_token ("", "(")))
                            (Grammar.s_facto
                               (Grammar.s_rules
                                  [Grammar.production
                                     (Grammar.r_next Grammar.r_stop
                                        (Grammar.s_token ("LIDENT", "")),
                                      (fun (a : string) (loc : Ploc.t) ->
                                         (Qast.VaVal (Qast.Str a) :
                                          'e__265)));
                                   Grammar.production
                                     (Grammar.r_next Grammar.r_stop
                                        (Grammar.s_token ("ANTIQUOT", "_")),
                                      (fun (a : string) (loc : Ploc.t) ->
                                         (Qast.VaAnt ("_", loc, a) :
                                          'e__265)));
                                   Grammar.production
                                     (Grammar.r_next Grammar.r_stop
                                        (Grammar.s_token ("ANTIQUOT", "")),
                                      (fun (a : string) (loc : Ploc.t) ->
                                         (Qast.VaVal
                                            (Qast.VaAnt ("", loc, a)) :
                                          'e__265)));
                                   Grammar.production
                                     (Grammar.r_next Grammar.r_stop
                                        (Grammar.s_token
                                           ("ANTIQUOT", "_lid")),
                                      (fun (a : string) (loc : Ploc.t) ->
                                         (Qast.VaAnt ("_lid", loc, a) :
                                          'e__265)));
                                   Grammar.production
                                     (Grammar.r_next Grammar.r_stop
                                        (Grammar.s_token ("ANTIQUOT", "lid")),
                                      (fun (a : string) (loc : Ploc.t) ->
                                         (Qast.VaVal
                                            (Qast.VaAnt ("lid", loc, a)) :
                                          'e__265)))])))
                         (Grammar.s_token ("", ":")))
                      (Grammar.s_nterm (ctyp : 'ctyp Grammar.Entry.e)))
                   (Grammar.s_token ("", "=")))
                (Grammar.s_nterm (expr : 'expr Grammar.Entry.e)))
             (Grammar.s_token ("", ")")),
           (fun _ (e : 'expr) _ (t : 'ctyp) _ (j : 'e__265) _ (i : 'e__264)
                (loc : Ploc.t) ->
              (Qast.Node
                 ("PaOlb",
                  [Qast.Loc;
                   Qast.Node
                     ("PaTyc",
                      [Qast.Loc; Qast.Node ("PaLid", [Qast.Loc; i]); t]);
                   Qast.VaVal
                     (Qast.Option
                        (Some
                           (Qast.Node
                              ("ExOlb",
                               [Qast.Loc; Qast.Node ("PaLid", [Qast.Loc; j]);
                                Qast.VaVal (Qast.Option (Some e))]))))]) :
               'patt_option_label)))]];
    Grammar.extension (expr : 'expr Grammar.Entry.e)
      (Some (Gramext.After "apply"))
      [Some "label", Some Gramext.NonA,
       [Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_nterm (a_qi : 'a_qi Grammar.Entry.e)),
                       (fun (a : 'a_qi) (loc : Ploc.t) -> (a : 'e__282)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("QUESTIONIDENT", "")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.Str a) : 'e__282)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "?_")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("?_", loc, a) : 'e__282)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "?")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("?", loc, a)) :
                           'e__282)))])),
           (fun (i : 'e__282) (loc : Ploc.t) ->
              (let _ = warning_deprecated_since_6_00 loc in
               Qast.Node
                 ("ExOlb",
                  [Qast.Loc; Qast.Node ("PaLid", [Qast.Loc; i]);
                   Qast.VaVal (Qast.Option None)]) :
               'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop
                (Grammar.s_facto
                   (Grammar.s_rules
                      [Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_nterm
                               (a_qic : 'a_qic Grammar.Entry.e)),
                          (fun (a : 'a_qic) (loc : Ploc.t) -> (a : 'e__281)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("QUESTIONIDENTCOLON", "")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.Str a) : 'e__281)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "?_:")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("?_:", loc, a) : 'e__281)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "?:")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("?:", loc, a)) :
                              'e__281)))])))
             Grammar.s_self,
           (fun (e : 'expr) (i : 'e__281) (loc : Ploc.t) ->
              (let _ = warning_deprecated_since_6_00 loc in
               Qast.Node
                 ("ExOlb",
                  [Qast.Loc; Qast.Node ("PaLid", [Qast.Loc; i]);
                   Qast.VaVal (Qast.Option (Some e))]) :
               'expr)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_nterm (a_ti : 'a_ti Grammar.Entry.e)),
                       (fun (a : 'a_ti) (loc : Ploc.t) -> (a : 'e__280)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("TILDEIDENT", "")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.Str a) : 'e__280)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "~_")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("~_", loc, a) : 'e__280)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "~")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("~", loc, a)) :
                           'e__280)))])),
           (fun (i : 'e__280) (loc : Ploc.t) ->
              (let _ = warning_deprecated_since_6_00 loc in
               Qast.Node
                 ("ExLab",
                  [Qast.Loc;
                   Qast.VaVal
                     (Qast.List
                        [Qast.Tuple
                           [Qast.Node ("PaLid", [Qast.Loc; i]);
                            Qast.VaVal (Qast.Option None)]])]) :
               'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop
                (Grammar.s_facto
                   (Grammar.s_rules
                      [Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_nterm
                               (a_tic : 'a_tic Grammar.Entry.e)),
                          (fun (a : 'a_tic) (loc : Ploc.t) -> (a : 'e__279)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("TILDEIDENTCOLON", "")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.Str a) : 'e__279)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "~_:")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("~_:", loc, a) : 'e__279)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "~:")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("~:", loc, a)) :
                              'e__279)))])))
             Grammar.s_self,
           (fun (e : 'expr) (i : 'e__279) (loc : Ploc.t) ->
              (let _ = warning_deprecated_since_6_00 loc in
               Qast.Node
                 ("ExLab",
                  [Qast.Loc;
                   Qast.VaVal
                     (Qast.List
                        [Qast.Tuple
                           [Qast.Node ("PaLid", [Qast.Loc; i]);
                            Qast.VaVal (Qast.Option (Some e))]])]) :
               'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("", "?")))
                      (Grammar.s_token ("", "{")))
                   (Grammar.s_nterm
                      (ipatt_tcon : 'ipatt_tcon Grammar.Entry.e)))
                (Grammar.s_facto
                   (Grammar.s_rules
                      [Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_opt
                               (Grammar.s_nterm
                                  (fun_binding :
                                   'fun_binding Grammar.Entry.e))),
                          (fun (a : 'fun_binding option) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.Option a) : 'e__278)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_opt")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_opt", loc, a) : 'e__278)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "opt")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("opt", loc, a)) :
                              'e__278)))])))
             (Grammar.s_token ("", "}")),
           (fun _ (eo : 'e__278) (p : 'ipatt_tcon) _ _ (loc : Ploc.t) ->
              (Qast.Node ("ExOlb", [Qast.Loc; p; eo]) : 'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "~")))
                   (Grammar.s_token ("", "{")))
                (Grammar.s_facto
                   (Grammar.s_rules
                      [Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_list1sep
                               (Grammar.s_nterm
                                  (ipatt_tcon_fun_binding :
                                   'ipatt_tcon_fun_binding Grammar.Entry.e))
                               (Grammar.s_token ("", ";")) false),
                          (fun (a : 'ipatt_tcon_fun_binding list)
                               (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.List a) : 'e__277)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_list")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_list", loc, a) : 'e__277)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "list")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                              'e__277)))])))
             (Grammar.s_token ("", "}")),
           (fun _ (lpeo : 'e__277) _ _ (loc : Ploc.t) ->
              (Qast.Node ("ExLab", [Qast.Loc; lpeo]) : 'expr)))]];
    Grammar.extension
      (ipatt_tcon_fun_binding : 'ipatt_tcon_fun_binding Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop
                (Grammar.s_nterm (ipatt_tcon : 'ipatt_tcon Grammar.Entry.e)))
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_opt
                            (Grammar.s_nterm
                               (fun_binding : 'fun_binding Grammar.Entry.e))),
                       (fun (a : 'fun_binding option) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.Option a) : 'e__283)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_opt")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_opt", loc, a) : 'e__283)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "opt")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("opt", loc, a)) :
                           'e__283)))])),
           (fun (eo : 'e__283) (p : 'ipatt_tcon) (loc : Ploc.t) ->
              (Qast.Tuple [p; eo] : 'ipatt_tcon_fun_binding)))]];
    Grammar.extension (expr : 'expr Grammar.Entry.e)
      (Some (Gramext.Level "simple"))
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "`")))
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_nterm (ident : 'ident Grammar.Entry.e)),
                       (fun (a : 'ident) (loc : Ploc.t) ->
                          (Qast.VaVal a : 'e__284)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_", loc, a) : 'e__284)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("", loc, a)) :
                           'e__284)))])),
           (fun (s : 'e__284) _ (loc : Ploc.t) ->
              (Qast.Node ("ExVrn", [Qast.Loc; s]) : 'expr)))]];
    Grammar.extension (str_item : 'str_item Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "def")))
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_list1sep
                            (Grammar.s_nterm
                               (joinautomaton :
                                'joinautomaton Grammar.Entry.e))
                            (Grammar.s_token ("", "and")) false),
                       (fun (a : 'joinautomaton list) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.List a) : 'e__285)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_list")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_list", loc, a) : 'e__285)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "list")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                           'e__285)))])),
           (fun (jal : 'e__285) _ (loc : Ploc.t) ->
              (Qast.Node ("StDef", [Qast.Loc; jal]) : 'str_item)))]];
    Grammar.extension (expr : 'expr Grammar.Entry.e)
      (Some (Gramext.Level "top"))
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next Grammar.r_stop
                      (Grammar.s_token ("", "def")))
                   (Grammar.s_facto
                      (Grammar.s_rules
                         [Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_list1sep
                                  (Grammar.s_nterm
                                     (joinautomaton :
                                      'joinautomaton Grammar.Entry.e))
                                  (Grammar.s_token ("", "and")) false),
                             (fun (a : 'joinautomaton list) (loc : Ploc.t) ->
                                (Qast.VaVal (Qast.List a) : 'e__286)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "_list")),
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaAnt ("_list", loc, a) : 'e__286)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "list")),
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                                 'e__286)))])))
                (Grammar.s_token ("", "in")))
             (Grammar.s_nterml (expr : 'expr Grammar.Entry.e) "top"),
           (fun (e : 'expr) _ (jal : 'e__286) _ (loc : Ploc.t) ->
              (Qast.Node ("ExJdf", [Qast.Loc; jal; e]) : 'expr)))]];
    Grammar.extension (expr : 'expr Grammar.Entry.e)
      (Some (Gramext.Level "apply"))
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next Grammar.r_stop
                      (Grammar.s_token ("", "reply")))
                   (Grammar.s_facto
                      (Grammar.s_rules
                         [Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_opt
                                  (Grammar.s_nterm
                                     (expr : 'expr Grammar.Entry.e))),
                             (fun (a : 'expr option) (loc : Ploc.t) ->
                                (Qast.VaVal (Qast.Option a) : 'e__287)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "_opt")),
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaAnt ("_opt", loc, a) : 'e__287)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "opt")),
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaVal (Qast.VaAnt ("opt", loc, a)) :
                                 'e__287)))])))
                (Grammar.s_token ("", "to")))
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_nterm
                            (joinident : 'joinident Grammar.Entry.e)),
                       (fun (a : 'joinident) (loc : Ploc.t) ->
                          (Qast.VaVal a : 'e__288)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_jid")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_jid", loc, a) : 'e__288)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "jid")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("jid", loc, a)) :
                           'e__288)))])),
           (fun (ji : 'e__288) _ (eo : 'e__287) _ (loc : Ploc.t) ->
              (Qast.Node ("ExRpl", [Qast.Loc; eo; ji]) : 'expr)))]];
    Grammar.extension (expr : 'expr Grammar.Entry.e)
      (Some (Gramext.Before ":="))
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "spawn")))
             Grammar.s_self,
           (fun (e : 'expr) _ (loc : Ploc.t) ->
              (Qast.Node ("ExSpw", [Qast.Loc; e]) : 'expr)))]];
    Grammar.extension (expr : 'expr Grammar.Entry.e)
      (Some (Gramext.Level "&&"))
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                (Grammar.s_token ("", "&")))
             Grammar.s_self,
           (fun (e2 : 'expr) _ (e1 : 'expr) (loc : Ploc.t) ->
              (Qast.Node ("ExPar", [Qast.Loc; e1; e2]) : 'expr)))]];
    Grammar.extension (joinautomaton : 'joinautomaton Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_list1sep
                            (Grammar.s_nterm
                               (joinclause : 'joinclause Grammar.Entry.e))
                            (Grammar.s_token ("", "or")) false),
                       (fun (a : 'joinclause list) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.List a) : 'e__289)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_list")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_list", loc, a) : 'e__289)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "list")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                           'e__289)))])),
           (fun (jcl : 'e__289) (loc : Ploc.t) ->
              (Qast.Record ["jcLoc", Qast.Loc; "jcVal", jcl] :
               'joinautomaton)))]];
    Grammar.extension (joinclause : 'joinclause Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop
                   (Grammar.s_facto
                      (Grammar.s_rules
                         [Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_list1sep
                                  (Grammar.s_nterm
                                     (joinpattern :
                                      'joinpattern Grammar.Entry.e))
                                  (Grammar.s_token ("", "&")) false),
                             (fun (a : 'joinpattern list) (loc : Ploc.t) ->
                                (Qast.VaVal (Qast.List a) : 'e__290)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "_list")),
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaAnt ("_list", loc, a) : 'e__290)));
                          Grammar.production
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("ANTIQUOT", "list")),
                             (fun (a : string) (loc : Ploc.t) ->
                                (Qast.VaVal (Qast.VaAnt ("list", loc, a)) :
                                 'e__290)))])))
                (Grammar.s_token ("", "=")))
             (Grammar.s_nterm (expr : 'expr Grammar.Entry.e)),
           (fun (e : 'expr) _ (jpl : 'e__290) (loc : Ploc.t) ->
              (Qast.Tuple [Qast.Loc; jpl; e] : 'joinclause)))]];
    Grammar.extension (joinpattern : 'joinpattern Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next Grammar.r_stop
                      (Grammar.s_nterm
                         (joinident : 'joinident Grammar.Entry.e)))
                   (Grammar.s_token ("", "(")))
                (Grammar.s_facto
                   (Grammar.s_rules
                      [Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_opt
                               (Grammar.s_nterm
                                  (patt : 'patt Grammar.Entry.e))),
                          (fun (a : 'patt option) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.Option a) : 'e__291)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "_opt")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaAnt ("_opt", loc, a) : 'e__291)));
                       Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("ANTIQUOT", "opt")),
                          (fun (a : string) (loc : Ploc.t) ->
                             (Qast.VaVal (Qast.VaAnt ("opt", loc, a)) :
                              'e__291)))])))
             (Grammar.s_token ("", ")")),
           (fun _ (op : 'e__291) _ (ji : 'joinident) (loc : Ploc.t) ->
              (Qast.Tuple [Qast.Loc; ji; op] : 'joinpattern)))]];
    Grammar.extension (joinident : 'joinident Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_facto
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("LIDENT", "")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.Str a) : 'e__292)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_", loc, a) : 'e__292)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("", loc, a)) : 'e__292)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "_lid")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaAnt ("_lid", loc, a) : 'e__292)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("ANTIQUOT", "lid")),
                       (fun (a : string) (loc : Ploc.t) ->
                          (Qast.VaVal (Qast.VaAnt ("lid", loc, a)) :
                           'e__292)))])),
           (fun (i : 'e__292) (loc : Ploc.t) ->
              (Qast.Tuple [Qast.Loc; i] : 'joinident)))]];
    (* -- end copy from pa_r to q_MLast -- *)
    Grammar.extension (a_ti : 'a_ti Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "~")))
             (Grammar.s_token ("ANTIQUOT", "")),
           (fun (a : string) _ (loc : Ploc.t) ->
              (Qast.VaAnt ("~", loc, a) : 'a_ti)))]];
    Grammar.extension (a_tic : 'a_tic Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "~")))
                (Grammar.s_token ("ANTIQUOT", "")))
             (Grammar.s_token ("", ":")),
           (fun _ (a : string) _ (loc : Ploc.t) ->
              (Qast.VaAnt ("~", loc, a) : 'a_tic)))]];
    Grammar.extension (a_qi : 'a_qi Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "?")))
             (Grammar.s_token ("ANTIQUOT", "")),
           (fun (a : string) _ (loc : Ploc.t) ->
              (Qast.VaAnt ("?", loc, a) : 'a_qi)))]];
    Grammar.extension (a_qic : 'a_qic Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "?")))
                (Grammar.s_token ("ANTIQUOT", "")))
             (Grammar.s_token ("", ":")),
           (fun _ (a : string) _ (loc : Ploc.t) ->
              (Qast.VaAnt ("?", loc, a) : 'a_qic)))]]]);;

(* Antiquotations *)

let antiquot_xtr loc n a =
  if !(Pcaml.strict_mode) then
    Qast.Node (n, [Qast.Loc; Qast.VaAnt ("xtr", loc, a); Qast.Option None])
  else Qast.Apply ("failwith", [Qast.Str "antiquotation not authorized"])
;;

Grammar.safe_extend
  [Grammar.extension (module_expr : 'module_expr Grammar.Entry.e)
     (Some (Gramext.Level "simple"))
     [None, None,
      [Grammar.production
         (Grammar.r_next Grammar.r_stop (Grammar.s_token ("ANTIQUOT", "")),
          (fun (a : string) (loc : Ploc.t) ->
             (Qast.VaAnt ("", loc, a) : 'module_expr)));
       Grammar.production
         (Grammar.r_next Grammar.r_stop (Grammar.s_token ("ANTIQUOT", "xtr")),
          (fun (a : string) (loc : Ploc.t) ->
             (antiquot_xtr loc "MeXtr" a : 'module_expr)));
       Grammar.production
         (Grammar.r_next Grammar.r_stop
            (Grammar.s_token ("ANTIQUOT", "mexp")),
          (fun (a : string) (loc : Ploc.t) ->
             (Qast.VaAnt ("mexp", loc, a) : 'module_expr)))]];
   Grammar.extension (str_item : 'str_item Grammar.Entry.e)
     (Some (Gramext.Level "top"))
     [None, None,
      [Grammar.production
         (Grammar.r_next Grammar.r_stop (Grammar.s_token ("ANTIQUOT", "")),
          (fun (a : string) (loc : Ploc.t) ->
             (Qast.VaAnt ("", loc, a) : 'str_item)));
       Grammar.production
         (Grammar.r_next Grammar.r_stop (Grammar.s_token ("ANTIQUOT", "xtr")),
          (fun (a : string) (loc : Ploc.t) ->
             (antiquot_xtr loc "StXtr" a : 'str_item)));
       Grammar.production
         (Grammar.r_next Grammar.r_stop
            (Grammar.s_token ("ANTIQUOT", "stri")),
          (fun (a : string) (loc : Ploc.t) ->
             (Qast.VaAnt ("stri", loc, a) : 'str_item)))]];
   Grammar.extension (module_type : 'module_type Grammar.Entry.e)
     (Some (Gramext.Level "simple"))
     [None, None,
      [Grammar.production
         (Grammar.r_next Grammar.r_stop (Grammar.s_token ("ANTIQUOT", "")),
          (fun (a : string) (loc : Ploc.t) ->
             (Qast.VaAnt ("", loc, a) : 'module_type)));
       Grammar.production
         (Grammar.r_next Grammar.r_stop (Grammar.s_token ("ANTIQUOT", "xtr")),
          (fun (a : string) (loc : Ploc.t) ->
             (antiquot_xtr loc "MtXtr" a : 'module_type)));
       Grammar.production
         (Grammar.r_next Grammar.r_stop
            (Grammar.s_token ("ANTIQUOT", "mtyp")),
          (fun (a : string) (loc : Ploc.t) ->
             (Qast.VaAnt ("mtyp", loc, a) : 'module_type)))]];
   Grammar.extension (sig_item : 'sig_item Grammar.Entry.e)
     (Some (Gramext.Level "top"))
     [None, None,
      [Grammar.production
         (Grammar.r_next Grammar.r_stop (Grammar.s_token ("ANTIQUOT", "")),
          (fun (a : string) (loc : Ploc.t) ->
             (Qast.VaAnt ("", loc, a) : 'sig_item)));
       Grammar.production
         (Grammar.r_next Grammar.r_stop (Grammar.s_token ("ANTIQUOT", "xtr")),
          (fun (a : string) (loc : Ploc.t) ->
             (antiquot_xtr loc "SgXtr" a : 'sig_item)));
       Grammar.production
         (Grammar.r_next Grammar.r_stop
            (Grammar.s_token ("ANTIQUOT", "sigi")),
          (fun (a : string) (loc : Ploc.t) ->
             (Qast.VaAnt ("sigi", loc, a) : 'sig_item)))]];
   Grammar.extension (expr : 'expr Grammar.Entry.e)
     (Some (Gramext.Level "simple"))
     [None, None,
      [Grammar.production
         (Grammar.r_next Grammar.r_stop
            (Grammar.s_token ("ANTIQUOT", "anti")),
          (fun (a : string) (loc : Ploc.t) ->
             (Qast.Node ("ExAnt", [Qast.Loc; Qast.VaAnt ("anti", loc, a)]) :
              'expr)));
       Grammar.production
         (Grammar.r_next Grammar.r_stop (Grammar.s_token ("ANTIQUOT", "xtr")),
          (fun (a : string) (loc : Ploc.t) ->
             (antiquot_xtr loc "ExXtr" a : 'expr)));
       Grammar.production
         (Grammar.r_next Grammar.r_stop (Grammar.s_token ("ANTIQUOT", "")),
          (fun (a : string) (loc : Ploc.t) ->
             (Qast.VaAnt ("", loc, a) : 'expr)));
       Grammar.production
         (Grammar.r_next Grammar.r_stop (Grammar.s_token ("ANTIQUOT", "exp")),
          (fun (a : string) (loc : Ploc.t) ->
             (Qast.VaAnt ("exp", loc, a) : 'expr)))]];
   Grammar.extension (patt : 'patt Grammar.Entry.e)
     (Some (Gramext.Level "simple"))
     [None, None,
      [Grammar.production
         (Grammar.r_next Grammar.r_stop
            (Grammar.s_token ("ANTIQUOT", "anti")),
          (fun (a : string) (loc : Ploc.t) ->
             (Qast.Node ("PaAnt", [Qast.Loc; Qast.VaAnt ("anti", loc, a)]) :
              'patt)));
       Grammar.production
         (Grammar.r_next Grammar.r_stop (Grammar.s_token ("ANTIQUOT", "xtr")),
          (fun (a : string) (loc : Ploc.t) ->
             (antiquot_xtr loc "PaXtr" a : 'patt)));
       Grammar.production
         (Grammar.r_next Grammar.r_stop (Grammar.s_token ("ANTIQUOT", "")),
          (fun (a : string) (loc : Ploc.t) ->
             (Qast.VaAnt ("", loc, a) : 'patt)));
       Grammar.production
         (Grammar.r_next Grammar.r_stop (Grammar.s_token ("ANTIQUOT", "pat")),
          (fun (a : string) (loc : Ploc.t) ->
             (Qast.VaAnt ("pat", loc, a) : 'patt)))]];
   Grammar.extension (ipatt : 'ipatt Grammar.Entry.e) None
     [None, None,
      [Grammar.production
         (Grammar.r_next Grammar.r_stop
            (Grammar.s_token ("ANTIQUOT", "anti")),
          (fun (a : string) (loc : Ploc.t) ->
             (Qast.Node ("PaAnt", [Qast.Loc; Qast.VaAnt ("anti", loc, a)]) :
              'ipatt)));
       Grammar.production
         (Grammar.r_next Grammar.r_stop (Grammar.s_token ("ANTIQUOT", "")),
          (fun (a : string) (loc : Ploc.t) ->
             (Qast.VaAnt ("", loc, a) : 'ipatt)));
       Grammar.production
         (Grammar.r_next Grammar.r_stop (Grammar.s_token ("ANTIQUOT", "xtr")),
          (fun (a : string) (loc : Ploc.t) ->
             (antiquot_xtr loc "PaXtr" a : 'ipatt)));
       Grammar.production
         (Grammar.r_next Grammar.r_stop (Grammar.s_token ("ANTIQUOT", "pat")),
          (fun (a : string) (loc : Ploc.t) ->
             (Qast.VaAnt ("pat", loc, a) : 'ipatt)))]];
   Grammar.extension (ctyp : 'ctyp Grammar.Entry.e)
     (Some (Gramext.Level "simple"))
     [None, None,
      [Grammar.production
         (Grammar.r_next Grammar.r_stop (Grammar.s_token ("ANTIQUOT", "")),
          (fun (a : string) (loc : Ploc.t) ->
             (Qast.VaAnt ("", loc, a) : 'ctyp)));
       Grammar.production
         (Grammar.r_next Grammar.r_stop (Grammar.s_token ("ANTIQUOT", "xtr")),
          (fun (a : string) (loc : Ploc.t) ->
             (antiquot_xtr loc "TyXtr" a : 'ctyp)));
       Grammar.production
         (Grammar.r_next Grammar.r_stop (Grammar.s_token ("ANTIQUOT", "typ")),
          (fun (a : string) (loc : Ploc.t) ->
             (Qast.VaAnt ("typ", loc, a) : 'ctyp)))]];
   Grammar.extension (class_expr : 'class_expr Grammar.Entry.e)
     (Some (Gramext.Level "simple"))
     [None, None,
      [Grammar.production
         (Grammar.r_next Grammar.r_stop (Grammar.s_token ("ANTIQUOT", "")),
          (fun (a : string) (loc : Ploc.t) ->
             (Qast.VaAnt ("", loc, a) : 'class_expr)));
       Grammar.production
         (Grammar.r_next Grammar.r_stop (Grammar.s_token ("ANTIQUOT", "xtr")),
          (fun (a : string) (loc : Ploc.t) ->
             (antiquot_xtr loc "CeXtr" a : 'class_expr)))]];
   Grammar.extension (class_str_item : 'class_str_item Grammar.Entry.e) None
     [None, None,
      [Grammar.production
         (Grammar.r_next Grammar.r_stop (Grammar.s_token ("ANTIQUOT", "")),
          (fun (a : string) (loc : Ploc.t) ->
             (Qast.VaAnt ("", loc, a) : 'class_str_item)))]];
   Grammar.extension (class_sig_item : 'class_sig_item Grammar.Entry.e) None
     [None, None,
      [Grammar.production
         (Grammar.r_next Grammar.r_stop (Grammar.s_token ("ANTIQUOT", "")),
          (fun (a : string) (loc : Ploc.t) ->
             (Qast.VaAnt ("", loc, a) : 'class_sig_item)))]];
   Grammar.extension (class_type : 'class_type Grammar.Entry.e)
     (Some (Gramext.Level "simple"))
     [None, None,
      [Grammar.production
         (Grammar.r_next Grammar.r_stop (Grammar.s_token ("ANTIQUOT", "")),
          (fun (a : string) (loc : Ploc.t) ->
             (Qast.VaAnt ("", loc, a) : 'class_type)));
       Grammar.production
         (Grammar.r_next Grammar.r_stop (Grammar.s_token ("ANTIQUOT", "xtr")),
          (fun (a : string) (loc : Ploc.t) ->
             (antiquot_xtr loc "CtXtr" a : 'class_type)))]]];;

let quot_mod = ref [];;
let any_quot_mod = ref "MLast";;

let set_qmod s =
  match try Some (String.index s ',') with Not_found -> None with
    Some i ->
      let q = String.sub s 0 i in
      let m = String.sub s (i + 1) (String.length s - i - 1) in
      quot_mod := (q, m) :: !quot_mod
  | None -> any_quot_mod := s
;;

Pcaml.add_directive "qmod"
  (function
     Some (MLast.ExStr (_, s)) -> set_qmod s
   | Some _ | None -> failwith "bad directive 1");;

let separate_locate s =
  let len = String.length s in
  if len > 0 && s.[0] = '@' then String.sub s 1 (len - 1), true else s, false
;;

let apply_entry e q =
  let f s = Grammar.Entry.parse e (Stream.of_string s) in
  let m () = try List.assoc q !quot_mod with Not_found -> !any_quot_mod in
  let expr s =
    let (s, locate) = separate_locate s in Qast.to_expr (m ()) (f s)
  in
  let patt s =
    let (s, locate) = separate_locate s in
    let qast =
      let qast = f s in
      if locate then
        match qast with
          Qast.Node (n, Qast.Loc :: nl) -> Qast.Node (n, Qast.TrueLoc :: nl)
        | x -> x
      else qast
    in
    Qast.to_patt (m ()) qast
  in
  Quotation.ExAst (expr, patt)
;;

let attribute_body_eoi = Grammar.Entry.create gram "attribute_body_eoi" in
let sig_item_eoi = Grammar.Entry.create gram "sig_item_eoi" in
let str_item_eoi = Grammar.Entry.create gram "str_item_eoi" in
let ctyp_eoi = Grammar.Entry.create gram "ctyp_eoi" in
let patt_eoi = Grammar.Entry.create gram "patt_eoi" in
let expr_eoi = Grammar.Entry.create gram "expr_eoi" in
let module_type_eoi = Grammar.Entry.create gram "module_type_eoi" in
let module_expr_eoi = Grammar.Entry.create gram "module_expr_eoi" in
let class_type_eoi = Grammar.Entry.create gram "class_type_eoi" in
let class_expr_eoi = Grammar.Entry.create gram "class_expr_eoi" in
let class_sig_item_eoi = Grammar.Entry.create gram "class_sig_item_eoi" in
let class_str_item_eoi = Grammar.Entry.create gram "class_str_item_eoi" in
let with_constr_eoi = Grammar.Entry.create gram "with_constr_eoi" in
let poly_variant_eoi = Grammar.Entry.create gram "poly_variant_eoi" in
let type_decl_eoi = Grammar.Entry.create gram "type_decl_eoi" in
Grammar.safe_extend
  [Grammar.extension
     (attribute_body_eoi : 'attribute_body_eoi Grammar.Entry.e) None
     [None, None,
      [Grammar.production
         (Grammar.r_next
            (Grammar.r_next Grammar.r_stop
               (Grammar.s_nterm
                  (attribute_body : 'attribute_body Grammar.Entry.e)))
            (Grammar.s_token ("EOI", "")),
          (fun _ (x : 'attribute_body) (loc : Ploc.t) ->
             (x : 'attribute_body_eoi)))]];
   Grammar.extension (sig_item_eoi : 'sig_item_eoi Grammar.Entry.e) None
     [None, None,
      [Grammar.production
         (Grammar.r_next
            (Grammar.r_next Grammar.r_stop
               (Grammar.s_nterm (sig_item : 'sig_item Grammar.Entry.e)))
            (Grammar.s_token ("EOI", "")),
          (fun _ (x : 'sig_item) (loc : Ploc.t) -> (x : 'sig_item_eoi)))]];
   Grammar.extension (str_item_eoi : 'str_item_eoi Grammar.Entry.e) None
     [None, None,
      [Grammar.production
         (Grammar.r_next
            (Grammar.r_next Grammar.r_stop
               (Grammar.s_nterm (str_item : 'str_item Grammar.Entry.e)))
            (Grammar.s_token ("EOI", "")),
          (fun _ (x : 'str_item) (loc : Ploc.t) -> (x : 'str_item_eoi)))]];
   Grammar.extension (ctyp_eoi : 'ctyp_eoi Grammar.Entry.e) None
     [None, None,
      [Grammar.production
         (Grammar.r_next
            (Grammar.r_next Grammar.r_stop
               (Grammar.s_nterm (ctyp : 'ctyp Grammar.Entry.e)))
            (Grammar.s_token ("EOI", "")),
          (fun _ (x : 'ctyp) (loc : Ploc.t) -> (x : 'ctyp_eoi)))]];
   Grammar.extension (patt_eoi : 'patt_eoi Grammar.Entry.e) None
     [None, None,
      [Grammar.production
         (Grammar.r_next
            (Grammar.r_next Grammar.r_stop
               (Grammar.s_nterm (patt : 'patt Grammar.Entry.e)))
            (Grammar.s_token ("EOI", "")),
          (fun _ (x : 'patt) (loc : Ploc.t) -> (x : 'patt_eoi)))]];
   Grammar.extension (expr_eoi : 'expr_eoi Grammar.Entry.e) None
     [None, None,
      [Grammar.production
         (Grammar.r_next
            (Grammar.r_next Grammar.r_stop
               (Grammar.s_nterm (expr : 'expr Grammar.Entry.e)))
            (Grammar.s_token ("EOI", "")),
          (fun _ (x : 'expr) (loc : Ploc.t) -> (x : 'expr_eoi)))]];
   Grammar.extension (module_type_eoi : 'module_type_eoi Grammar.Entry.e) None
     [None, None,
      [Grammar.production
         (Grammar.r_next
            (Grammar.r_next Grammar.r_stop
               (Grammar.s_nterm (module_type : 'module_type Grammar.Entry.e)))
            (Grammar.s_token ("EOI", "")),
          (fun _ (x : 'module_type) (loc : Ploc.t) ->
             (x : 'module_type_eoi)))]];
   Grammar.extension (module_expr_eoi : 'module_expr_eoi Grammar.Entry.e) None
     [None, None,
      [Grammar.production
         (Grammar.r_next
            (Grammar.r_next Grammar.r_stop
               (Grammar.s_nterm (module_expr : 'module_expr Grammar.Entry.e)))
            (Grammar.s_token ("EOI", "")),
          (fun _ (x : 'module_expr) (loc : Ploc.t) ->
             (x : 'module_expr_eoi)))]];
   Grammar.extension (class_type_eoi : 'class_type_eoi Grammar.Entry.e) None
     [None, None,
      [Grammar.production
         (Grammar.r_next
            (Grammar.r_next Grammar.r_stop
               (Grammar.s_nterm (class_type : 'class_type Grammar.Entry.e)))
            (Grammar.s_token ("EOI", "")),
          (fun _ (x : 'class_type) (loc : Ploc.t) ->
             (x : 'class_type_eoi)))]];
   Grammar.extension (class_expr_eoi : 'class_expr_eoi Grammar.Entry.e) None
     [None, None,
      [Grammar.production
         (Grammar.r_next
            (Grammar.r_next Grammar.r_stop
               (Grammar.s_nterm (class_expr : 'class_expr Grammar.Entry.e)))
            (Grammar.s_token ("EOI", "")),
          (fun _ (x : 'class_expr) (loc : Ploc.t) ->
             (x : 'class_expr_eoi)))]];
   Grammar.extension
     (class_sig_item_eoi : 'class_sig_item_eoi Grammar.Entry.e) None
     [None, None,
      [Grammar.production
         (Grammar.r_next
            (Grammar.r_next Grammar.r_stop
               (Grammar.s_nterm
                  (class_sig_item : 'class_sig_item Grammar.Entry.e)))
            (Grammar.s_token ("EOI", "")),
          (fun _ (x : 'class_sig_item) (loc : Ploc.t) ->
             (x : 'class_sig_item_eoi)))]];
   Grammar.extension
     (class_str_item_eoi : 'class_str_item_eoi Grammar.Entry.e) None
     [None, None,
      [Grammar.production
         (Grammar.r_next
            (Grammar.r_next Grammar.r_stop
               (Grammar.s_nterm
                  (class_str_item : 'class_str_item Grammar.Entry.e)))
            (Grammar.s_token ("EOI", "")),
          (fun _ (x : 'class_str_item) (loc : Ploc.t) ->
             (x : 'class_str_item_eoi)))]];
   Grammar.extension (with_constr_eoi : 'with_constr_eoi Grammar.Entry.e) None
     [None, None,
      [Grammar.production
         (Grammar.r_next
            (Grammar.r_next Grammar.r_stop
               (Grammar.s_nterm (with_constr : 'with_constr Grammar.Entry.e)))
            (Grammar.s_token ("EOI", "")),
          (fun _ (x : 'with_constr) (loc : Ploc.t) ->
             (x : 'with_constr_eoi)))]];
   Grammar.extension (poly_variant_eoi : 'poly_variant_eoi Grammar.Entry.e)
     None
     [None, None,
      [Grammar.production
         (Grammar.r_next
            (Grammar.r_next Grammar.r_stop
               (Grammar.s_nterm
                  (poly_variant : 'poly_variant Grammar.Entry.e)))
            (Grammar.s_token ("EOI", "")),
          (fun _ (x : 'poly_variant) (loc : Ploc.t) ->
             (x : 'poly_variant_eoi)))]];
   Grammar.extension (type_decl_eoi : 'type_decl_eoi Grammar.Entry.e) None
     [None, None,
      [Grammar.production
         (Grammar.r_next
            (Grammar.r_next Grammar.r_stop
               (Grammar.s_nterm (type_decl : 'type_decl Grammar.Entry.e)))
            (Grammar.s_token ("EOI", "")),
          (fun _ (x : 'type_decl) (loc : Ploc.t) -> (x : 'type_decl_eoi)))]]];
List.iter (fun (q, f) -> Quotation.add q (f q))
  ["attribute_body", apply_entry attribute_body_eoi;
   "sig_item", apply_entry sig_item_eoi; "str_item", apply_entry str_item_eoi;
   "ctyp", apply_entry ctyp_eoi; "patt", apply_entry patt_eoi;
   "expr", apply_entry expr_eoi; "module_type", apply_entry module_type_eoi;
   "module_expr", apply_entry module_expr_eoi;
   "class_type", apply_entry class_type_eoi;
   "class_expr", apply_entry class_expr_eoi;
   "class_sig_item", apply_entry class_sig_item_eoi;
   "class_str_item", apply_entry class_str_item_eoi;
   "with_constr", apply_entry with_constr_eoi;
   "poly_variant", apply_entry poly_variant_eoi;
   "type_decl", apply_entry type_decl_eoi];;

let expr_eoi = Grammar.Entry.create Pcaml.gram "expr_eoi" in
Grammar.safe_extend
  [Grammar.extension (expr_eoi : 'expr_eoi Grammar.Entry.e) None
     [None, None,
      [Grammar.production
         (Grammar.r_next
            (Grammar.r_next Grammar.r_stop
               (Grammar.s_token ("ANTIQUOT_LOC", "")))
            (Grammar.s_token ("EOI", "")),
          (fun _ (a : string) (loc : Ploc.t) ->
             (let loc = Ploc.make_unlined (0, 0) in
              if !(Pcaml.strict_mode) then
                let a =
                  let i = String.index a ':' in
                  let i = String.index_from a (i + 1) ':' in
                  let a = String.sub a (i + 1) (String.length a - i - 1) in
                  Grammar.Entry.parse Pcaml.expr_eoi (Stream.of_string a)
                in
                MLast.ExApp
                  (loc,
                   MLast.ExAcc
                     (loc, MLast.ExUid (loc, "Ploc"),
                      MLast.ExUid (loc, "VaAnt")),
                   MLast.ExAnt (loc, a))
              else
                MLast.ExApp
                  (loc, MLast.ExLid (loc, "failwith"),
                   MLast.ExStr (loc, "antiquot")) :
              'expr_eoi)));
       Grammar.production
         (Grammar.r_next
            (Grammar.r_next Grammar.r_stop
               (Grammar.s_nterm (Pcaml.expr : 'Pcaml__expr Grammar.Entry.e)))
            (Grammar.s_token ("EOI", "")),
          (fun _ (e : 'Pcaml__expr) (loc : Ploc.t) ->
             (let loc = Ploc.make_unlined (0, 0) in
              if !(Pcaml.strict_mode) then
                MLast.ExApp
                  (loc,
                   MLast.ExAcc
                     (loc, MLast.ExUid (loc, "Ploc"),
                      MLast.ExUid (loc, "VaVal")),
                   MLast.ExAnt (loc, e))
              else MLast.ExAnt (loc, e) :
              'expr_eoi)))]]];
let expr s =
  Ploc.call_with Plexer.force_antiquot_loc true (Grammar.Entry.parse expr_eoi)
    (Stream.of_string s)
in
let patt_eoi = Grammar.Entry.create Pcaml.gram "patt_eoi" in
Grammar.safe_extend
  [Grammar.extension (patt_eoi : 'patt_eoi Grammar.Entry.e) None
     [None, None,
      [Grammar.production
         (Grammar.r_next
            (Grammar.r_next Grammar.r_stop
               (Grammar.s_token ("ANTIQUOT_LOC", "")))
            (Grammar.s_token ("EOI", "")),
          (fun _ (a : string) (loc : Ploc.t) ->
             (let loc = Ploc.make_unlined (0, 0) in
              if !(Pcaml.strict_mode) then
                let a =
                  let i = String.index a ':' in
                  let i = String.index_from a (i + 1) ':' in
                  let a = String.sub a (i + 1) (String.length a - i - 1) in
                  Grammar.Entry.parse Pcaml.patt_eoi (Stream.of_string a)
                in
                MLast.PaApp
                  (loc,
                   MLast.PaAcc
                     (loc, MLast.PaUid (loc, "Ploc"),
                      MLast.PaUid (loc, "VaAnt")),
                   MLast.PaAnt (loc, a))
              else MLast.PaAny loc :
              'patt_eoi)));
       Grammar.production
         (Grammar.r_next
            (Grammar.r_next Grammar.r_stop
               (Grammar.s_nterm (Pcaml.patt : 'Pcaml__patt Grammar.Entry.e)))
            (Grammar.s_token ("EOI", "")),
          (fun _ (p : 'Pcaml__patt) (loc : Ploc.t) ->
             (let loc = Ploc.make_unlined (0, 0) in
              if !(Pcaml.strict_mode) then
                MLast.PaApp
                  (loc,
                   MLast.PaAcc
                     (loc, MLast.PaUid (loc, "Ploc"),
                      MLast.PaUid (loc, "VaVal")),
                   MLast.PaAnt (loc, p))
              else MLast.PaAnt (loc, p) :
              'patt_eoi)))]]];
let patt s =
  Ploc.call_with Plexer.force_antiquot_loc true (Grammar.Entry.parse patt_eoi)
    (Stream.of_string s)
in
Quotation.add "vala" (Quotation.ExAst (expr, patt));;
