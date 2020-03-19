(* camlp5r *)
(* pa_r.ml,v *)
(* Copyright (c) INRIA 2007-2017 *)

(* #load "pa_extend.cmo" *)
(* #load "q_MLast.cmo" *)
(* #load "pa_macro.cmo" *)
(* #load "pa_macro_gram.cmo" *)

open Pcaml;;
open Mlsyntax.Revised;;

Pcaml.syntax_name := "Revised";;
Pcaml.no_constructors_arity := false;;

let odfa = !(Plexer.dollar_for_antiquotation) in
let osrs = !(Plexer.simplest_raw_strings) in
let odni = !(Plexer.dot_newline_is) in
Plexer.dollar_for_antiquotation := false;
Plexer.simplest_raw_strings := false;
Plexer.utf8_lexing := true;
Plexer.dot_newline_is := ";";
Grammar.Unsafe.gram_reinit gram (Plexer.gmake ());
Plexer.dot_newline_is := odni;
Plexer.dollar_for_antiquotation := odfa;
Plexer.simplest_raw_strings := osrs;
Grammar.Unsafe.clear_entry attribute_body;
Grammar.Unsafe.clear_entry interf;
Grammar.Unsafe.clear_entry implem;
Grammar.Unsafe.clear_entry top_phrase;
Grammar.Unsafe.clear_entry use_file;
Grammar.Unsafe.clear_entry functor_parameter;
Grammar.Unsafe.clear_entry module_type;
Grammar.Unsafe.clear_entry extended_longident;
Grammar.Unsafe.clear_entry module_expr;
Grammar.Unsafe.clear_entry sig_item;
Grammar.Unsafe.clear_entry str_item;
Grammar.Unsafe.clear_entry signature;
Grammar.Unsafe.clear_entry structure;
Grammar.Unsafe.clear_entry expr;
Grammar.Unsafe.clear_entry patt;
Grammar.Unsafe.clear_entry ipatt;
Grammar.Unsafe.clear_entry ctyp;
Grammar.Unsafe.clear_entry let_binding;
Grammar.Unsafe.clear_entry type_decl;
Grammar.Unsafe.clear_entry type_extension;
Grammar.Unsafe.clear_entry extension_constructor;
Grammar.Unsafe.clear_entry constructor_declaration;
Grammar.Unsafe.clear_entry label_declaration;
Grammar.Unsafe.clear_entry match_case;
Grammar.Unsafe.clear_entry with_constr;
Grammar.Unsafe.clear_entry poly_variant;
Grammar.Unsafe.clear_entry class_type;
Grammar.Unsafe.clear_entry class_expr;
Grammar.Unsafe.clear_entry alg_attribute;
Grammar.Unsafe.clear_entry alg_attributes;
Grammar.Unsafe.clear_entry ext_attributes;
Grammar.Unsafe.clear_entry class_sig_item;
Grammar.Unsafe.clear_entry class_str_item;;

Pcaml.parse_interf := Grammar.Entry.parse interf;;
Pcaml.parse_implem := Grammar.Entry.parse implem;;

Pcaml.add_option "-ignloaddir"
  (Arg.Unit (fun _ -> add_directive "load" (fun _ -> ())))
  "Ignore the #load directives in the input file.";;

let mksequence2 loc =
  function
    [e] -> e
  | seq -> MLast.ExSeq (loc, seq)
;;

let mksequence loc =
  function
    [e] -> e
  | el -> MLast.ExSeq (loc, el)
;;

let mkmatchcase loc p aso w e =
  let p =
    match aso with
      Some p2 -> MLast.PaAli (loc, p, p2)
    | None -> p
  in
  p, w, e
;;

let neg_string n =
  let len = String.length n in
  if len > 0 && n.[0] = '-' then String.sub n 1 (len - 1) else "-" ^ n
;;

let mklistexp loc last =
  let rec loop top =
    function
      [] ->
        begin match last with
          Some e -> e
        | None -> MLast.ExUid (loc, "[]")
        end
    | e1 :: el ->
        let loc = if top then loc else Ploc.encl (MLast.loc_of_expr e1) loc in
        MLast.ExApp
          (loc, MLast.ExApp (loc, MLast.ExUid (loc, "::"), e1), loop false el)
  in
  loop true
;;

let mklistpat loc last =
  let rec loop top =
    function
      [] ->
        begin match last with
          Some p -> p
        | None -> MLast.PaUid (loc, "[]")
        end
    | p1 :: pl ->
        let loc = if top then loc else Ploc.encl (MLast.loc_of_patt p1) loc in
        MLast.PaApp
          (loc, MLast.PaApp (loc, MLast.PaUid (loc, "::"), p1), loop false pl)
  in
  loop true
;;

let operator_rparen =
  Grammar.Entry.of_parser gram "operator_rparen"
    (fun strm ->
       match Stream.npeek 2 strm with
         ["", s; "", ")"] when is_operator s || is_letop s || is_andop s ->
           Stream.junk strm; Stream.junk strm; s
       | _ -> raise Stream.Failure)
;;

let check_not_part_of_patt =
  Grammar.Entry.of_parser gram "check_not_part_of_patt"
    (fun strm ->
       let tok =
         match Stream.npeek 4 strm with
           ("LIDENT", _) :: tok :: _ -> tok
         | ["", "("; "", s; "", ")"; tok] when is_operator s -> tok
         | _ -> raise Stream.Failure
       in
       match tok with
         "", ("," | "as" | "|" | "::") -> raise Stream.Failure
       | _ -> ())
;;

let prefixop =
  Grammar.Entry.of_parser gram "prefixop"
    (fun (strm__ : _ Stream.t) ->
       match Stream.peek strm__ with
         Some ("", x) when is_prefixop x -> Stream.junk strm__; x
       | _ -> raise Stream.Failure)
;;

let infixop0 =
  Grammar.Entry.of_parser gram "infixop0"
    (fun (strm__ : _ Stream.t) ->
       match Stream.peek strm__ with
         Some ("", x) when is_infixop0 x -> Stream.junk strm__; x
       | _ -> raise Stream.Failure)
;;

let infixop1 =
  Grammar.Entry.of_parser gram "infixop1"
    (fun (strm__ : _ Stream.t) ->
       match Stream.peek strm__ with
         Some ("", x) when is_infixop1 x -> Stream.junk strm__; x
       | _ -> raise Stream.Failure)
;;

let infixop2 =
  Grammar.Entry.of_parser gram "infixop2"
    (fun (strm__ : _ Stream.t) ->
       match Stream.peek strm__ with
         Some ("", x) when is_infixop2 x -> Stream.junk strm__; x
       | _ -> raise Stream.Failure)
;;

let infixop3 =
  Grammar.Entry.of_parser gram "infixop3"
    (fun (strm__ : _ Stream.t) ->
       match Stream.peek strm__ with
         Some ("", x) when is_infixop3 x -> Stream.junk strm__; x
       | _ -> raise Stream.Failure)
;;

let infixop4 =
  Grammar.Entry.of_parser gram "infixop4"
    (fun (strm__ : _ Stream.t) ->
       match Stream.peek strm__ with
         Some ("", x) when is_infixop4 x -> Stream.junk strm__; x
       | _ -> raise Stream.Failure)
;;

let hashop =
  Grammar.Entry.of_parser gram "hashop"
    (fun (strm__ : _ Stream.t) ->
       match Stream.peek strm__ with
         Some ("", x) when is_hashop x -> Stream.junk strm__; x
       | _ -> raise Stream.Failure)
;;

let letop =
  Grammar.Entry.of_parser gram "letop"
    (fun (strm__ : _ Stream.t) ->
       match Stream.peek strm__ with
         Some ("", x) when is_letop x -> Stream.junk strm__; x
       | _ -> raise Stream.Failure)
;;

let andop =
  Grammar.Entry.of_parser gram "andop"
    (fun (strm__ : _ Stream.t) ->
       match Stream.peek strm__ with
         Some ("", x) when is_andop x -> Stream.junk strm__; x
       | _ -> raise Stream.Failure)
;;

let mktupexp loc e el = MLast.ExTup (loc, e :: el);;
let mktuppat loc p pl = MLast.PaTup (loc, p :: pl);;
let mktuptyp loc t tl = MLast.TyTup (loc, t :: tl);;

let mklabdecl loc i mf t attrs = loc, i, mf, t, attrs;;
let mkident i : string = i;;

let rec generalized_type_of_type =
  function
    MLast.TyArr (_, t1, t2) ->
      let (tl, rt) = generalized_type_of_type t2 in t1 :: tl, rt
  | t -> [], t
;;

let warned = ref false;;
let warning_deprecated_since_6_00 loc =
  if not !warned then
    begin
      !(Pcaml.warning) loc "syntax deprecated since version 6.00";
      warned := true
    end
;;

let build_op_attributed loc op attrs =
  List.fold_left (fun e a -> MLast.ExAtt (loc, e, a)) (MLast.ExLid (loc, op))
    attrs
;;

let build_letop_binder loc letop b l e =
  let (argpat, argexp) =
    (* TODO FIX THIS CHET *)
    List.fold_left
      (fun (argpat, argexp) (andop, (pat, exp)) ->
         MLast.PaTup (loc, [argpat; pat]),
         MLast.ExApp
           (loc, MLast.ExApp (loc, MLast.ExLid (loc, andop), argexp), exp))
      b l
  in
  MLast.ExApp
    (loc, MLast.ExApp (loc, MLast.ExLid (loc, letop), argexp),
     MLast.ExFun (loc, [argpat, None, e]))
;;

let check_let_exception =
  Grammar.Entry.of_parser gram "check_let_exception"
    (fun strm ->
       match Stream.npeek 2 strm with
         ["", "let"; "", "exception"] -> ()
       | _ -> raise Stream.Failure)
;;

let check_let_not_exception_f strm =
  match Stream.npeek 2 strm with
    ["", "let"; "", "exception"] -> raise Stream.Failure
  | ["", "let"; _] -> ()
  | _ -> raise Stream.Failure
;;

let check_let_not_exception =
  Grammar.Entry.of_parser gram "check_let_not_exception"
    check_let_not_exception_f
;;

let stream_peek_nth n strm =
  let rec loop n =
    function
      [] -> None
    | [x] -> if n == 1 then Some x else None
    | _ :: l -> loop (n - 1) l
  in
  loop n (Stream.npeek n strm)
;;

(* returns True if the stream is a type-decl, and not an extension.
   returns False if the stream is an extension and not a type-decl.
   Since a type-decl might not have an "=" (if it's a list of decls)
   the default is "type-decl".
*)
let word_keywordp s =
  let rec wrec (strm__ : _ Stream.t) =
    match Stream.peek strm__ with
      Some ('a'..'z' | 'A'..'Z' | '_' | '0'..'9') ->
        Stream.junk strm__; let strm = strm__ in wrec strm
    | _ -> let strm = strm__ in Stream.empty strm; true
  in
  let check (strm__ : _ Stream.t) =
    match Stream.peek strm__ with
      Some ('a'..'z' | 'A'..'Z' | '_') ->
        Stream.junk strm__; let strm = strm__ in wrec strm
    | _ -> false
  in
  try check (Stream.of_string s) with Stream.Failure | Stream.Error _ -> false
;;

let is_type_decl_not_extension strm =
  let rec wrec n =
    match stream_peek_nth n strm with
      None -> assert false
    | Some ("", "=" | "", ";" | "", ";;") -> true
    | Some ("", s) when word_keywordp s -> true
    | Some ("EOI", "") -> true
    | Some ("", "+=") -> false
    | Some
        ("", _ | "UIDENT", _ | "LIDENT", _ | "GIDENT", _ | "ANTIQUOT", _) ->
        wrec (n + 1)
    | Some (a, b) ->
        raise
          (Stream.Error
             (Printf.sprintf
                "unexpected tokens in a type-decl/extension: (\"%s\",\"%s\")"
                a b))
  in
  wrec 1
;;

let check_type_decl_f strm =
  if is_type_decl_not_extension strm then () else raise Stream.Failure
;;

let check_type_decl =
  Grammar.Entry.of_parser gram "check_type_decl" check_type_decl_f
;;

let check_type_extension_f strm =
  if not (is_type_decl_not_extension strm) then () else raise Stream.Failure
;;

let check_type_extension =
  Grammar.Entry.of_parser gram "check_type_extension" check_type_extension_f
;;

let check_dot_uid_f strm =
  match Stream.npeek 5 strm with
    ("", ".") :: ("UIDENT", _) :: _ -> ()
  | ("", ".") :: ("", "$") :: ("LIDENT", ("uid" | "_uid")) :: ("", ":") ::
    ("LIDENT", _) :: _ ->
      ()
  | _ -> raise Stream.Failure
;;

let check_dot_uid =
  Grammar.Entry.of_parser gram "check_dot_uid" check_dot_uid_f
;;

let expr_wrap_attrs loc e l =
  let rec wrec e =
    function
      [] -> e
    | h :: t -> wrec (MLast.ExAtt (loc, e, h)) t
  in
  wrec e l
;;

let expr_to_inline loc e ext attrs =
  let e = expr_wrap_attrs loc e attrs in
  match ext with
    None -> e
  | Some attrid ->
      MLast.ExExten
        (loc, (attrid, MLast.StAttr (loc, [MLast.StExp (loc, e, [])])))
;;

let patt_wrap_attrs loc e l =
  let rec wrec e =
    function
      [] -> e
    | h :: t -> wrec (MLast.PaAtt (loc, e, h)) t
  in
  wrec e l
;;

let patt_to_inline loc p ext attrs =
  let p = patt_wrap_attrs loc p attrs in
  match ext with
    None -> p
  | Some attrid -> MLast.PaExten (loc, (attrid, MLast.PaAttr (loc, p, None)))
;;

let class_expr_wrap_attrs loc e l =
  let rec wrec e =
    function
      [] -> e
    | h :: t -> wrec (MLast.CeAtt (loc, e, h)) t
  in
  wrec e l
;;

let str_item_to_inline loc si ext =
  match ext with
    None -> si
  | Some attrid -> MLast.StExten (loc, (attrid, MLast.StAttr (loc, [si])))
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
   and _ = (extended_longident : 'extended_longident Grammar.Entry.e)
   and _ = (signature : 'signature Grammar.Entry.e)
   and _ = (structure : 'structure Grammar.Entry.e)
   and _ = (class_type : 'class_type Grammar.Entry.e)
   and _ = (class_expr : 'class_expr Grammar.Entry.e)
   and _ = (class_sig_item : 'class_sig_item Grammar.Entry.e)
   and _ = (class_str_item : 'class_str_item Grammar.Entry.e)
   and _ = (let_binding : 'let_binding Grammar.Entry.e)
   and _ = (type_decl : 'type_decl Grammar.Entry.e)
   and _ = (type_extension : 'type_extension Grammar.Entry.e)
   and _ = (extension_constructor : 'extension_constructor Grammar.Entry.e)
   and _ =
     (constructor_declaration : 'constructor_declaration Grammar.Entry.e)
   and _ = (label_declaration : 'label_declaration Grammar.Entry.e)
   and _ = (match_case : 'match_case Grammar.Entry.e)
   and _ = (ipatt : 'ipatt Grammar.Entry.e)
   and _ = (with_constr : 'with_constr Grammar.Entry.e)
   and _ = (poly_variant : 'poly_variant Grammar.Entry.e)
   and _ = (attribute_body : 'attribute_body Grammar.Entry.e)
   and _ = (alg_attribute : 'alg_attribute Grammar.Entry.e)
   and _ = (alg_attributes : 'alg_attributes Grammar.Entry.e)
   and _ = (check_type_decl : 'check_type_decl Grammar.Entry.e)
   and _ = (check_type_extension : 'check_type_extension Grammar.Entry.e)
   and _ = (check_dot_uid : 'check_dot_uid Grammar.Entry.e)
   and _ = (ext_attributes : 'ext_attributes Grammar.Entry.e) in
   let grammar_entry_create s =
     Grammar.create_local_entry (Grammar.of_entry sig_item) s
   in
   let attribute_id : 'attribute_id Grammar.Entry.e =
     grammar_entry_create "attribute_id"
   and attribute_structure : 'attribute_structure Grammar.Entry.e =
     grammar_entry_create "attribute_structure"
   and attribute_signature : 'attribute_signature Grammar.Entry.e =
     grammar_entry_create "attribute_signature"
   and floating_attribute : 'floating_attribute Grammar.Entry.e =
     grammar_entry_create "floating_attribute"
   and item_attribute : 'item_attribute Grammar.Entry.e =
     grammar_entry_create "item_attribute"
   and item_attributes : 'item_attributes Grammar.Entry.e =
     grammar_entry_create "item_attributes"
   and alg_attributes_no_anti : 'alg_attributes_no_anti Grammar.Entry.e =
     grammar_entry_create "alg_attributes_no_anti"
   and item_extension : 'item_extension Grammar.Entry.e =
     grammar_entry_create "item_extension"
   and alg_extension : 'alg_extension Grammar.Entry.e =
     grammar_entry_create "alg_extension"
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
   and andop_binding : 'andop_binding Grammar.Entry.e =
     grammar_entry_create "andop_binding"
   and ext_opt : 'ext_opt Grammar.Entry.e = grammar_entry_create "ext_opt"
   and closed_case_list : 'closed_case_list Grammar.Entry.e =
     grammar_entry_create "closed_case_list"
   and cons_expr_opt : 'cons_expr_opt Grammar.Entry.e =
     grammar_entry_create "cons_expr_opt"
   and dummy : 'dummy Grammar.Entry.e = grammar_entry_create "dummy"
   and sequence : 'sequence Grammar.Entry.e = grammar_entry_create "sequence"
   and letop_binding : 'letop_binding Grammar.Entry.e =
     grammar_entry_create "letop_binding"
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
   and mod_ident_patt : 'mod_ident_patt Grammar.Entry.e =
     grammar_entry_create "mod_ident_patt"
   and type_patt : 'type_patt Grammar.Entry.e =
     grammar_entry_create "type_patt"
   and constrain : 'constrain Grammar.Entry.e =
     grammar_entry_create "constrain"
   and type_parameter : 'type_parameter Grammar.Entry.e =
     grammar_entry_create "type_parameter"
   and simple_type_parameter : 'simple_type_parameter Grammar.Entry.e =
     grammar_entry_create "simple_type_parameter"
   and ctyp_ident : 'ctyp_ident Grammar.Entry.e =
     grammar_entry_create "ctyp_ident"
   and ctyp_below_alg_attribute : 'ctyp_below_alg_attribute Grammar.Entry.e =
     grammar_entry_create "ctyp_below_alg_attribute"
   and cons_ident : 'cons_ident Grammar.Entry.e =
     grammar_entry_create "cons_ident"
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
   and class_expr_apply : 'class_expr_apply Grammar.Entry.e =
     grammar_entry_create "class_expr_apply"
   and class_expr_simple : 'class_expr_simple Grammar.Entry.e =
     grammar_entry_create "class_expr_simple"
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
   in
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
              (String.concat "." l : 'attribute_id)))]];
    Grammar.extension
      (attribute_structure : 'attribute_structure Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_list1
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_nterm
                               (str_item : 'str_item Grammar.Entry.e)))
                         (Grammar.s_token ("", ";")),
                       (fun _ (s : 'str_item) (loc : Ploc.t) ->
                          (s : 'e__2)))])),
           (fun (st : 'e__2 list) (loc : Ploc.t) ->
              (st : 'attribute_structure)))]];
    Grammar.extension
      (attribute_signature : 'attribute_signature Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_list1
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_nterm
                               (sig_item : 'sig_item Grammar.Entry.e)))
                         (Grammar.s_token ("", ";")),
                       (fun _ (s : 'sig_item) (loc : Ploc.t) ->
                          (s : 'e__3)))])),
           (fun (st : 'e__3 list) (loc : Ploc.t) ->
              (st : 'attribute_signature)))]];
    Grammar.extension (attribute_body : 'attribute_body Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_nterm
                            (attribute_id : 'attribute_id Grammar.Entry.e)))
                      (Grammar.s_token ("", "?")))
                   (Grammar.s_nterm (patt : 'patt Grammar.Entry.e)))
                (Grammar.s_token ("", "when")))
             (Grammar.s_nterm (expr : 'expr Grammar.Entry.e)),
           (fun (e : 'expr) _ (p : 'patt) _ (id : 'attribute_id)
                (loc : Ploc.t) ->
              (id, MLast.PaAttr (loc, p, Some e) : 'attribute_body)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop
                   (Grammar.s_nterm
                      (attribute_id : 'attribute_id Grammar.Entry.e)))
                (Grammar.s_token ("", "?")))
             (Grammar.s_nterm (patt : 'patt Grammar.Entry.e)),
           (fun (p : 'patt) _ (id : 'attribute_id) (loc : Ploc.t) ->
              (id, MLast.PaAttr (loc, p, None) : 'attribute_body)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop
                   (Grammar.s_nterm
                      (attribute_id : 'attribute_id Grammar.Entry.e)))
                (Grammar.s_token ("", ":")))
             (Grammar.s_nterm (ctyp : 'ctyp Grammar.Entry.e)),
           (fun (ty : 'ctyp) _ (id : 'attribute_id) (loc : Ploc.t) ->
              (id, MLast.TyAttr (loc, ty) : 'attribute_body)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop
                   (Grammar.s_nterm
                      (attribute_id : 'attribute_id Grammar.Entry.e)))
                (Grammar.s_token ("", ":")))
             (Grammar.s_nterm
                (attribute_signature : 'attribute_signature Grammar.Entry.e)),
           (fun (si : 'attribute_signature) _ (id : 'attribute_id)
                (loc : Ploc.t) ->
              (id, MLast.SiAttr (loc, si) : 'attribute_body)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_nterm (attribute_id : 'attribute_id Grammar.Entry.e)),
           (fun (id : 'attribute_id) (loc : Ploc.t) ->
              (id, MLast.StAttr (loc, []) : 'attribute_body)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop
                (Grammar.s_nterm
                   (attribute_id : 'attribute_id Grammar.Entry.e)))
             (Grammar.s_nterm
                (attribute_structure : 'attribute_structure Grammar.Entry.e)),
           (fun (st : 'attribute_structure) (id : 'attribute_id)
                (loc : Ploc.t) ->
              (id, MLast.StAttr (loc, st) : 'attribute_body)))]];
    Grammar.extension
      (floating_attribute : 'floating_attribute Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "[@@@")))
                (Grammar.s_nterm
                   (attribute_body : 'attribute_body Grammar.Entry.e)))
             (Grammar.s_token ("", "]")),
           (fun _ (attr : 'attribute_body) _ (loc : Ploc.t) ->
              (attr : 'floating_attribute)))]];
    Grammar.extension (alg_attribute : 'alg_attribute Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "[@")))
                (Grammar.s_nterm
                   (attribute_body : 'attribute_body Grammar.Entry.e)))
             (Grammar.s_token ("", "]")),
           (fun _ (attr : 'attribute_body) _ (loc : Ploc.t) ->
              (attr : 'alg_attribute)))]];
    Grammar.extension (item_attribute : 'item_attribute Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "[@@")))
                (Grammar.s_nterm
                   (attribute_body : 'attribute_body Grammar.Entry.e)))
             (Grammar.s_token ("", "]")),
           (fun _ (attr : 'attribute_body) _ (loc : Ploc.t) ->
              (attr : 'item_attribute)))]];
    Grammar.extension (item_attributes : 'item_attributes Grammar.Entry.e)
      None
      [None, None,
       [Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_list0
                (Grammar.s_nterm
                   (item_attribute : 'item_attribute Grammar.Entry.e))),
           (fun (l : 'item_attribute list) (loc : Ploc.t) ->
              (l : 'item_attributes)))]];
    Grammar.extension (alg_attributes : 'alg_attributes Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_list0
                (Grammar.s_nterm
                   (alg_attribute : 'alg_attribute Grammar.Entry.e))),
           (fun (l : 'alg_attribute list) (loc : Ploc.t) ->
              (l : 'alg_attributes)))]];
    Grammar.extension
      (alg_attributes_no_anti : 'alg_attributes_no_anti Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_list0
                (Grammar.s_nterm
                   (alg_attribute : 'alg_attribute Grammar.Entry.e))),
           (fun (l : 'alg_attribute list) (loc : Ploc.t) ->
              (l : 'alg_attributes_no_anti)))]];
    Grammar.extension (item_extension : 'item_extension Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "[%%")))
                (Grammar.s_nterm
                   (attribute_body : 'attribute_body Grammar.Entry.e)))
             (Grammar.s_token ("", "]")),
           (fun _ (e : 'attribute_body) _ (loc : Ploc.t) ->
              (e : 'item_extension)))]];
    Grammar.extension (alg_extension : 'alg_extension Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "[%")))
                (Grammar.s_nterm
                   (attribute_body : 'attribute_body Grammar.Entry.e)))
             (Grammar.s_token ("", "]")),
           (fun _ (e : 'attribute_body) _ (loc : Ploc.t) ->
              (e : 'alg_extension)))]];
    Grammar.extension (functor_parameter : 'functor_parameter Grammar.Entry.e)
      None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "(")))
             (Grammar.s_token ("", ")")),
           (fun _ _ (loc : Ploc.t) -> (None : 'functor_parameter)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("", "(")))
                      (Grammar.s_nterm (uidopt : 'uidopt Grammar.Entry.e)))
                   (Grammar.s_token ("", ":")))
                (Grammar.s_nterm
                   (module_type : 'module_type Grammar.Entry.e)))
             (Grammar.s_token ("", ")")),
           (fun _ (t : 'module_type) _ (i : 'uidopt) _ (loc : Ploc.t) ->
              (Some (i, t) : 'functor_parameter)))]];
    Grammar.extension (module_expr : 'module_expr Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next Grammar.r_stop
                      (Grammar.s_token ("", "functor")))
                   (Grammar.s_nterm
                      (functor_parameter :
                       'functor_parameter Grammar.Entry.e)))
                (Grammar.s_token ("", "->")))
             Grammar.s_self,
           (fun (me : 'module_expr) _ (arg : 'functor_parameter) _
                (loc : Ploc.t) ->
              (MLast.MeFun (loc, arg, me) : 'module_expr)))];
       Some "alg_attribute", Some Gramext.LeftA,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                   (Grammar.s_token ("", "[@")))
                (Grammar.s_nterm
                   (attribute_body : 'attribute_body Grammar.Entry.e)))
             (Grammar.s_token ("", "]")),
           (fun _ (attr : 'attribute_body) _ (e1 : 'module_expr)
                (loc : Ploc.t) ->
              (MLast.MeAtt (loc, e1, attr) : 'module_expr)))];
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
              (MLast.MeStr (loc, st) : 'module_expr)))];
       None, None,
       [Grammar.production
          (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
             Grammar.s_self,
           (fun (me2 : 'module_expr) (me1 : 'module_expr) (loc : Ploc.t) ->
              (MLast.MeApp (loc, me1, me2) : 'module_expr)))];
       None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                (Grammar.s_token ("", ".")))
             Grammar.s_self,
           (fun (me2 : 'module_expr) _ (me1 : 'module_expr) (loc : Ploc.t) ->
              (MLast.MeAcc (loc, me1, me2) : 'module_expr)))];
       Some "simple", None,
       [Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_nterm
                (alg_extension : 'alg_extension Grammar.Entry.e)),
           (fun (e : 'alg_extension) (loc : Ploc.t) ->
              (MLast.MeExten (loc, e) : 'module_expr)));
        Grammar.production
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
              (MLast.MeTyc (loc, me, mt) : 'module_expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "(")))
                   (Grammar.s_token ("", "value")))
                (Grammar.s_nterm (expr : 'expr Grammar.Entry.e)))
             (Grammar.s_token ("", ")")),
           (fun _ (e : 'expr) _ _ (loc : Ploc.t) ->
              (MLast.MeUnp (loc, e, None, None) : 'module_expr)));
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
           (fun _ (mt1 : 'module_type) _ (e : 'expr) _ _ (loc : Ploc.t) ->
              (MLast.MeUnp (loc, e, Some mt1, None) : 'module_expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
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
                   (Grammar.s_token ("", ":>")))
                (Grammar.s_nterm
                   (module_type : 'module_type Grammar.Entry.e)))
             (Grammar.s_token ("", ")")),
           (fun _ (mt2 : 'module_type) _ (mt1 : 'module_type) _ (e : 'expr) _
                _ (loc : Ploc.t) ->
              (MLast.MeUnp (loc, e, Some mt1, Some mt2) : 'module_expr)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop (Grammar.s_token ("UIDENT", "")),
           (fun (i : string) (loc : Ploc.t) ->
              (MLast.MeUid (loc, i) : 'module_expr)))]];
    Grammar.extension (structure : 'structure Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_list0
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_nterm
                               (str_item : 'str_item Grammar.Entry.e)))
                         (Grammar.s_token ("", ";")),
                       (fun _ (s : 'str_item) (loc : Ploc.t) ->
                          (s : 'e__4)))])),
           (fun (st : 'e__4 list) (loc : Ploc.t) -> (st : 'structure)))]];
    (*
      extension_constructor:
      [ [ check_extension_rebind ; c = cons_ident ; b = rebind_exn ; alg_attrs = alg_attributes ->
            <:extension_constructor< $_uid:c$ = $_list:b$ $_algattrs:alg_attrs$ >>
        | check_extension_decl ; (_, c, tl, _) = constructor_declaration_sans_alg_attrs ; alg_attrs = alg_attributes ->
            <:extension_constructor< $_uid:c$ of $_list:tl$ $_algattrs:alg_attrs$ >>
        ] ]
      ;
    *)
    Grammar.extension
      (extension_constructor : 'extension_constructor Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop
                (Grammar.s_nterm (cons_ident : 'cons_ident Grammar.Entry.e)))
             (Grammar.s_nterm
                (alg_attributes : 'alg_attributes Grammar.Entry.e)),
           (fun (alg_attrs : 'alg_attributes) (ci : 'cons_ident)
                (loc : Ploc.t) ->
              (MLast.EcTuple (ci, [], alg_attrs) : 'extension_constructor)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next Grammar.r_stop
                      (Grammar.s_nterm
                         (cons_ident : 'cons_ident Grammar.Entry.e)))
                   (Grammar.s_token ("", "of")))
                (Grammar.s_list1sep
                   (Grammar.s_nterm
                      (ctyp_below_alg_attribute :
                       'ctyp_below_alg_attribute Grammar.Entry.e))
                   (Grammar.s_token ("", "and")) false))
             (Grammar.s_nterm
                (alg_attributes : 'alg_attributes Grammar.Entry.e)),
           (fun (alg_attrs : 'alg_attributes)
                (tl : 'ctyp_below_alg_attribute list) _ (ci : 'cons_ident)
                (loc : Ploc.t) ->
              (MLast.EcTuple (ci, tl, alg_attrs) : 'extension_constructor)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop
                   (Grammar.s_nterm
                      (cons_ident : 'cons_ident Grammar.Entry.e)))
                (Grammar.s_nterm (rebind_exn : 'rebind_exn Grammar.Entry.e)))
             (Grammar.s_nterm
                (alg_attributes : 'alg_attributes Grammar.Entry.e)),
           (fun (alg_attrs : 'alg_attributes) (b : 'rebind_exn)
                (ci : 'cons_ident) (loc : Ploc.t) ->
              (MLast.EcRebind (ci, b, alg_attrs) :
               'extension_constructor)))]];
    Grammar.extension (str_item : 'str_item Grammar.Entry.e) None
      [Some "top", None,
       [Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_nterm
                (item_extension : 'item_extension Grammar.Entry.e)),
           (fun (e : 'item_extension) (loc : Ploc.t) ->
              (MLast.StExten (loc, e) : 'str_item)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_nterm
                (floating_attribute : 'floating_attribute Grammar.Entry.e)),
           (fun (attr : 'floating_attribute) (loc : Ploc.t) ->
              (MLast.StFlAtt (loc, attr) : 'str_item)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop
                (Grammar.s_nterm (expr : 'expr Grammar.Entry.e)))
             (Grammar.s_nterm
                (item_attributes : 'item_attributes Grammar.Entry.e)),
           (fun (attrs : 'item_attributes) (e : 'expr) (loc : Ploc.t) ->
              (MLast.StExp (loc, e, attrs) : 'str_item)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "#")))
                (Grammar.s_token ("STRING", "")))
             (Grammar.s_list0
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_nterm
                            (str_item : 'str_item Grammar.Entry.e)),
                       (fun (si : 'str_item) (loc : Ploc.t) ->
                          (si, loc : 'e__6)))])),
           (fun (sil : 'e__6 list) (s : string) _ (loc : Ploc.t) ->
              (MLast.StUse (loc, s, sil) : 'str_item)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "#")))
                (Grammar.s_token ("LIDENT", "")))
             (Grammar.s_opt (Grammar.s_nterm (expr : 'expr Grammar.Entry.e))),
           (fun (dp : 'expr option) (n : string) _ (loc : Ploc.t) ->
              (MLast.StDir (loc, n, dp) : 'str_item)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next Grammar.r_stop
                      (Grammar.s_token ("", "value")))
                   (Grammar.s_nterm (ext_opt : 'ext_opt Grammar.Entry.e)))
                (Grammar.s_flag (Grammar.s_token ("", "rec"))))
             (Grammar.s_list1sep
                (Grammar.s_nterm (let_binding : 'let_binding Grammar.Entry.e))
                (Grammar.s_token ("", "and")) false),
           (fun (l : 'let_binding list) (r : bool) (ext : 'ext_opt) _
                (loc : Ploc.t) ->
              (str_item_to_inline loc (MLast.StVal (loc, r, l)) ext :
               'str_item)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "type")))
                (Grammar.s_nterm
                   (check_type_extension :
                    'check_type_extension Grammar.Entry.e)))
             (Grammar.s_nterm
                (type_extension : 'type_extension Grammar.Entry.e)),
           (fun (te : 'type_extension) _ _ (loc : Ploc.t) ->
              (MLast.StTypExten
                 (loc,
                  {MLast.teNam = te.MLast.teNam; MLast.tePrm = te.MLast.tePrm;
                   MLast.tePrv = te.MLast.tePrv; MLast.teECs = te.MLast.teECs;
                   MLast.teAttributes = te.MLast.teAttributes}) :
               'str_item)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next Grammar.r_stop
                      (Grammar.s_token ("", "type")))
                   (Grammar.s_nterm
                      (check_type_decl : 'check_type_decl Grammar.Entry.e)))
                (Grammar.s_flag (Grammar.s_token ("", "nonrec"))))
             (Grammar.s_list1sep
                (Grammar.s_nterm (type_decl : 'type_decl Grammar.Entry.e))
                (Grammar.s_token ("", "and")) false),
           (fun (tdl : 'type_decl list) (nrfl : bool) _ _ (loc : Ploc.t) ->
              (MLast.StTyp (loc, nrfl, tdl) : 'str_item)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next Grammar.r_stop
                      (Grammar.s_token ("", "open")))
                   (Grammar.s_flag (Grammar.s_token ("", "!"))))
                (Grammar.s_nterm
                   (module_expr : 'module_expr Grammar.Entry.e)))
             (Grammar.s_nterm
                (item_attributes : 'item_attributes Grammar.Entry.e)),
           (fun (attrs : 'item_attributes) (me : 'module_expr) (ovf : bool) _
                (loc : Ploc.t) ->
              (MLast.StOpn (loc, ovf, me, attrs) : 'str_item)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next Grammar.r_stop
                      (Grammar.s_token ("", "module")))
                   (Grammar.s_token ("", "type")))
                (Grammar.s_nterm (ident : 'ident Grammar.Entry.e)))
             (Grammar.s_nterm
                (item_attributes : 'item_attributes Grammar.Entry.e)),
           (fun (attrs : 'item_attributes) (i : 'ident) _ _ (loc : Ploc.t) ->
              (MLast.StMtyAbs (loc, i, attrs) : 'str_item)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("", "module")))
                         (Grammar.s_token ("", "type")))
                      (Grammar.s_nterm (ident : 'ident Grammar.Entry.e)))
                   (Grammar.s_token ("", "=")))
                (Grammar.s_nterm
                   (module_type : 'module_type Grammar.Entry.e)))
             (Grammar.s_nterm
                (item_attributes : 'item_attributes Grammar.Entry.e)),
           (fun (attrs : 'item_attributes) (mt : 'module_type) _ (i : 'ident)
                _ _ (loc : Ploc.t) ->
              (MLast.StMty (loc, i, mt, attrs) : 'str_item)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop
                   (Grammar.s_token ("", "module")))
                (Grammar.s_flag (Grammar.s_token ("", "rec"))))
             (Grammar.s_list1sep
                (Grammar.s_nterm (mod_binding : 'mod_binding Grammar.Entry.e))
                (Grammar.s_token ("", "and")) false),
           (fun (l : 'mod_binding list) (r : bool) _ (loc : Ploc.t) ->
              (MLast.StMod (loc, r, l) : 'str_item)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop
                   (Grammar.s_token ("", "include")))
                (Grammar.s_nterm
                   (module_expr : 'module_expr Grammar.Entry.e)))
             (Grammar.s_nterm
                (item_attributes : 'item_attributes Grammar.Entry.e)),
           (fun (attrs : 'item_attributes) (me : 'module_expr) _
                (loc : Ploc.t) ->
              (MLast.StInc (loc, me, attrs) : 'str_item)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next
                         (Grammar.r_next
                            (Grammar.r_next
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("", "external")))
                               (Grammar.s_token ("", "(")))
                            (Grammar.s_nterm
                               (operator_rparen :
                                'operator_rparen Grammar.Entry.e)))
                         (Grammar.s_token ("", ":")))
                      (Grammar.s_nterm (ctyp : 'ctyp Grammar.Entry.e)))
                   (Grammar.s_token ("", "=")))
                (Grammar.s_list1 (Grammar.s_token ("STRING", ""))))
             (Grammar.s_nterm
                (item_attributes : 'item_attributes Grammar.Entry.e)),
           (fun (attrs : 'item_attributes) (pd : string list) _ (t : 'ctyp) _
                (i : 'operator_rparen) _ _ (loc : Ploc.t) ->
              (MLast.StExt (loc, i, t, pd, attrs) : 'str_item)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next
                         (Grammar.r_next
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("", "external")))
                            (Grammar.s_token ("LIDENT", "")))
                         (Grammar.s_token ("", ":")))
                      (Grammar.s_nterm (ctyp : 'ctyp Grammar.Entry.e)))
                   (Grammar.s_token ("", "=")))
                (Grammar.s_list1 (Grammar.s_token ("STRING", ""))))
             (Grammar.s_nterm
                (item_attributes : 'item_attributes Grammar.Entry.e)),
           (fun (attrs : 'item_attributes) (pd : string list) _ (t : 'ctyp) _
                (i : string) _ (loc : Ploc.t) ->
              (MLast.StExt (loc, i, t, pd, attrs) : 'str_item)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop
                   (Grammar.s_token ("", "exception")))
                (Grammar.s_nterm
                   (extension_constructor :
                    'extension_constructor Grammar.Entry.e)))
             (Grammar.s_nterm
                (item_attributes : 'item_attributes Grammar.Entry.e)),
           (fun (item_attrs : 'item_attributes) (ec : 'extension_constructor)
                _ (loc : Ploc.t) ->
              (MLast.StExc (loc, ec, item_attrs) : 'str_item)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop
                   (Grammar.s_token ("", "declare")))
                (Grammar.s_list0
                   (Grammar.s_rules
                      [Grammar.production
                         (Grammar.r_next
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_nterm
                                  (str_item : 'str_item Grammar.Entry.e)))
                            (Grammar.s_token ("", ";")),
                          (fun _ (s : 'str_item) (loc : Ploc.t) ->
                             (s : 'e__5)))])))
             (Grammar.s_token ("", "end")),
           (fun _ (st : 'e__5 list) _ (loc : Ploc.t) ->
              (MLast.StDcl (loc, st) : 'str_item)))]];
    Grammar.extension (rebind_exn : 'rebind_exn Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "=")))
             (Grammar.s_nterm (mod_ident : 'mod_ident Grammar.Entry.e)),
           (fun (a : 'mod_ident) _ (loc : Ploc.t) -> (a : 'rebind_exn)))]];
    Grammar.extension (mod_binding : 'mod_binding Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop
                   (Grammar.s_nterm (uidopt : 'uidopt Grammar.Entry.e)))
                (Grammar.s_nterm
                   (mod_fun_binding : 'mod_fun_binding Grammar.Entry.e)))
             (Grammar.s_nterm
                (item_attributes : 'item_attributes Grammar.Entry.e)),
           (fun (attrs : 'item_attributes) (me : 'mod_fun_binding)
                (i : 'uidopt) (loc : Ploc.t) ->
              (i, me, attrs : 'mod_binding)))]];
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
              (MLast.MeTyc (loc, me, mt) : 'mod_fun_binding)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop
                (Grammar.s_nterm
                   (functor_parameter : 'functor_parameter Grammar.Entry.e)))
             Grammar.s_self,
           (fun (mb : 'mod_fun_binding) (arg : 'functor_parameter)
                (loc : Ploc.t) ->
              (MLast.MeFun (loc, arg, mb) : 'mod_fun_binding)))]];
    Grammar.extension (module_type : 'module_type Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next Grammar.r_stop
                      (Grammar.s_token ("", "functor")))
                   (Grammar.s_nterm
                      (functor_parameter :
                       'functor_parameter Grammar.Entry.e)))
                (Grammar.s_token ("", "->")))
             Grammar.s_self,
           (fun (mt : 'module_type) _ (arg : 'functor_parameter) _
                (loc : Ploc.t) ->
              (MLast.MtFun (loc, arg, mt) : 'module_type)))];
       Some "->", Some Gramext.RightA,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                (Grammar.s_token ("", "->")))
             Grammar.s_self,
           (fun (mt2 : 'module_type) _ (mt1 : 'module_type) (loc : Ploc.t) ->
              (MLast.MtFun (loc, Some (None, mt1), mt2) : 'module_type)))];
       Some "alg_attribute", Some Gramext.LeftA,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                   (Grammar.s_token ("", "[@")))
                (Grammar.s_nterm
                   (attribute_body : 'attribute_body Grammar.Entry.e)))
             (Grammar.s_token ("", "]")),
           (fun _ (attr : 'attribute_body) _ (e1 : 'module_type)
                (loc : Ploc.t) ->
              (MLast.MtAtt (loc, e1, attr) : 'module_type)))];
       None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                (Grammar.s_token ("", "with")))
             (Grammar.s_list1sep
                (Grammar.s_nterm (with_constr : 'with_constr Grammar.Entry.e))
                (Grammar.s_token ("", "and")) false),
           (fun (wcl : 'with_constr list) _ (mt : 'module_type)
                (loc : Ploc.t) ->
              (MLast.MtWit (loc, mt, wcl) : 'module_type)))];
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
              (MLast.MtTyo (loc, me) : 'module_type)));
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
              (MLast.MtSig (loc, sg) : 'module_type)))];
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
             (Grammar.s_nterm (ident : 'ident Grammar.Entry.e)),
           (fun (i : 'ident) _ (loc : Ploc.t) ->
              (MLast.MtQuo (loc, i) : 'module_type)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_nterm
                (alg_extension : 'alg_extension Grammar.Entry.e)),
           (fun (e : 'alg_extension) (loc : Ploc.t) ->
              (MLast.MtExten (loc, e) : 'module_type)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop (Grammar.s_token ("LIDENT", "")),
           (fun (i : string) (loc : Ploc.t) ->
              (MLast.MtLid (loc, i) : 'module_type)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_nterm
                (extended_longident : 'extended_longident Grammar.Entry.e)),
           (fun (li : 'extended_longident) (loc : Ploc.t) ->
              (MLast.MtLong (loc, li) : 'module_type)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop
                   (Grammar.s_nterm
                      (extended_longident :
                       'extended_longident Grammar.Entry.e)))
                (Grammar.s_token ("", ".")))
             (Grammar.s_token ("LIDENT", "")),
           (fun (i : string) _ (li : 'extended_longident) (loc : Ploc.t) ->
              (MLast.MtLongLid (loc, li, i) : 'module_type)))]];
    Grammar.extension (signature : 'signature Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_list0
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_nterm
                               (sig_item : 'sig_item Grammar.Entry.e)))
                         (Grammar.s_token ("", ";")),
                       (fun _ (s : 'sig_item) (loc : Ploc.t) ->
                          (s : 'e__7)))])),
           (fun (st : 'e__7 list) (loc : Ploc.t) -> (st : 'signature)))]];
    Grammar.extension (sig_item : 'sig_item Grammar.Entry.e) None
      [Some "top", None,
       [Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_nterm
                (item_extension : 'item_extension Grammar.Entry.e)),
           (fun (e : 'item_extension) (loc : Ploc.t) ->
              (MLast.SgExten (loc, e) : 'sig_item)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_nterm
                (floating_attribute : 'floating_attribute Grammar.Entry.e)),
           (fun (attr : 'floating_attribute) (loc : Ploc.t) ->
              (MLast.SgFlAtt (loc, attr) : 'sig_item)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "#")))
                (Grammar.s_token ("STRING", "")))
             (Grammar.s_list0
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_nterm
                            (sig_item : 'sig_item Grammar.Entry.e)),
                       (fun (si : 'sig_item) (loc : Ploc.t) ->
                          (si, loc : 'e__9)))])),
           (fun (sil : 'e__9 list) (s : string) _ (loc : Ploc.t) ->
              (MLast.SgUse (loc, s, sil) : 'sig_item)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "#")))
                (Grammar.s_token ("LIDENT", "")))
             (Grammar.s_opt (Grammar.s_nterm (expr : 'expr Grammar.Entry.e))),
           (fun (dp : 'expr option) (n : string) _ (loc : Ploc.t) ->
              (MLast.SgDir (loc, n, dp) : 'sig_item)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("", "value")))
                         (Grammar.s_token ("", "(")))
                      (Grammar.s_nterm
                         (operator_rparen :
                          'operator_rparen Grammar.Entry.e)))
                   (Grammar.s_token ("", ":")))
                (Grammar.s_nterm (ctyp : 'ctyp Grammar.Entry.e)))
             (Grammar.s_nterm
                (item_attributes : 'item_attributes Grammar.Entry.e)),
           (fun (attrs : 'item_attributes) (t : 'ctyp) _
                (i : 'operator_rparen) _ _ (loc : Ploc.t) ->
              (MLast.SgVal (loc, i, t, attrs) : 'sig_item)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("", "value")))
                      (Grammar.s_token ("LIDENT", "")))
                   (Grammar.s_token ("", ":")))
                (Grammar.s_nterm (ctyp : 'ctyp Grammar.Entry.e)))
             (Grammar.s_nterm
                (item_attributes : 'item_attributes Grammar.Entry.e)),
           (fun (attrs : 'item_attributes) (t : 'ctyp) _ (i : string) _
                (loc : Ploc.t) ->
              (MLast.SgVal (loc, i, t, attrs) : 'sig_item)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "type")))
                (Grammar.s_nterm
                   (check_type_extension :
                    'check_type_extension Grammar.Entry.e)))
             (Grammar.s_nterm
                (type_extension : 'type_extension Grammar.Entry.e)),
           (fun (te : 'type_extension) _ _ (loc : Ploc.t) ->
              (MLast.SgTypExten
                 (loc,
                  {MLast.teNam = te.MLast.teNam; MLast.tePrm = te.MLast.tePrm;
                   MLast.tePrv = te.MLast.tePrv; MLast.teECs = te.MLast.teECs;
                   MLast.teAttributes = te.MLast.teAttributes}) :
               'sig_item)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next Grammar.r_stop
                      (Grammar.s_token ("", "type")))
                   (Grammar.s_nterm
                      (check_type_decl : 'check_type_decl Grammar.Entry.e)))
                (Grammar.s_flag (Grammar.s_token ("", "nonrec"))))
             (Grammar.s_list1sep
                (Grammar.s_nterm (type_decl : 'type_decl Grammar.Entry.e))
                (Grammar.s_token ("", "and")) false),
           (fun (tdl : 'type_decl list) (nrfl : bool) _ _ (loc : Ploc.t) ->
              (MLast.SgTyp (loc, nrfl, tdl) : 'sig_item)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "open")))
                (Grammar.s_nterm
                   (extended_longident :
                    'extended_longident Grammar.Entry.e)))
             (Grammar.s_nterm
                (item_attributes : 'item_attributes Grammar.Entry.e)),
           (fun (attrs : 'item_attributes) (i : 'extended_longident) _
                (loc : Ploc.t) ->
              (MLast.SgOpn (loc, i, attrs) : 'sig_item)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("", "module")))
                         (Grammar.s_token ("", "alias")))
                      (Grammar.s_token ("UIDENT", "")))
                   (Grammar.s_token ("", "=")))
                (Grammar.s_nterm (mod_ident : 'mod_ident Grammar.Entry.e)))
             (Grammar.s_nterm
                (item_attributes : 'item_attributes Grammar.Entry.e)),
           (fun (attrs : 'item_attributes) (li : 'mod_ident) _ (i : string) _
                _ (loc : Ploc.t) ->
              (MLast.SgMtyAlias (loc, i, li, attrs) : 'sig_item)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next Grammar.r_stop
                      (Grammar.s_token ("", "module")))
                   (Grammar.s_token ("", "type")))
                (Grammar.s_nterm (ident : 'ident Grammar.Entry.e)))
             (Grammar.s_nterm
                (item_attributes : 'item_attributes Grammar.Entry.e)),
           (fun (attrs : 'item_attributes) (i : 'ident) _ _ (loc : Ploc.t) ->
              (MLast.SgMtyAbs (loc, i, attrs) : 'sig_item)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("", "module")))
                         (Grammar.s_token ("", "type")))
                      (Grammar.s_nterm (ident : 'ident Grammar.Entry.e)))
                   (Grammar.s_token ("", "=")))
                (Grammar.s_nterm
                   (module_type : 'module_type Grammar.Entry.e)))
             (Grammar.s_nterm
                (item_attributes : 'item_attributes Grammar.Entry.e)),
           (fun (attrs : 'item_attributes) (mt : 'module_type) _ (i : 'ident)
                _ _ (loc : Ploc.t) ->
              (MLast.SgMty (loc, i, mt, attrs) : 'sig_item)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop
                   (Grammar.s_token ("", "module")))
                (Grammar.s_flag (Grammar.s_token ("", "rec"))))
             (Grammar.s_list1sep
                (Grammar.s_nterm
                   (mod_decl_binding : 'mod_decl_binding Grammar.Entry.e))
                (Grammar.s_token ("", "and")) false),
           (fun (l : 'mod_decl_binding list) (rf : bool) _ (loc : Ploc.t) ->
              (MLast.SgMod (loc, rf, l) : 'sig_item)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop
                   (Grammar.s_token ("", "include")))
                (Grammar.s_nterm
                   (module_type : 'module_type Grammar.Entry.e)))
             (Grammar.s_nterm
                (item_attributes : 'item_attributes Grammar.Entry.e)),
           (fun (attrs : 'item_attributes) (mt : 'module_type) _
                (loc : Ploc.t) ->
              (MLast.SgInc (loc, mt, attrs) : 'sig_item)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next
                         (Grammar.r_next
                            (Grammar.r_next
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("", "external")))
                               (Grammar.s_token ("", "(")))
                            (Grammar.s_nterm
                               (operator_rparen :
                                'operator_rparen Grammar.Entry.e)))
                         (Grammar.s_token ("", ":")))
                      (Grammar.s_nterm (ctyp : 'ctyp Grammar.Entry.e)))
                   (Grammar.s_token ("", "=")))
                (Grammar.s_list1 (Grammar.s_token ("STRING", ""))))
             (Grammar.s_nterm
                (item_attributes : 'item_attributes Grammar.Entry.e)),
           (fun (attrs : 'item_attributes) (pd : string list) _ (t : 'ctyp) _
                (i : 'operator_rparen) _ _ (loc : Ploc.t) ->
              (MLast.SgExt (loc, i, t, pd, attrs) : 'sig_item)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next
                         (Grammar.r_next
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("", "external")))
                            (Grammar.s_token ("LIDENT", "")))
                         (Grammar.s_token ("", ":")))
                      (Grammar.s_nterm (ctyp : 'ctyp Grammar.Entry.e)))
                   (Grammar.s_token ("", "=")))
                (Grammar.s_list1 (Grammar.s_token ("STRING", ""))))
             (Grammar.s_nterm
                (item_attributes : 'item_attributes Grammar.Entry.e)),
           (fun (attrs : 'item_attributes) (pd : string list) _ (t : 'ctyp) _
                (i : string) _ (loc : Ploc.t) ->
              (MLast.SgExt (loc, i, t, pd, attrs) : 'sig_item)));
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
                (Grammar.s_nterm
                   (alg_attributes : 'alg_attributes Grammar.Entry.e)))
             (Grammar.s_nterm
                (item_attributes : 'item_attributes Grammar.Entry.e)),
           (fun (item_attrs : 'item_attributes) (alg_attrs : 'alg_attributes)
                (_, c, tl, _ : 'constructor_declaration_sans_alg_attrs) _
                (loc : Ploc.t) ->
              (MLast.SgExc (loc, c, tl, alg_attrs, item_attrs) : 'sig_item)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop
                   (Grammar.s_token ("", "declare")))
                (Grammar.s_list0
                   (Grammar.s_rules
                      [Grammar.production
                         (Grammar.r_next
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_nterm
                                  (sig_item : 'sig_item Grammar.Entry.e)))
                            (Grammar.s_token ("", ";")),
                          (fun _ (s : 'sig_item) (loc : Ploc.t) ->
                             (s : 'e__8)))])))
             (Grammar.s_token ("", "end")),
           (fun _ (st : 'e__8 list) _ (loc : Ploc.t) ->
              (MLast.SgDcl (loc, st) : 'sig_item)))]];
    Grammar.extension (mod_decl_binding : 'mod_decl_binding Grammar.Entry.e)
      None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop
                   (Grammar.s_nterm (uidopt : 'uidopt Grammar.Entry.e)))
                (Grammar.s_nterm
                   (module_declaration :
                    'module_declaration Grammar.Entry.e)))
             (Grammar.s_nterm
                (item_attributes : 'item_attributes Grammar.Entry.e)),
           (fun (attrs : 'item_attributes) (mt : 'module_declaration)
                (i : 'uidopt) (loc : Ploc.t) ->
              (i, mt, attrs : 'mod_decl_binding)))]];
    Grammar.extension
      (module_declaration : 'module_declaration Grammar.Entry.e) None
      [None, Some Gramext.RightA,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop
                (Grammar.s_nterm
                   (functor_parameter : 'functor_parameter Grammar.Entry.e)))
             Grammar.s_self,
           (fun (mt : 'module_declaration) (arg : 'functor_parameter)
                (loc : Ploc.t) ->
              (MLast.MtFun (loc, arg, mt) : 'module_declaration)));
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
                   (Grammar.s_nterm (mod_ident : 'mod_ident Grammar.Entry.e)))
                (Grammar.s_token ("", ":=")))
             (Grammar.s_nterm (module_expr : 'module_expr Grammar.Entry.e)),
           (fun (me : 'module_expr) _ (i : 'mod_ident) _ (loc : Ploc.t) ->
              (MLast.WcMos (loc, i, me) : 'with_constr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next Grammar.r_stop
                      (Grammar.s_token ("", "module")))
                   (Grammar.s_nterm (mod_ident : 'mod_ident Grammar.Entry.e)))
                (Grammar.s_token ("", "=")))
             (Grammar.s_nterm (module_expr : 'module_expr Grammar.Entry.e)),
           (fun (me : 'module_expr) _ (i : 'mod_ident) _ (loc : Ploc.t) ->
              (MLast.WcMod (loc, i, me) : 'with_constr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("", "type")))
                      (Grammar.s_nterm
                         (mod_ident : 'mod_ident Grammar.Entry.e)))
                   (Grammar.s_list0
                      (Grammar.s_nterm
                         (type_parameter : 'type_parameter Grammar.Entry.e))))
                (Grammar.s_token ("", ":=")))
             (Grammar.s_nterm
                (ctyp_below_alg_attribute :
                 'ctyp_below_alg_attribute Grammar.Entry.e)),
           (fun (t : 'ctyp_below_alg_attribute) _ (tpl : 'type_parameter list)
                (i : 'mod_ident) _ (loc : Ploc.t) ->
              (MLast.WcTys (loc, i, tpl, t) : 'with_constr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("", "type")))
                         (Grammar.s_nterm
                            (mod_ident : 'mod_ident Grammar.Entry.e)))
                      (Grammar.s_list0
                         (Grammar.s_nterm
                            (type_parameter :
                             'type_parameter Grammar.Entry.e))))
                   (Grammar.s_token ("", "=")))
                (Grammar.s_flag (Grammar.s_token ("", "private"))))
             (Grammar.s_nterm
                (ctyp_below_alg_attribute :
                 'ctyp_below_alg_attribute Grammar.Entry.e)),
           (fun (t : 'ctyp_below_alg_attribute) (pf : bool) _
                (tpl : 'type_parameter list) (i : 'mod_ident) _
                (loc : Ploc.t) ->
              (MLast.WcTyp (loc, i, tpl, pf, t) : 'with_constr)))]];
    Grammar.extension (uidopt : 'uidopt Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "_")),
           (fun _ (loc : Ploc.t) -> (None : 'uidopt)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop (Grammar.s_token ("UIDENT", "")),
           (fun (m : string) (loc : Ploc.t) -> (Some m : 'uidopt)))]];
    Grammar.extension (andop_binding : 'andop_binding Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop
                (Grammar.s_nterm (andop : 'andop Grammar.Entry.e)))
             (Grammar.s_nterm
                (letop_binding : 'letop_binding Grammar.Entry.e)),
           (fun (b : 'letop_binding) (op : 'andop) (loc : Ploc.t) ->
              (op, b : 'andop_binding)))]];
    Grammar.extension (ext_opt : 'ext_opt Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_opt
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("", "%")))
                         (Grammar.s_nterm
                            (attribute_id : 'attribute_id Grammar.Entry.e)),
                       (fun (id : 'attribute_id) _ (loc : Ploc.t) ->
                          (id : 'e__10)))])),
           (fun (ext : 'e__10 option) (loc : Ploc.t) -> (ext : 'ext_opt)))]];
    Grammar.extension (ext_attributes : 'ext_attributes Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop
                (Grammar.s_nterm (ext_opt : 'ext_opt Grammar.Entry.e)))
             (Grammar.s_nterm
                (alg_attributes_no_anti :
                 'alg_attributes_no_anti Grammar.Entry.e)),
           (fun (l : 'alg_attributes_no_anti) (e : 'ext_opt) (loc : Ploc.t) ->
              (e, l : 'ext_attributes)))]];
    Grammar.extension (expr : 'expr Grammar.Entry.e) None
      [Some "top", Some Gramext.RightA,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next
                         (Grammar.r_next
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("", "while")))
                            (Grammar.s_nterm
                               (ext_attributes :
                                'ext_attributes Grammar.Entry.e)))
                         Grammar.s_self)
                      (Grammar.s_token ("", "do")))
                   (Grammar.s_token ("", "{")))
                (Grammar.s_nterm (sequence : 'sequence Grammar.Entry.e)))
             (Grammar.s_token ("", "}")),
           (fun _ (seq : 'sequence) _ _ (e : 'expr)
                (ext, attrs : 'ext_attributes) _ (loc : Ploc.t) ->
              (expr_to_inline loc (MLast.ExWhi (loc, e, seq)) ext attrs :
               'expr)));
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
                                     (Grammar.r_next
                                        (Grammar.r_next Grammar.r_stop
                                           (Grammar.s_token ("", "for")))
                                        (Grammar.s_nterm
                                           (ext_attributes :
                                            'ext_attributes Grammar.Entry.e)))
                                     (Grammar.s_nterm
                                        (patt : 'patt Grammar.Entry.e)))
                                  (Grammar.s_token ("", "=")))
                               Grammar.s_self)
                            (Grammar.s_nterm
                               (direction_flag :
                                'direction_flag Grammar.Entry.e)))
                         Grammar.s_self)
                      (Grammar.s_token ("", "do")))
                   (Grammar.s_token ("", "{")))
                (Grammar.s_nterm (sequence : 'sequence Grammar.Entry.e)))
             (Grammar.s_token ("", "}")),
           (fun _ (seq : 'sequence) _ _ (e2 : 'expr) (df : 'direction_flag)
                (e1 : 'expr) _ (i : 'patt) (ext, attrs : 'ext_attributes) _
                (loc : Ploc.t) ->
              (expr_to_inline loc (MLast.ExFor (loc, i, e1, e2, df, seq)) ext
                 attrs :
               'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("", "do")))
                      (Grammar.s_nterm
                         (ext_attributes : 'ext_attributes Grammar.Entry.e)))
                   (Grammar.s_token ("", "{")))
                (Grammar.s_nterm (sequence : 'sequence Grammar.Entry.e)))
             (Grammar.s_token ("", "}")),
           (fun _ (seq : 'sequence) _ (ext, attrs : 'ext_attributes) _
                (loc : Ploc.t) ->
              (expr_to_inline loc (mksequence2 loc seq) ext attrs : 'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next
                         (Grammar.r_next
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("", "if")))
                            (Grammar.s_nterm
                               (ext_attributes :
                                'ext_attributes Grammar.Entry.e)))
                         Grammar.s_self)
                      (Grammar.s_token ("", "then")))
                   Grammar.s_self)
                (Grammar.s_token ("", "else")))
             Grammar.s_self,
           (fun (e3 : 'expr) _ (e2 : 'expr) _ (e1 : 'expr)
                (ext, attrs : 'ext_attributes) _ (loc : Ploc.t) ->
              (expr_to_inline loc (MLast.ExIfe (loc, e1, e2, e3)) ext attrs :
               'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("", "try")))
                      (Grammar.s_nterm
                         (ext_attributes : 'ext_attributes Grammar.Entry.e)))
                   Grammar.s_self)
                (Grammar.s_token ("", "with")))
             (Grammar.s_nterm (match_case : 'match_case Grammar.Entry.e)),
           (fun (mc : 'match_case) _ (e : 'expr)
                (ext, attrs : 'ext_attributes) _ (loc : Ploc.t) ->
              (expr_to_inline loc (MLast.ExTry (loc, e, [mc])) ext attrs :
               'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("", "try")))
                      (Grammar.s_nterm
                         (ext_attributes : 'ext_attributes Grammar.Entry.e)))
                   Grammar.s_self)
                (Grammar.s_token ("", "with")))
             (Grammar.s_nterm
                (closed_case_list : 'closed_case_list Grammar.Entry.e)),
           (fun (l : 'closed_case_list) _ (e : 'expr)
                (ext, attrs : 'ext_attributes) _ (loc : Ploc.t) ->
              (expr_to_inline loc (MLast.ExTry (loc, e, l)) ext attrs :
               'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next
                         (Grammar.r_next
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("", "match")))
                            (Grammar.s_nterm
                               (ext_attributes :
                                'ext_attributes Grammar.Entry.e)))
                         Grammar.s_self)
                      (Grammar.s_token ("", "with")))
                   (Grammar.s_nterm (ipatt : 'ipatt Grammar.Entry.e)))
                (Grammar.s_token ("", "->")))
             Grammar.s_self,
           (fun (e1 : 'expr) _ (p1 : 'ipatt) _ (e : 'expr)
                (ext, attrs : 'ext_attributes) _ (loc : Ploc.t) ->
              (expr_to_inline loc (MLast.ExMat (loc, e, [p1, None, e1])) ext
                 attrs :
               'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("", "match")))
                      (Grammar.s_nterm
                         (ext_attributes : 'ext_attributes Grammar.Entry.e)))
                   Grammar.s_self)
                (Grammar.s_token ("", "with")))
             (Grammar.s_nterm
                (closed_case_list : 'closed_case_list Grammar.Entry.e)),
           (fun (l : 'closed_case_list) _ (e : 'expr)
                (ext, attrs : 'ext_attributes) _ (loc : Ploc.t) ->
              (expr_to_inline loc (MLast.ExMat (loc, e, l)) ext attrs :
               'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next Grammar.r_stop
                      (Grammar.s_token ("", "fun")))
                   (Grammar.s_nterm
                      (ext_attributes : 'ext_attributes Grammar.Entry.e)))
                (Grammar.s_nterm (ipatt : 'ipatt Grammar.Entry.e)))
             (Grammar.s_nterm (fun_def : 'fun_def Grammar.Entry.e)),
           (fun (e : 'fun_def) (p : 'ipatt) (ext, attrs : 'ext_attributes) _
                (loc : Ploc.t) ->
              (expr_to_inline loc (MLast.ExFun (loc, [p, None, e])) ext
                 attrs :
               'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "fun")))
                (Grammar.s_nterm
                   (ext_attributes : 'ext_attributes Grammar.Entry.e)))
             (Grammar.s_nterm
                (closed_case_list : 'closed_case_list Grammar.Entry.e)),
           (fun (l : 'closed_case_list) (ext, attrs : 'ext_attributes) _
                (loc : Ploc.t) ->
              (expr_to_inline loc (MLast.ExFun (loc, l)) ext attrs : 'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next
                         (Grammar.r_next
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_nterm
                                  (check_let_not_exception :
                                   'check_let_not_exception Grammar.Entry.e)))
                            (Grammar.s_token ("", "let")))
                         (Grammar.s_token ("", "open")))
                      (Grammar.s_nterm
                         (ext_attributes : 'ext_attributes Grammar.Entry.e)))
                   (Grammar.s_nterm
                      (module_expr : 'module_expr Grammar.Entry.e)))
                (Grammar.s_token ("", "in")))
             Grammar.s_self,
           (fun (e : 'expr) _ (m : 'module_expr)
                (ext, attrs : 'ext_attributes) _ _ _ (loc : Ploc.t) ->
              (expr_to_inline loc (MLast.ExLop (loc, m, e)) ext attrs :
               'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next
                         (Grammar.r_next
                            (Grammar.r_next
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_nterm
                                     (check_let_not_exception :
                                      'check_let_not_exception
                                        Grammar.Entry.e)))
                               (Grammar.s_token ("", "let")))
                            (Grammar.s_token ("", "module")))
                         (Grammar.s_nterm
                            (ext_attributes :
                             'ext_attributes Grammar.Entry.e)))
                      (Grammar.s_nterm (uidopt : 'uidopt Grammar.Entry.e)))
                   (Grammar.s_nterm
                      (mod_fun_binding : 'mod_fun_binding Grammar.Entry.e)))
                (Grammar.s_token ("", "in")))
             Grammar.s_self,
           (fun (e : 'expr) _ (mb : 'mod_fun_binding) (m : 'uidopt)
                (ext, attrs : 'ext_attributes) _ _ _ (loc : Ploc.t) ->
              (expr_to_inline loc (MLast.ExLmd (loc, m, mb, e)) ext attrs :
               'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_nterm (letop : 'letop Grammar.Entry.e)))
                      (Grammar.s_nterm
                         (letop_binding : 'letop_binding Grammar.Entry.e)))
                   (Grammar.s_list0
                      (Grammar.s_nterm
                         (andop_binding : 'andop_binding Grammar.Entry.e))))
                (Grammar.s_token ("", "in")))
             (Grammar.s_nterml (expr : 'expr Grammar.Entry.e) "top"),
           (fun (x : 'expr) _ (l : 'andop_binding list) (b : 'letop_binding)
                (letop : 'letop) (loc : Ploc.t) ->
              (build_letop_binder loc letop b l x : 'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next
                         (Grammar.r_next
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_nterm
                                  (check_let_not_exception :
                                   'check_let_not_exception Grammar.Entry.e)))
                            (Grammar.s_token ("", "let")))
                         (Grammar.s_nterm
                            (ext_opt : 'ext_opt Grammar.Entry.e)))
                      (Grammar.s_flag (Grammar.s_token ("", "rec"))))
                   (Grammar.s_list1sep
                      (Grammar.s_nterm
                         (let_binding : 'let_binding Grammar.Entry.e))
                      (Grammar.s_token ("", "and")) false))
                (Grammar.s_token ("", "in")))
             Grammar.s_self,
           (fun (x : 'expr) _ (l : 'let_binding list) (r : bool)
                (ext : 'ext_opt) _ _ (loc : Ploc.t) ->
              (expr_to_inline loc (MLast.ExLet (loc, r, l, x)) ext [] :
               'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next
                         (Grammar.r_next
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_nterm
                                  (check_let_exception :
                                   'check_let_exception Grammar.Entry.e)))
                            (Grammar.s_token ("", "let")))
                         (Grammar.s_token ("", "exception")))
                      (Grammar.s_token ("UIDENT", "")))
                   (Grammar.s_nterm
                      (alg_attributes : 'alg_attributes Grammar.Entry.e)))
                (Grammar.s_token ("", "in")))
             Grammar.s_self,
           (fun (x : 'expr) _ (alg_attrs : 'alg_attributes) (id : string) _ _
                _ (loc : Ploc.t) ->
              (MLast.ExLEx (loc, id, [], x, alg_attrs) : 'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next
                         (Grammar.r_next
                            (Grammar.r_next
                               (Grammar.r_next
                                  (Grammar.r_next Grammar.r_stop
                                     (Grammar.s_nterm
                                        (check_let_exception :
                                         'check_let_exception
                                           Grammar.Entry.e)))
                                  (Grammar.s_token ("", "let")))
                               (Grammar.s_token ("", "exception")))
                            (Grammar.s_token ("UIDENT", "")))
                         (Grammar.s_token ("", "of")))
                      (Grammar.s_list1
                         (Grammar.s_nterm
                            (ctyp_below_alg_attribute :
                             'ctyp_below_alg_attribute Grammar.Entry.e))))
                   (Grammar.s_nterm
                      (alg_attributes : 'alg_attributes Grammar.Entry.e)))
                (Grammar.s_token ("", "in")))
             Grammar.s_self,
           (fun (x : 'expr) _ (alg_attrs : 'alg_attributes)
                (tyl : 'ctyp_below_alg_attribute list) _ (id : string) _ _ _
                (loc : Ploc.t) ->
              (MLast.ExLEx (loc, id, tyl, x, alg_attrs) : 'expr)))];
       Some "where", None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next Grammar.r_stop Grammar.s_self)
                      (Grammar.s_token ("", "where")))
                   (Grammar.s_nterm
                      (ext_attributes : 'ext_attributes Grammar.Entry.e)))
                (Grammar.s_flag (Grammar.s_token ("", "rec"))))
             (Grammar.s_nterm (let_binding : 'let_binding Grammar.Entry.e)),
           (fun (lb : 'let_binding) (rf : bool) (ext, attrs : 'ext_attributes)
                _ (e : 'expr) (loc : Ploc.t) ->
              (expr_to_inline loc (MLast.ExLet (loc, rf, [lb], e)) ext attrs :
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
              (MLast.ExAss (loc, e1, e2) : 'expr)))];
       Some "||", Some Gramext.RightA,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                (Grammar.s_token ("", "||")))
             Grammar.s_self,
           (fun (e2 : 'expr) _ (e1 : 'expr) (loc : Ploc.t) ->
              (MLast.ExApp
                 (loc, MLast.ExApp (loc, MLast.ExLid (loc, "||"), e1), e2) :
               'expr)))];
       Some "&&", Some Gramext.RightA,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                (Grammar.s_token ("", "&&")))
             Grammar.s_self,
           (fun (e2 : 'expr) _ (e1 : 'expr) (loc : Ploc.t) ->
              (MLast.ExApp
                 (loc, MLast.ExApp (loc, MLast.ExLid (loc, "&&"), e1), e2) :
               'expr)))];
       Some "<", Some Gramext.LeftA,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                (Grammar.s_nterm (infixop0 : 'infixop0 Grammar.Entry.e)))
             Grammar.s_self,
           (fun (e2 : 'expr) (op : 'infixop0) (e1 : 'expr) (loc : Ploc.t) ->
              (MLast.ExApp
                 (loc, MLast.ExApp (loc, MLast.ExLid (loc, op), e1), e2) :
               'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                (Grammar.s_token ("", "!=")))
             Grammar.s_self,
           (fun (e2 : 'expr) _ (e1 : 'expr) (loc : Ploc.t) ->
              (MLast.ExApp
                 (loc, MLast.ExApp (loc, MLast.ExLid (loc, "!="), e1), e2) :
               'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                (Grammar.s_token ("", "==")))
             Grammar.s_self,
           (fun (e2 : 'expr) _ (e1 : 'expr) (loc : Ploc.t) ->
              (MLast.ExApp
                 (loc, MLast.ExApp (loc, MLast.ExLid (loc, "=="), e1), e2) :
               'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                (Grammar.s_token ("", "<>")))
             Grammar.s_self,
           (fun (e2 : 'expr) _ (e1 : 'expr) (loc : Ploc.t) ->
              (MLast.ExApp
                 (loc, MLast.ExApp (loc, MLast.ExLid (loc, "<>"), e1), e2) :
               'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                (Grammar.s_token ("", "=")))
             Grammar.s_self,
           (fun (e2 : 'expr) _ (e1 : 'expr) (loc : Ploc.t) ->
              (MLast.ExApp
                 (loc, MLast.ExApp (loc, MLast.ExLid (loc, "="), e1), e2) :
               'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                (Grammar.s_token ("", ">=")))
             Grammar.s_self,
           (fun (e2 : 'expr) _ (e1 : 'expr) (loc : Ploc.t) ->
              (MLast.ExApp
                 (loc, MLast.ExApp (loc, MLast.ExLid (loc, ">="), e1), e2) :
               'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                (Grammar.s_token ("", "<=")))
             Grammar.s_self,
           (fun (e2 : 'expr) _ (e1 : 'expr) (loc : Ploc.t) ->
              (MLast.ExApp
                 (loc, MLast.ExApp (loc, MLast.ExLid (loc, "<="), e1), e2) :
               'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                (Grammar.s_token ("", ">")))
             Grammar.s_self,
           (fun (e2 : 'expr) _ (e1 : 'expr) (loc : Ploc.t) ->
              (MLast.ExApp
                 (loc, MLast.ExApp (loc, MLast.ExLid (loc, ">"), e1), e2) :
               'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                (Grammar.s_token ("", "<")))
             Grammar.s_self,
           (fun (e2 : 'expr) _ (e1 : 'expr) (loc : Ploc.t) ->
              (MLast.ExApp
                 (loc, MLast.ExApp (loc, MLast.ExLid (loc, "<"), e1), e2) :
               'expr)))];
       Some "^", Some Gramext.RightA,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                (Grammar.s_nterm (infixop1 : 'infixop1 Grammar.Entry.e)))
             Grammar.s_self,
           (fun (e2 : 'expr) (op : 'infixop1) (e1 : 'expr) (loc : Ploc.t) ->
              (MLast.ExApp
                 (loc, MLast.ExApp (loc, MLast.ExLid (loc, op), e1), e2) :
               'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                (Grammar.s_token ("", "@")))
             Grammar.s_self,
           (fun (e2 : 'expr) _ (e1 : 'expr) (loc : Ploc.t) ->
              (MLast.ExApp
                 (loc, MLast.ExApp (loc, MLast.ExLid (loc, "@"), e1), e2) :
               'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                (Grammar.s_token ("", "^")))
             Grammar.s_self,
           (fun (e2 : 'expr) _ (e1 : 'expr) (loc : Ploc.t) ->
              (MLast.ExApp
                 (loc, MLast.ExApp (loc, MLast.ExLid (loc, "^"), e1), e2) :
               'expr)))];
       Some "alg_attribute", Some Gramext.LeftA,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                   (Grammar.s_token ("", "[@")))
                (Grammar.s_nterm
                   (attribute_body : 'attribute_body Grammar.Entry.e)))
             (Grammar.s_token ("", "]")),
           (fun _ (attr : 'attribute_body) _ (e1 : 'expr) (loc : Ploc.t) ->
              (MLast.ExAtt (loc, e1, attr) : 'expr)))];
       Some "+", Some Gramext.LeftA,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                (Grammar.s_nterm (infixop2 : 'infixop2 Grammar.Entry.e)))
             Grammar.s_self,
           (fun (e2 : 'expr) (op : 'infixop2) (e1 : 'expr) (loc : Ploc.t) ->
              (MLast.ExApp
                 (loc, MLast.ExApp (loc, MLast.ExLid (loc, op), e1), e2) :
               'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                (Grammar.s_token ("", "-.")))
             Grammar.s_self,
           (fun (e2 : 'expr) _ (e1 : 'expr) (loc : Ploc.t) ->
              (MLast.ExApp
                 (loc, MLast.ExApp (loc, MLast.ExLid (loc, "-."), e1), e2) :
               'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                (Grammar.s_token ("", "+.")))
             Grammar.s_self,
           (fun (e2 : 'expr) _ (e1 : 'expr) (loc : Ploc.t) ->
              (MLast.ExApp
                 (loc, MLast.ExApp (loc, MLast.ExLid (loc, "+."), e1), e2) :
               'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                (Grammar.s_token ("", "-")))
             Grammar.s_self,
           (fun (e2 : 'expr) _ (e1 : 'expr) (loc : Ploc.t) ->
              (MLast.ExApp
                 (loc, MLast.ExApp (loc, MLast.ExLid (loc, "-"), e1), e2) :
               'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                (Grammar.s_token ("", "+")))
             Grammar.s_self,
           (fun (e2 : 'expr) _ (e1 : 'expr) (loc : Ploc.t) ->
              (MLast.ExApp
                 (loc, MLast.ExApp (loc, MLast.ExLid (loc, "+"), e1), e2) :
               'expr)))];
       Some "*", Some Gramext.LeftA,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                (Grammar.s_nterm (infixop3 : 'infixop3 Grammar.Entry.e)))
             Grammar.s_self,
           (fun (e2 : 'expr) (op : 'infixop3) (e1 : 'expr) (loc : Ploc.t) ->
              (MLast.ExApp
                 (loc, MLast.ExApp (loc, MLast.ExLid (loc, op), e1), e2) :
               'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                (Grammar.s_token ("", "mod")))
             Grammar.s_self,
           (fun (e2 : 'expr) _ (e1 : 'expr) (loc : Ploc.t) ->
              (MLast.ExApp
                 (loc, MLast.ExApp (loc, MLast.ExLid (loc, "mod"), e1), e2) :
               'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                (Grammar.s_token ("", "lxor")))
             Grammar.s_self,
           (fun (e2 : 'expr) _ (e1 : 'expr) (loc : Ploc.t) ->
              (MLast.ExApp
                 (loc, MLast.ExApp (loc, MLast.ExLid (loc, "lxor"), e1), e2) :
               'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                (Grammar.s_token ("", "lor")))
             Grammar.s_self,
           (fun (e2 : 'expr) _ (e1 : 'expr) (loc : Ploc.t) ->
              (MLast.ExApp
                 (loc, MLast.ExApp (loc, MLast.ExLid (loc, "lor"), e1), e2) :
               'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                (Grammar.s_token ("", "land")))
             Grammar.s_self,
           (fun (e2 : 'expr) _ (e1 : 'expr) (loc : Ploc.t) ->
              (MLast.ExApp
                 (loc, MLast.ExApp (loc, MLast.ExLid (loc, "land"), e1), e2) :
               'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                (Grammar.s_token ("", "/.")))
             Grammar.s_self,
           (fun (e2 : 'expr) _ (e1 : 'expr) (loc : Ploc.t) ->
              (MLast.ExApp
                 (loc, MLast.ExApp (loc, MLast.ExLid (loc, "/."), e1), e2) :
               'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                (Grammar.s_token ("", "*.")))
             Grammar.s_self,
           (fun (e2 : 'expr) _ (e1 : 'expr) (loc : Ploc.t) ->
              (MLast.ExApp
                 (loc, MLast.ExApp (loc, MLast.ExLid (loc, "*."), e1), e2) :
               'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                (Grammar.s_token ("", "/")))
             Grammar.s_self,
           (fun (e2 : 'expr) _ (e1 : 'expr) (loc : Ploc.t) ->
              (MLast.ExApp
                 (loc, MLast.ExApp (loc, MLast.ExLid (loc, "/"), e1), e2) :
               'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                (Grammar.s_token ("", "*")))
             Grammar.s_self,
           (fun (e2 : 'expr) _ (e1 : 'expr) (loc : Ploc.t) ->
              (MLast.ExApp
                 (loc, MLast.ExApp (loc, MLast.ExLid (loc, "*"), e1), e2) :
               'expr)))];
       Some "**", Some Gramext.RightA,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                (Grammar.s_nterm (infixop4 : 'infixop4 Grammar.Entry.e)))
             Grammar.s_self,
           (fun (e2 : 'expr) (op : 'infixop4) (e1 : 'expr) (loc : Ploc.t) ->
              (MLast.ExApp
                 (loc, MLast.ExApp (loc, MLast.ExLid (loc, op), e1), e2) :
               'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                (Grammar.s_token ("", "lsr")))
             Grammar.s_self,
           (fun (e2 : 'expr) _ (e1 : 'expr) (loc : Ploc.t) ->
              (MLast.ExApp
                 (loc, MLast.ExApp (loc, MLast.ExLid (loc, "lsr"), e1), e2) :
               'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                (Grammar.s_token ("", "lsl")))
             Grammar.s_self,
           (fun (e2 : 'expr) _ (e1 : 'expr) (loc : Ploc.t) ->
              (MLast.ExApp
                 (loc, MLast.ExApp (loc, MLast.ExLid (loc, "lsl"), e1), e2) :
               'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                (Grammar.s_token ("", "asr")))
             Grammar.s_self,
           (fun (e2 : 'expr) _ (e1 : 'expr) (loc : Ploc.t) ->
              (MLast.ExApp
                 (loc, MLast.ExApp (loc, MLast.ExLid (loc, "asr"), e1), e2) :
               'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                (Grammar.s_token ("", "**")))
             Grammar.s_self,
           (fun (e2 : 'expr) _ (e1 : 'expr) (loc : Ploc.t) ->
              (MLast.ExApp
                 (loc, MLast.ExApp (loc, MLast.ExLid (loc, "**"), e1), e2) :
               'expr)))];
       Some "unary minus", Some Gramext.NonA,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "+.")))
             Grammar.s_self,
           (fun (e : 'expr) _ (loc : Ploc.t) ->
              (match e with
                 MLast.ExFlo (_, _) -> e
               | _ -> MLast.ExApp (loc, MLast.ExLid (loc, "~+."), e) :
               'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "+")))
             Grammar.s_self,
           (fun (e : 'expr) _ (loc : Ploc.t) ->
              (match e with
                 MLast.ExInt (_, _, "") -> e
               | _ -> MLast.ExApp (loc, MLast.ExLid (loc, "~+"), e) :
               'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "-.")))
             Grammar.s_self,
           (fun (e : 'expr) _ (loc : Ploc.t) ->
              (MLast.ExApp (loc, MLast.ExLid (loc, "-."), e) : 'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "-")))
             Grammar.s_self,
           (fun (e : 'expr) _ (loc : Ploc.t) ->
              (MLast.ExApp (loc, MLast.ExLid (loc, "-"), e) : 'expr)))];
       Some "apply", Some Gramext.LeftA,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "lazy")))
                (Grammar.s_nterm
                   (ext_attributes : 'ext_attributes Grammar.Entry.e)))
             Grammar.s_self,
           (fun (e : 'expr) (ext, attrs : 'ext_attributes) _ (loc : Ploc.t) ->
              (expr_to_inline loc (MLast.ExLaz (loc, e)) ext attrs : 'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop
                   (Grammar.s_token ("", "assert")))
                (Grammar.s_nterm
                   (ext_attributes : 'ext_attributes Grammar.Entry.e)))
             Grammar.s_self,
           (fun (e : 'expr) (ext, attrs : 'ext_attributes) _ (loc : Ploc.t) ->
              (expr_to_inline loc (MLast.ExAsr (loc, e)) ext attrs : 'expr)));
        Grammar.production
          (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
             Grammar.s_self,
           (fun (e2 : 'expr) (e1 : 'expr) (loc : Ploc.t) ->
              (MLast.ExApp (loc, e1, e2) : 'expr)))];
       Some ".", Some Gramext.LeftA,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                (Grammar.s_token ("", ".")))
             Grammar.s_self,
           (fun (e2 : 'expr) _ (e1 : 'expr) (loc : Ploc.t) ->
              (MLast.ExAcc (loc, e1, e2) : 'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next Grammar.r_stop Grammar.s_self)
                      (Grammar.s_token ("", ".")))
                   (Grammar.s_token ("", "{")))
                (Grammar.s_list1sep
                   (Grammar.s_nterm (expr : 'expr Grammar.Entry.e))
                   (Grammar.s_token ("", ",")) false))
             (Grammar.s_token ("", "}")),
           (fun _ (el : 'expr list) _ _ (e : 'expr) (loc : Ploc.t) ->
              (MLast.ExBae (loc, e, el) : 'expr)));
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
              (MLast.ExSte (loc, e1, e2) : 'expr)));
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
              (MLast.ExAre (loc, e1, e2) : 'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                   (Grammar.s_token ("", ".")))
                (Grammar.s_token ("", "(")))
             (Grammar.s_nterm
                (operator_rparen : 'operator_rparen Grammar.Entry.e)),
           (fun (op : 'operator_rparen) _ _ (e1 : 'expr) (loc : Ploc.t) ->
              (MLast.ExAre (loc, e1, MLast.ExLid (loc, op)) : 'expr)))];
       Some "~-", Some Gramext.NonA,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop
                (Grammar.s_nterm (prefixop : 'prefixop Grammar.Entry.e)))
             Grammar.s_self,
           (fun (e : 'expr) (f : 'prefixop) (loc : Ploc.t) ->
              (MLast.ExApp (loc, MLast.ExLid (loc, f), e) : 'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "~-.")))
             Grammar.s_self,
           (fun (e : 'expr) _ (loc : Ploc.t) ->
              (MLast.ExApp (loc, MLast.ExLid (loc, "~-."), e) : 'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "~-")))
             Grammar.s_self,
           (fun (e : 'expr) _ (loc : Ploc.t) ->
              (MLast.ExApp (loc, MLast.ExLid (loc, "~-"), e) : 'expr)))];
       Some "simple", None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "(")))
                (Grammar.s_list1sep
                   (Grammar.s_nterm (expr : 'expr Grammar.Entry.e))
                   (Grammar.s_token ("", ",")) false))
             (Grammar.s_token ("", ")")),
           (fun _ (el : 'expr list) _ (loc : Ploc.t) ->
              (MLast.ExTup (loc, el) : 'expr)));
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
              (mktupexp loc e el : 'expr)));
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
              (MLast.ExTyc (loc, e, t) : 'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "(")))
             (Grammar.s_nterm
                (operator_rparen : 'operator_rparen Grammar.Entry.e)),
           (fun (op : 'operator_rparen) _ (loc : Ploc.t) ->
              (MLast.ExLid (loc, op) : 'expr)));
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
              (MLast.ExPck (loc, me, None) : 'expr)));
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
              (MLast.ExPck (loc, me, Some mt) : 'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "(")))
             (Grammar.s_token ("", ")")),
           (fun _ _ (loc : Ploc.t) -> (MLast.ExUid (loc, "()") : 'expr)));
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
                (Grammar.s_list1sep
                   (Grammar.s_nterm
                      (label_expr : 'label_expr Grammar.Entry.e))
                   (Grammar.s_token ("", ";")) false))
             (Grammar.s_token ("", "}")),
           (fun _ (lel : 'label_expr list) _ _ (e : 'expr) _ _
                (loc : Ploc.t) ->
              (MLast.ExRec (loc, lel, Some e) : 'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "{")))
                (Grammar.s_list1sep
                   (Grammar.s_nterm
                      (label_expr : 'label_expr Grammar.Entry.e))
                   (Grammar.s_token ("", ";")) false))
             (Grammar.s_token ("", "}")),
           (fun _ (lel : 'label_expr list) _ (loc : Ploc.t) ->
              (MLast.ExRec (loc, lel, None) : 'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "[|")))
                (Grammar.s_list0sep
                   (Grammar.s_nterm (expr : 'expr Grammar.Entry.e))
                   (Grammar.s_token ("", ";")) false))
             (Grammar.s_token ("", "|]")),
           (fun _ (el : 'expr list) _ (loc : Ploc.t) ->
              (MLast.ExArr (loc, el) : 'expr)));
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
              (mklistexp loc last el : 'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "[")))
             (Grammar.s_token ("", "]")),
           (fun _ _ (loc : Ploc.t) -> (MLast.ExUid (loc, "[]") : 'expr)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop (Grammar.s_token ("UIDENT", "")),
           (fun (i : string) (loc : Ploc.t) ->
              (MLast.ExUid (loc, i) : 'expr)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop (Grammar.s_token ("GIDENT", "")),
           (fun (i : string) (loc : Ploc.t) ->
              (MLast.ExLid (loc, i) : 'expr)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop (Grammar.s_token ("LIDENT", "")),
           (fun (i : string) (loc : Ploc.t) ->
              (MLast.ExLid (loc, i) : 'expr)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_nterm
                (alg_extension : 'alg_extension Grammar.Entry.e)),
           (fun (e : 'alg_extension) (loc : Ploc.t) ->
              (MLast.ExExten (loc, e) : 'expr)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", ".")),
           (fun _ (loc : Ploc.t) -> (MLast.ExUnr loc : 'expr)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop (Grammar.s_token ("CHAR", "")),
           (fun (s : string) (loc : Ploc.t) ->
              (MLast.ExChr (loc, s) : 'expr)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop (Grammar.s_token ("STRING", "")),
           (fun (s : string) (loc : Ploc.t) ->
              (MLast.ExStr (loc, s) : 'expr)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop (Grammar.s_token ("FLOAT", "")),
           (fun (s : string) (loc : Ploc.t) ->
              (MLast.ExFlo (loc, s) : 'expr)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop (Grammar.s_token ("INT_n", "")),
           (fun (s : string) (loc : Ploc.t) ->
              (MLast.ExInt (loc, s, "n") : 'expr)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop (Grammar.s_token ("INT_L", "")),
           (fun (s : string) (loc : Ploc.t) ->
              (MLast.ExInt (loc, s, "L") : 'expr)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop (Grammar.s_token ("INT_l", "")),
           (fun (s : string) (loc : Ploc.t) ->
              (MLast.ExInt (loc, s, "l") : 'expr)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop (Grammar.s_token ("INT", "")),
           (fun (s : string) (loc : Ploc.t) ->
              (MLast.ExInt (loc, s, "") : 'expr)))]];
    Grammar.extension (closed_case_list : 'closed_case_list Grammar.Entry.e)
      None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "|")))
                (Grammar.s_list0sep
                   (Grammar.s_nterm
                      (match_case : 'match_case Grammar.Entry.e))
                   (Grammar.s_token ("", "|")) false))
             (Grammar.s_token ("", "end")),
           (fun _ (l : 'match_case list) _ (loc : Ploc.t) ->
              (l : 'closed_case_list)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "[")))
                (Grammar.s_list0sep
                   (Grammar.s_nterm
                      (match_case : 'match_case Grammar.Entry.e))
                   (Grammar.s_token ("", "|")) false))
             (Grammar.s_token ("", "]")),
           (fun _ (l : 'match_case list) _ (loc : Ploc.t) ->
              (l : 'closed_case_list)))]];
    Grammar.extension (cons_expr_opt : 'cons_expr_opt Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_stop, (fun (loc : Ploc.t) -> (None : 'cons_expr_opt)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "::")))
             (Grammar.s_nterm (expr : 'expr Grammar.Entry.e)),
           (fun (e : 'expr) _ (loc : Ploc.t) -> (Some e : 'cons_expr_opt)))]];
    Grammar.extension (dummy : 'dummy Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_stop, (fun (loc : Ploc.t) -> (() : 'dummy)))]];
    Grammar.extension (sequence : 'sequence Grammar.Entry.e) None
      [None, Some Gramext.RightA,
       [Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_nterm (expr : 'expr Grammar.Entry.e)),
           (fun (e : 'expr) (loc : Ploc.t) -> ([e] : 'sequence)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop
                (Grammar.s_nterm (expr : 'expr Grammar.Entry.e)))
             (Grammar.s_token ("", ";")),
           (fun _ (e : 'expr) (loc : Ploc.t) -> ([e] : 'sequence)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop
                   (Grammar.s_nterm (expr : 'expr Grammar.Entry.e)))
                (Grammar.s_token ("", ";")))
             Grammar.s_self,
           (fun (el : 'sequence) _ (e : 'expr) (loc : Ploc.t) ->
              (e :: el : 'sequence)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("", "let")))
                         (Grammar.s_token ("", "open")))
                      (Grammar.s_nterm
                         (ext_attributes : 'ext_attributes Grammar.Entry.e)))
                   (Grammar.s_nterm
                      (module_expr : 'module_expr Grammar.Entry.e)))
                (Grammar.s_token ("", "in")))
             Grammar.s_self,
           (fun (el : 'sequence) _ (m : 'module_expr)
                (ext, attrs : 'ext_attributes) _ _ (loc : Ploc.t) ->
              ([expr_to_inline loc (MLast.ExLop (loc, m, mksequence loc el))
                  ext attrs] :
               'sequence)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next
                         (Grammar.r_next
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("", "let")))
                            (Grammar.s_token ("", "module")))
                         (Grammar.s_nterm
                            (ext_attributes :
                             'ext_attributes Grammar.Entry.e)))
                      (Grammar.s_nterm (uidopt : 'uidopt Grammar.Entry.e)))
                   (Grammar.s_nterm
                      (mod_fun_binding : 'mod_fun_binding Grammar.Entry.e)))
                (Grammar.s_token ("", "in")))
             Grammar.s_self,
           (fun (el : 'sequence) _ (mb : 'mod_fun_binding) (m : 'uidopt)
                (ext, attrs : 'ext_attributes) _ _ (loc : Ploc.t) ->
              ([expr_to_inline loc
                  (MLast.ExLmd (loc, m, mb, mksequence loc el)) ext attrs] :
               'sequence)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("", "let")))
                      (Grammar.s_flag (Grammar.s_token ("", "rec"))))
                   (Grammar.s_list1sep
                      (Grammar.s_nterm
                         (let_binding : 'let_binding Grammar.Entry.e))
                      (Grammar.s_token ("", "and")) false))
                (Grammar.s_token ("", "in")))
             Grammar.s_self,
           (fun (el : 'sequence) _ (l : 'let_binding list) (rf : bool) _
                (loc : Ploc.t) ->
              ([MLast.ExLet (loc, rf, l, mksequence loc el)] : 'sequence)))]];
    Grammar.extension (let_binding : 'let_binding Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop
                   (Grammar.s_nterm (ipatt : 'ipatt Grammar.Entry.e)))
                (Grammar.s_nterm
                   (fun_binding : 'fun_binding Grammar.Entry.e)))
             (Grammar.s_nterm
                (item_attributes : 'item_attributes Grammar.Entry.e)),
           (fun (attrs : 'item_attributes) (e : 'fun_binding) (p : 'ipatt)
                (loc : Ploc.t) ->
              (p, e, attrs : 'let_binding)))]];
    Grammar.extension (letop_binding : 'letop_binding Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop
                (Grammar.s_nterm (ipatt : 'ipatt Grammar.Entry.e)))
             (Grammar.s_nterm (fun_binding : 'fun_binding Grammar.Entry.e)),
           (fun (e : 'fun_binding) (p : 'ipatt) (loc : Ploc.t) ->
              (p, e : 'letop_binding)))]];
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
              (MLast.ExTyc (loc, e, t) : 'fun_binding)));
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
              (MLast.ExFun (loc, [p, None, e]) : 'fun_binding)))]];
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
                   (Grammar.s_opt
                      (Grammar.s_nterm
                         (when_expr : 'when_expr Grammar.Entry.e))))
                (Grammar.s_token ("", "->")))
             (Grammar.s_nterm (expr : 'expr Grammar.Entry.e)),
           (fun (e : 'expr) _ (w : 'when_expr option) (aso : 'as_patt_opt)
                (p : 'patt) (loc : Ploc.t) ->
              (mkmatchcase loc p aso w e : 'match_case)))]];
    Grammar.extension (as_patt_opt : 'as_patt_opt Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_stop, (fun (loc : Ploc.t) -> (None : 'as_patt_opt)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "as")))
             (Grammar.s_nterm (patt : 'patt Grammar.Entry.e)),
           (fun (p : 'patt) _ (loc : Ploc.t) -> (Some p : 'as_patt_opt)))]];
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
              (i, e : 'label_expr)))]];
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
              (MLast.ExFun (loc, [p, None, e]) : 'fun_def)))]];
    Grammar.extension (patt : 'patt Grammar.Entry.e) None
      [None, Some Gramext.LeftA,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                (Grammar.s_token ("", "|")))
             Grammar.s_self,
           (fun (p2 : 'patt) _ (p1 : 'patt) (loc : Ploc.t) ->
              (MLast.PaOrp (loc, p1, p2) : 'patt)))];
       Some "alg_attribute", Some Gramext.LeftA,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                   (Grammar.s_token ("", "[@")))
                (Grammar.s_nterm
                   (attribute_body : 'attribute_body Grammar.Entry.e)))
             (Grammar.s_token ("", "]")),
           (fun _ (attr : 'attribute_body) _ (p : 'patt) (loc : Ploc.t) ->
              (MLast.PaAtt (loc, p, attr) : 'patt)))];
       None, Some Gramext.NonA,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop
                   (Grammar.s_token ("", "exception")))
                (Grammar.s_nterm
                   (ext_attributes : 'ext_attributes Grammar.Entry.e)))
             Grammar.s_self,
           (fun (p : 'patt) (ext, attrs : 'ext_attributes) _ (loc : Ploc.t) ->
              (patt_to_inline loc (MLast.PaExc (loc, p)) ext attrs :
               'patt)))];
       None, Some Gramext.NonA,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                (Grammar.s_token ("", "..")))
             Grammar.s_self,
           (fun (p2 : 'patt) _ (p1 : 'patt) (loc : Ploc.t) ->
              (MLast.PaRng (loc, p1, p2) : 'patt)))];
       None, Some Gramext.LeftA,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "lazy")))
                (Grammar.s_nterm
                   (ext_attributes : 'ext_attributes Grammar.Entry.e)))
             Grammar.s_self,
           (fun (p : 'patt) (ext, attrs : 'ext_attributes) _ (loc : Ploc.t) ->
              (patt_to_inline loc (MLast.PaLaz (loc, p)) ext attrs : 'patt)));
        Grammar.production
          (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
             Grammar.s_self,
           (fun (p2 : 'patt) (p1 : 'patt) (loc : Ploc.t) ->
              (MLast.PaApp (loc, p1, p2) : 'patt)))];
       None, Some Gramext.LeftA,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                (Grammar.s_token ("", ".")))
             Grammar.s_self,
           (fun (p2 : 'patt) _ (p1 : 'patt) (loc : Ploc.t) ->
              (MLast.PaAcc (loc, p1, p2) : 'patt)))];
       Some "simple", None,
       [Grammar.production
          (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "_")),
           (fun _ (loc : Ploc.t) -> (MLast.PaAny loc : 'patt)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "(")))
                (Grammar.s_nterm (paren_patt : 'paren_patt Grammar.Entry.e)))
             (Grammar.s_token ("", ")")),
           (fun _ (p : 'paren_patt) _ (loc : Ploc.t) -> (p : 'patt)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "(")))
             (Grammar.s_nterm
                (operator_rparen : 'operator_rparen Grammar.Entry.e)),
           (fun (op : 'operator_rparen) _ (loc : Ploc.t) ->
              (MLast.PaLid (loc, op) : 'patt)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "{")))
                (Grammar.s_list1sep
                   (Grammar.s_nterm
                      (label_patt : 'label_patt Grammar.Entry.e))
                   (Grammar.s_token ("", ";")) false))
             (Grammar.s_token ("", "}")),
           (fun _ (lpl : 'label_patt list) _ (loc : Ploc.t) ->
              (MLast.PaRec (loc, lpl) : 'patt)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "[|")))
                (Grammar.s_list0sep
                   (Grammar.s_nterm (patt : 'patt Grammar.Entry.e))
                   (Grammar.s_token ("", ";")) false))
             (Grammar.s_token ("", "|]")),
           (fun _ (pl : 'patt list) _ (loc : Ploc.t) ->
              (MLast.PaArr (loc, pl) : 'patt)));
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
              (mklistpat loc last pl : 'patt)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "[")))
             (Grammar.s_token ("", "]")),
           (fun _ _ (loc : Ploc.t) -> (MLast.PaUid (loc, "[]") : 'patt)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "-")))
             (Grammar.s_token ("FLOAT", "")),
           (fun (s : string) _ (loc : Ploc.t) ->
              (MLast.PaFlo (loc, neg_string s) : 'patt)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "-")))
             (Grammar.s_token ("INT_n", "")),
           (fun (s : string) _ (loc : Ploc.t) ->
              (MLast.PaInt (loc, neg_string s, "n") : 'patt)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "-")))
             (Grammar.s_token ("INT_L", "")),
           (fun (s : string) _ (loc : Ploc.t) ->
              (MLast.PaInt (loc, neg_string s, "L") : 'patt)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "-")))
             (Grammar.s_token ("INT_l", "")),
           (fun (s : string) _ (loc : Ploc.t) ->
              (MLast.PaInt (loc, neg_string s, "l") : 'patt)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "-")))
             (Grammar.s_token ("INT", "")),
           (fun (s : string) _ (loc : Ploc.t) ->
              (MLast.PaInt (loc, neg_string s, "") : 'patt)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "+")))
             (Grammar.s_token ("FLOAT", "")),
           (fun (s : string) _ (loc : Ploc.t) ->
              (MLast.PaFlo (loc, s) : 'patt)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "+")))
             (Grammar.s_token ("INT", "")),
           (fun (s : string) _ (loc : Ploc.t) ->
              (MLast.PaInt (loc, s, "") : 'patt)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop (Grammar.s_token ("CHAR", "")),
           (fun (s : string) (loc : Ploc.t) ->
              (MLast.PaChr (loc, s) : 'patt)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop (Grammar.s_token ("STRING", "")),
           (fun (s : string) (loc : Ploc.t) ->
              (MLast.PaStr (loc, s) : 'patt)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop (Grammar.s_token ("FLOAT", "")),
           (fun (s : string) (loc : Ploc.t) ->
              (MLast.PaFlo (loc, s) : 'patt)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop (Grammar.s_token ("INT_n", "")),
           (fun (s : string) (loc : Ploc.t) ->
              (MLast.PaInt (loc, s, "n") : 'patt)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop (Grammar.s_token ("INT_L", "")),
           (fun (s : string) (loc : Ploc.t) ->
              (MLast.PaInt (loc, s, "L") : 'patt)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop (Grammar.s_token ("INT_l", "")),
           (fun (s : string) (loc : Ploc.t) ->
              (MLast.PaInt (loc, s, "l") : 'patt)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop (Grammar.s_token ("INT", "")),
           (fun (s : string) (loc : Ploc.t) ->
              (MLast.PaInt (loc, s, "") : 'patt)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_nterm
                (alg_extension : 'alg_extension Grammar.Entry.e)),
           (fun (e : 'alg_extension) (loc : Ploc.t) ->
              (MLast.PaExten (loc, e) : 'patt)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop (Grammar.s_token ("UIDENT", "")),
           (fun (s : string) (loc : Ploc.t) ->
              (MLast.PaUid (loc, s) : 'patt)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop (Grammar.s_token ("GIDENT", "")),
           (fun (s : string) (loc : Ploc.t) ->
              (MLast.PaLid (loc, s) : 'patt)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop (Grammar.s_token ("LIDENT", "")),
           (fun (s : string) (loc : Ploc.t) ->
              (MLast.PaLid (loc, s) : 'patt)))]];
    Grammar.extension (paren_patt : 'paren_patt Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_stop,
           (fun (loc : Ploc.t) -> (MLast.PaUid (loc, "()") : 'paren_patt)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "module")))
             (Grammar.s_nterm (uidopt : 'uidopt Grammar.Entry.e)),
           (fun (s : 'uidopt) _ (loc : Ploc.t) ->
              (MLast.PaUnp (loc, s, None) : 'paren_patt)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next Grammar.r_stop
                      (Grammar.s_token ("", "module")))
                   (Grammar.s_nterm (uidopt : 'uidopt Grammar.Entry.e)))
                (Grammar.s_token ("", ":")))
             (Grammar.s_nterm (module_type : 'module_type Grammar.Entry.e)),
           (fun (mt : 'module_type) _ (s : 'uidopt) _ (loc : Ploc.t) ->
              (MLast.PaUnp (loc, s, Some mt) : 'paren_patt)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "type")))
             (Grammar.s_token ("LIDENT", "")),
           (fun (s : string) _ (loc : Ploc.t) ->
              (MLast.PaNty (loc, s) : 'paren_patt)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_list1sep
                (Grammar.s_nterm (patt : 'patt Grammar.Entry.e))
                (Grammar.s_token ("", ",")) false),
           (fun (pl : 'patt list) (loc : Ploc.t) ->
              (MLast.PaTup (loc, pl) : 'paren_patt)));
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
              (mktuppat loc p pl : 'paren_patt)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop
                   (Grammar.s_nterm (patt : 'patt Grammar.Entry.e)))
                (Grammar.s_token ("", "as")))
             (Grammar.s_nterm (patt : 'patt Grammar.Entry.e)),
           (fun (p2 : 'patt) _ (p : 'patt) (loc : Ploc.t) ->
              (MLast.PaAli (loc, p, p2) : 'paren_patt)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop
                   (Grammar.s_nterm (patt : 'patt Grammar.Entry.e)))
                (Grammar.s_token ("", ":")))
             (Grammar.s_nterm (ctyp : 'ctyp Grammar.Entry.e)),
           (fun (t : 'ctyp) _ (p : 'patt) (loc : Ploc.t) ->
              (MLast.PaTyc (loc, p, t) : 'paren_patt)))]];
    Grammar.extension (cons_patt_opt : 'cons_patt_opt Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_stop, (fun (loc : Ploc.t) -> (None : 'cons_patt_opt)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "::")))
             (Grammar.s_nterm (patt : 'patt Grammar.Entry.e)),
           (fun (p : 'patt) _ (loc : Ploc.t) -> (Some p : 'cons_patt_opt)))]];
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
              (i, p : 'label_patt)))]];
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
              (MLast.PaAcc (loc, p1, p2) : 'patt_label_ident)))];
       Some "simple", Some Gramext.RightA,
       [Grammar.production
          (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "_")),
           (fun _ (loc : Ploc.t) -> (MLast.PaAny loc : 'patt_label_ident)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop (Grammar.s_token ("LIDENT", "")),
           (fun (i : string) (loc : Ploc.t) ->
              (MLast.PaLid (loc, i) : 'patt_label_ident)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop (Grammar.s_token ("UIDENT", "")),
           (fun (i : string) (loc : Ploc.t) ->
              (MLast.PaUid (loc, i) : 'patt_label_ident)))]];
    Grammar.extension (ipatt : 'ipatt Grammar.Entry.e) None
      [Some "top", Some Gramext.LeftA,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                   (Grammar.s_token ("", "[@")))
                (Grammar.s_nterm
                   (attribute_body : 'attribute_body Grammar.Entry.e)))
             (Grammar.s_token ("", "]")),
           (fun _ (attr : 'attribute_body) _ (e1 : 'ipatt) (loc : Ploc.t) ->
              (MLast.PaAtt (loc, e1, attr) : 'ipatt)))];
       Some "simple", None,
       [Grammar.production
          (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "_")),
           (fun _ (loc : Ploc.t) -> (MLast.PaAny loc : 'ipatt)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop (Grammar.s_token ("GIDENT", "")),
           (fun (s : string) (loc : Ploc.t) ->
              (MLast.PaLid (loc, s) : 'ipatt)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop (Grammar.s_token ("LIDENT", "")),
           (fun (s : string) (loc : Ploc.t) ->
              (MLast.PaLid (loc, s) : 'ipatt)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_nterm
                (alg_extension : 'alg_extension Grammar.Entry.e)),
           (fun (e : 'alg_extension) (loc : Ploc.t) ->
              (MLast.PaExten (loc, e) : 'ipatt)));
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
                (Grammar.s_list1sep
                   (Grammar.s_nterm
                      (label_ipatt : 'label_ipatt Grammar.Entry.e))
                   (Grammar.s_token ("", ";")) false))
             (Grammar.s_token ("", "}")),
           (fun _ (lpl : 'label_ipatt list) _ (loc : Ploc.t) ->
              (MLast.PaRec (loc, lpl) : 'ipatt)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "(")))
             (Grammar.s_nterm
                (operator_rparen : 'operator_rparen Grammar.Entry.e)),
           (fun (op : 'operator_rparen) _ (loc : Ploc.t) ->
              (MLast.PaLid (loc, op) : 'ipatt)))]];
    Grammar.extension (paren_ipatt : 'paren_ipatt Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_stop,
           (fun (loc : Ploc.t) -> (MLast.PaUid (loc, "()") : 'paren_ipatt)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "module")))
             (Grammar.s_nterm (uidopt : 'uidopt Grammar.Entry.e)),
           (fun (s : 'uidopt) _ (loc : Ploc.t) ->
              (MLast.PaUnp (loc, s, None) : 'paren_ipatt)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next Grammar.r_stop
                      (Grammar.s_token ("", "module")))
                   (Grammar.s_nterm (uidopt : 'uidopt Grammar.Entry.e)))
                (Grammar.s_token ("", ":")))
             (Grammar.s_nterm (module_type : 'module_type Grammar.Entry.e)),
           (fun (mt : 'module_type) _ (s : 'uidopt) _ (loc : Ploc.t) ->
              (MLast.PaUnp (loc, s, Some mt) : 'paren_ipatt)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "type")))
             (Grammar.s_token ("LIDENT", "")),
           (fun (s : string) _ (loc : Ploc.t) ->
              (MLast.PaNty (loc, s) : 'paren_ipatt)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_list1sep
                (Grammar.s_nterm (ipatt : 'ipatt Grammar.Entry.e))
                (Grammar.s_token ("", ",")) false),
           (fun (pl : 'ipatt list) (loc : Ploc.t) ->
              (MLast.PaTup (loc, pl) : 'paren_ipatt)));
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
              (mktuppat loc p pl : 'paren_ipatt)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop
                   (Grammar.s_nterm (ipatt : 'ipatt Grammar.Entry.e)))
                (Grammar.s_token ("", "as")))
             (Grammar.s_nterm (ipatt : 'ipatt Grammar.Entry.e)),
           (fun (p2 : 'ipatt) _ (p : 'ipatt) (loc : Ploc.t) ->
              (MLast.PaAli (loc, p, p2) : 'paren_ipatt)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop
                   (Grammar.s_nterm (ipatt : 'ipatt Grammar.Entry.e)))
                (Grammar.s_token ("", ":")))
             (Grammar.s_nterm (ctyp : 'ctyp Grammar.Entry.e)),
           (fun (t : 'ctyp) _ (p : 'ipatt) (loc : Ploc.t) ->
              (MLast.PaTyc (loc, p, t) : 'paren_ipatt)))]];
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
              (i, p : 'label_ipatt)))]];
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
                               (Grammar.s_nterm
                                  (type_patt : 'type_patt Grammar.Entry.e)))
                            (Grammar.s_list0
                               (Grammar.s_nterm
                                  (type_parameter :
                                   'type_parameter Grammar.Entry.e))))
                         (Grammar.s_token ("", "=")))
                      (Grammar.s_flag (Grammar.s_token ("", "private"))))
                   (Grammar.s_nterm (ctyp : 'ctyp Grammar.Entry.e)))
                (Grammar.s_list0
                   (Grammar.s_nterm
                      (constrain : 'constrain Grammar.Entry.e))))
             (Grammar.s_nterm
                (item_attributes : 'item_attributes Grammar.Entry.e)),
           (fun (attrs : 'item_attributes) (cl : 'constrain list) (tk : 'ctyp)
                (pf : bool) _ (tpl : 'type_parameter list) (n : 'type_patt)
                (loc : Ploc.t) ->
              ({MLast.tdNam = n; MLast.tdPrm = tpl; MLast.tdPrv = pf;
                MLast.tdDef = tk; MLast.tdCon = cl;
                MLast.tdAttributes = attrs} :
               'type_decl)))]];
    (* TODO FIX: this should be a longident+lid, to match ocaml's grammar *)
    Grammar.extension (type_extension : 'type_extension Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next
                         (Grammar.r_next
                            (Grammar.r_next
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_nterm
                                     (mod_ident_patt :
                                      'mod_ident_patt Grammar.Entry.e)))
                               (Grammar.s_list0
                                  (Grammar.s_nterm
                                     (type_parameter :
                                      'type_parameter Grammar.Entry.e))))
                            (Grammar.s_token ("", "+=")))
                         (Grammar.s_flag (Grammar.s_token ("", "private"))))
                      (Grammar.s_token ("", "[")))
                   (Grammar.s_list1sep
                      (Grammar.s_nterm
                         (extension_constructor :
                          'extension_constructor Grammar.Entry.e))
                      (Grammar.s_token ("", "|")) false))
                (Grammar.s_token ("", "]")))
             (Grammar.s_nterm
                (item_attributes : 'item_attributes Grammar.Entry.e)),
           (fun (attrs : 'item_attributes) _
                (ecs : 'extension_constructor list) _ (pf : bool) _
                (tpl : 'type_parameter list) (n : 'mod_ident_patt)
                (loc : Ploc.t) ->
              ({MLast.teNam = n; tePrm = tpl; tePrv = pf;
                teAttributes = attrs; teECs = ecs} :
               'type_extension)))]];
    Grammar.extension (mod_ident_patt : 'mod_ident_patt Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_nterm (mod_ident : 'mod_ident Grammar.Entry.e)),
           (fun (n : 'mod_ident) (loc : Ploc.t) ->
              (loc, n : 'mod_ident_patt)))]];
    Grammar.extension (type_patt : 'type_patt Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next Grammar.r_stop (Grammar.s_token ("LIDENT", "")),
           (fun (n : string) (loc : Ploc.t) -> (loc, n : 'type_patt)))]];
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
              (t1, t2 : 'constrain)))]];
    Grammar.extension (type_parameter : 'type_parameter Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_nterm
                (simple_type_parameter :
                 'simple_type_parameter Grammar.Entry.e)),
           (fun (p : 'simple_type_parameter) (loc : Ploc.t) ->
              (p, None : 'type_parameter)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "-")))
             (Grammar.s_nterm
                (simple_type_parameter :
                 'simple_type_parameter Grammar.Entry.e)),
           (fun (p : 'simple_type_parameter) _ (loc : Ploc.t) ->
              (p, Some false : 'type_parameter)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "+")))
             (Grammar.s_nterm
                (simple_type_parameter :
                 'simple_type_parameter Grammar.Entry.e)),
           (fun (p : 'simple_type_parameter) _ (loc : Ploc.t) ->
              (p, Some true : 'type_parameter)))]];
    Grammar.extension
      (simple_type_parameter : 'simple_type_parameter Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "_")),
           (fun _ (loc : Ploc.t) -> (None : 'simple_type_parameter)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop (Grammar.s_token ("GIDENT", "")),
           (fun (i : string) (loc : Ploc.t) ->
              (Some (greek_ascii_equiv i) : 'simple_type_parameter)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "'")))
             (Grammar.s_nterm (ident : 'ident Grammar.Entry.e)),
           (fun (i : 'ident) _ (loc : Ploc.t) ->
              (Some i : 'simple_type_parameter)))]];
    Grammar.extension
      (extended_longident : 'extended_longident Grammar.Entry.e) None
      [None, Some Gramext.LeftA,
       [Grammar.production
          (Grammar.r_next Grammar.r_stop (Grammar.s_token ("UIDENT", "")),
           (fun (i : string) (loc : Ploc.t) ->
              (MLast.LiUid (loc, i) : 'extended_longident)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                   (Grammar.s_nterm
                      (check_dot_uid : 'check_dot_uid Grammar.Entry.e)))
                (Grammar.s_token ("", ".")))
             (Grammar.s_token ("UIDENT", "")),
           (fun (i : string) _ _ (me1 : 'extended_longident) (loc : Ploc.t) ->
              (MLast.LiAcc (loc, me1, i) : 'extended_longident)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                   (Grammar.s_token ("", "(")))
                Grammar.s_self)
             (Grammar.s_token ("", ")")),
           (fun _ (me2 : 'extended_longident) _ (me1 : 'extended_longident)
                (loc : Ploc.t) ->
              (MLast.LiApp (loc, me1, me2) : 'extended_longident)))]];
    Grammar.extension (ctyp_ident : 'ctyp_ident Grammar.Entry.e) None
      [None, Some Gramext.LeftA,
       [Grammar.production
          (Grammar.r_next Grammar.r_stop (Grammar.s_token ("LIDENT", "")),
           (fun (i : string) (loc : Ploc.t) ->
              (MLast.TyLid (loc, i) : 'ctyp_ident)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop
                   (Grammar.s_nterm
                      (extended_longident :
                       'extended_longident Grammar.Entry.e)))
                (Grammar.s_token ("", ".")))
             (Grammar.s_token ("LIDENT", "")),
           (fun (i : string) _ (me1 : 'extended_longident) (loc : Ploc.t) ->
              (MLast.TyAcc (loc, me1, i) : 'ctyp_ident)))]];
    Grammar.extension (ctyp : 'ctyp Grammar.Entry.e) None
      [Some "top", Some Gramext.LeftA,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                   (Grammar.s_token ("", "==")))
                (Grammar.s_flag (Grammar.s_token ("", "private"))))
             Grammar.s_self,
           (fun (t2 : 'ctyp) (pf : bool) _ (t1 : 'ctyp) (loc : Ploc.t) ->
              (MLast.TyMan (loc, t1, pf, t2) : 'ctyp)))];
       Some "alg_attribute", Some Gramext.LeftA,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                   (Grammar.s_token ("", "[@")))
                (Grammar.s_nterm
                   (attribute_body : 'attribute_body Grammar.Entry.e)))
             (Grammar.s_token ("", "]")),
           (fun _ (attr : 'attribute_body) _ (e1 : 'ctyp) (loc : Ploc.t) ->
              (MLast.TyAtt (loc, e1, attr) : 'ctyp)))];
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
              (MLast.TyAli (loc, t1, t2) : 'ctyp)))];
       None, Some Gramext.LeftA,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next Grammar.r_stop
                      (Grammar.s_token ("", "type")))
                   (Grammar.s_list1 (Grammar.s_token ("LIDENT", ""))))
                (Grammar.s_token ("", ".")))
             Grammar.s_self,
           (fun (t : 'ctyp) _ (pl : string list) _ (loc : Ploc.t) ->
              (MLast.TyPot (loc, pl, t) : 'ctyp)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "!")))
                   (Grammar.s_list1
                      (Grammar.s_nterm (typevar : 'typevar Grammar.Entry.e))))
                (Grammar.s_token ("", ".")))
             Grammar.s_self,
           (fun (t : 'ctyp) _ (pl : 'typevar list) _ (loc : Ploc.t) ->
              (MLast.TyPol (loc, pl, t) : 'ctyp)))];
       Some "arrow", Some Gramext.RightA,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                (Grammar.s_token ("", "->")))
             Grammar.s_self,
           (fun (t2 : 'ctyp) _ (t1 : 'ctyp) (loc : Ploc.t) ->
              (MLast.TyArr (loc, t1, t2) : 'ctyp)))];
       Some "apply", Some Gramext.LeftA,
       [Grammar.production
          (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
             Grammar.s_self,
           (fun (t2 : 'ctyp) (t1 : 'ctyp) (loc : Ploc.t) ->
              (MLast.TyApp (loc, t1, t2) : 'ctyp)))];
       None, Some Gramext.LeftA,
       [Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_nterm (ctyp_ident : 'ctyp_ident Grammar.Entry.e)),
           (fun (t : 'ctyp_ident) (loc : Ploc.t) -> (t : 'ctyp)))];
       Some "simple", None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "{")))
                (Grammar.s_list1sep
                   (Grammar.s_nterm
                      (label_declaration :
                       'label_declaration Grammar.Entry.e))
                   (Grammar.s_token ("", ";")) false))
             (Grammar.s_token ("", "}")),
           (fun _ (ldl : 'label_declaration list) _ (loc : Ploc.t) ->
              (MLast.TyRec (loc, ldl) : 'ctyp)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "[")))
                (Grammar.s_list0sep
                   (Grammar.s_nterm
                      (constructor_declaration :
                       'constructor_declaration Grammar.Entry.e))
                   (Grammar.s_token ("", "|")) false))
             (Grammar.s_token ("", "]")),
           (fun _ (cdl : 'constructor_declaration list) _ (loc : Ploc.t) ->
              (MLast.TySum (loc, cdl) : 'ctyp)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "(")))
                (Grammar.s_list1sep
                   (Grammar.s_nterm (ctyp : 'ctyp Grammar.Entry.e))
                   (Grammar.s_token ("", "*")) false))
             (Grammar.s_token ("", ")")),
           (fun _ (tl : 'ctyp list) _ (loc : Ploc.t) ->
              (MLast.TyTup (loc, tl) : 'ctyp)));
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
              (mktuptyp loc t tl : 'ctyp)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "module")))
             (Grammar.s_nterm (module_type : 'module_type Grammar.Entry.e)),
           (fun (mt : 'module_type) _ (loc : Ploc.t) ->
              (MLast.TyPck (loc, mt) : 'ctyp)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_nterm
                (alg_extension : 'alg_extension Grammar.Entry.e)),
           (fun (e : 'alg_extension) (loc : Ploc.t) ->
              (MLast.TyExten (loc, e) : 'ctyp)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "_")),
           (fun _ (loc : Ploc.t) -> (MLast.TyAny loc : 'ctyp)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "..")),
           (fun _ (loc : Ploc.t) -> (MLast.TyOpn loc : 'ctyp)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop (Grammar.s_token ("GIDENT", "")),
           (fun (i : string) (loc : Ploc.t) ->
              (MLast.TyQuo (loc, greek_ascii_equiv i) : 'ctyp)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "'")))
             (Grammar.s_nterm (ident : 'ident Grammar.Entry.e)),
           (fun (i : 'ident) _ (loc : Ploc.t) ->
              (MLast.TyQuo (loc, i) : 'ctyp)))]];
    Grammar.extension
      (ctyp_below_alg_attribute : 'ctyp_below_alg_attribute Grammar.Entry.e)
      None
      [None, None,
       [Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_nterml (ctyp : 'ctyp Grammar.Entry.e)
                "below_alg_attribute"),
           (fun (x : 'ctyp) (loc : Ploc.t) ->
              (x : 'ctyp_below_alg_attribute)))]];
    Grammar.extension (cons_ident : 'cons_ident Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "(")))
                (Grammar.s_token ("", "::")))
             (Grammar.s_token ("", ")")),
           (fun _ _ _ (loc : Ploc.t) -> ("::" : 'cons_ident)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "(")))
             (Grammar.s_token ("", ")")),
           (fun _ _ (loc : Ploc.t) -> ("()" : 'cons_ident)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "[")))
             (Grammar.s_token ("", "]")),
           (fun _ _ (loc : Ploc.t) -> ("[]" : 'cons_ident)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop (Grammar.s_token ("UIDENT", "")),
           (fun (ci : string) (loc : Ploc.t) -> (ci : 'cons_ident)))]];
    Grammar.extension
      (constructor_declaration : 'constructor_declaration Grammar.Entry.e)
      None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop
                (Grammar.s_nterm (cons_ident : 'cons_ident Grammar.Entry.e)))
             (Grammar.s_nterm
                (alg_attributes : 'alg_attributes Grammar.Entry.e)),
           (fun (attrs : 'alg_attributes) (ci : 'cons_ident) (loc : Ploc.t) ->
              (loc, ci, [], None, attrs : 'constructor_declaration)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next Grammar.r_stop
                      (Grammar.s_nterm
                         (cons_ident : 'cons_ident Grammar.Entry.e)))
                   (Grammar.s_token ("", ":")))
                (Grammar.s_nterm
                   (ctyp_below_alg_attribute :
                    'ctyp_below_alg_attribute Grammar.Entry.e)))
             (Grammar.s_nterm
                (alg_attributes : 'alg_attributes Grammar.Entry.e)),
           (fun (attrs : 'alg_attributes) (t : 'ctyp_below_alg_attribute) _
                (ci : 'cons_ident) (loc : Ploc.t) ->
              (let (tl, rt) = generalized_type_of_type t in
               loc, ci, tl, Some rt, attrs :
               'constructor_declaration)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next Grammar.r_stop
                      (Grammar.s_nterm
                         (cons_ident : 'cons_ident Grammar.Entry.e)))
                   (Grammar.s_token ("", "of")))
                (Grammar.s_list1sep
                   (Grammar.s_nterm
                      (ctyp_below_alg_attribute :
                       'ctyp_below_alg_attribute Grammar.Entry.e))
                   (Grammar.s_token ("", "and")) false))
             (Grammar.s_nterm
                (alg_attributes : 'alg_attributes Grammar.Entry.e)),
           (fun (attrs : 'alg_attributes)
                (cal : 'ctyp_below_alg_attribute list) _ (ci : 'cons_ident)
                (loc : Ploc.t) ->
              (loc, ci, cal, None, attrs : 'constructor_declaration)))]];
    Grammar.extension
      (constructor_declaration_sans_alg_attrs :
       'constructor_declaration_sans_alg_attrs Grammar.Entry.e)
      None
      [None, None,
       [Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_nterm (cons_ident : 'cons_ident Grammar.Entry.e)),
           (fun (ci : 'cons_ident) (loc : Ploc.t) ->
              (loc, ci, [], None : 'constructor_declaration_sans_alg_attrs)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop
                   (Grammar.s_nterm
                      (cons_ident : 'cons_ident Grammar.Entry.e)))
                (Grammar.s_token ("", ":")))
             (Grammar.s_nterm
                (ctyp_below_alg_attribute :
                 'ctyp_below_alg_attribute Grammar.Entry.e)),
           (fun (t : 'ctyp_below_alg_attribute) _ (ci : 'cons_ident)
                (loc : Ploc.t) ->
              (let (tl, rt) = generalized_type_of_type t in
               loc, ci, tl, Some rt :
               'constructor_declaration_sans_alg_attrs)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop
                   (Grammar.s_nterm
                      (cons_ident : 'cons_ident Grammar.Entry.e)))
                (Grammar.s_token ("", "of")))
             (Grammar.s_list1sep
                (Grammar.s_nterm
                   (ctyp_below_alg_attribute :
                    'ctyp_below_alg_attribute Grammar.Entry.e))
                (Grammar.s_token ("", "and")) false),
           (fun (cal : 'ctyp_below_alg_attribute list) _ (ci : 'cons_ident)
                (loc : Ploc.t) ->
              (loc, ci, cal, None :
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
             (Grammar.s_nterm
                (alg_attributes : 'alg_attributes Grammar.Entry.e)),
           (fun (attrs : 'alg_attributes) (t : 'ctyp) (mf : bool) _
                (i : string) (loc : Ploc.t) ->
              (mklabdecl loc i mf t attrs : 'label_declaration)))]];
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
              (mkident i :: j : 'mod_ident)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop (Grammar.s_token ("LIDENT", "")),
           (fun (i : string) (loc : Ploc.t) -> ([mkident i] : 'mod_ident)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop (Grammar.s_token ("UIDENT", "")),
           (fun (i : string) (loc : Ploc.t) -> ([mkident i] : 'mod_ident)))]];
    Grammar.extension (direction_flag : 'direction_flag Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "downto")),
           (fun _ (loc : Ploc.t) -> (false : 'direction_flag)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "to")),
           (fun _ (loc : Ploc.t) -> (true : 'direction_flag)))]];
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
             (Grammar.s_list1sep
                (Grammar.s_nterm
                   (class_type_declaration :
                    'class_type_declaration Grammar.Entry.e))
                (Grammar.s_token ("", "and")) false),
           (fun (ctd : 'class_type_declaration list) _ _ (loc : Ploc.t) ->
              (MLast.StClt (loc, ctd) : 'str_item)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "class")))
             (Grammar.s_list1sep
                (Grammar.s_nterm
                   (class_declaration : 'class_declaration Grammar.Entry.e))
                (Grammar.s_token ("", "and")) false),
           (fun (cd : 'class_declaration list) _ (loc : Ploc.t) ->
              (MLast.StCls (loc, cd) : 'str_item)))]];
    Grammar.extension (sig_item : 'sig_item Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop
                   (Grammar.s_token ("", "class")))
                (Grammar.s_token ("", "type")))
             (Grammar.s_list1sep
                (Grammar.s_nterm
                   (class_type_declaration :
                    'class_type_declaration Grammar.Entry.e))
                (Grammar.s_token ("", "and")) false),
           (fun (ctd : 'class_type_declaration list) _ _ (loc : Ploc.t) ->
              (MLast.SgClt (loc, ctd) : 'sig_item)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "class")))
             (Grammar.s_list1sep
                (Grammar.s_nterm
                   (class_description : 'class_description Grammar.Entry.e))
                (Grammar.s_token ("", "and")) false),
           (fun (cd : 'class_description list) _ (loc : Ploc.t) ->
              (MLast.SgCls (loc, cd) : 'sig_item)))]];
    Grammar.extension (class_declaration : 'class_declaration Grammar.Entry.e)
      None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_flag (Grammar.s_token ("", "virtual"))))
                      (Grammar.s_token ("LIDENT", "")))
                   (Grammar.s_nterm
                      (class_type_parameters :
                       'class_type_parameters Grammar.Entry.e)))
                (Grammar.s_nterm
                   (class_fun_binding : 'class_fun_binding Grammar.Entry.e)))
             (Grammar.s_nterm
                (item_attributes : 'item_attributes Grammar.Entry.e)),
           (fun (attrs : 'item_attributes) (cfb : 'class_fun_binding)
                (ctp : 'class_type_parameters) (i : string) (vf : bool)
                (loc : Ploc.t) ->
              ({MLast.ciLoc = loc; MLast.ciVir = vf; MLast.ciPrm = ctp;
                MLast.ciNam = i; MLast.ciExp = cfb;
                MLast.ciAttributes = attrs} :
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
              (MLast.CeFun (loc, p, cfb) : 'class_fun_binding)));
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
              (MLast.CeTyc (loc, ce, ct) : 'class_fun_binding)));
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
                (Grammar.s_list1sep
                   (Grammar.s_nterm
                      (type_parameter : 'type_parameter Grammar.Entry.e))
                   (Grammar.s_token ("", ",")) false))
             (Grammar.s_token ("", "]")),
           (fun _ (tpl : 'type_parameter list) _ (loc : Ploc.t) ->
              (loc, tpl : 'class_type_parameters)));
        Grammar.production
          (Grammar.r_stop,
           (fun (loc : Ploc.t) -> (loc, [] : 'class_type_parameters)))]];
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
              (MLast.CeFun (loc, p, ce) : 'class_fun_def)))]];
    Grammar.extension (class_expr : 'class_expr Grammar.Entry.e) None
      [Some "top", None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("", "let")))
                      (Grammar.s_flag (Grammar.s_token ("", "rec"))))
                   (Grammar.s_list1sep
                      (Grammar.s_nterm
                         (let_binding : 'let_binding Grammar.Entry.e))
                      (Grammar.s_token ("", "and")) false))
                (Grammar.s_token ("", "in")))
             Grammar.s_self,
           (fun (ce : 'class_expr) _ (lb : 'let_binding list) (rf : bool) _
                (loc : Ploc.t) ->
              (MLast.CeLet (loc, rf, lb, ce) : 'class_expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next Grammar.r_stop
                      (Grammar.s_token ("", "fun")))
                   (Grammar.s_nterm
                      (alg_attributes_no_anti :
                       'alg_attributes_no_anti Grammar.Entry.e)))
                (Grammar.s_nterm (ipatt : 'ipatt Grammar.Entry.e)))
             (Grammar.s_nterm
                (class_fun_def : 'class_fun_def Grammar.Entry.e)),
           (fun (ce : 'class_fun_def) (p : 'ipatt)
                (alg_attrs : 'alg_attributes_no_anti) _ (loc : Ploc.t) ->
              (class_expr_wrap_attrs loc (MLast.CeFun (loc, p, ce))
                 alg_attrs :
               'class_expr)))];
       Some "alg_attribute", Some Gramext.LeftA,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                   (Grammar.s_token ("", "[@")))
                (Grammar.s_nterm
                   (attribute_body : 'attribute_body Grammar.Entry.e)))
             (Grammar.s_token ("", "]")),
           (fun _ (attr : 'attribute_body) _ (ct : 'class_expr)
                (loc : Ploc.t) ->
              (MLast.CeAtt (loc, ct, attr) : 'class_expr)))];
       None, None,
       [Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_nterm
                (alg_extension : 'alg_extension Grammar.Entry.e)),
           (fun (e : 'alg_extension) (loc : Ploc.t) ->
              (MLast.CeExten (loc, e) : 'class_expr)))];
       None, None,
       [Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_nterm
                (class_expr_apply : 'class_expr_apply Grammar.Entry.e)),
           (fun (ce : 'class_expr_apply) (loc : Ploc.t) ->
              (ce : 'class_expr)))]];
    Grammar.extension (class_expr_apply : 'class_expr_apply Grammar.Entry.e)
      None
      [Some "apply", Some Gramext.LeftA,
       [Grammar.production
          (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
             (Grammar.s_nterml (expr : 'expr Grammar.Entry.e) "label"),
           (fun (e : 'expr) (ce : 'class_expr_apply) (loc : Ploc.t) ->
              (MLast.CeApp (loc, ce, e) : 'class_expr_apply)))];
       None, None,
       [Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_nterm
                (class_expr_simple : 'class_expr_simple Grammar.Entry.e)),
           (fun (ce : 'class_expr_simple) (loc : Ploc.t) ->
              (ce : 'class_expr_apply)))]];
    Grammar.extension (class_expr_simple : 'class_expr_simple Grammar.Entry.e)
      None
      [Some "simple", None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "(")))
                (Grammar.s_nterm (class_expr : 'class_expr Grammar.Entry.e)))
             (Grammar.s_token ("", ")")),
           (fun _ (ce : 'class_expr) _ (loc : Ploc.t) ->
              (ce : 'class_expr_simple)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("", "(")))
                      (Grammar.s_nterm
                         (class_expr : 'class_expr Grammar.Entry.e)))
                   (Grammar.s_token ("", ":")))
                (Grammar.s_nterm (class_type : 'class_type Grammar.Entry.e)))
             (Grammar.s_token ("", ")")),
           (fun _ (ct : 'class_type) _ (ce : 'class_expr) _ (loc : Ploc.t) ->
              (MLast.CeTyc (loc, ce, ct) : 'class_expr_simple)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "[")))
                   (Grammar.s_list1sep
                      (Grammar.s_nterm (ctyp : 'ctyp Grammar.Entry.e))
                      (Grammar.s_token ("", ",")) false))
                (Grammar.s_token ("", "]")))
             (Grammar.s_nterm
                (class_longident : 'class_longident Grammar.Entry.e)),
           (fun (ci : 'class_longident) _ (ctcl : 'ctyp list) _
                (loc : Ploc.t) ->
              (MLast.CeCon (loc, ci, ctcl) : 'class_expr_simple)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next Grammar.r_stop
                      (Grammar.s_token ("", "object")))
                   (Grammar.s_opt
                      (Grammar.s_nterm
                         (class_self_patt :
                          'class_self_patt Grammar.Entry.e))))
                (Grammar.s_nterm
                   (class_structure : 'class_structure Grammar.Entry.e)))
             (Grammar.s_token ("", "end")),
           (fun _ (cf : 'class_structure) (cspo : 'class_self_patt option) _
                (loc : Ploc.t) ->
              (MLast.CeStr (loc, cspo, cf) : 'class_expr_simple)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_nterm
                (class_longident : 'class_longident Grammar.Entry.e)),
           (fun (ci : 'class_longident) (loc : Ploc.t) ->
              (MLast.CeCon (loc, ci, []) : 'class_expr_simple)))]];
    Grammar.extension (class_structure : 'class_structure Grammar.Entry.e)
      None
      [None, None,
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
                       (fun _ (cf : 'class_str_item) (loc : Ploc.t) ->
                          (cf : 'e__11)))])),
           (fun (cf : 'e__11 list) (loc : Ploc.t) ->
              (cf : 'class_structure)))]];
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
              (MLast.PaTyc (loc, p, t) : 'class_self_patt)));
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
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_nterm
                (item_extension : 'item_extension Grammar.Entry.e)),
           (fun (e : 'item_extension) (loc : Ploc.t) ->
              (MLast.CrExten (loc, e) : 'class_str_item)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_nterm
                (floating_attribute : 'floating_attribute Grammar.Entry.e)),
           (fun (attr : 'floating_attribute) (loc : Ploc.t) ->
              (MLast.CrFlAtt (loc, attr) : 'class_str_item)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop
                   (Grammar.s_token ("", "initializer")))
                (Grammar.s_nterm (expr : 'expr Grammar.Entry.e)))
             (Grammar.s_nterm
                (item_attributes : 'item_attributes Grammar.Entry.e)),
           (fun (attrs : 'item_attributes) (se : 'expr) _ (loc : Ploc.t) ->
              (MLast.CrIni (loc, se, attrs) : 'class_str_item)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("", "type")))
                      (Grammar.s_nterm (ctyp : 'ctyp Grammar.Entry.e)))
                   (Grammar.s_token ("", "=")))
                (Grammar.s_nterm (ctyp : 'ctyp Grammar.Entry.e)))
             (Grammar.s_nterm
                (item_attributes : 'item_attributes Grammar.Entry.e)),
           (fun (attrs : 'item_attributes) (t2 : 'ctyp) _ (t1 : 'ctyp) _
                (loc : Ploc.t) ->
              (MLast.CrCtr (loc, t1, t2, attrs) : 'class_str_item)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next
                         (Grammar.r_next
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("", "method")))
                            (Grammar.s_flag (Grammar.s_token ("", "!"))))
                         (Grammar.s_flag (Grammar.s_token ("", "private"))))
                      (Grammar.s_nterm (lident : 'lident Grammar.Entry.e)))
                   (Grammar.s_opt
                      (Grammar.s_nterm (polyt : 'polyt Grammar.Entry.e))))
                (Grammar.s_nterm
                   (fun_binding : 'fun_binding Grammar.Entry.e)))
             (Grammar.s_nterm
                (item_attributes : 'item_attributes Grammar.Entry.e)),
           (fun (attrs : 'item_attributes) (e : 'fun_binding)
                (topt : 'polyt option) (l : 'lident) (pf : bool) (ovf : bool)
                _ (loc : Ploc.t) ->
              (MLast.CrMth (loc, ovf, pf, l, topt, e, attrs) :
               'class_str_item)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next
                         (Grammar.r_next
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("", "method")))
                            (Grammar.s_token ("", "virtual")))
                         (Grammar.s_flag (Grammar.s_token ("", "private"))))
                      (Grammar.s_nterm (lident : 'lident Grammar.Entry.e)))
                   (Grammar.s_token ("", ":")))
                (Grammar.s_nterm (ctyp : 'ctyp Grammar.Entry.e)))
             (Grammar.s_nterm
                (item_attributes : 'item_attributes Grammar.Entry.e)),
           (fun (attrs : 'item_attributes) (t : 'ctyp) _ (l : 'lident)
                (pf : bool) _ _ (loc : Ploc.t) ->
              (MLast.CrVir (loc, pf, l, t, attrs) : 'class_str_item)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next
                         (Grammar.r_next
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("", "value")))
                            (Grammar.s_token ("", "virtual")))
                         (Grammar.s_flag (Grammar.s_token ("", "mutable"))))
                      (Grammar.s_nterm (lident : 'lident Grammar.Entry.e)))
                   (Grammar.s_token ("", ":")))
                (Grammar.s_nterm (ctyp : 'ctyp Grammar.Entry.e)))
             (Grammar.s_nterm
                (item_attributes : 'item_attributes Grammar.Entry.e)),
           (fun (attrs : 'item_attributes) (t : 'ctyp) _ (lab : 'lident)
                (mf : bool) _ _ (loc : Ploc.t) ->
              (MLast.CrVav (loc, mf, lab, t, attrs) : 'class_str_item)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("", "value")))
                         (Grammar.s_flag (Grammar.s_token ("", "!"))))
                      (Grammar.s_flag (Grammar.s_token ("", "mutable"))))
                   (Grammar.s_nterm (lident : 'lident Grammar.Entry.e)))
                (Grammar.s_nterm
                   (cvalue_binding : 'cvalue_binding Grammar.Entry.e)))
             (Grammar.s_nterm
                (item_attributes : 'item_attributes Grammar.Entry.e)),
           (fun (attrs : 'item_attributes) (e : 'cvalue_binding)
                (lab : 'lident) (mf : bool) (ovf : bool) _ (loc : Ploc.t) ->
              (MLast.CrVal (loc, ovf, mf, lab, e, attrs) : 'class_str_item)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("", "inherit")))
                      (Grammar.s_flag (Grammar.s_token ("", "!"))))
                   (Grammar.s_nterm
                      (class_expr : 'class_expr Grammar.Entry.e)))
                (Grammar.s_opt
                   (Grammar.s_nterm
                      (as_lident : 'as_lident Grammar.Entry.e))))
             (Grammar.s_nterm
                (item_attributes : 'item_attributes Grammar.Entry.e)),
           (fun (attrs : 'item_attributes) (pb : 'as_lident option)
                (ce : 'class_expr) (ovf : bool) _ (loc : Ploc.t) ->
              (MLast.CrInh (loc, ovf, ce, pb, attrs) : 'class_str_item)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop
                   (Grammar.s_token ("", "declare")))
                (Grammar.s_list0
                   (Grammar.s_rules
                      [Grammar.production
                         (Grammar.r_next
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_nterm
                                  (class_str_item :
                                   'class_str_item Grammar.Entry.e)))
                            (Grammar.s_token ("", ";")),
                          (fun _ (s : 'class_str_item) (loc : Ploc.t) ->
                             (s : 'e__12)))])))
             (Grammar.s_token ("", "end")),
           (fun _ (st : 'e__12 list) _ (loc : Ploc.t) ->
              (MLast.CrDcl (loc, st) : 'class_str_item)))]];
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
              (MLast.ExCoe (loc, e, None, t) : 'cvalue_binding)));
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
              (MLast.ExCoe (loc, e, Some t, t2) : 'cvalue_binding)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", ":")))
                   (Grammar.s_nterm (ctyp : 'ctyp Grammar.Entry.e)))
                (Grammar.s_token ("", "=")))
             (Grammar.s_nterm (expr : 'expr Grammar.Entry.e)),
           (fun (e : 'expr) _ (t : 'ctyp) _ (loc : Ploc.t) ->
              (MLast.ExTyc (loc, e, t) : 'cvalue_binding)));
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
              (MLast.CtFun (loc, t, ct) : 'class_type)))];
       Some "alg_attribute", Some Gramext.LeftA,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                   (Grammar.s_token ("", "[@")))
                (Grammar.s_nterm
                   (attribute_body : 'attribute_body Grammar.Entry.e)))
             (Grammar.s_token ("", "]")),
           (fun _ (attr : 'attribute_body) _ (ct : 'class_type)
                (loc : Ploc.t) ->
              (MLast.CtAtt (loc, ct, attr) : 'class_type)))];
       None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                   (Grammar.s_token ("", "[")))
                (Grammar.s_list1sep
                   (Grammar.s_nterm (ctyp : 'ctyp Grammar.Entry.e))
                   (Grammar.s_token ("", ",")) false))
             (Grammar.s_token ("", "]")),
           (fun _ (tl : 'ctyp list) _ (ct : 'class_type) (loc : Ploc.t) ->
              (MLast.CtCon (loc, ct, tl) : 'class_type)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next Grammar.r_stop
                      (Grammar.s_token ("", "object")))
                   (Grammar.s_opt
                      (Grammar.s_nterm
                         (class_self_type :
                          'class_self_type Grammar.Entry.e))))
                (Grammar.s_list0
                   (Grammar.s_rules
                      [Grammar.production
                         (Grammar.r_next
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_nterm
                                  (class_sig_item :
                                   'class_sig_item Grammar.Entry.e)))
                            (Grammar.s_token ("", ";")),
                          (fun _ (csf : 'class_sig_item) (loc : Ploc.t) ->
                             (csf : 'e__13)))])))
             (Grammar.s_token ("", "end")),
           (fun _ (csf : 'e__13 list) (cst : 'class_self_type option) _
                (loc : Ploc.t) ->
              (MLast.CtSig (loc, cst, csf) : 'class_type)))];
       Some "simple", None,
       [Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_nterm
                (alg_extension : 'alg_extension Grammar.Entry.e)),
           (fun (e : 'alg_extension) (loc : Ploc.t) ->
              (MLast.CtExten (loc, e) : 'class_type)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "(")))
                Grammar.s_self)
             (Grammar.s_token ("", ")")),
           (fun _ (ct : 'class_type) _ (loc : Ploc.t) -> (ct : 'class_type)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop (Grammar.s_token ("LIDENT", "")),
           (fun (i : string) (loc : Ploc.t) ->
              (MLast.CtLid (loc, i) : 'class_type)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_nterm
                (extended_longident : 'extended_longident Grammar.Entry.e)),
           (fun (li : 'extended_longident) (loc : Ploc.t) ->
              (MLast.CtLong (loc, li) : 'class_type)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop
                   (Grammar.s_nterm
                      (extended_longident :
                       'extended_longident Grammar.Entry.e)))
                (Grammar.s_token ("", ".")))
             (Grammar.s_token ("LIDENT", "")),
           (fun (i : string) _ (li : 'extended_longident) (loc : Ploc.t) ->
              (MLast.CtLongLid (loc, li, i) : 'class_type)))]];
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
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_nterm
                (item_extension : 'item_extension Grammar.Entry.e)),
           (fun (e : 'item_extension) (loc : Ploc.t) ->
              (MLast.CgExten (loc, e) : 'class_sig_item)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_nterm
                (floating_attribute : 'floating_attribute Grammar.Entry.e)),
           (fun (attr : 'floating_attribute) (loc : Ploc.t) ->
              (MLast.CgFlAtt (loc, attr) : 'class_sig_item)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("", "type")))
                      (Grammar.s_nterm (ctyp : 'ctyp Grammar.Entry.e)))
                   (Grammar.s_token ("", "=")))
                (Grammar.s_nterm (ctyp : 'ctyp Grammar.Entry.e)))
             (Grammar.s_nterm
                (item_attributes : 'item_attributes Grammar.Entry.e)),
           (fun (attrs : 'item_attributes) (t2 : 'ctyp) _ (t1 : 'ctyp) _
                (loc : Ploc.t) ->
              (MLast.CgCtr (loc, t1, t2, attrs) : 'class_sig_item)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("", "method")))
                         (Grammar.s_flag (Grammar.s_token ("", "private"))))
                      (Grammar.s_nterm (lident : 'lident Grammar.Entry.e)))
                   (Grammar.s_token ("", ":")))
                (Grammar.s_nterm (ctyp : 'ctyp Grammar.Entry.e)))
             (Grammar.s_nterm
                (item_attributes : 'item_attributes Grammar.Entry.e)),
           (fun (attrs : 'item_attributes) (t : 'ctyp) _ (l : 'lident)
                (pf : bool) _ (loc : Ploc.t) ->
              (MLast.CgMth (loc, pf, l, t, attrs) : 'class_sig_item)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next
                         (Grammar.r_next
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("", "method")))
                            (Grammar.s_token ("", "virtual")))
                         (Grammar.s_flag (Grammar.s_token ("", "private"))))
                      (Grammar.s_nterm (lident : 'lident Grammar.Entry.e)))
                   (Grammar.s_token ("", ":")))
                (Grammar.s_nterm (ctyp : 'ctyp Grammar.Entry.e)))
             (Grammar.s_nterm
                (item_attributes : 'item_attributes Grammar.Entry.e)),
           (fun (attrs : 'item_attributes) (t : 'ctyp) _ (l : 'lident)
                (pf : bool) _ _ (loc : Ploc.t) ->
              (MLast.CgVir (loc, pf, l, t, attrs) : 'class_sig_item)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next
                         (Grammar.r_next
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("", "value")))
                            (Grammar.s_flag
                               (Grammar.s_token ("", "mutable"))))
                         (Grammar.s_flag (Grammar.s_token ("", "virtual"))))
                      (Grammar.s_nterm (lident : 'lident Grammar.Entry.e)))
                   (Grammar.s_token ("", ":")))
                (Grammar.s_nterm (ctyp : 'ctyp Grammar.Entry.e)))
             (Grammar.s_nterm
                (item_attributes : 'item_attributes Grammar.Entry.e)),
           (fun (attrs : 'item_attributes) (t : 'ctyp) _ (l : 'lident)
                (vf : bool) (mf : bool) _ (loc : Ploc.t) ->
              (MLast.CgVal (loc, mf, vf, l, t, attrs) : 'class_sig_item)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop
                   (Grammar.s_token ("", "inherit")))
                (Grammar.s_nterm (class_type : 'class_type Grammar.Entry.e)))
             (Grammar.s_nterm
                (item_attributes : 'item_attributes Grammar.Entry.e)),
           (fun (attrs : 'item_attributes) (cs : 'class_type) _
                (loc : Ploc.t) ->
              (MLast.CgInh (loc, cs, attrs) : 'class_sig_item)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop
                   (Grammar.s_token ("", "declare")))
                (Grammar.s_list0
                   (Grammar.s_rules
                      [Grammar.production
                         (Grammar.r_next
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_nterm
                                  (class_sig_item :
                                   'class_sig_item Grammar.Entry.e)))
                            (Grammar.s_token ("", ";")),
                          (fun _ (s : 'class_sig_item) (loc : Ploc.t) ->
                             (s : 'e__14)))])))
             (Grammar.s_token ("", "end")),
           (fun _ (st : 'e__14 list) _ (loc : Ploc.t) ->
              (MLast.CgDcl (loc, st) : 'class_sig_item)))]];
    Grammar.extension (class_description : 'class_description Grammar.Entry.e)
      None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_flag
                               (Grammar.s_token ("", "virtual"))))
                         (Grammar.s_token ("LIDENT", "")))
                      (Grammar.s_nterm
                         (class_type_parameters :
                          'class_type_parameters Grammar.Entry.e)))
                   (Grammar.s_token ("", ":")))
                (Grammar.s_nterm (class_type : 'class_type Grammar.Entry.e)))
             (Grammar.s_nterm
                (item_attributes : 'item_attributes Grammar.Entry.e)),
           (fun (attrs : 'item_attributes) (ct : 'class_type) _
                (ctp : 'class_type_parameters) (n : string) (vf : bool)
                (loc : Ploc.t) ->
              ({MLast.ciLoc = loc; MLast.ciVir = vf; MLast.ciPrm = ctp;
                MLast.ciNam = n; MLast.ciExp = ct;
                MLast.ciAttributes = attrs} :
               'class_description)))]];
    Grammar.extension
      (class_type_declaration : 'class_type_declaration Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_flag
                               (Grammar.s_token ("", "virtual"))))
                         (Grammar.s_token ("LIDENT", "")))
                      (Grammar.s_nterm
                         (class_type_parameters :
                          'class_type_parameters Grammar.Entry.e)))
                   (Grammar.s_token ("", "=")))
                (Grammar.s_nterm (class_type : 'class_type Grammar.Entry.e)))
             (Grammar.s_nterm
                (item_attributes : 'item_attributes Grammar.Entry.e)),
           (fun (attrs : 'item_attributes) (cs : 'class_type) _
                (ctp : 'class_type_parameters) (n : string) (vf : bool)
                (loc : Ploc.t) ->
              ({MLast.ciLoc = loc; MLast.ciVir = vf; MLast.ciPrm = ctp;
                MLast.ciNam = n; MLast.ciExp = cs;
                MLast.ciAttributes = attrs} :
               'class_type_declaration)))]];
    Grammar.extension (expr : 'expr Grammar.Entry.e)
      (Some (Gramext.Level "apply"))
      [None, Some Gramext.LeftA,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("", "object")))
                      (Grammar.s_nterm
                         (ext_attributes : 'ext_attributes Grammar.Entry.e)))
                   (Grammar.s_opt
                      (Grammar.s_nterm
                         (class_self_patt :
                          'class_self_patt Grammar.Entry.e))))
                (Grammar.s_nterm
                   (class_structure : 'class_structure Grammar.Entry.e)))
             (Grammar.s_token ("", "end")),
           (fun _ (cf : 'class_structure) (cspo : 'class_self_patt option)
                (ext, attrs : 'ext_attributes) _ (loc : Ploc.t) ->
              (expr_to_inline loc (MLast.ExObj (loc, cspo, cf)) ext attrs :
               'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "new")))
                (Grammar.s_nterm
                   (ext_attributes : 'ext_attributes Grammar.Entry.e)))
             (Grammar.s_nterm
                (class_longident : 'class_longident Grammar.Entry.e)),
           (fun (i : 'class_longident) (ext, attrs : 'ext_attributes) _
                (loc : Ploc.t) ->
              (expr_to_inline loc (MLast.ExNew (loc, i)) ext attrs :
               'expr)))]];
    Grammar.extension (expr : 'expr Grammar.Entry.e)
      (Some (Gramext.Level "."))
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                (Grammar.s_nterm (hashop : 'hashop Grammar.Entry.e)))
             Grammar.s_self,
           (fun (e2 : 'expr) (op : 'hashop) (e : 'expr) (loc : Ploc.t) ->
              (MLast.ExApp
                 (loc, MLast.ExApp (loc, MLast.ExLid (loc, op), e), e2) :
               'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                (Grammar.s_token ("", "#")))
             (Grammar.s_nterm (lident : 'lident Grammar.Entry.e)),
           (fun (lab : 'lident) _ (e : 'expr) (loc : Ploc.t) ->
              (MLast.ExSnd (loc, e, lab) : 'expr)))]];
    Grammar.extension (expr : 'expr Grammar.Entry.e)
      (Some (Gramext.Level "simple"))
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "{<")))
                (Grammar.s_list0sep
                   (Grammar.s_nterm
                      (field_expr : 'field_expr Grammar.Entry.e))
                   (Grammar.s_token ("", ";")) false))
             (Grammar.s_token ("", ">}")),
           (fun _ (fel : 'field_expr list) _ (loc : Ploc.t) ->
              (MLast.ExOvr (loc, fel) : 'expr)));
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
              (MLast.ExCoe (loc, e, None, t) : 'expr)));
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
              (MLast.ExCoe (loc, e, Some t, t2) : 'expr)))]];
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
              (l, e : 'field_expr)))]];
    Grammar.extension (ctyp : 'ctyp Grammar.Entry.e)
      (Some (Gramext.Level "simple"))
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "<")))
                   (Grammar.s_list0sep
                      (Grammar.s_nterm (field : 'field Grammar.Entry.e))
                      (Grammar.s_token ("", ";")) false))
                (Grammar.s_flag (Grammar.s_token ("", ".."))))
             (Grammar.s_token ("", ">")),
           (fun _ (v : bool) (ml : 'field list) _ (loc : Ploc.t) ->
              (MLast.TyObj (loc, ml, v) : 'ctyp)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "#")))
             (Grammar.s_nterm
                (class_longident : 'class_longident Grammar.Entry.e)),
           (fun (id : 'class_longident) _ (loc : Ploc.t) ->
              (MLast.TyCls (loc, id) : 'ctyp)))]];
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
              (mkident lab, t : 'field)))]];
    Grammar.extension (class_longident : 'class_longident Grammar.Entry.e)
      None
      [None, None,
       [Grammar.production
          (Grammar.r_next Grammar.r_stop (Grammar.s_token ("LIDENT", "")),
           (fun (i : string) (loc : Ploc.t) ->
              ([mkident i] : 'class_longident)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop
                   (Grammar.s_token ("UIDENT", "")))
                (Grammar.s_token ("", ".")))
             Grammar.s_self,
           (fun (l : 'class_longident) _ (m : string) (loc : Ploc.t) ->
              (mkident m :: l : 'class_longident)))]];
    (* Labels *)
    Grammar.extension (ctyp : 'ctyp Grammar.Entry.e)
      (Some (Gramext.After "arrow"))
      [None, Some Gramext.NonA,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop
                (Grammar.s_token ("QUESTIONIDENTCOLON", "")))
             Grammar.s_self,
           (fun (t : 'ctyp) (i : string) (loc : Ploc.t) ->
              (MLast.TyOlb (loc, i, t) : 'ctyp)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop
                (Grammar.s_token ("TILDEIDENTCOLON", "")))
             Grammar.s_self,
           (fun (t : 'ctyp) (i : string) (loc : Ploc.t) ->
              (MLast.TyLab (loc, i, t) : 'ctyp)))]];
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
                (Grammar.s_list1
                   (Grammar.s_nterm (name_tag : 'name_tag Grammar.Entry.e))))
             (Grammar.s_token ("", "]")),
           (fun _ (ntl : 'name_tag list) _ (rfl : 'poly_variant_list) _ _
                (loc : Ploc.t) ->
              (MLast.TyVrn (loc, rfl, Some (Some ntl)) : 'ctyp)));
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
              (MLast.TyVrn (loc, rfl, Some (Some [])) : 'ctyp)));
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
              (MLast.TyVrn (loc, rfl, Some None) : 'ctyp)));
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
              (MLast.TyVrn (loc, rfl, None) : 'ctyp)))]];
    Grammar.extension (poly_variant_list : 'poly_variant_list Grammar.Entry.e)
      None
      [None, None,
       [Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_list0sep
                (Grammar.s_nterm
                   (poly_variant : 'poly_variant Grammar.Entry.e))
                (Grammar.s_token ("", "|")) false),
           (fun (rfl : 'poly_variant list) (loc : Ploc.t) ->
              (rfl : 'poly_variant_list)))]];
    Grammar.extension (poly_variant : 'poly_variant Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_nterm (ctyp : 'ctyp Grammar.Entry.e)),
           (fun (t : 'ctyp) (loc : Ploc.t) ->
              (MLast.PvInh (loc, t) : 'poly_variant)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("", "`")))
                         (Grammar.s_nterm (ident : 'ident Grammar.Entry.e)))
                      (Grammar.s_token ("", "of")))
                   (Grammar.s_flag (Grammar.s_token ("", "&"))))
                (Grammar.s_list1sep
                   (Grammar.s_nterm
                      (ctyp_below_alg_attribute :
                       'ctyp_below_alg_attribute Grammar.Entry.e))
                   (Grammar.s_token ("", "&")) false))
             (Grammar.s_nterm
                (alg_attributes : 'alg_attributes Grammar.Entry.e)),
           (fun (attrs : 'alg_attributes) (l : 'ctyp_below_alg_attribute list)
                (ao : bool) _ (i : 'ident) _ (loc : Ploc.t) ->
              (MLast.PvTag (loc, i, ao, l, attrs) : 'poly_variant)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "`")))
                (Grammar.s_nterm (ident : 'ident Grammar.Entry.e)))
             (Grammar.s_nterm
                (alg_attributes : 'alg_attributes Grammar.Entry.e)),
           (fun (attrs : 'alg_attributes) (i : 'ident) _ (loc : Ploc.t) ->
              (MLast.PvTag (loc, i, true, [], attrs) : 'poly_variant)))]];
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
          (Grammar.r_next Grammar.r_stop (Grammar.s_token ("TILDEIDENT", "")),
           (fun (i : string) (loc : Ploc.t) ->
              (let _ = warning_deprecated_since_6_00 loc in
               MLast.PaLab (loc, [MLast.PaLid (loc, i), None]) :
               'patt)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop
                (Grammar.s_token ("TILDEIDENTCOLON", "")))
             Grammar.s_self,
           (fun (p : 'patt) (i : string) (loc : Ploc.t) ->
              (let _ = warning_deprecated_since_6_00 loc in
               MLast.PaLab (loc, [MLast.PaLid (loc, i), Some p]) :
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
                (Grammar.s_opt
                   (Grammar.s_rules
                      [Grammar.production
                         (Grammar.r_next
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("", "=")))
                            (Grammar.s_nterm (expr : 'expr Grammar.Entry.e)),
                          (fun (e : 'expr) _ (loc : Ploc.t) ->
                             (e : 'e__15)))])))
             (Grammar.s_token ("", "}")),
           (fun _ (eo : 'e__15 option) (p : 'patt_tcon) _ _ (loc : Ploc.t) ->
              (MLast.PaOlb (loc, p, eo) : 'patt)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "~")))
                   (Grammar.s_token ("", "{")))
                (Grammar.s_list1sep
                   (Grammar.s_nterm
                      (patt_tcon_opt_eq_patt :
                       'patt_tcon_opt_eq_patt Grammar.Entry.e))
                   (Grammar.s_token ("", ";")) false))
             (Grammar.s_token ("", "}")),
           (fun _ (lppo : 'patt_tcon_opt_eq_patt list) _ _ (loc : Ploc.t) ->
              (MLast.PaLab (loc, lppo) : 'patt)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "#")))
             (Grammar.s_nterm (mod_ident : 'mod_ident Grammar.Entry.e)),
           (fun (sl : 'mod_ident) _ (loc : Ploc.t) ->
              (MLast.PaTyp (loc, sl) : 'patt)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "`")))
             (Grammar.s_nterm (ident : 'ident Grammar.Entry.e)),
           (fun (s : 'ident) _ (loc : Ploc.t) ->
              (MLast.PaVrn (loc, s) : 'patt)))]];
    Grammar.extension
      (patt_tcon_opt_eq_patt : 'patt_tcon_opt_eq_patt Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop
                (Grammar.s_nterm (patt_tcon : 'patt_tcon Grammar.Entry.e)))
             (Grammar.s_opt
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("", "=")))
                         (Grammar.s_nterm (patt : 'patt Grammar.Entry.e)),
                       (fun (p : 'patt) _ (loc : Ploc.t) -> (p : 'e__16)))])),
           (fun (po : 'e__16 option) (p : 'patt_tcon) (loc : Ploc.t) ->
              (p, po : 'patt_tcon_opt_eq_patt)))]];
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
              (MLast.PaTyc (loc, p, t) : 'patt_tcon)));
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
          (Grammar.r_next Grammar.r_stop (Grammar.s_token ("TILDEIDENT", "")),
           (fun (i : string) (loc : Ploc.t) ->
              (let _ = warning_deprecated_since_6_00 loc in
               MLast.PaLab (loc, [MLast.PaLid (loc, i), None]) :
               'ipatt)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop
                (Grammar.s_token ("TILDEIDENTCOLON", "")))
             Grammar.s_self,
           (fun (p : 'ipatt) (i : string) (loc : Ploc.t) ->
              (let _ = warning_deprecated_since_6_00 loc in
               MLast.PaLab (loc, [MLast.PaLid (loc, i), Some p]) :
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
                (Grammar.s_opt
                   (Grammar.s_rules
                      [Grammar.production
                         (Grammar.r_next
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("", "=")))
                            (Grammar.s_nterm (expr : 'expr Grammar.Entry.e)),
                          (fun (e : 'expr) _ (loc : Ploc.t) ->
                             (e : 'e__17)))])))
             (Grammar.s_token ("", "}")),
           (fun _ (eo : 'e__17 option) (p : 'ipatt_tcon) _ _ (loc : Ploc.t) ->
              (MLast.PaOlb (loc, p, eo) : 'ipatt)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "~")))
                   (Grammar.s_token ("", "{")))
                (Grammar.s_list1sep
                   (Grammar.s_nterm
                      (ipatt_tcon_opt_eq_patt :
                       'ipatt_tcon_opt_eq_patt Grammar.Entry.e))
                   (Grammar.s_token ("", ";")) false))
             (Grammar.s_token ("", "}")),
           (fun _ (lppo : 'ipatt_tcon_opt_eq_patt list) _ _ (loc : Ploc.t) ->
              (MLast.PaLab (loc, lppo) : 'ipatt)))]];
    Grammar.extension
      (ipatt_tcon_opt_eq_patt : 'ipatt_tcon_opt_eq_patt Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop
                (Grammar.s_nterm (ipatt_tcon : 'ipatt_tcon Grammar.Entry.e)))
             (Grammar.s_opt
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("", "=")))
                         (Grammar.s_nterm (patt : 'patt Grammar.Entry.e)),
                       (fun (p : 'patt) _ (loc : Ploc.t) -> (p : 'e__18)))])),
           (fun (po : 'e__18 option) (p : 'ipatt_tcon) (loc : Ploc.t) ->
              (p, po : 'ipatt_tcon_opt_eq_patt)))]];
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
              (MLast.PaTyc (loc, p, t) : 'ipatt_tcon)));
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
                (Grammar.s_token ("LIDENT", "")))
             (Grammar.s_token ("", ")")),
           (fun _ (i : string) _ _ (loc : Ploc.t) ->
              (MLast.PaOlb (loc, MLast.PaLid (loc, i), None) :
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
                      (Grammar.s_token ("LIDENT", "")))
                   (Grammar.s_token ("", "=")))
                (Grammar.s_nterm (expr : 'expr Grammar.Entry.e)))
             (Grammar.s_token ("", ")")),
           (fun _ (e : 'expr) _ (i : string) _ _ (loc : Ploc.t) ->
              (MLast.PaOlb (loc, MLast.PaLid (loc, i), Some e) :
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
                      (Grammar.s_token ("LIDENT", "")))
                   (Grammar.s_token ("", ":")))
                (Grammar.s_nterm (ctyp : 'ctyp Grammar.Entry.e)))
             (Grammar.s_token ("", ")")),
           (fun _ (t : 'ctyp) _ (i : string) _ _ (loc : Ploc.t) ->
              (MLast.PaOlb
                 (loc, MLast.PaTyc (loc, MLast.PaLid (loc, i), t), None) :
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
                            (Grammar.s_token ("LIDENT", "")))
                         (Grammar.s_token ("", ":")))
                      (Grammar.s_nterm (ctyp : 'ctyp Grammar.Entry.e)))
                   (Grammar.s_token ("", "=")))
                (Grammar.s_nterm (expr : 'expr Grammar.Entry.e)))
             (Grammar.s_token ("", ")")),
           (fun _ (e : 'expr) _ (t : 'ctyp) _ (i : string) _ _
                (loc : Ploc.t) ->
              (MLast.PaOlb
                 (loc, MLast.PaTyc (loc, MLast.PaLid (loc, i), t), Some e) :
               'patt_option_label)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_token ("QUESTIONIDENT", "")),
           (fun (i : string) (loc : Ploc.t) ->
              (MLast.PaOlb (loc, MLast.PaLid (loc, i), None) :
               'patt_option_label)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next Grammar.r_stop
                      (Grammar.s_token ("QUESTIONIDENTCOLON", "")))
                   (Grammar.s_token ("", "(")))
                (Grammar.s_token ("LIDENT", "")))
             (Grammar.s_token ("", ")")),
           (fun _ (j : string) _ (i : string) (loc : Ploc.t) ->
              (MLast.PaOlb
                 (loc, MLast.PaLid (loc, i), Some (MLast.ExLid (loc, j))) :
               'patt_option_label)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("QUESTIONIDENTCOLON", "")))
                         (Grammar.s_token ("", "(")))
                      (Grammar.s_token ("LIDENT", "")))
                   (Grammar.s_token ("", "=")))
                (Grammar.s_nterm (expr : 'expr Grammar.Entry.e)))
             (Grammar.s_token ("", ")")),
           (fun _ (e : 'expr) _ (j : string) _ (i : string) (loc : Ploc.t) ->
              (MLast.PaOlb
                 (loc, MLast.PaLid (loc, i),
                  Some (MLast.ExOlb (loc, MLast.PaLid (loc, j), Some e))) :
               'patt_option_label)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("QUESTIONIDENTCOLON", "")))
                         (Grammar.s_token ("", "(")))
                      (Grammar.s_token ("LIDENT", "")))
                   (Grammar.s_token ("", ":")))
                (Grammar.s_nterm (ctyp : 'ctyp Grammar.Entry.e)))
             (Grammar.s_token ("", ")")),
           (fun _ (t : 'ctyp) _ (j : string) _ (i : string) (loc : Ploc.t) ->
              (MLast.PaOlb
                 (loc, MLast.PaTyc (loc, MLast.PaLid (loc, i), t),
                  Some (MLast.ExOlb (loc, MLast.PaLid (loc, j), None))) :
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
                                  (Grammar.s_token
                                     ("QUESTIONIDENTCOLON", "")))
                               (Grammar.s_token ("", "(")))
                            (Grammar.s_token ("LIDENT", "")))
                         (Grammar.s_token ("", ":")))
                      (Grammar.s_nterm (ctyp : 'ctyp Grammar.Entry.e)))
                   (Grammar.s_token ("", "=")))
                (Grammar.s_nterm (expr : 'expr Grammar.Entry.e)))
             (Grammar.s_token ("", ")")),
           (fun _ (e : 'expr) _ (t : 'ctyp) _ (j : string) _ (i : string)
                (loc : Ploc.t) ->
              (MLast.PaOlb
                 (loc, MLast.PaTyc (loc, MLast.PaLid (loc, i), t),
                  Some (MLast.ExOlb (loc, MLast.PaLid (loc, j), Some e))) :
               'patt_option_label)))]];
    Grammar.extension (expr : 'expr Grammar.Entry.e)
      (Some (Gramext.After "apply"))
      [Some "label", Some Gramext.NonA,
       [Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_token ("QUESTIONIDENT", "")),
           (fun (i : string) (loc : Ploc.t) ->
              (let _ = warning_deprecated_since_6_00 loc in
               MLast.ExOlb (loc, MLast.PaLid (loc, i), None) :
               'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop
                (Grammar.s_token ("QUESTIONIDENTCOLON", "")))
             Grammar.s_self,
           (fun (e : 'expr) (i : string) (loc : Ploc.t) ->
              (let _ = warning_deprecated_since_6_00 loc in
               MLast.ExOlb (loc, MLast.PaLid (loc, i), Some e) :
               'expr)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop (Grammar.s_token ("TILDEIDENT", "")),
           (fun (i : string) (loc : Ploc.t) ->
              (let _ = warning_deprecated_since_6_00 loc in
               MLast.ExLab (loc, [MLast.PaLid (loc, i), None]) :
               'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop
                (Grammar.s_token ("TILDEIDENTCOLON", "")))
             Grammar.s_self,
           (fun (e : 'expr) (i : string) (loc : Ploc.t) ->
              (let _ = warning_deprecated_since_6_00 loc in
               MLast.ExLab (loc, [MLast.PaLid (loc, i), Some e]) :
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
                (Grammar.s_opt
                   (Grammar.s_nterm
                      (fun_binding : 'fun_binding Grammar.Entry.e))))
             (Grammar.s_token ("", "}")),
           (fun _ (eo : 'fun_binding option) (p : 'ipatt_tcon) _ _
                (loc : Ploc.t) ->
              (MLast.ExOlb (loc, p, eo) : 'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "~")))
                   (Grammar.s_token ("", "{")))
                (Grammar.s_list1sep
                   (Grammar.s_nterm
                      (ipatt_tcon_fun_binding :
                       'ipatt_tcon_fun_binding Grammar.Entry.e))
                   (Grammar.s_token ("", ";")) false))
             (Grammar.s_token ("", "}")),
           (fun _ (lpeo : 'ipatt_tcon_fun_binding list) _ _ (loc : Ploc.t) ->
              (MLast.ExLab (loc, lpeo) : 'expr)))]];
    Grammar.extension
      (ipatt_tcon_fun_binding : 'ipatt_tcon_fun_binding Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop
                (Grammar.s_nterm (ipatt_tcon : 'ipatt_tcon Grammar.Entry.e)))
             (Grammar.s_opt
                (Grammar.s_nterm
                   (fun_binding : 'fun_binding Grammar.Entry.e))),
           (fun (eo : 'fun_binding option) (p : 'ipatt_tcon) (loc : Ploc.t) ->
              (p, eo : 'ipatt_tcon_fun_binding)))]];
    Grammar.extension (expr : 'expr Grammar.Entry.e)
      (Some (Gramext.Level "simple"))
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "`")))
             (Grammar.s_nterm (ident : 'ident Grammar.Entry.e)),
           (fun (s : 'ident) _ (loc : Ploc.t) ->
              (MLast.ExVrn (loc, s) : 'expr)))]];
    (* -- cut 1 begin -- *)
    Grammar.extension (expr : 'expr Grammar.Entry.e) None [None, None, []]]);;

(* -- cut 2 end -- *)
(* -- end copy from pa_r to q_MLast -- *)

let quotation_content s =
  let rec loop i =
    if i = String.length s then "", s
    else if s.[i] = ':' || s.[i] = '@' then
      let i = i + 1 in String.sub s 0 i, String.sub s i (String.length s - i)
    else loop (i + 1)
  in
  loop 0
;;

Grammar.safe_extend
  (let _ = (interf : 'interf Grammar.Entry.e)
   and _ = (implem : 'implem Grammar.Entry.e)
   and _ = (use_file : 'use_file Grammar.Entry.e)
   and _ = (top_phrase : 'top_phrase Grammar.Entry.e)
   and _ = (expr : 'expr Grammar.Entry.e)
   and _ = (patt : 'patt Grammar.Entry.e) in
   let grammar_entry_create s =
     Grammar.create_local_entry (Grammar.of_entry interf) s
   in
   let sig_item_semi : 'sig_item_semi Grammar.Entry.e =
     grammar_entry_create "sig_item_semi"
   and str_item_semi : 'str_item_semi Grammar.Entry.e =
     grammar_entry_create "str_item_semi"
   and phrase : 'phrase Grammar.Entry.e = grammar_entry_create "phrase" in
   [Grammar.extension (interf : 'interf Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next Grammar.r_stop (Grammar.s_token ("EOI", "")),
           (fun _ (loc : Ploc.t) -> ([], Some loc : 'interf)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop
                (Grammar.s_nterm
                   (sig_item_semi : 'sig_item_semi Grammar.Entry.e)))
             Grammar.s_self,
           (fun (sil, stopped : 'interf) (si : 'sig_item_semi)
                (loc : Ploc.t) ->
              (si :: sil, stopped : 'interf)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "#")))
                   (Grammar.s_token ("LIDENT", "")))
                (Grammar.s_opt
                   (Grammar.s_nterm (expr : 'expr Grammar.Entry.e))))
             (Grammar.s_token ("", ";")),
           (fun _ (dp : 'expr option) (n : string) _ (loc : Ploc.t) ->
              ([MLast.SgDir (loc, n, dp), loc], None : 'interf)))]];
    Grammar.extension (sig_item_semi : 'sig_item_semi Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop
                (Grammar.s_nterm (sig_item : 'sig_item Grammar.Entry.e)))
             (Grammar.s_token ("", ";")),
           (fun _ (si : 'sig_item) (loc : Ploc.t) ->
              (si, loc : 'sig_item_semi)))]];
    Grammar.extension (implem : 'implem Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next Grammar.r_stop (Grammar.s_token ("EOI", "")),
           (fun _ (loc : Ploc.t) -> ([], Some loc : 'implem)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop
                (Grammar.s_nterm
                   (str_item_semi : 'str_item_semi Grammar.Entry.e)))
             Grammar.s_self,
           (fun (sil, stopped : 'implem) (si : 'str_item_semi)
                (loc : Ploc.t) ->
              (si :: sil, stopped : 'implem)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "#")))
                   (Grammar.s_token ("LIDENT", "")))
                (Grammar.s_opt
                   (Grammar.s_nterm (expr : 'expr Grammar.Entry.e))))
             (Grammar.s_token ("", ";")),
           (fun _ (dp : 'expr option) (n : string) _ (loc : Ploc.t) ->
              ([MLast.StDir (loc, n, dp), loc], None : 'implem)))]];
    Grammar.extension (str_item_semi : 'str_item_semi Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop
                (Grammar.s_nterm (str_item : 'str_item Grammar.Entry.e)))
             (Grammar.s_token ("", ";")),
           (fun _ (si : 'str_item) (loc : Ploc.t) ->
              (si, loc : 'str_item_semi)))]];
    Grammar.extension (top_phrase : 'top_phrase Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next Grammar.r_stop (Grammar.s_token ("EOI", "")),
           (fun _ (loc : Ploc.t) -> (None : 'top_phrase)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_nterm (phrase : 'phrase Grammar.Entry.e)),
           (fun (ph : 'phrase) (loc : Ploc.t) -> (Some ph : 'top_phrase)))]];
    Grammar.extension (use_file : 'use_file Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next Grammar.r_stop (Grammar.s_token ("EOI", "")),
           (fun _ (loc : Ploc.t) -> ([], false : 'use_file)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop
                   (Grammar.s_nterm (str_item : 'str_item Grammar.Entry.e)))
                (Grammar.s_token ("", ";")))
             Grammar.s_self,
           (fun (sil, stopped : 'use_file) _ (si : 'str_item)
                (loc : Ploc.t) ->
              (si :: sil, stopped : 'use_file)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "#")))
                   (Grammar.s_token ("LIDENT", "")))
                (Grammar.s_opt
                   (Grammar.s_nterm (expr : 'expr Grammar.Entry.e))))
             (Grammar.s_token ("", ";")),
           (fun _ (dp : 'expr option) (n : string) _ (loc : Ploc.t) ->
              ([MLast.StDir (loc, n, dp)], true : 'use_file)))]];
    Grammar.extension (phrase : 'phrase Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop
                (Grammar.s_nterm (str_item : 'str_item Grammar.Entry.e)))
             (Grammar.s_token ("", ";")),
           (fun _ (sti : 'str_item) (loc : Ploc.t) -> (sti : 'phrase)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "#")))
                   (Grammar.s_token ("LIDENT", "")))
                (Grammar.s_opt
                   (Grammar.s_nterm (expr : 'expr Grammar.Entry.e))))
             (Grammar.s_token ("", ";")),
           (fun _ (dp : 'expr option) (n : string) _ (loc : Ploc.t) ->
              (MLast.StDir (loc, n, dp) : 'phrase)))]];
    Grammar.extension (expr : 'expr Grammar.Entry.e)
      (Some (Gramext.Level "simple"))
      [None, None,
       [Grammar.production
          (Grammar.r_next Grammar.r_stop (Grammar.s_token ("QUOTATION", "")),
           (fun (x : string) (loc : Ploc.t) ->
              (let con = quotation_content x in
               Pcaml.handle_expr_quotation loc con :
               'expr)))]];
    Grammar.extension (patt : 'patt Grammar.Entry.e)
      (Some (Gramext.Level "simple"))
      [None, None,
       [Grammar.production
          (Grammar.r_next Grammar.r_stop (Grammar.s_token ("QUOTATION", "")),
           (fun (x : string) (loc : Ploc.t) ->
              (let con = quotation_content x in
               Pcaml.handle_patt_quotation loc con :
               'patt)))]]]);;
