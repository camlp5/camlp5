(* camlp5r *)
(* pa_r.ml,v *)
(* Copyright (c) INRIA 2007-2017 *)

(* #load "pa_extend.cmo" *)
(* #load "q_MLast.cmo" *)
(* #load "pa_macro.cmo" *)
(* #load "pa_macro_gram.cmo" *)

open Asttools;;
open Pcaml;;
open Mlsyntax.Revised;;

Pcaml.syntax_name := "Revised";;
Pcaml.no_constructors_arity := false;;

let odfa = !(Plexer.dollar_for_antiquotation) in
let osrs = !(Plexer.simplest_raw_strings) in
Plexer.dollar_for_antiquotation := false;
Plexer.simplest_raw_strings := false;
Plexer.utf8_lexing := true;
Grammar.Unsafe.gram_reinit gram (Plexer.gmake ());
Plexer.dollar_for_antiquotation := odfa;
Plexer.simplest_raw_strings := osrs;
Grammar.Unsafe.clear_entry attribute_body;
Grammar.Unsafe.clear_entry interf;
Grammar.Unsafe.clear_entry implem;
Grammar.Unsafe.clear_entry top_phrase;
Grammar.Unsafe.clear_entry use_file;
Grammar.Unsafe.clear_entry functor_parameter;
Grammar.Unsafe.clear_entry module_type;
Grammar.Unsafe.clear_entry longident;
Grammar.Unsafe.clear_entry longident_lident;
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
Grammar.Unsafe.clear_entry class_expr_simple;
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
        | None -> MLast.ExLong (loc, MLast.LiUid (loc, "[]"))
        end
    | e1 :: el ->
        let loc = if top then loc else Ploc.encl (MLast.loc_of_expr e1) loc in
        MLast.ExApp
          (loc,
           MLast.ExApp (loc, MLast.ExLong (loc, MLast.LiUid (loc, "::")), e1),
           loop false el)
  in
  loop true
;;

let mklistpat loc last =
  let rec loop top =
    function
      [] ->
        begin match last with
          Some p -> p
        | None -> MLast.PaLong (loc, MLast.LiUid (loc, "[]"), [])
        end
    | p1 :: pl ->
        let loc = if top then loc else Ploc.encl (MLast.loc_of_patt p1) loc in
        MLast.PaApp
          (loc,
           MLast.PaApp
             (loc, MLast.PaLong (loc, MLast.LiUid (loc, "::"), []), p1),
           loop false pl)
  in
  loop true
;;

let operator_rparen_f strm =
  let id x = x in
  let app suff s = s ^ suff in
  let trials =
    [1,
     Right
       (function
          (("LIDENT" | "UIDENT"), _) :: _ -> true
        | _ -> false);
     2, Left (is_operator, id, [["", ")"]]);
     2, Left (is_letop, id, [["", ")"]]); 2, Left (is_andop, id, [["", ")"]]);
     4, Left (is_dotop, app "()", [["", "("; "", ")"; "", ")"]]);
     4, Left (is_dotop, app "{}", [["", "{"; "", "}"; "", ")"]]);
     4, Left (is_dotop, app "[]", [["", "["; "", "]"; "", ")"]]);
     6,
     Left
       (is_dotop, app "(;..)",
        [["", "("; "", ";"; "", ".."; "", ")"; "", ")"]]);
     6,
     Left
       (is_dotop, app "{;..}",
        [["", "{"; "", ";"; "", ".."; "", "}"; "", ")"]]);
     6,
     Left
       (is_dotop, app "[;..]",
        [["", "["; "", ";"; "", ".."; "", "]"; "", ")"]]);
     5, Left (is_dotop, app "()<-", [["", "("; "", ")"; "", "<-"; "", ")"]]);
     5, Left (is_dotop, app "{}<-", [["", "{"; "", "}"; "", "<-"; "", ")"]]);
     5, Left (is_dotop, app "[]<-", [["", "["; "", "]"; "", "<-"; "", ")"]]);
     7,
     Left
       (is_dotop, app "(;..)<-",
        [["", "("; "", ";"; "", ".."; "", ")"; "", "<-"; "", ")"]]);
     7,
     Left
       (is_dotop, app "{;..}<-",
        [["", "{"; "", ";"; "", ".."; "", "}"; "", "<-"; "", ")"]]);
     7,
     Left
       (is_dotop, app "[;..]<-",
        [["", "["; "", ";"; "", ".."; "", "]"; "", "<-"; "", ")"]])]
  in
  let matchers =
    List.map
      (function
         n, Left (pred, xform, suffixes) ->
           n,
           Left
             (function
                ("", s) :: l when pred s && List.mem l suffixes ->
                  Some (xform s)
              | _ -> None)
       | n, Right f -> n, Right f)
      trials
  in
  let (n, tok) = check_stream matchers strm in
  for i = 1 to n do Stream.junk strm done; tok
;;

let operator_rparen =
  Grammar.Entry.of_parser gram "operator_rparen" operator_rparen_f
;;

let check_not_part_of_patt_f strm =
  let matchers =
    [2,
     (function
        ("LIDENT", _) :: tok :: _ -> Some tok
      | _ -> None);
     4,
     (function
        ("", "(") :: ("", s) :: ("", ")") :: tok :: _ when is_special_op s ->
          Some tok
      | _ -> None);
     6,
     (function
        ("", "(") :: ("", s) :: ("", "(") :: ("", ")") :: ("", ")") :: tok ::
        _
        when is_special_op s ->
          Some tok
      | ("", "(") :: ("", s) :: ("", "{") :: ("", "}") :: ("", ")") :: tok ::
        _
        when is_special_op s ->
          Some tok
      | ("", "(") :: ("", s) :: ("", "[") :: ("", "]") :: ("", ")") :: tok ::
        _
        when is_special_op s ->
          Some tok
      | _ -> None);
     7,
     (function
        ("", "(") :: ("", s) :: ("", "(") :: ("", ")") :: ("", "<-") ::
        ("", ")") :: tok :: _
        when is_special_op s ->
          Some tok
      | ("", "(") :: ("", s) :: ("", "{") :: ("", "}") :: ("", "<-") ::
        ("", ")") :: tok :: _
        when is_special_op s ->
          Some tok
      | ("", "(") :: ("", s) :: ("", "[") :: ("", "]") :: ("", "<-") ::
        ("", ")") :: tok :: _
        when is_special_op s ->
          Some tok
      | _ -> None);
     8,
     (function
        ("", "(") :: ("", s) :: ("", "(") :: ("", ";") :: ("", "..") ::
        ("", ")") :: ("", ")") :: tok :: _
        when is_special_op s ->
          Some tok
      | ("", "(") :: ("", s) :: ("", "{") :: ("", ";") :: ("", "..") ::
        ("", "}") :: ("", ")") :: tok :: _
        when is_special_op s ->
          Some tok
      | ("", "(") :: ("", s) :: ("", "[") :: ("", ";") :: ("", "..") ::
        ("", "]") :: ("", ")") :: tok :: _
        when is_special_op s ->
          Some tok
      | _ -> None);
     9,
     (function
        ("", "(") :: ("", s) :: ("", "(") :: ("", ";") :: ("", "..") ::
        ("", ")") :: ("", "<-") :: ("", ")") :: tok :: _
        when is_special_op s ->
          Some tok
      | ("", "(") :: ("", s) :: ("", "{") :: ("", ";") :: ("", "..") ::
        ("", "}") :: ("", "<-") :: ("", ")") :: tok :: _
        when is_special_op s ->
          Some tok
      | ("", "(") :: ("", s) :: ("", "[") :: ("", ";") :: ("", "..") ::
        ("", "]") :: ("", "<-") :: ("", ")") :: tok :: _
        when is_special_op s ->
          Some tok
      | _ -> None)]
  in
  let rec crec i =
    function
      (n, _) :: _ as ml when i < n ->
        let l = stream_npeek i strm in
        let last = fst (sep_last l) in
        if last = ("EOI", "") || last = ("", ";;") then raise Stream.Failure
        else crec (i + 1) ml
    | (n, f) :: t ->
        begin match f (stream_npeek n strm) with
          None -> crec (i + 1) t
        | Some tok -> tok
        end
    | [] -> raise Stream.Failure
  in
  let tok = crec 1 matchers in
  match tok with
    "", ("," | "as" | "|" | "::") -> raise Stream.Failure
  | _ -> ()
;;

let check_not_part_of_patt =
  Grammar.Entry.of_parser gram "check_not_part_of_patt"
    check_not_part_of_patt_f
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

let dotop =
  Grammar.Entry.of_parser gram "dotop"
    (fun (strm__ : _ Stream.t) ->
       match Stream.peek strm__ with
         Some ("", x) when is_dotop x -> Stream.junk strm__; x
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

let check_let_exception_f strm =
  match Stream.npeek 2 strm with
    ["", "let"; "", "exception"] -> ()
  | _ -> raise Stream.Failure
;;

let check_let_exception =
  Grammar.Entry.of_parser gram "check_let_exception" check_let_exception_f
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
  try check (Stream.of_string s) && s <> "_" with
    Stream.Failure | Stream.Error _ -> false
;;

let is_type_decl_not_extension strm =
  let rec wrec n =
    match stream_peek_nth n strm with
      None -> assert false
    | Some ("", "=" | "", ":=" | "", ";" | "", ";;") -> true
    | Some ("", s) when word_keywordp s -> true
    | Some ("EOI", "") -> true
    | Some ("", "+=") -> false
    | Some
        ("", _ | "UIDENT", _ | "LIDENT", _ | "GIDENT", _ | "ANTIQUOT", _) ->
        wrec (n + 1)
    | Some ("ANTIQUOT_LOC", s)
      when
        match Plexer.parse_antiloc s with
          Some
            (_, ("list" | "_list" | "lid" | "_lid" | "flag" | "_flag"), _) ->
            true
        | _ -> false ->
        wrec (n + 1)
    | Some ("ANTIQUOT_LOC", s)
      when
        match Plexer.parse_antiloc s with
          Some (_, ("lilongid" | "_lilongid"), _) -> true
        | _ -> false ->
        false
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
  let rec crec n =
    match stream_npeek n strm with
      (_, tok) :: _ when tok <> "." -> raise Stream.Failure
    | ["", "."] -> crec (n + 1)
    | ["", "."; "UIDENT", _] -> ()
    | ["", "."; "ANTIQUOT_LOC", s]
      when
        match Plexer.parse_antiloc s with
          Some (_, ("uid" | "_uid"), _) -> true
        | _ -> false ->
        ()
    | ["", "."; "", "$"] -> crec (n + 1)
    | ["", "."; "", "$"; "LIDENT", ("uid" | "_uid")] -> crec (n + 1)
    | ["", "."; "", "$"; "LIDENT", ("uid" | "_uid"); "", ":"] -> ()
    | _ -> raise Stream.Failure
  in
  crec 1
;;

let check_dot_uid =
  Grammar.Entry.of_parser gram "check_dot_uid" check_dot_uid_f
;;

let is_lbracket_f strm =
  match Stream.npeek 1 strm with
    ["", "["] -> true
  | _ -> false
;;

let check_lbracket_f strm =
  if is_lbracket_f strm then () else raise Stream.Failure
;;

let check_lbracket =
  Grammar.Entry.of_parser gram "check_lbracket" check_lbracket_f
;;

let is_lbracketbar_f strm =
  match Stream.npeek 1 strm with
    ["", "[|"] -> true
  | _ -> false
;;

let check_lbracketbar_f strm =
  if is_lbracketbar_f strm then () else raise Stream.Failure
;;

let check_lbracketbar =
  Grammar.Entry.of_parser gram "check_lbracketbar" check_lbracketbar_f
;;


let is_lbrace_f strm =
  match Stream.npeek 1 strm with
    ["", "{"] -> true
  | _ -> false
;;

let check_lbrace_f strm =
  if is_lbrace_f strm then () else raise Stream.Failure
;;

let check_lbrace =
  Grammar.Entry.of_parser gram "check_lbrace" check_lbrace_f
;;

let is_lident_colon_f strm =
  match Stream.npeek 2 strm with
    ("LIDENT", _) :: ("", ":") :: _ -> true
  | _ -> false
;;

let check_lident_colon_f strm =
  if is_lident_colon_f strm then () else raise Stream.Failure
;;

let check_lident_colon =
  Grammar.Entry.of_parser gram "check_lident_colon" check_lident_colon_f
;;

let check_not_lident_colon_f strm =
  if not (is_lident_colon_f strm) then () else raise Stream.Failure
;;

let check_not_lident_colon =
  Grammar.Entry.of_parser gram "check_not_lident_colon"
    check_not_lident_colon_f
;;

let check_uident_coloneq_f strm =
  match stream_npeek 2 strm with
    ["UIDENT", _; "", ":="] -> ()
  | ["ANTIQUOT", qs; "", ":="]
    when prefix_eq "uid:" qs || prefix_eq "_uid:" qs ->
      ()
  | ("ANTIQUOT_LOC", s) :: ("", ":=") :: _
    when
      match Plexer.parse_antiloc s with
        Some (_, ("uid" | "_uid"), _) -> true
      | _ -> false ->
      ()
  | _ -> raise Stream.Failure
;;

let check_uident_coloneq =
  Grammar.Entry.of_parser gram "check_uident_coloneq" check_uident_coloneq_f
;;

let check_colon_f strm =
  match stream_npeek 1 strm with
    ["", ":"] -> ()
  | _ -> raise Stream.Failure
;;

let check_colon = Grammar.Entry.of_parser gram "check_colon" check_colon_f;;

let check_not_colon_f strm =
  match stream_npeek 1 strm with
    ["", ":"] -> raise Stream.Failure
  | _ -> ()
;;

let check_not_colon =
  Grammar.Entry.of_parser gram "check_not_colon" check_not_colon_f
;;

let test_label_eq =
  Grammar.Entry.of_parser gram "test_label_eq"
    (let rec test lev strm =
       match stream_peek_nth lev strm with
         Some ("UIDENT", _ | "LIDENT", _ | "", ".") -> test (lev + 1) strm
       | Some ("ANTIQUOT_LOC", _) -> ()
       | Some ("", ("=" | ";" | "}" | ":")) -> ()
       | _ -> raise Stream.Failure
     in
     test 1)
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
  | Some attrid -> MLast.StExten (loc, (attrid, MLast.StAttr (loc, [si])), [])
;;

let is_lparen_f strm =
  match Stream.npeek 1 strm with
    ["", "("] -> true
  | _ -> false
;;

let is_lparen_type_f strm =
  is_lparen_f strm &&
  (match Stream.npeek 2 strm with
     ["", "("; "", "type"] -> true
   | _ -> false)
;;

let check_lparen_type_f strm =
  if is_lparen_type_f strm then () else raise Stream.Failure
;;

let check_lparen_type =
  Grammar.Entry.of_parser gram "check_lparen_type" check_lparen_type_f
;;

let is_type_binder_f strm = check_fsm type_binder_fsm strm;;

let check_type_binder_f strm =
  if is_type_binder_f strm then () else raise Stream.Failure
;;

let check_type_binder =
  Grammar.Entry.of_parser gram "check_type_binder" check_type_binder_f
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
   and _ = (longident : 'longident Grammar.Entry.e)
   and _ = (longident_lident : 'longident_lident Grammar.Entry.e)
   and _ = (extended_longident : 'extended_longident Grammar.Entry.e)
   and _ = (signature : 'signature Grammar.Entry.e)
   and _ = (structure : 'structure Grammar.Entry.e)
   and _ = (class_type : 'class_type Grammar.Entry.e)
   and _ = (class_expr : 'class_expr Grammar.Entry.e)
   and _ = (class_expr_simple : 'class_expr_simple Grammar.Entry.e)
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
   and _ = (check_type_binder : 'check_type_binder Grammar.Entry.e)
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
   and type_binder_opt : 'type_binder_opt Grammar.Entry.e =
     grammar_entry_create "type_binder_opt"
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
   and expr_longident : 'expr_longident Grammar.Entry.e =
     grammar_entry_create "expr_longident"
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
   and patt_ident : 'patt_ident Grammar.Entry.e =
     grammar_entry_create "patt_ident"
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
   and rest_constructor_declaration : 'rest_constructor_declaration Grammar.Entry.e =
     grammar_entry_create "rest_constructor_declaration"
   and ident : 'ident Grammar.Entry.e = grammar_entry_create "ident"
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
   and extended_longident_lident : 'extended_longident_lident Grammar.Entry.e =
     grammar_entry_create "extended_longident_lident"
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
          (Grammar.r_next Grammar.r_stop (Grammar.s_token ("STRING", "")),
           "194fe98d",
           (fun (s : string) (loc : Ploc.t) -> (loc, s : 'attribute_id)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_list1sep
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("UIDENT", "")),
                       "194fe98d",
                       (fun (i : string) (loc : Ploc.t) -> (i : 'e__1)));
                    Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("LIDENT", "")),
                       "194fe98d",
                       (fun (i : string) (loc : Ploc.t) -> (i : 'e__1)))])
                (Grammar.s_token ("", ".")) false),
           "194fe98d",
           (fun (l : 'e__1 list) (loc : Ploc.t) ->
              (loc, String.concat "." l : 'attribute_id)))]];
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
                       "194fe98d",
                       (fun _ (s : 'str_item) (loc : Ploc.t) ->
                          (s : 'e__2)))])),
           "194fe98d",
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
                       "194fe98d",
                       (fun _ (s : 'sig_item) (loc : Ploc.t) ->
                          (s : 'e__3)))])),
           "194fe98d",
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
           "194fe98d",
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
           "194fe98d",
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
           "194fe98d",
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
           "194fe98d",
           (fun (si : 'attribute_signature) _ (id : 'attribute_id)
                (loc : Ploc.t) ->
              (id, MLast.SiAttr (loc, si) : 'attribute_body)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_nterm (attribute_id : 'attribute_id Grammar.Entry.e)),
           "194fe98d",
           (fun (id : 'attribute_id) (loc : Ploc.t) ->
              (id, MLast.StAttr (loc, []) : 'attribute_body)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop
                (Grammar.s_nterm
                   (attribute_id : 'attribute_id Grammar.Entry.e)))
             (Grammar.s_nterm
                (attribute_structure : 'attribute_structure Grammar.Entry.e)),
           "194fe98d",
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
           "194fe98d",
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
           "194fe98d",
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
           "194fe98d",
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
           "194fe98d",
           (fun (l : 'item_attribute list) (loc : Ploc.t) ->
              (l : 'item_attributes)))]];
    Grammar.extension (alg_attributes : 'alg_attributes Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_list0
                (Grammar.s_nterm
                   (alg_attribute : 'alg_attribute Grammar.Entry.e))),
           "194fe98d",
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
           "194fe98d",
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
           "194fe98d",
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
           "194fe98d",
           (fun _ (e : 'attribute_body) _ (loc : Ploc.t) ->
              (e : 'alg_extension)))]];
    Grammar.extension (functor_parameter : 'functor_parameter Grammar.Entry.e)
      None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "(")))
             (Grammar.s_token ("", ")")),
           "194fe98d",
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
           "194fe98d",
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
           "194fe98d",
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
           "194fe98d",
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
           "194fe98d",
           (fun _ (st : 'structure) _ (loc : Ploc.t) ->
              (MLast.MeStr (loc, st) : 'module_expr)))];
       None, None,
       [Grammar.production
          (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
             Grammar.s_self,
           "194fe98d",
           (fun (me2 : 'module_expr) (me1 : 'module_expr) (loc : Ploc.t) ->
              (MLast.MeApp (loc, me1, me2) : 'module_expr)))];
       None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                (Grammar.s_token ("", ".")))
             Grammar.s_self,
           "194fe98d",
           (fun (me2 : 'module_expr) _ (me1 : 'module_expr) (loc : Ploc.t) ->
              (MLast.MeAcc (loc, me1, me2) : 'module_expr)))];
       Some "simple", None,
       [Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_nterm
                (alg_extension : 'alg_extension Grammar.Entry.e)),
           "194fe98d",
           (fun (e : 'alg_extension) (loc : Ploc.t) ->
              (MLast.MeExten (loc, e) : 'module_expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "(")))
                Grammar.s_self)
             (Grammar.s_token ("", ")")),
           "194fe98d",
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
           "194fe98d",
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
           "194fe98d",
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
           "194fe98d",
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
           "194fe98d",
           (fun _ (mt2 : 'module_type) _ (mt1 : 'module_type) _ (e : 'expr) _
                _ (loc : Ploc.t) ->
              (MLast.MeUnp (loc, e, Some mt1, Some mt2) : 'module_expr)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop (Grammar.s_token ("UIDENT", "")),
           "194fe98d",
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
                       "194fe98d",
                       (fun _ (s : 'str_item) (loc : Ploc.t) ->
                          (s : 'e__4)))])),
           "194fe98d",
           (fun (st : 'e__4 list) (loc : Ploc.t) -> (st : 'structure)))]];
    Grammar.extension (type_binder_opt : 'type_binder_opt Grammar.Entry.e)
      None
      [None, None,
       [Grammar.production
          (Grammar.r_stop, "194fe98d",
           (fun (loc : Ploc.t) -> ([] : 'type_binder_opt)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop
                   (Grammar.s_nterm
                      (check_type_binder :
                       'check_type_binder Grammar.Entry.e)))
                (Grammar.s_list1
                   (Grammar.s_nterm (typevar : 'typevar Grammar.Entry.e))))
             (Grammar.s_token ("", ".")),
           "194fe98d",
           (fun _ (ls : 'typevar list) _ (loc : Ploc.t) ->
              (ls : 'type_binder_opt)))]];
    Grammar.extension (str_item : 'str_item Grammar.Entry.e) None
      [Some "top", None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop
                (Grammar.s_nterm
                   (item_extension : 'item_extension Grammar.Entry.e)))
             (Grammar.s_nterm
                (item_attributes : 'item_attributes Grammar.Entry.e)),
           "194fe98d",
           (fun (attrs : 'item_attributes) (e : 'item_extension)
                (loc : Ploc.t) ->
              (MLast.StExten (loc, e, attrs) : 'str_item)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_nterm
                (floating_attribute : 'floating_attribute Grammar.Entry.e)),
           "194fe98d",
           (fun (attr : 'floating_attribute) (loc : Ploc.t) ->
              (MLast.StFlAtt (loc, attr) : 'str_item)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop
                (Grammar.s_nterm (expr : 'expr Grammar.Entry.e)))
             (Grammar.s_nterm
                (item_attributes : 'item_attributes Grammar.Entry.e)),
           "194fe98d",
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
                       "194fe98d",
                       (fun (si : 'str_item) (loc : Ploc.t) ->
                          (si, loc : 'e__6)))])),
           "194fe98d",
           (fun (sil : 'e__6 list) (s : string) _ (loc : Ploc.t) ->
              (MLast.StUse (loc, s, sil) : 'str_item)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "#")))
                (Grammar.s_token ("LIDENT", "")))
             (Grammar.s_opt (Grammar.s_nterm (expr : 'expr Grammar.Entry.e))),
           "194fe98d",
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
           "194fe98d",
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
           "194fe98d",
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
           "194fe98d",
           (fun (tdl : 'type_decl list) (nrfl : bool) _ _ (loc : Ploc.t) ->
              (vala_it
                 (fun tdl ->
                    if List.exists
                         (fun td -> not (Pcaml.unvala td.MLast.tdIsDecl)) tdl
                    then
                      failwith "type-declaration cannot mix decl and subst")
                 tdl;
               MLast.StTyp (loc, nrfl, tdl) :
               'str_item)));
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
           "194fe98d",
           (fun (attrs : 'item_attributes) (me : 'module_expr) (ovf : bool) _
                (loc : Ploc.t) ->
              (MLast.StOpn (loc, ovf, me, attrs) : 'str_item)));
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
           "194fe98d",
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
           "194fe98d",
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
           "194fe98d",
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
                               (Grammar.r_next
                                  (Grammar.r_next Grammar.r_stop
                                     (Grammar.s_token ("", "external")))
                                  (Grammar.s_token ("", "(")))
                               (Grammar.s_nterm
                                  (operator_rparen :
                                   'operator_rparen Grammar.Entry.e)))
                            (Grammar.s_token ("", ":")))
                         (Grammar.s_nterm
                            (type_binder_opt :
                             'type_binder_opt Grammar.Entry.e)))
                      (Grammar.s_nterm (ctyp : 'ctyp Grammar.Entry.e)))
                   (Grammar.s_token ("", "=")))
                (Grammar.s_list1 (Grammar.s_token ("STRING", ""))))
             (Grammar.s_nterm
                (item_attributes : 'item_attributes Grammar.Entry.e)),
           "194fe98d",
           (fun (attrs : 'item_attributes) (pd : string list) _ (t : 'ctyp)
                (ls : 'type_binder_opt) _ (i : 'operator_rparen) _ _
                (loc : Ploc.t) ->
              (MLast.StExt (loc, i, ls, t, pd, attrs) : 'str_item)));
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
                               (Grammar.s_token ("LIDENT", "")))
                            (Grammar.s_token ("", ":")))
                         (Grammar.s_nterm
                            (type_binder_opt :
                             'type_binder_opt Grammar.Entry.e)))
                      (Grammar.s_nterm (ctyp : 'ctyp Grammar.Entry.e)))
                   (Grammar.s_token ("", "=")))
                (Grammar.s_list1 (Grammar.s_token ("STRING", ""))))
             (Grammar.s_nterm
                (item_attributes : 'item_attributes Grammar.Entry.e)),
           "194fe98d",
           (fun (attrs : 'item_attributes) (pd : string list) _ (t : 'ctyp)
                (ls : 'type_binder_opt) _ (i : string) _ (loc : Ploc.t) ->
              (MLast.StExt (loc, i, ls, t, pd, attrs) : 'str_item)));
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
           "194fe98d",
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
                          "194fe98d",
                          (fun _ (s : 'str_item) (loc : Ploc.t) ->
                             (s : 'e__5)))])))
             (Grammar.s_token ("", "end")),
           "194fe98d",
           (fun _ (st : 'e__5 list) _ (loc : Ploc.t) ->
              (MLast.StDcl (loc, st) : 'str_item)))]];
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
           "194fe98d",
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
           "194fe98d",
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
           "194fe98d",
           (fun (me : 'module_expr) _ (mt : 'module_type) _ (loc : Ploc.t) ->
              (MLast.MeTyc (loc, me, mt) : 'mod_fun_binding)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop
                (Grammar.s_nterm
                   (functor_parameter : 'functor_parameter Grammar.Entry.e)))
             Grammar.s_self,
           "194fe98d",
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
           "194fe98d",
           (fun (mt : 'module_type) _ (arg : 'functor_parameter) _
                (loc : Ploc.t) ->
              (MLast.MtFun (loc, arg, mt) : 'module_type)))];
       Some "->", Some Gramext.RightA,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                (Grammar.s_token ("", "->")))
             Grammar.s_self,
           "194fe98d",
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
           "194fe98d",
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
           "194fe98d",
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
           "194fe98d",
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
           "194fe98d",
           (fun _ (sg : 'signature) _ (loc : Ploc.t) ->
              (MLast.MtSig (loc, sg) : 'module_type)))];
       Some "simple", None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "(")))
                Grammar.s_self)
             (Grammar.s_token ("", ")")),
           "194fe98d",
           (fun _ (mt : 'module_type) _ (loc : Ploc.t) ->
              (mt : 'module_type)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "'")))
             (Grammar.s_nterm (ident : 'ident Grammar.Entry.e)),
           "194fe98d",
           (fun (i : 'ident) _ (loc : Ploc.t) ->
              (MLast.MtQuo (loc, i) : 'module_type)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_nterm
                (alg_extension : 'alg_extension Grammar.Entry.e)),
           "194fe98d",
           (fun (e : 'alg_extension) (loc : Ploc.t) ->
              (MLast.MtExten (loc, e) : 'module_type)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop (Grammar.s_token ("LIDENT", "")),
           "194fe98d",
           (fun (i : string) (loc : Ploc.t) ->
              (MLast.MtLid (loc, i) : 'module_type)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_nterm
                (extended_longident : 'extended_longident Grammar.Entry.e)),
           "194fe98d",
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
           "194fe98d",
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
                       "194fe98d",
                       (fun _ (s : 'sig_item) (loc : Ploc.t) ->
                          (s : 'e__7)))])),
           "194fe98d",
           (fun (st : 'e__7 list) (loc : Ploc.t) -> (st : 'signature)))]];
    Grammar.extension (sig_item : 'sig_item Grammar.Entry.e) None
      [Some "top", None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop
                (Grammar.s_nterm
                   (item_extension : 'item_extension Grammar.Entry.e)))
             (Grammar.s_nterm
                (item_attributes : 'item_attributes Grammar.Entry.e)),
           "194fe98d",
           (fun (attrs : 'item_attributes) (e : 'item_extension)
                (loc : Ploc.t) ->
              (MLast.SgExten (loc, e, attrs) : 'sig_item)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_nterm
                (floating_attribute : 'floating_attribute Grammar.Entry.e)),
           "194fe98d",
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
                       "194fe98d",
                       (fun (si : 'sig_item) (loc : Ploc.t) ->
                          (si, loc : 'e__9)))])),
           "194fe98d",
           (fun (sil : 'e__9 list) (s : string) _ (loc : Ploc.t) ->
              (MLast.SgUse (loc, s, sil) : 'sig_item)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "#")))
                (Grammar.s_token ("LIDENT", "")))
             (Grammar.s_opt (Grammar.s_nterm (expr : 'expr Grammar.Entry.e))),
           "194fe98d",
           (fun (dp : 'expr option) (n : string) _ (loc : Ploc.t) ->
              (MLast.SgDir (loc, n, dp) : 'sig_item)));
        Grammar.production
          (Grammar.r_next
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
                   (Grammar.s_nterm
                      (type_binder_opt : 'type_binder_opt Grammar.Entry.e)))
                (Grammar.s_nterm (ctyp : 'ctyp Grammar.Entry.e)))
             (Grammar.s_nterm
                (item_attributes : 'item_attributes Grammar.Entry.e)),
           "194fe98d",
           (fun (attrs : 'item_attributes) (t : 'ctyp) (ls : 'type_binder_opt)
                _ (i : 'operator_rparen) _ _ (loc : Ploc.t) ->
              (let t =
                 match Pcaml.unvala ls with
                   [] -> t
                 | _ -> MLast.TyPol (loc, ls, t)
               in
               MLast.SgVal (loc, i, t, attrs) :
               'sig_item)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("", "value")))
                         (Grammar.s_token ("LIDENT", "")))
                      (Grammar.s_token ("", ":")))
                   (Grammar.s_nterm
                      (type_binder_opt : 'type_binder_opt Grammar.Entry.e)))
                (Grammar.s_nterm (ctyp : 'ctyp Grammar.Entry.e)))
             (Grammar.s_nterm
                (item_attributes : 'item_attributes Grammar.Entry.e)),
           "194fe98d",
           (fun (attrs : 'item_attributes) (t : 'ctyp) (ls : 'type_binder_opt)
                _ (i : string) _ (loc : Ploc.t) ->
              (let t =
                 match Pcaml.unvala ls with
                   [] -> t
                 | _ -> MLast.TyPol (loc, ls, t)
               in
               MLast.SgVal (loc, i, t, attrs) :
               'sig_item)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "type")))
                (Grammar.s_nterm
                   (check_type_extension :
                    'check_type_extension Grammar.Entry.e)))
             (Grammar.s_nterm
                (type_extension : 'type_extension Grammar.Entry.e)),
           "194fe98d",
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
           "194fe98d",
           (fun (tdl : 'type_decl list) (nrfl : bool) _ _ (loc : Ploc.t) ->
              (vala_it
                 (fun tdl ->
                    if List.for_all (fun td -> Pcaml.unvala td.MLast.tdIsDecl)
                         tdl
                    then
                      ()
                    else if
                      List.for_all
                        (fun td -> not (Pcaml.unvala td.MLast.tdIsDecl)) tdl
                    then
                      vala_it
                        (fun nrfl ->
                           if nrfl then
                             failwith
                               "type-subst declaration must not specify <<nonrec>>")
                        nrfl
                    else
                      failwith "type-declaration cannot mix decl and subst")
                 tdl;
               MLast.SgTyp (loc, nrfl, tdl) :
               'sig_item)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "open")))
                (Grammar.s_nterm
                   (extended_longident :
                    'extended_longident Grammar.Entry.e)))
             (Grammar.s_nterm
                (item_attributes : 'item_attributes Grammar.Entry.e)),
           "194fe98d",
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
                (Grammar.s_nterm (longident : 'longident Grammar.Entry.e)))
             (Grammar.s_nterm
                (item_attributes : 'item_attributes Grammar.Entry.e)),
           "194fe98d",
           (fun (attrs : 'item_attributes) (li : 'longident) _ (i : string) _
                _ (loc : Ploc.t) ->
              (MLast.SgMtyAlias (loc, i, li, attrs) : 'sig_item)));
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
                   (Grammar.s_token ("", ":=")))
                (Grammar.s_nterm
                   (module_type : 'module_type Grammar.Entry.e)))
             (Grammar.s_nterm
                (item_attributes : 'item_attributes Grammar.Entry.e)),
           "194fe98d",
           (fun (attrs : 'item_attributes) (mt : 'module_type) _ (i : 'ident)
                _ _ (loc : Ploc.t) ->
              (MLast.SgMtySubst (loc, i, mt, attrs) : 'sig_item)));
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
           "194fe98d",
           (fun (attrs : 'item_attributes) (mt : 'module_type) _ (i : 'ident)
                _ _ (loc : Ploc.t) ->
              (MLast.SgMty (loc, i, mt, attrs) : 'sig_item)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("", "module")))
                         (Grammar.s_nterm
                            (check_uident_coloneq :
                             'check_uident_coloneq Grammar.Entry.e)))
                      (Grammar.s_token ("UIDENT", "")))
                   (Grammar.s_token ("", ":=")))
                (Grammar.s_nterm
                   (extended_longident :
                    'extended_longident Grammar.Entry.e)))
             (Grammar.s_nterm
                (item_attributes : 'item_attributes Grammar.Entry.e)),
           "194fe98d",
           (fun (attrs : 'item_attributes) (li : 'extended_longident) _
                (i : string) _ _ (loc : Ploc.t) ->
              (MLast.SgModSubst (loc, i, li, attrs) : 'sig_item)));
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
           "194fe98d",
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
           "194fe98d",
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
                               (Grammar.r_next
                                  (Grammar.r_next Grammar.r_stop
                                     (Grammar.s_token ("", "external")))
                                  (Grammar.s_token ("", "(")))
                               (Grammar.s_nterm
                                  (operator_rparen :
                                   'operator_rparen Grammar.Entry.e)))
                            (Grammar.s_token ("", ":")))
                         (Grammar.s_nterm
                            (type_binder_opt :
                             'type_binder_opt Grammar.Entry.e)))
                      (Grammar.s_nterm (ctyp : 'ctyp Grammar.Entry.e)))
                   (Grammar.s_token ("", "=")))
                (Grammar.s_list1 (Grammar.s_token ("STRING", ""))))
             (Grammar.s_nterm
                (item_attributes : 'item_attributes Grammar.Entry.e)),
           "194fe98d",
           (fun (attrs : 'item_attributes) (pd : string list) _ (t : 'ctyp)
                (ls : 'type_binder_opt) _ (i : 'operator_rparen) _ _
                (loc : Ploc.t) ->
              (MLast.SgExt (loc, i, ls, t, pd, attrs) : 'sig_item)));
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
                               (Grammar.s_token ("LIDENT", "")))
                            (Grammar.s_token ("", ":")))
                         (Grammar.s_nterm
                            (type_binder_opt :
                             'type_binder_opt Grammar.Entry.e)))
                      (Grammar.s_nterm (ctyp : 'ctyp Grammar.Entry.e)))
                   (Grammar.s_token ("", "=")))
                (Grammar.s_list1 (Grammar.s_token ("STRING", ""))))
             (Grammar.s_nterm
                (item_attributes : 'item_attributes Grammar.Entry.e)),
           "194fe98d",
           (fun (attrs : 'item_attributes) (pd : string list) _ (t : 'ctyp)
                (ls : 'type_binder_opt) _ (i : string) _ (loc : Ploc.t) ->
              (MLast.SgExt (loc, i, ls, t, pd, attrs) : 'sig_item)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop
                   (Grammar.s_token ("", "exception")))
                (Grammar.s_nterm
                   (constructor_declaration :
                    'constructor_declaration Grammar.Entry.e)))
             (Grammar.s_nterm
                (item_attributes : 'item_attributes Grammar.Entry.e)),
           "194fe98d",
           (fun (item_attrs : 'item_attributes)
                (gc : 'constructor_declaration) _ (loc : Ploc.t) ->
              (MLast.SgExc (loc, gc, item_attrs) : 'sig_item)));
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
                          "194fe98d",
                          (fun _ (s : 'sig_item) (loc : Ploc.t) ->
                             (s : 'e__8)))])))
             (Grammar.s_token ("", "end")),
           "194fe98d",
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
           "194fe98d",
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
           "194fe98d",
           (fun (mt : 'module_declaration) (arg : 'functor_parameter)
                (loc : Ploc.t) ->
              (MLast.MtFun (loc, arg, mt) : 'module_declaration)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", ":")))
             (Grammar.s_nterm (module_type : 'module_type Grammar.Entry.e)),
           "194fe98d",
           (fun (mt : 'module_type) _ (loc : Ploc.t) ->
              (mt : 'module_declaration)))]];
    Grammar.extension (with_constr : 'with_constr Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("", "module")))
                      (Grammar.s_token ("", "type")))
                   (Grammar.s_nterm (longident : 'longident Grammar.Entry.e)))
                (Grammar.s_token ("", ":=")))
             (Grammar.s_nterm (module_type : 'module_type Grammar.Entry.e)),
           "194fe98d",
           (fun (mt : 'module_type) _ (li : 'longident) _ _ (loc : Ploc.t) ->
              (MLast.WcMts (loc, li, mt) : 'with_constr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("", "module")))
                      (Grammar.s_token ("", "type")))
                   (Grammar.s_nterm (longident : 'longident Grammar.Entry.e)))
                (Grammar.s_token ("", "=")))
             (Grammar.s_nterm (module_type : 'module_type Grammar.Entry.e)),
           "194fe98d",
           (fun (mt : 'module_type) _ (li : 'longident) _ _ (loc : Ploc.t) ->
              (MLast.WcMty (loc, li, mt) : 'with_constr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next Grammar.r_stop
                      (Grammar.s_token ("", "module")))
                   (Grammar.s_nterm (longident : 'longident Grammar.Entry.e)))
                (Grammar.s_token ("", ":=")))
             (Grammar.s_nterm (module_expr : 'module_expr Grammar.Entry.e)),
           "194fe98d",
           (fun (me : 'module_expr) _ (li : 'longident) _ (loc : Ploc.t) ->
              (MLast.WcMos (loc, li, me) : 'with_constr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next Grammar.r_stop
                      (Grammar.s_token ("", "module")))
                   (Grammar.s_nterm (longident : 'longident Grammar.Entry.e)))
                (Grammar.s_token ("", "=")))
             (Grammar.s_nterm (module_expr : 'module_expr Grammar.Entry.e)),
           "194fe98d",
           (fun (me : 'module_expr) _ (li : 'longident) _ (loc : Ploc.t) ->
              (MLast.WcMod (loc, li, me) : 'with_constr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("", "type")))
                      (Grammar.s_nterm
                         (longident_lident :
                          'longident_lident Grammar.Entry.e)))
                   (Grammar.s_list0
                      (Grammar.s_nterm
                         (type_parameter : 'type_parameter Grammar.Entry.e))))
                (Grammar.s_token ("", ":=")))
             (Grammar.s_nterm
                (ctyp_below_alg_attribute :
                 'ctyp_below_alg_attribute Grammar.Entry.e)),
           "194fe98d",
           (fun (t : 'ctyp_below_alg_attribute) _ (tpl : 'type_parameter list)
                (i : 'longident_lident) _ (loc : Ploc.t) ->
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
                            (longident_lident :
                             'longident_lident Grammar.Entry.e)))
                      (Grammar.s_list0
                         (Grammar.s_nterm
                            (type_parameter :
                             'type_parameter Grammar.Entry.e))))
                   (Grammar.s_token ("", "=")))
                (Grammar.s_flag (Grammar.s_token ("", "private"))))
             (Grammar.s_nterm
                (ctyp_below_alg_attribute :
                 'ctyp_below_alg_attribute Grammar.Entry.e)),
           "194fe98d",
           (fun (t : 'ctyp_below_alg_attribute) (pf : bool) _
                (tpl : 'type_parameter list) (i : 'longident_lident) _
                (loc : Ploc.t) ->
              (MLast.WcTyp (loc, i, tpl, pf, t) : 'with_constr)))]];
    Grammar.extension (uidopt : 'uidopt Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "_")),
           "194fe98d", (fun _ (loc : Ploc.t) -> (None : 'uidopt)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop (Grammar.s_token ("UIDENT", "")),
           "194fe98d",
           (fun (m : string) (loc : Ploc.t) -> (Some m : 'uidopt)))]];
    Grammar.extension (andop_binding : 'andop_binding Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop
                (Grammar.s_nterm (andop : 'andop Grammar.Entry.e)))
             (Grammar.s_nterm
                (letop_binding : 'letop_binding Grammar.Entry.e)),
           "194fe98d",
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
                       "194fe98d",
                       (fun (id : 'attribute_id) _ (loc : Ploc.t) ->
                          (id : 'e__10)))])),
           "194fe98d",
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
           "194fe98d",
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
           "194fe98d",
           (fun _ (seq : 'sequence) _ _ (e : 'expr)
                (ext, attrs : 'ext_attributes) _ (loc : Ploc.t) ->
              (expr_to_inline (MLast.ExWhi (loc, e, seq)) ext attrs :
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
           "194fe98d",
           (fun _ (seq : 'sequence) _ _ (e2 : 'expr) (df : 'direction_flag)
                (e1 : 'expr) _ (i : 'patt) (ext, attrs : 'ext_attributes) _
                (loc : Ploc.t) ->
              (expr_to_inline (MLast.ExFor (loc, i, e1, e2, df, seq)) ext
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
           "194fe98d",
           (fun _ (seq : 'sequence) _ (ext, attrs : 'ext_attributes) _
                (loc : Ploc.t) ->
              (expr_to_inline (mksequence2 loc seq) ext attrs : 'expr)));
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
           "194fe98d",
           (fun (e3 : 'expr) _ (e2 : 'expr) _ (e1 : 'expr)
                (ext, attrs : 'ext_attributes) _ (loc : Ploc.t) ->
              (expr_to_inline (MLast.ExIfe (loc, e1, e2, e3)) ext attrs :
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
           "194fe98d",
           (fun (mc : 'match_case) _ (e : 'expr)
                (ext, attrs : 'ext_attributes) _ (loc : Ploc.t) ->
              (expr_to_inline (MLast.ExTry (loc, e, [mc])) ext attrs :
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
           "194fe98d",
           (fun (l : 'closed_case_list) _ (e : 'expr)
                (ext, attrs : 'ext_attributes) _ (loc : Ploc.t) ->
              (expr_to_inline (MLast.ExTry (loc, e, l)) ext attrs : 'expr)));
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
           "194fe98d",
           (fun (e1 : 'expr) _ (p1 : 'ipatt) _ (e : 'expr)
                (ext, attrs : 'ext_attributes) _ (loc : Ploc.t) ->
              (expr_to_inline (MLast.ExMat (loc, e, [p1, None, e1])) ext
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
           "194fe98d",
           (fun (l : 'closed_case_list) _ (e : 'expr)
                (ext, attrs : 'ext_attributes) _ (loc : Ploc.t) ->
              (expr_to_inline (MLast.ExMat (loc, e, l)) ext attrs : 'expr)));
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
           "194fe98d",
           (fun (e : 'fun_def) (p : 'ipatt) (ext, attrs : 'ext_attributes) _
                (loc : Ploc.t) ->
              (expr_to_inline (MLast.ExFun (loc, [p, None, e])) ext attrs :
               'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "fun")))
                (Grammar.s_nterm
                   (ext_attributes : 'ext_attributes Grammar.Entry.e)))
             (Grammar.s_nterm
                (closed_case_list : 'closed_case_list Grammar.Entry.e)),
           "194fe98d",
           (fun (l : 'closed_case_list) (ext, attrs : 'ext_attributes) _
                (loc : Ploc.t) ->
              (expr_to_inline (MLast.ExFun (loc, l)) ext attrs : 'expr)));
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
                            (Grammar.s_token ("", "open")))
                         (Grammar.s_flag (Grammar.s_token ("", "!"))))
                      (Grammar.s_nterm
                         (ext_attributes : 'ext_attributes Grammar.Entry.e)))
                   (Grammar.s_nterm
                      (module_expr : 'module_expr Grammar.Entry.e)))
                (Grammar.s_token ("", "in")))
             Grammar.s_self,
           "194fe98d",
           (fun (e : 'expr) _ (m : 'module_expr)
                (ext, attrs : 'ext_attributes) (ovf : bool) _ _ _
                (loc : Ploc.t) ->
              (expr_to_inline (MLast.ExLop (loc, ovf, m, e)) ext attrs :
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
           "194fe98d",
           (fun (e : 'expr) _ (mb : 'mod_fun_binding) (m : 'uidopt)
                (ext, attrs : 'ext_attributes) _ _ _ (loc : Ploc.t) ->
              (expr_to_inline (MLast.ExLmd (loc, m, mb, e)) ext attrs :
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
           "194fe98d",
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
           "194fe98d",
           (fun (x : 'expr) _ (l : 'let_binding list) (r : bool)
                (ext : 'ext_opt) _ _ (loc : Ploc.t) ->
              (expr_to_inline (MLast.ExLet (loc, r, l, x)) ext [] : 'expr)));
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
           "194fe98d",
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
           "194fe98d",
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
           "194fe98d",
           (fun (lb : 'let_binding) (rf : bool) (ext, attrs : 'ext_attributes)
                _ (e : 'expr) (loc : Ploc.t) ->
              (expr_to_inline (MLast.ExLet (loc, rf, [lb], e)) ext attrs :
               'expr)))];
       Some ":=", Some Gramext.NonA,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                   (Grammar.s_token ("", ":=")))
                Grammar.s_self)
             (Grammar.s_nterm (dummy : 'dummy Grammar.Entry.e)),
           "194fe98d",
           (fun _ (e2 : 'expr) _ (e1 : 'expr) (loc : Ploc.t) ->
              (MLast.ExAss (loc, e1, e2) : 'expr)))];
       Some "||", Some Gramext.RightA,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                (Grammar.s_token ("", "||")))
             Grammar.s_self,
           "194fe98d",
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
           "194fe98d",
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
           "194fe98d",
           (fun (e2 : 'expr) (op : 'infixop0) (e1 : 'expr) (loc : Ploc.t) ->
              (MLast.ExApp
                 (loc, MLast.ExApp (loc, MLast.ExLid (loc, op), e1), e2) :
               'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                (Grammar.s_token ("", "!=")))
             Grammar.s_self,
           "194fe98d",
           (fun (e2 : 'expr) _ (e1 : 'expr) (loc : Ploc.t) ->
              (MLast.ExApp
                 (loc, MLast.ExApp (loc, MLast.ExLid (loc, "!="), e1), e2) :
               'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                (Grammar.s_token ("", "==")))
             Grammar.s_self,
           "194fe98d",
           (fun (e2 : 'expr) _ (e1 : 'expr) (loc : Ploc.t) ->
              (MLast.ExApp
                 (loc, MLast.ExApp (loc, MLast.ExLid (loc, "=="), e1), e2) :
               'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                (Grammar.s_token ("", "<>")))
             Grammar.s_self,
           "194fe98d",
           (fun (e2 : 'expr) _ (e1 : 'expr) (loc : Ploc.t) ->
              (MLast.ExApp
                 (loc, MLast.ExApp (loc, MLast.ExLid (loc, "<>"), e1), e2) :
               'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                (Grammar.s_token ("", "=")))
             Grammar.s_self,
           "194fe98d",
           (fun (e2 : 'expr) _ (e1 : 'expr) (loc : Ploc.t) ->
              (MLast.ExApp
                 (loc, MLast.ExApp (loc, MLast.ExLid (loc, "="), e1), e2) :
               'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                (Grammar.s_token ("", ">=")))
             Grammar.s_self,
           "194fe98d",
           (fun (e2 : 'expr) _ (e1 : 'expr) (loc : Ploc.t) ->
              (MLast.ExApp
                 (loc, MLast.ExApp (loc, MLast.ExLid (loc, ">="), e1), e2) :
               'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                (Grammar.s_token ("", "<=")))
             Grammar.s_self,
           "194fe98d",
           (fun (e2 : 'expr) _ (e1 : 'expr) (loc : Ploc.t) ->
              (MLast.ExApp
                 (loc, MLast.ExApp (loc, MLast.ExLid (loc, "<="), e1), e2) :
               'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                (Grammar.s_token ("", ">")))
             Grammar.s_self,
           "194fe98d",
           (fun (e2 : 'expr) _ (e1 : 'expr) (loc : Ploc.t) ->
              (MLast.ExApp
                 (loc, MLast.ExApp (loc, MLast.ExLid (loc, ">"), e1), e2) :
               'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                (Grammar.s_token ("", "<")))
             Grammar.s_self,
           "194fe98d",
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
           "194fe98d",
           (fun (e2 : 'expr) (op : 'infixop1) (e1 : 'expr) (loc : Ploc.t) ->
              (MLast.ExApp
                 (loc, MLast.ExApp (loc, MLast.ExLid (loc, op), e1), e2) :
               'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                (Grammar.s_token ("", "@")))
             Grammar.s_self,
           "194fe98d",
           (fun (e2 : 'expr) _ (e1 : 'expr) (loc : Ploc.t) ->
              (MLast.ExApp
                 (loc, MLast.ExApp (loc, MLast.ExLid (loc, "@"), e1), e2) :
               'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                (Grammar.s_token ("", "^")))
             Grammar.s_self,
           "194fe98d",
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
           "194fe98d",
           (fun _ (attr : 'attribute_body) _ (e1 : 'expr) (loc : Ploc.t) ->
              (MLast.ExAtt (loc, e1, attr) : 'expr)))];
       Some "+", Some Gramext.LeftA,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                (Grammar.s_nterm (infixop2 : 'infixop2 Grammar.Entry.e)))
             Grammar.s_self,
           "194fe98d",
           (fun (e2 : 'expr) (op : 'infixop2) (e1 : 'expr) (loc : Ploc.t) ->
              (MLast.ExApp
                 (loc, MLast.ExApp (loc, MLast.ExLid (loc, op), e1), e2) :
               'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                (Grammar.s_token ("", "-.")))
             Grammar.s_self,
           "194fe98d",
           (fun (e2 : 'expr) _ (e1 : 'expr) (loc : Ploc.t) ->
              (MLast.ExApp
                 (loc, MLast.ExApp (loc, MLast.ExLid (loc, "-."), e1), e2) :
               'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                (Grammar.s_token ("", "+.")))
             Grammar.s_self,
           "194fe98d",
           (fun (e2 : 'expr) _ (e1 : 'expr) (loc : Ploc.t) ->
              (MLast.ExApp
                 (loc, MLast.ExApp (loc, MLast.ExLid (loc, "+."), e1), e2) :
               'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                (Grammar.s_token ("", "-")))
             Grammar.s_self,
           "194fe98d",
           (fun (e2 : 'expr) _ (e1 : 'expr) (loc : Ploc.t) ->
              (MLast.ExApp
                 (loc, MLast.ExApp (loc, MLast.ExLid (loc, "-"), e1), e2) :
               'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                (Grammar.s_token ("", "+")))
             Grammar.s_self,
           "194fe98d",
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
           "194fe98d",
           (fun (e2 : 'expr) (op : 'infixop3) (e1 : 'expr) (loc : Ploc.t) ->
              (MLast.ExApp
                 (loc, MLast.ExApp (loc, MLast.ExLid (loc, op), e1), e2) :
               'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                (Grammar.s_token ("", "mod")))
             Grammar.s_self,
           "194fe98d",
           (fun (e2 : 'expr) _ (e1 : 'expr) (loc : Ploc.t) ->
              (MLast.ExApp
                 (loc, MLast.ExApp (loc, MLast.ExLid (loc, "mod"), e1), e2) :
               'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                (Grammar.s_token ("", "lxor")))
             Grammar.s_self,
           "194fe98d",
           (fun (e2 : 'expr) _ (e1 : 'expr) (loc : Ploc.t) ->
              (MLast.ExApp
                 (loc, MLast.ExApp (loc, MLast.ExLid (loc, "lxor"), e1), e2) :
               'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                (Grammar.s_token ("", "lor")))
             Grammar.s_self,
           "194fe98d",
           (fun (e2 : 'expr) _ (e1 : 'expr) (loc : Ploc.t) ->
              (MLast.ExApp
                 (loc, MLast.ExApp (loc, MLast.ExLid (loc, "lor"), e1), e2) :
               'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                (Grammar.s_token ("", "land")))
             Grammar.s_self,
           "194fe98d",
           (fun (e2 : 'expr) _ (e1 : 'expr) (loc : Ploc.t) ->
              (MLast.ExApp
                 (loc, MLast.ExApp (loc, MLast.ExLid (loc, "land"), e1), e2) :
               'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                (Grammar.s_token ("", "/.")))
             Grammar.s_self,
           "194fe98d",
           (fun (e2 : 'expr) _ (e1 : 'expr) (loc : Ploc.t) ->
              (MLast.ExApp
                 (loc, MLast.ExApp (loc, MLast.ExLid (loc, "/."), e1), e2) :
               'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                (Grammar.s_token ("", "*.")))
             Grammar.s_self,
           "194fe98d",
           (fun (e2 : 'expr) _ (e1 : 'expr) (loc : Ploc.t) ->
              (MLast.ExApp
                 (loc, MLast.ExApp (loc, MLast.ExLid (loc, "*."), e1), e2) :
               'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                (Grammar.s_token ("", "/")))
             Grammar.s_self,
           "194fe98d",
           (fun (e2 : 'expr) _ (e1 : 'expr) (loc : Ploc.t) ->
              (MLast.ExApp
                 (loc, MLast.ExApp (loc, MLast.ExLid (loc, "/"), e1), e2) :
               'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                (Grammar.s_token ("", "*")))
             Grammar.s_self,
           "194fe98d",
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
           "194fe98d",
           (fun (e2 : 'expr) (op : 'infixop4) (e1 : 'expr) (loc : Ploc.t) ->
              (MLast.ExApp
                 (loc, MLast.ExApp (loc, MLast.ExLid (loc, op), e1), e2) :
               'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                (Grammar.s_token ("", "lsr")))
             Grammar.s_self,
           "194fe98d",
           (fun (e2 : 'expr) _ (e1 : 'expr) (loc : Ploc.t) ->
              (MLast.ExApp
                 (loc, MLast.ExApp (loc, MLast.ExLid (loc, "lsr"), e1), e2) :
               'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                (Grammar.s_token ("", "lsl")))
             Grammar.s_self,
           "194fe98d",
           (fun (e2 : 'expr) _ (e1 : 'expr) (loc : Ploc.t) ->
              (MLast.ExApp
                 (loc, MLast.ExApp (loc, MLast.ExLid (loc, "lsl"), e1), e2) :
               'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                (Grammar.s_token ("", "asr")))
             Grammar.s_self,
           "194fe98d",
           (fun (e2 : 'expr) _ (e1 : 'expr) (loc : Ploc.t) ->
              (MLast.ExApp
                 (loc, MLast.ExApp (loc, MLast.ExLid (loc, "asr"), e1), e2) :
               'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                (Grammar.s_token ("", "**")))
             Grammar.s_self,
           "194fe98d",
           (fun (e2 : 'expr) _ (e1 : 'expr) (loc : Ploc.t) ->
              (MLast.ExApp
                 (loc, MLast.ExApp (loc, MLast.ExLid (loc, "**"), e1), e2) :
               'expr)))];
       Some "unary minus", Some Gramext.NonA,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "+.")))
             Grammar.s_self,
           "194fe98d",
           (fun (e : 'expr) _ (loc : Ploc.t) ->
              (match e with
                 MLast.ExFlo (_, _) -> e
               | _ -> MLast.ExApp (loc, MLast.ExLid (loc, "~+."), e) :
               'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "+")))
             Grammar.s_self,
           "194fe98d",
           (fun (e : 'expr) _ (loc : Ploc.t) ->
              (match e with
                 MLast.ExInt (_, _, "") -> e
               | _ -> MLast.ExApp (loc, MLast.ExLid (loc, "~+"), e) :
               'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "-.")))
             Grammar.s_self,
           "194fe98d",
           (fun (e : 'expr) _ (loc : Ploc.t) ->
              (MLast.ExApp (loc, MLast.ExLid (loc, "-."), e) : 'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "-")))
             Grammar.s_self,
           "194fe98d",
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
           "194fe98d",
           (fun (e : 'expr) (ext, attrs : 'ext_attributes) _ (loc : Ploc.t) ->
              (expr_to_inline (MLast.ExLaz (loc, e)) ext attrs : 'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop
                   (Grammar.s_token ("", "assert")))
                (Grammar.s_nterm
                   (ext_attributes : 'ext_attributes Grammar.Entry.e)))
             Grammar.s_self,
           "194fe98d",
           (fun (e : 'expr) (ext, attrs : 'ext_attributes) _ (loc : Ploc.t) ->
              (expr_to_inline (MLast.ExAsr (loc, e)) ext attrs : 'expr)));
        Grammar.production
          (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
             Grammar.s_self,
           "194fe98d",
           (fun (e2 : 'expr) (e1 : 'expr) (loc : Ploc.t) ->
              (MLast.ExApp (loc, e1, e2) : 'expr)))];
       Some ".", Some Gramext.LeftA,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next Grammar.r_stop Grammar.s_self)
                      (Grammar.s_nterm (dotop : 'dotop Grammar.Entry.e)))
                   (Grammar.s_token ("", "{")))
                (Grammar.s_list1sep
                   (Grammar.s_nterml (expr : 'expr Grammar.Entry.e) "+")
                   (Grammar.s_token ("", ";")) false))
             (Grammar.s_token ("", "}")),
           "194fe98d",
           (fun _ (el : 'expr list) _ (op : 'dotop) (e1 : 'expr)
                (loc : Ploc.t) ->
              (MLast.ExBae (loc, op, e1, el) : 'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next Grammar.r_stop Grammar.s_self)
                      (Grammar.s_token ("", ".")))
                   (Grammar.s_token ("", "{")))
                (Grammar.s_list1sep
                   (Grammar.s_nterml (expr : 'expr Grammar.Entry.e) "+")
                   (Grammar.s_token ("", ",")) false))
             (Grammar.s_token ("", "}")),
           "194fe98d",
           (fun _ (el : 'expr list) _ _ (e1 : 'expr) (loc : Ploc.t) ->
              (MLast.ExBae (loc, ".", e1, el) : 'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next Grammar.r_stop Grammar.s_self)
                      (Grammar.s_nterm (dotop : 'dotop Grammar.Entry.e)))
                   (Grammar.s_token ("", "[")))
                (Grammar.s_list1sep
                   (Grammar.s_nterml (expr : 'expr Grammar.Entry.e) "+")
                   (Grammar.s_token ("", ";")) false))
             (Grammar.s_token ("", "]")),
           "194fe98d",
           (fun _ (el : 'expr list) _ (op : 'dotop) (e1 : 'expr)
                (loc : Ploc.t) ->
              (MLast.ExSte (loc, op, e1, el) : 'expr)));
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
           "194fe98d",
           (fun _ (e2 : 'expr) _ _ (e1 : 'expr) (loc : Ploc.t) ->
              (MLast.ExSte (loc, ".", e1, [e2]) : 'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next Grammar.r_stop Grammar.s_self)
                      (Grammar.s_nterm (dotop : 'dotop Grammar.Entry.e)))
                   (Grammar.s_token ("", "(")))
                (Grammar.s_list1sep
                   (Grammar.s_nterml (expr : 'expr Grammar.Entry.e) "+")
                   (Grammar.s_token ("", ";")) false))
             (Grammar.s_token ("", ")")),
           "194fe98d",
           (fun _ (el : 'expr list) _ (op : 'dotop) (e1 : 'expr)
                (loc : Ploc.t) ->
              (MLast.ExAre (loc, op, e1, el) : 'expr)));
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
           "194fe98d",
           (fun _ (e2 : 'expr) _ _ (e1 : 'expr) (loc : Ploc.t) ->
              (if expr_last_is_uid e1 then
                 failwith
                   "internal error in original-syntax parser at dot-lparen"
               else MLast.ExAre (loc, ".", e1, [e2]) :
               'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                   (Grammar.s_token ("", ".")))
                (Grammar.s_token ("", "(")))
             (Grammar.s_nterm
                (operator_rparen : 'operator_rparen Grammar.Entry.e)),
           "194fe98d",
           (fun (op : 'operator_rparen) _ _ (e1 : 'expr) (loc : Ploc.t) ->
              (if op = "::" then
                 Ploc.raise loc
                   (Failure
                      ".(::) (dot paren colon colon paren) cannot appear except after longident")
               else MLast.ExFle (loc, e1, (None, op)) :
               'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                (Grammar.s_token ("", ".")))
             (Grammar.s_nterm
                (longident_lident : 'longident_lident Grammar.Entry.e)),
           "194fe98d",
           (fun (lili : 'longident_lident) _ (e1 : 'expr) (loc : Ploc.t) ->
              (MLast.ExFle (loc, e1, lili) : 'expr)))];
       Some "~-", Some Gramext.NonA,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop
                (Grammar.s_nterm (prefixop : 'prefixop Grammar.Entry.e)))
             Grammar.s_self,
           "194fe98d",
           (fun (e : 'expr) (f : 'prefixop) (loc : Ploc.t) ->
              (MLast.ExApp (loc, MLast.ExLid (loc, f), e) : 'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "~-.")))
             Grammar.s_self,
           "194fe98d",
           (fun (e : 'expr) _ (loc : Ploc.t) ->
              (MLast.ExApp (loc, MLast.ExLid (loc, "~-."), e) : 'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "~-")))
             Grammar.s_self,
           "194fe98d",
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
           "194fe98d",
           (fun _ (el : 'expr list) _ (loc : Ploc.t) ->
              (MLast.ExTup (loc, el) : 'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "(")))
                Grammar.s_self)
             (Grammar.s_token ("", ")")),
           "194fe98d", (fun _ (e : 'expr) _ (loc : Ploc.t) -> (e : 'expr)));
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
           "194fe98d",
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
           "194fe98d",
           (fun _ (t : 'ctyp) _ (e : 'expr) _ (loc : Ploc.t) ->
              (MLast.ExTyc (loc, e, t) : 'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "(")))
             (Grammar.s_nterm
                (operator_rparen : 'operator_rparen Grammar.Entry.e)),
           "194fe98d",
           (fun (op : 'operator_rparen) _ (loc : Ploc.t) ->
              (if op = "::" then MLast.ExLong (loc, MLast.LiUid (loc, op))
               else MLast.ExLid (loc, op) :
               'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "(")))
                   (Grammar.s_token ("", "module")))
                (Grammar.s_nterm
                   (module_expr : 'module_expr Grammar.Entry.e)))
             (Grammar.s_token ("", ")")),
           "194fe98d",
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
           "194fe98d",
           (fun _ (mt : 'module_type) _ (me : 'module_expr) _ _
                (loc : Ploc.t) ->
              (MLast.ExPck (loc, me, Some mt) : 'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "(")))
             (Grammar.s_token ("", ")")),
           "194fe98d",
           (fun _ _ (loc : Ploc.t) ->
              (MLast.ExLong (loc, MLast.LiUid (loc, "()")) : 'expr)));
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
           "194fe98d",
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
           "194fe98d",
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
           "194fe98d",
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
           "194fe98d",
           (fun _ (last : 'cons_expr_opt) (el : 'expr list) _
                (loc : Ploc.t) ->
              (mklistexp loc last el : 'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "[")))
             (Grammar.s_token ("", "]")),
           "194fe98d",
           (fun _ _ (loc : Ploc.t) ->
              (MLast.ExLong (loc, MLast.LiUid (loc, "[]")) : 'expr)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_nterm
                (expr_longident : 'expr_longident Grammar.Entry.e)),
           "194fe98d",
           (fun (e : 'expr_longident) (loc : Ploc.t) -> (e : 'expr)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop (Grammar.s_token ("GIDENT", "")),
           "194fe98d",
           (fun (i : string) (loc : Ploc.t) ->
              (MLast.ExLid (loc, i) : 'expr)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop (Grammar.s_token ("LIDENT", "")),
           "194fe98d",
           (fun (i : string) (loc : Ploc.t) ->
              (MLast.ExLid (loc, i) : 'expr)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_nterm
                (alg_extension : 'alg_extension Grammar.Entry.e)),
           "194fe98d",
           (fun (e : 'alg_extension) (loc : Ploc.t) ->
              (MLast.ExExten (loc, e) : 'expr)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", ".")),
           "194fe98d", (fun _ (loc : Ploc.t) -> (MLast.ExUnr loc : 'expr)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop (Grammar.s_token ("CHAR", "")),
           "194fe98d",
           (fun (s : string) (loc : Ploc.t) ->
              (MLast.ExChr (loc, s) : 'expr)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop (Grammar.s_token ("STRING", "")),
           "194fe98d",
           (fun (s : string) (loc : Ploc.t) ->
              (MLast.ExStr (loc, s) : 'expr)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop (Grammar.s_token ("FLOAT", "")),
           "194fe98d",
           (fun (s : string) (loc : Ploc.t) ->
              (MLast.ExFlo (loc, s) : 'expr)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop (Grammar.s_token ("INT_n", "")),
           "194fe98d",
           (fun (s : string) (loc : Ploc.t) ->
              (MLast.ExInt (loc, s, "n") : 'expr)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop (Grammar.s_token ("INT_L", "")),
           "194fe98d",
           (fun (s : string) (loc : Ploc.t) ->
              (MLast.ExInt (loc, s, "L") : 'expr)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop (Grammar.s_token ("INT_l", "")),
           "194fe98d",
           (fun (s : string) (loc : Ploc.t) ->
              (MLast.ExInt (loc, s, "l") : 'expr)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop (Grammar.s_token ("INT", "")),
           "194fe98d",
           (fun (s : string) (loc : Ploc.t) ->
              (MLast.ExInt (loc, s, "") : 'expr)))]];
    Grammar.extension (expr_longident : 'expr_longident Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next Grammar.r_stop
                      (Grammar.s_nterm
                         (longident : 'longident Grammar.Entry.e)))
                   (Grammar.s_token ("", ".")))
                (Grammar.s_nterm
                   (check_lbracketbar : 'check_lbracketbar Grammar.Entry.e)))
             (Grammar.s_nterml (expr : 'expr Grammar.Entry.e) "simple"),
           "194fe98d",
           (fun (e : 'expr) _ _ (li : 'longident) (loc : Ploc.t) ->
              (MLast.ExOpen (loc, li, e) : 'expr_longident)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next Grammar.r_stop
                      (Grammar.s_nterm
                         (longident : 'longident Grammar.Entry.e)))
                   (Grammar.s_token ("", ".")))
                (Grammar.s_nterm
                   (check_lbrace : 'check_lbrace Grammar.Entry.e)))
             (Grammar.s_nterml (expr : 'expr Grammar.Entry.e) "simple"),
           "194fe98d",
           (fun (e : 'expr) _ _ (li : 'longident) (loc : Ploc.t) ->
              (MLast.ExOpen (loc, li, e) : 'expr_longident)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next Grammar.r_stop
                      (Grammar.s_nterm
                         (longident : 'longident Grammar.Entry.e)))
                   (Grammar.s_token ("", ".")))
                (Grammar.s_nterm
                   (check_lbracket : 'check_lbracket Grammar.Entry.e)))
             (Grammar.s_nterml (expr : 'expr Grammar.Entry.e) "simple"),
           "194fe98d",
           (fun (e : 'expr) _ _ (li : 'longident) (loc : Ploc.t) ->
              (MLast.ExOpen (loc, li, e) : 'expr_longident)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop
                   (Grammar.s_nterm (longident : 'longident Grammar.Entry.e)))
                (Grammar.s_token ("", ".")))
             (Grammar.s_token ("LIDENT", "")),
           "194fe98d",
           (fun (id : string) _ (li : 'longident) (loc : Ploc.t) ->
              (MLast.ExFle (loc, MLast.ExLong (loc, li), (None, id)) :
               'expr_longident)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_nterm
                            (longident : 'longident Grammar.Entry.e)))
                      (Grammar.s_token ("", ".")))
                   (Grammar.s_token ("", "(")))
                (Grammar.s_nterm (expr : 'expr Grammar.Entry.e)))
             (Grammar.s_token ("", ")")),
           "194fe98d",
           (fun _ (e : 'expr) _ _ (li : 'longident) (loc : Ploc.t) ->
              (MLast.ExOpen (loc, li, e) : 'expr_longident)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next Grammar.r_stop
                      (Grammar.s_nterm
                         (longident : 'longident Grammar.Entry.e)))
                   (Grammar.s_token ("", ".")))
                (Grammar.s_token ("", "(")))
             (Grammar.s_nterm
                (operator_rparen : 'operator_rparen Grammar.Entry.e)),
           "194fe98d",
           (fun (op : 'operator_rparen) _ _ (li : 'longident)
                (loc : Ploc.t) ->
              (if op = "::" then MLast.ExLong (loc, MLast.LiAcc (loc, li, op))
               else MLast.ExFle (loc, MLast.ExLong (loc, li), (None, op)) :
               'expr_longident)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_nterm (longident : 'longident Grammar.Entry.e)),
           "194fe98d",
           (fun (li : 'longident) (loc : Ploc.t) ->
              (MLast.ExLong (loc, li) : 'expr_longident)))]];
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
           "194fe98d",
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
           "194fe98d",
           (fun _ (l : 'match_case list) _ (loc : Ploc.t) ->
              (l : 'closed_case_list)))]];
    Grammar.extension (cons_expr_opt : 'cons_expr_opt Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_stop, "194fe98d",
           (fun (loc : Ploc.t) -> (None : 'cons_expr_opt)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "::")))
             (Grammar.s_nterm (expr : 'expr Grammar.Entry.e)),
           "194fe98d",
           (fun (e : 'expr) _ (loc : Ploc.t) -> (Some e : 'cons_expr_opt)))]];
    Grammar.extension (dummy : 'dummy Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_stop, "194fe98d",
           (fun (loc : Ploc.t) -> (() : 'dummy)))]];
    Grammar.extension (sequence : 'sequence Grammar.Entry.e) None
      [None, Some Gramext.RightA,
       [Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_nterm (expr : 'expr Grammar.Entry.e)),
           "194fe98d", (fun (e : 'expr) (loc : Ploc.t) -> ([e] : 'sequence)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop
                (Grammar.s_nterm (expr : 'expr Grammar.Entry.e)))
             (Grammar.s_token ("", ";")),
           "194fe98d",
           (fun _ (e : 'expr) (loc : Ploc.t) -> ([e] : 'sequence)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop
                   (Grammar.s_nterm (expr : 'expr Grammar.Entry.e)))
                (Grammar.s_token ("", ";")))
             Grammar.s_self,
           "194fe98d",
           (fun (el : 'sequence) _ (e : 'expr) (loc : Ploc.t) ->
              (e :: el : 'sequence)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next
                         (Grammar.r_next
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("", "let")))
                            (Grammar.s_token ("", "open")))
                         (Grammar.s_flag (Grammar.s_token ("", "!"))))
                      (Grammar.s_nterm
                         (ext_attributes : 'ext_attributes Grammar.Entry.e)))
                   (Grammar.s_nterm
                      (module_expr : 'module_expr Grammar.Entry.e)))
                (Grammar.s_token ("", "in")))
             Grammar.s_self,
           "194fe98d",
           (fun (el : 'sequence) _ (m : 'module_expr)
                (ext, attrs : 'ext_attributes) (ovf : bool) _ _
                (loc : Ploc.t) ->
              ([expr_to_inline (MLast.ExLop (loc, ovf, m, mksequence loc el))
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
           "194fe98d",
           (fun (el : 'sequence) _ (mb : 'mod_fun_binding) (m : 'uidopt)
                (ext, attrs : 'ext_attributes) _ _ (loc : Ploc.t) ->
              ([expr_to_inline (MLast.ExLmd (loc, m, mb, mksequence loc el))
                  ext attrs] :
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
           "194fe98d",
           (fun (el : 'sequence) _ (l : 'let_binding list) (rf : bool) _
                (loc : Ploc.t) ->
              ([MLast.ExLet (loc, rf, l, mksequence loc el)] : 'sequence)))]];
    Grammar.extension (let_binding : 'let_binding Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next Grammar.r_stop
                      (Grammar.s_nterm (ipatt : 'ipatt Grammar.Entry.e)))
                   (Grammar.s_nterm
                      (check_not_colon : 'check_not_colon Grammar.Entry.e)))
                (Grammar.s_nterm
                   (fun_binding : 'fun_binding Grammar.Entry.e)))
             (Grammar.s_nterm
                (item_attributes : 'item_attributes Grammar.Entry.e)),
           "194fe98d",
           (fun (attrs : 'item_attributes) (e : 'fun_binding) _ (p : 'ipatt)
                (loc : Ploc.t) ->
              (p, e, attrs : 'let_binding)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next Grammar.r_stop
                      (Grammar.s_nterm (ipatt : 'ipatt Grammar.Entry.e)))
                   (Grammar.s_nterm
                      (check_colon : 'check_colon Grammar.Entry.e)))
                (Grammar.s_nterm
                   (fun_binding : 'fun_binding Grammar.Entry.e)))
             (Grammar.s_nterm
                (item_attributes : 'item_attributes Grammar.Entry.e)),
           "194fe98d",
           (fun (attrs : 'item_attributes) (e : 'fun_binding) _ (p : 'ipatt)
                (loc : Ploc.t) ->
              (let (p, e) =
                 match e with
                   MLast.ExTyc (_, e, t) -> MLast.PaTyc (loc, p, t), e
                 | _ -> p, e
               in
               p, e, attrs :
               'let_binding)))]];
    Grammar.extension (letop_binding : 'letop_binding Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop
                (Grammar.s_nterm (ipatt : 'ipatt Grammar.Entry.e)))
             (Grammar.s_nterm (fun_binding : 'fun_binding Grammar.Entry.e)),
           "194fe98d",
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
           "194fe98d",
           (fun (e : 'expr) _ (t : 'ctyp) _ (loc : Ploc.t) ->
              (MLast.ExTyc (loc, e, t) : 'fun_binding)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "=")))
             (Grammar.s_nterm (expr : 'expr Grammar.Entry.e)),
           "194fe98d",
           (fun (e : 'expr) _ (loc : Ploc.t) -> (e : 'fun_binding)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop
                (Grammar.s_nterm (ipatt : 'ipatt Grammar.Entry.e)))
             Grammar.s_self,
           "194fe98d",
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
           "194fe98d",
           (fun (e : 'expr) _ (w : 'when_expr option) (aso : 'as_patt_opt)
                (p : 'patt) (loc : Ploc.t) ->
              (mkmatchcase loc p aso w e : 'match_case)))]];
    Grammar.extension (as_patt_opt : 'as_patt_opt Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_stop, "194fe98d",
           (fun (loc : Ploc.t) -> (None : 'as_patt_opt)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "as")))
             (Grammar.s_nterm (patt : 'patt Grammar.Entry.e)),
           "194fe98d",
           (fun (p : 'patt) _ (loc : Ploc.t) -> (Some p : 'as_patt_opt)))]];
    Grammar.extension (when_expr : 'when_expr Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "when")))
             (Grammar.s_nterm (expr : 'expr Grammar.Entry.e)),
           "194fe98d",
           (fun (e : 'expr) _ (loc : Ploc.t) -> (e : 'when_expr)))]];
    Grammar.extension (label_expr : 'label_expr Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop
                (Grammar.s_nterm
                   (patt_label_ident : 'patt_label_ident Grammar.Entry.e)))
             (Grammar.s_nterm (fun_binding : 'fun_binding Grammar.Entry.e)),
           "194fe98d",
           (fun (e : 'fun_binding) (i : 'patt_label_ident) (loc : Ploc.t) ->
              (i, e : 'label_expr)))]];
    Grammar.extension (fun_def : 'fun_def Grammar.Entry.e) None
      [None, Some Gramext.RightA,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "->")))
             (Grammar.s_nterm (expr : 'expr Grammar.Entry.e)),
           "194fe98d", (fun (e : 'expr) _ (loc : Ploc.t) -> (e : 'fun_def)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop
                (Grammar.s_nterm (ipatt : 'ipatt Grammar.Entry.e)))
             Grammar.s_self,
           "194fe98d",
           (fun (e : 'fun_def) (p : 'ipatt) (loc : Ploc.t) ->
              (MLast.ExFun (loc, [p, None, e]) : 'fun_def)))]];
    Grammar.extension (patt_ident : 'patt_ident Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_nterm (longident : 'longident Grammar.Entry.e)),
           "194fe98d",
           (fun (li : 'longident) (loc : Ploc.t) ->
              (MLast.PaLong (loc, li, []) : 'patt_ident)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_nterm
                               (longident : 'longident Grammar.Entry.e)))
                         (Grammar.s_nterm
                            (check_lparen_type :
                             'check_lparen_type Grammar.Entry.e)))
                      (Grammar.s_token ("", "(")))
                   (Grammar.s_token ("", "type")))
                (Grammar.s_list1
                   (Grammar.s_rules
                      [Grammar.production
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("LIDENT", "")),
                          "194fe98d",
                          (fun (s : string) (loc : Ploc.t) ->
                             (loc, s : 'e__11)))])))
             (Grammar.s_token ("", ")")),
           "194fe98d",
           (fun _ (loc_ids : 'e__11 list) _ _ _ (li : 'longident)
                (loc : Ploc.t) ->
              (MLast.PaLong (loc, li, loc_ids) : 'patt_ident)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop
                   (Grammar.s_nterm (longident : 'longident Grammar.Entry.e)))
                (Grammar.s_token ("", ".")))
             (Grammar.s_nterml (patt : 'patt Grammar.Entry.e) "simple"),
           "194fe98d",
           (fun (p : 'patt) _ (li : 'longident) (loc : Ploc.t) ->
              (match p with
                 MLast.PaLong (_, MLast.LiUid (_, i), []) ->
                   let li = MLast.LiAcc (loc, li, i) in
                   MLast.PaLong (loc, li, [])
               | _ -> MLast.PaPfx (loc, li, p) :
               'patt_ident)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop (Grammar.s_token ("GIDENT", "")),
           "194fe98d",
           (fun (s : string) (loc : Ploc.t) ->
              (MLast.PaLid (loc, s) : 'patt_ident)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop (Grammar.s_token ("LIDENT", "")),
           "194fe98d",
           (fun (s : string) (loc : Ploc.t) ->
              (MLast.PaLid (loc, s) : 'patt_ident)))]];
    Grammar.extension (patt : 'patt Grammar.Entry.e) None
      [None, Some Gramext.LeftA,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                (Grammar.s_token ("", "|")))
             Grammar.s_self,
           "194fe98d",
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
           "194fe98d",
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
           "194fe98d",
           (fun (p : 'patt) (ext, attrs : 'ext_attributes) _ (loc : Ploc.t) ->
              (patt_to_inline loc (MLast.PaExc (loc, p)) ext attrs :
               'patt)))];
       None, Some Gramext.NonA,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                (Grammar.s_token ("", "..")))
             Grammar.s_self,
           "194fe98d",
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
           "194fe98d",
           (fun (p : 'patt) (ext, attrs : 'ext_attributes) _ (loc : Ploc.t) ->
              (patt_to_inline loc (MLast.PaLaz (loc, p)) ext attrs : 'patt)));
        Grammar.production
          (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
             Grammar.s_self,
           "194fe98d",
           (fun (p2 : 'patt) (p1 : 'patt) (loc : Ploc.t) ->
              (MLast.PaApp (loc, p1, p2) : 'patt)))];
       Some "simple", None,
       [Grammar.production
          (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "_")),
           "194fe98d", (fun _ (loc : Ploc.t) -> (MLast.PaAny loc : 'patt)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "(")))
                (Grammar.s_nterm (paren_patt : 'paren_patt Grammar.Entry.e)))
             (Grammar.s_token ("", ")")),
           "194fe98d",
           (fun _ (p : 'paren_patt) _ (loc : Ploc.t) -> (p : 'patt)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "(")))
             (Grammar.s_nterm
                (operator_rparen : 'operator_rparen Grammar.Entry.e)),
           "194fe98d",
           (fun (op : 'operator_rparen) _ (loc : Ploc.t) ->
              (if op = "::" then MLast.PaLong (loc, MLast.LiUid (loc, op), [])
               else MLast.PaLid (loc, op) :
               'patt)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "{")))
                (Grammar.s_list1sep
                   (Grammar.s_nterm
                      (label_patt : 'label_patt Grammar.Entry.e))
                   (Grammar.s_token ("", ";")) false))
             (Grammar.s_token ("", "}")),
           "194fe98d",
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
           "194fe98d",
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
           "194fe98d",
           (fun _ (last : 'cons_patt_opt) (pl : 'patt list) _
                (loc : Ploc.t) ->
              (mklistpat loc last pl : 'patt)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "[")))
             (Grammar.s_token ("", "]")),
           "194fe98d",
           (fun _ _ (loc : Ploc.t) ->
              (MLast.PaLong (loc, MLast.LiUid (loc, "[]"), []) : 'patt)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "-")))
             (Grammar.s_token ("FLOAT", "")),
           "194fe98d",
           (fun (s : string) _ (loc : Ploc.t) ->
              (MLast.PaFlo (loc, neg_string s) : 'patt)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "-")))
             (Grammar.s_token ("INT_n", "")),
           "194fe98d",
           (fun (s : string) _ (loc : Ploc.t) ->
              (MLast.PaInt (loc, neg_string s, "n") : 'patt)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "-")))
             (Grammar.s_token ("INT_L", "")),
           "194fe98d",
           (fun (s : string) _ (loc : Ploc.t) ->
              (MLast.PaInt (loc, neg_string s, "L") : 'patt)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "-")))
             (Grammar.s_token ("INT_l", "")),
           "194fe98d",
           (fun (s : string) _ (loc : Ploc.t) ->
              (MLast.PaInt (loc, neg_string s, "l") : 'patt)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "-")))
             (Grammar.s_token ("INT", "")),
           "194fe98d",
           (fun (s : string) _ (loc : Ploc.t) ->
              (MLast.PaInt (loc, neg_string s, "") : 'patt)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "+")))
             (Grammar.s_token ("FLOAT", "")),
           "194fe98d",
           (fun (s : string) _ (loc : Ploc.t) ->
              (MLast.PaFlo (loc, s) : 'patt)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "+")))
             (Grammar.s_token ("INT", "")),
           "194fe98d",
           (fun (s : string) _ (loc : Ploc.t) ->
              (MLast.PaInt (loc, s, "") : 'patt)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop (Grammar.s_token ("CHAR", "")),
           "194fe98d",
           (fun (s : string) (loc : Ploc.t) ->
              (MLast.PaChr (loc, s) : 'patt)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop (Grammar.s_token ("STRING", "")),
           "194fe98d",
           (fun (s : string) (loc : Ploc.t) ->
              (MLast.PaStr (loc, s) : 'patt)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop (Grammar.s_token ("FLOAT", "")),
           "194fe98d",
           (fun (s : string) (loc : Ploc.t) ->
              (MLast.PaFlo (loc, s) : 'patt)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop (Grammar.s_token ("INT_n", "")),
           "194fe98d",
           (fun (s : string) (loc : Ploc.t) ->
              (MLast.PaInt (loc, s, "n") : 'patt)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop (Grammar.s_token ("INT_L", "")),
           "194fe98d",
           (fun (s : string) (loc : Ploc.t) ->
              (MLast.PaInt (loc, s, "L") : 'patt)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop (Grammar.s_token ("INT_l", "")),
           "194fe98d",
           (fun (s : string) (loc : Ploc.t) ->
              (MLast.PaInt (loc, s, "l") : 'patt)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop (Grammar.s_token ("INT", "")),
           "194fe98d",
           (fun (s : string) (loc : Ploc.t) ->
              (MLast.PaInt (loc, s, "") : 'patt)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_nterm
                (alg_extension : 'alg_extension Grammar.Entry.e)),
           "194fe98d",
           (fun (e : 'alg_extension) (loc : Ploc.t) ->
              (MLast.PaExten (loc, e) : 'patt)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_nterm (patt_ident : 'patt_ident Grammar.Entry.e)),
           "194fe98d",
           (fun (p : 'patt_ident) (loc : Ploc.t) -> (p : 'patt)))]];
    Grammar.extension (paren_patt : 'paren_patt Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_stop, "194fe98d",
           (fun (loc : Ploc.t) ->
              (MLast.PaLong (loc, MLast.LiUid (loc, "()"), []) :
               'paren_patt)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "module")))
             (Grammar.s_nterm (uidopt : 'uidopt Grammar.Entry.e)),
           "194fe98d",
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
           "194fe98d",
           (fun (mt : 'module_type) _ (s : 'uidopt) _ (loc : Ploc.t) ->
              (MLast.PaUnp (loc, s, Some mt) : 'paren_patt)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "type")))
             (Grammar.s_token ("LIDENT", "")),
           "194fe98d",
           (fun (s : string) _ (loc : Ploc.t) ->
              (MLast.PaNty (loc, s) : 'paren_patt)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_list1sep
                (Grammar.s_nterm (patt : 'patt Grammar.Entry.e))
                (Grammar.s_token ("", ",")) false),
           "194fe98d",
           (fun (pl : 'patt list) (loc : Ploc.t) ->
              (MLast.PaTup (loc, pl) : 'paren_patt)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_nterm (patt : 'patt Grammar.Entry.e)),
           "194fe98d", (fun (p : 'patt) (loc : Ploc.t) -> (p : 'paren_patt)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop
                   (Grammar.s_nterm (patt : 'patt Grammar.Entry.e)))
                (Grammar.s_token ("", ",")))
             (Grammar.s_list1sep
                (Grammar.s_nterm (patt : 'patt Grammar.Entry.e))
                (Grammar.s_token ("", ",")) false),
           "194fe98d",
           (fun (pl : 'patt list) _ (p : 'patt) (loc : Ploc.t) ->
              (mktuppat loc p pl : 'paren_patt)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop
                   (Grammar.s_nterm (patt : 'patt Grammar.Entry.e)))
                (Grammar.s_token ("", "as")))
             (Grammar.s_nterm (patt : 'patt Grammar.Entry.e)),
           "194fe98d",
           (fun (p2 : 'patt) _ (p : 'patt) (loc : Ploc.t) ->
              (MLast.PaAli (loc, p, p2) : 'paren_patt)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop
                   (Grammar.s_nterm (patt : 'patt Grammar.Entry.e)))
                (Grammar.s_token ("", ":")))
             (Grammar.s_nterm (ctyp : 'ctyp Grammar.Entry.e)),
           "194fe98d",
           (fun (t : 'ctyp) _ (p : 'patt) (loc : Ploc.t) ->
              (MLast.PaTyc (loc, p, t) : 'paren_patt)))]];
    Grammar.extension (cons_patt_opt : 'cons_patt_opt Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_stop, "194fe98d",
           (fun (loc : Ploc.t) -> (None : 'cons_patt_opt)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "::")))
             (Grammar.s_nterm (patt : 'patt Grammar.Entry.e)),
           "194fe98d",
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
           "194fe98d",
           (fun (p : 'patt) _ (i : 'patt_label_ident) (loc : Ploc.t) ->
              (i, p : 'label_patt)))]];
    Grammar.extension (patt_label_ident : 'patt_label_ident Grammar.Entry.e)
      None
      [None, None,
       [Grammar.production
          (Grammar.r_next Grammar.r_stop (Grammar.s_token ("LIDENT", "")),
           "194fe98d",
           (fun (i : string) (loc : Ploc.t) ->
              (MLast.PaLid (loc, i) : 'patt_label_ident)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop
                   (Grammar.s_nterm (longident : 'longident Grammar.Entry.e)))
                (Grammar.s_token ("", ".")))
             Grammar.s_self,
           "194fe98d",
           (fun (p2 : 'patt_label_ident) _ (p1 : 'longident) (loc : Ploc.t) ->
              (MLast.PaPfx (loc, p1, p2) : 'patt_label_ident)))]];
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
           "194fe98d",
           (fun _ (attr : 'attribute_body) _ (e1 : 'ipatt) (loc : Ploc.t) ->
              (MLast.PaAtt (loc, e1, attr) : 'ipatt)))];
       Some "simple", None,
       [Grammar.production
          (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "_")),
           "194fe98d", (fun _ (loc : Ploc.t) -> (MLast.PaAny loc : 'ipatt)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_nterm
                (alg_extension : 'alg_extension Grammar.Entry.e)),
           "194fe98d",
           (fun (e : 'alg_extension) (loc : Ploc.t) ->
              (MLast.PaExten (loc, e) : 'ipatt)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "(")))
                (Grammar.s_nterm
                   (paren_ipatt : 'paren_ipatt Grammar.Entry.e)))
             (Grammar.s_token ("", ")")),
           "194fe98d",
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
           "194fe98d",
           (fun _ (lpl : 'label_ipatt list) _ (loc : Ploc.t) ->
              (MLast.PaRec (loc, lpl) : 'ipatt)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "(")))
             (Grammar.s_nterm
                (operator_rparen : 'operator_rparen Grammar.Entry.e)),
           "194fe98d",
           (fun (op : 'operator_rparen) _ (loc : Ploc.t) ->
              (if op = "::" then MLast.PaLong (loc, MLast.LiUid (loc, op), [])
               else MLast.PaLid (loc, op) :
               'ipatt)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_nterm (patt_ident : 'patt_ident Grammar.Entry.e)),
           "194fe98d",
           (fun (p : 'patt_ident) (loc : Ploc.t) -> (p : 'ipatt)))]];
    Grammar.extension (paren_ipatt : 'paren_ipatt Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_stop, "194fe98d",
           (fun (loc : Ploc.t) ->
              (MLast.PaLong (loc, MLast.LiUid (loc, "()"), []) :
               'paren_ipatt)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "module")))
             (Grammar.s_nterm (uidopt : 'uidopt Grammar.Entry.e)),
           "194fe98d",
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
           "194fe98d",
           (fun (mt : 'module_type) _ (s : 'uidopt) _ (loc : Ploc.t) ->
              (MLast.PaUnp (loc, s, Some mt) : 'paren_ipatt)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "type")))
             (Grammar.s_token ("LIDENT", "")),
           "194fe98d",
           (fun (s : string) _ (loc : Ploc.t) ->
              (MLast.PaNty (loc, s) : 'paren_ipatt)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_list1sep
                (Grammar.s_nterm (ipatt : 'ipatt Grammar.Entry.e))
                (Grammar.s_token ("", ",")) false),
           "194fe98d",
           (fun (pl : 'ipatt list) (loc : Ploc.t) ->
              (MLast.PaTup (loc, pl) : 'paren_ipatt)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_nterm (ipatt : 'ipatt Grammar.Entry.e)),
           "194fe98d",
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
           "194fe98d",
           (fun (pl : 'ipatt list) _ (p : 'ipatt) (loc : Ploc.t) ->
              (mktuppat loc p pl : 'paren_ipatt)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop
                   (Grammar.s_nterm (ipatt : 'ipatt Grammar.Entry.e)))
                (Grammar.s_token ("", "as")))
             (Grammar.s_nterm (ipatt : 'ipatt Grammar.Entry.e)),
           "194fe98d",
           (fun (p2 : 'ipatt) _ (p : 'ipatt) (loc : Ploc.t) ->
              (MLast.PaAli (loc, p, p2) : 'paren_ipatt)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop
                   (Grammar.s_nterm (ipatt : 'ipatt Grammar.Entry.e)))
                (Grammar.s_token ("", ":")))
             (Grammar.s_nterm (ctyp : 'ctyp Grammar.Entry.e)),
           "194fe98d",
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
           "194fe98d",
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
                         (Grammar.s_rules
                            [Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("", ":=")),
                                "194fe98d",
                                (fun _ (loc : Ploc.t) -> (false : 'e__12)));
                             Grammar.production
                               (Grammar.r_next Grammar.r_stop
                                  (Grammar.s_token ("", "=")),
                                "194fe98d",
                                (fun _ (loc : Ploc.t) -> (true : 'e__12)))]))
                      (Grammar.s_flag (Grammar.s_token ("", "private"))))
                   (Grammar.s_nterm (ctyp : 'ctyp Grammar.Entry.e)))
                (Grammar.s_list0
                   (Grammar.s_nterm
                      (constrain : 'constrain Grammar.Entry.e))))
             (Grammar.s_nterm
                (item_attributes : 'item_attributes Grammar.Entry.e)),
           "194fe98d",
           (fun (attrs : 'item_attributes) (cl : 'constrain list) (tk : 'ctyp)
                (pf : bool) (isDecl : 'e__12) (tpl : 'type_parameter list)
                (n : 'type_patt) (loc : Ploc.t) ->
              ({MLast.tdIsDecl = isDecl; MLast.tdNam = n; MLast.tdPrm = tpl;
                MLast.tdPrv = pf; MLast.tdDef = tk; MLast.tdCon = cl;
                MLast.tdAttributes = attrs} :
               'type_decl)))]];
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
                                     (longident_lident :
                                      'longident_lident Grammar.Entry.e)))
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
           "194fe98d",
           (fun (attrs : 'item_attributes) _
                (ecs : 'extension_constructor list) _ (pf : bool) _
                (tpl : 'type_parameter list) (n : 'longident_lident)
                (loc : Ploc.t) ->
              ({MLast.teNam = n; MLast.tePrm = tpl; MLast.tePrv = pf;
                MLast.teECs = ecs; MLast.teAttributes = attrs} :
               'type_extension)))]];
    Grammar.extension (type_patt : 'type_patt Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next Grammar.r_stop (Grammar.s_token ("LIDENT", "")),
           "194fe98d",
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
           "194fe98d",
           (fun (t2 : 'ctyp) _ (t1 : 'ctyp) _ (loc : Ploc.t) ->
              (t1, t2 : 'constrain)))]];
    Grammar.extension (type_parameter : 'type_parameter Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_nterm
                (simple_type_parameter :
                 'simple_type_parameter Grammar.Entry.e)),
           "194fe98d",
           (fun (p : 'simple_type_parameter) (loc : Ploc.t) ->
              (p, (None, false) : 'type_parameter)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "-!")))
             (Grammar.s_nterm
                (simple_type_parameter :
                 'simple_type_parameter Grammar.Entry.e)),
           "194fe98d",
           (fun (p : 'simple_type_parameter) _ (loc : Ploc.t) ->
              (p, (Some false, true) : 'type_parameter)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "!-")))
             (Grammar.s_nterm
                (simple_type_parameter :
                 'simple_type_parameter Grammar.Entry.e)),
           "194fe98d",
           (fun (p : 'simple_type_parameter) _ (loc : Ploc.t) ->
              (p, (Some false, true) : 'type_parameter)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "+!")))
             (Grammar.s_nterm
                (simple_type_parameter :
                 'simple_type_parameter Grammar.Entry.e)),
           "194fe98d",
           (fun (p : 'simple_type_parameter) _ (loc : Ploc.t) ->
              (p, (Some true, true) : 'type_parameter)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "!+")))
             (Grammar.s_nterm
                (simple_type_parameter :
                 'simple_type_parameter Grammar.Entry.e)),
           "194fe98d",
           (fun (p : 'simple_type_parameter) _ (loc : Ploc.t) ->
              (p, (Some true, true) : 'type_parameter)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "!")))
                (Grammar.s_token ("", "-")))
             (Grammar.s_nterm
                (simple_type_parameter :
                 'simple_type_parameter Grammar.Entry.e)),
           "194fe98d",
           (fun (p : 'simple_type_parameter) _ _ (loc : Ploc.t) ->
              (p, (Some false, true) : 'type_parameter)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "!")))
                (Grammar.s_token ("", "+")))
             (Grammar.s_nterm
                (simple_type_parameter :
                 'simple_type_parameter Grammar.Entry.e)),
           "194fe98d",
           (fun (p : 'simple_type_parameter) _ _ (loc : Ploc.t) ->
              (p, (Some true, true) : 'type_parameter)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "!")))
             (Grammar.s_nterm
                (simple_type_parameter :
                 'simple_type_parameter Grammar.Entry.e)),
           "194fe98d",
           (fun (p : 'simple_type_parameter) _ (loc : Ploc.t) ->
              (p, (None, true) : 'type_parameter)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "-")))
                (Grammar.s_token ("", "!")))
             (Grammar.s_nterm
                (simple_type_parameter :
                 'simple_type_parameter Grammar.Entry.e)),
           "194fe98d",
           (fun (p : 'simple_type_parameter) _ _ (loc : Ploc.t) ->
              (p, (Some false, true) : 'type_parameter)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "-")))
             (Grammar.s_nterm
                (simple_type_parameter :
                 'simple_type_parameter Grammar.Entry.e)),
           "194fe98d",
           (fun (p : 'simple_type_parameter) _ (loc : Ploc.t) ->
              (p, (Some false, false) : 'type_parameter)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "+")))
                (Grammar.s_token ("", "!")))
             (Grammar.s_nterm
                (simple_type_parameter :
                 'simple_type_parameter Grammar.Entry.e)),
           "194fe98d",
           (fun (p : 'simple_type_parameter) _ _ (loc : Ploc.t) ->
              (p, (Some true, true) : 'type_parameter)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "+")))
             (Grammar.s_nterm
                (simple_type_parameter :
                 'simple_type_parameter Grammar.Entry.e)),
           "194fe98d",
           (fun (p : 'simple_type_parameter) _ (loc : Ploc.t) ->
              (p, (Some true, false) : 'type_parameter)))]];
    Grammar.extension
      (simple_type_parameter : 'simple_type_parameter Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "_")),
           "194fe98d",
           (fun _ (loc : Ploc.t) -> (None : 'simple_type_parameter)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop (Grammar.s_token ("GIDENT", "")),
           "194fe98d",
           (fun (i : string) (loc : Ploc.t) ->
              (Some (greek_ascii_equiv i) : 'simple_type_parameter)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "'")))
             (Grammar.s_nterm (ident : 'ident Grammar.Entry.e)),
           "194fe98d",
           (fun (i : 'ident) _ (loc : Ploc.t) ->
              (Some i : 'simple_type_parameter)))]];
    Grammar.extension (longident : 'longident Grammar.Entry.e) None
      [None, Some Gramext.LeftA,
       [Grammar.production
          (Grammar.r_next Grammar.r_stop (Grammar.s_token ("UIDENT", "")),
           "194fe98d",
           (fun (i : string) (loc : Ploc.t) ->
              (MLast.LiUid (loc, i) : 'longident)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                   (Grammar.s_nterm
                      (check_dot_uid : 'check_dot_uid Grammar.Entry.e)))
                (Grammar.s_token ("", ".")))
             (Grammar.s_token ("UIDENT", "")),
           "194fe98d",
           (fun (i : string) _ _ (me1 : 'longident) (loc : Ploc.t) ->
              (MLast.LiAcc (loc, me1, i) : 'longident)))]];
    Grammar.extension
      (extended_longident : 'extended_longident Grammar.Entry.e) None
      [None, Some Gramext.LeftA,
       [Grammar.production
          (Grammar.r_next Grammar.r_stop (Grammar.s_token ("UIDENT", "")),
           "194fe98d",
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
           "194fe98d",
           (fun (i : string) _ _ (me1 : 'extended_longident) (loc : Ploc.t) ->
              (MLast.LiAcc (loc, me1, i) : 'extended_longident)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                   (Grammar.s_token ("", "(")))
                Grammar.s_self)
             (Grammar.s_token ("", ")")),
           "194fe98d",
           (fun _ (me2 : 'extended_longident) _ (me1 : 'extended_longident)
                (loc : Ploc.t) ->
              (MLast.LiApp (loc, me1, me2) : 'extended_longident)))]];
    Grammar.extension (ctyp_ident : 'ctyp_ident Grammar.Entry.e) None
      [None, Some Gramext.LeftA,
       [Grammar.production
          (Grammar.r_next Grammar.r_stop (Grammar.s_token ("LIDENT", "")),
           "194fe98d",
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
           "194fe98d",
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
           "194fe98d",
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
           "194fe98d",
           (fun _ (attr : 'attribute_body) _ (e1 : 'ctyp) (loc : Ploc.t) ->
              (MLast.TyAtt (loc, e1, attr) : 'ctyp)))];
       Some "below_alg_attribute", None,
       [Grammar.production
          (Grammar.r_next Grammar.r_stop Grammar.s_next, "194fe98d",
           (fun (t : 'ctyp) (loc : Ploc.t) -> (t : 'ctyp)))];
       Some "as", Some Gramext.LeftA,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                (Grammar.s_token ("", "as")))
             Grammar.s_self,
           "194fe98d",
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
           "194fe98d",
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
           "194fe98d",
           (fun (t : 'ctyp) _ (pl : 'typevar list) _ (loc : Ploc.t) ->
              (MLast.TyPol (loc, pl, t) : 'ctyp)))];
       Some "arrow", Some Gramext.RightA,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                (Grammar.s_token ("", "->")))
             Grammar.s_self,
           "194fe98d",
           (fun (t2 : 'ctyp) _ (t1 : 'ctyp) (loc : Ploc.t) ->
              (MLast.TyArr (loc, t1, t2) : 'ctyp)))];
       Some "apply", Some Gramext.LeftA,
       [Grammar.production
          (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
             Grammar.s_self,
           "194fe98d",
           (fun (t2 : 'ctyp) (t1 : 'ctyp) (loc : Ploc.t) ->
              (MLast.TyApp (loc, t1, t2) : 'ctyp)))];
       None, Some Gramext.LeftA,
       [Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_nterm (ctyp_ident : 'ctyp_ident Grammar.Entry.e)),
           "194fe98d",
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
           "194fe98d",
           (fun _ (ldl : 'label_declaration list) _ (loc : Ploc.t) ->
              (MLast.TyRec (loc, ldl) : 'ctyp)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "[")))
                (Grammar.s_token ("", "|")))
             (Grammar.s_token ("", "]")),
           "194fe98d",
           (fun _ _ _ (loc : Ploc.t) -> (MLast.TySum (loc, []) : 'ctyp)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "[")))
                (Grammar.s_list1sep
                   (Grammar.s_nterm
                      (constructor_declaration :
                       'constructor_declaration Grammar.Entry.e))
                   (Grammar.s_token ("", "|")) false))
             (Grammar.s_token ("", "]")),
           "194fe98d",
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
           "194fe98d",
           (fun _ (tl : 'ctyp list) _ (loc : Ploc.t) ->
              (MLast.TyTup (loc, tl) : 'ctyp)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "(")))
                Grammar.s_self)
             (Grammar.s_token ("", ")")),
           "194fe98d", (fun _ (t : 'ctyp) _ (loc : Ploc.t) -> (t : 'ctyp)));
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
           "194fe98d",
           (fun _ (tl : 'ctyp list) _ (t : 'ctyp) _ (loc : Ploc.t) ->
              (mktuptyp loc t tl : 'ctyp)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "(")))
                   (Grammar.s_token ("", "module")))
                (Grammar.s_nterm
                   (module_type : 'module_type Grammar.Entry.e)))
             (Grammar.s_token ("", ")")),
           "194fe98d",
           (fun _ (mt : 'module_type) _ _ (loc : Ploc.t) ->
              (MLast.TyPck (loc, mt) : 'ctyp)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_nterm
                (alg_extension : 'alg_extension Grammar.Entry.e)),
           "194fe98d",
           (fun (e : 'alg_extension) (loc : Ploc.t) ->
              (MLast.TyExten (loc, e) : 'ctyp)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "_")),
           "194fe98d", (fun _ (loc : Ploc.t) -> (MLast.TyAny loc : 'ctyp)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "..")),
           "194fe98d", (fun _ (loc : Ploc.t) -> (MLast.TyOpn loc : 'ctyp)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop (Grammar.s_token ("GIDENT", "")),
           "194fe98d",
           (fun (i : string) (loc : Ploc.t) ->
              (MLast.TyQuo (loc, greek_ascii_equiv i) : 'ctyp)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "'")))
             (Grammar.s_nterm (ident : 'ident Grammar.Entry.e)),
           "194fe98d",
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
           "194fe98d",
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
           "194fe98d", (fun _ _ _ (loc : Ploc.t) -> ("::" : 'cons_ident)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "(")))
             (Grammar.s_token ("", ")")),
           "194fe98d", (fun _ _ (loc : Ploc.t) -> ("()" : 'cons_ident)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "[")))
             (Grammar.s_token ("", "]")),
           "194fe98d", (fun _ _ (loc : Ploc.t) -> ("[]" : 'cons_ident)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop (Grammar.s_token ("UIDENT", "")),
           "194fe98d",
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
                (rest_constructor_declaration :
                 'rest_constructor_declaration Grammar.Entry.e)),
           "194fe98d",
           (fun (ls, tl, rto, attrs : 'rest_constructor_declaration)
                (ci : 'cons_ident) (loc : Ploc.t) ->
              (loc, ci, ls, tl, rto, attrs : 'constructor_declaration)))]];
    Grammar.extension
      (rest_constructor_declaration :
       'rest_constructor_declaration Grammar.Entry.e)
      None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop
                (Grammar.s_opt
                   (Grammar.s_rules
                      [Grammar.production
                         (Grammar.r_next
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("", ":")))
                            (Grammar.s_nterm
                               (ctyp_below_alg_attribute :
                                'ctyp_below_alg_attribute Grammar.Entry.e)),
                          "194fe98d",
                          (fun (t : 'ctyp_below_alg_attribute) _
                               (loc : Ploc.t) ->
                             (t : 'e__14)))])))
             (Grammar.s_nterm
                (alg_attributes : 'alg_attributes Grammar.Entry.e)),
           "194fe98d",
           (fun (attrs : 'alg_attributes) (rto : 'e__14 option)
                (loc : Ploc.t) ->
              ([], [], rto, attrs : 'rest_constructor_declaration)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("", "of")))
                      (Grammar.s_nterm
                         (type_binder_opt :
                          'type_binder_opt Grammar.Entry.e)))
                   (Grammar.s_list1sep
                      (Grammar.s_nterm
                         (ctyp_below_alg_attribute :
                          'ctyp_below_alg_attribute Grammar.Entry.e))
                      (Grammar.s_token ("", "and")) false))
                (Grammar.s_opt
                   (Grammar.s_rules
                      [Grammar.production
                         (Grammar.r_next
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("", ":")))
                            (Grammar.s_nterm
                               (ctyp_below_alg_attribute :
                                'ctyp_below_alg_attribute Grammar.Entry.e)),
                          "194fe98d",
                          (fun (t : 'ctyp_below_alg_attribute) _
                               (loc : Ploc.t) ->
                             (t : 'e__13)))])))
             (Grammar.s_nterm
                (alg_attributes : 'alg_attributes Grammar.Entry.e)),
           "194fe98d",
           (fun (attrs : 'alg_attributes) (rto : 'e__13 option)
                (cal : 'ctyp_below_alg_attribute list) (ls : 'type_binder_opt)
                _ (loc : Ploc.t) ->
              (ls, cal, rto, attrs : 'rest_constructor_declaration)))]];
    Grammar.extension
      (extension_constructor : 'extension_constructor Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop
                (Grammar.s_nterm (cons_ident : 'cons_ident Grammar.Entry.e)))
             (Grammar.s_nterm
                (rest_constructor_declaration :
                 'rest_constructor_declaration Grammar.Entry.e)),
           "194fe98d",
           (fun (ls, tl, rto, attrs : 'rest_constructor_declaration)
                (ci : 'cons_ident) (loc : Ploc.t) ->
              (MLast.EcTuple (loc, (loc, ci, ls, tl, rto, attrs)) :
               'extension_constructor)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next Grammar.r_stop
                      (Grammar.s_nterm
                         (cons_ident : 'cons_ident Grammar.Entry.e)))
                   (Grammar.s_token ("", "=")))
                (Grammar.s_nterm (longident : 'longident Grammar.Entry.e)))
             (Grammar.s_nterm
                (alg_attributes : 'alg_attributes Grammar.Entry.e)),
           "194fe98d",
           (fun (alg_attrs : 'alg_attributes) (b : 'longident) _
                (ci : 'cons_ident) (loc : Ploc.t) ->
              (MLast.EcRebind (loc, ci, b, alg_attrs) :
               'extension_constructor)))]];
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
           "194fe98d",
           (fun (attrs : 'alg_attributes) (t : 'ctyp) (mf : bool) _
                (i : string) (loc : Ploc.t) ->
              (mklabdecl loc i mf t attrs : 'label_declaration)))]];
    Grammar.extension (ident : 'ident Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next Grammar.r_stop (Grammar.s_token ("UIDENT", "")),
           "194fe98d",
           (fun (i : string) (loc : Ploc.t) -> (mkident i : 'ident)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop (Grammar.s_token ("LIDENT", "")),
           "194fe98d",
           (fun (i : string) (loc : Ploc.t) -> (mkident i : 'ident)))]];
    Grammar.extension (direction_flag : 'direction_flag Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "downto")),
           "194fe98d", (fun _ (loc : Ploc.t) -> (false : 'direction_flag)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "to")),
           "194fe98d", (fun _ (loc : Ploc.t) -> (true : 'direction_flag)))]];
    Grammar.extension (typevar : 'typevar Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next Grammar.r_stop (Grammar.s_token ("GIDENT", "")),
           "194fe98d",
           (fun (i : string) (loc : Ploc.t) ->
              (greek_ascii_equiv i : 'typevar)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "'")))
             (Grammar.s_nterm (ident : 'ident Grammar.Entry.e)),
           "194fe98d",
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
           "194fe98d",
           (fun (ctd : 'class_type_declaration list) _ _ (loc : Ploc.t) ->
              (MLast.StClt (loc, ctd) : 'str_item)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "class")))
             (Grammar.s_list1sep
                (Grammar.s_nterm
                   (class_declaration : 'class_declaration Grammar.Entry.e))
                (Grammar.s_token ("", "and")) false),
           "194fe98d",
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
           "194fe98d",
           (fun (ctd : 'class_type_declaration list) _ _ (loc : Ploc.t) ->
              (MLast.SgClt (loc, ctd) : 'sig_item)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "class")))
             (Grammar.s_list1sep
                (Grammar.s_nterm
                   (class_description : 'class_description Grammar.Entry.e))
                (Grammar.s_token ("", "and")) false),
           "194fe98d",
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
           "194fe98d",
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
           "194fe98d",
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
           "194fe98d",
           (fun (ce : 'class_expr) _ (ct : 'class_type) _ (loc : Ploc.t) ->
              (MLast.CeTyc (loc, ce, ct) : 'class_fun_binding)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "=")))
             (Grammar.s_nterm (class_expr : 'class_expr Grammar.Entry.e)),
           "194fe98d",
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
           "194fe98d",
           (fun _ (tpl : 'type_parameter list) _ (loc : Ploc.t) ->
              (loc, tpl : 'class_type_parameters)));
        Grammar.production
          (Grammar.r_stop, "194fe98d",
           (fun (loc : Ploc.t) -> (loc, [] : 'class_type_parameters)))]];
    Grammar.extension (class_fun_def : 'class_fun_def Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "->")))
             (Grammar.s_nterm (class_expr : 'class_expr Grammar.Entry.e)),
           "194fe98d",
           (fun (ce : 'class_expr) _ (loc : Ploc.t) ->
              (ce : 'class_fun_def)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop
                (Grammar.s_nterm (ipatt : 'ipatt Grammar.Entry.e)))
             Grammar.s_self,
           "194fe98d",
           (fun (ce : 'class_fun_def) (p : 'ipatt) (loc : Ploc.t) ->
              (MLast.CeFun (loc, p, ce) : 'class_fun_def)))]];
    Grammar.extension (class_expr : 'class_expr Grammar.Entry.e) None
      [Some "top", None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("", "let")))
                         (Grammar.s_token ("", "open")))
                      (Grammar.s_flag (Grammar.s_token ("", "!"))))
                   (Grammar.s_nterm
                      (extended_longident :
                       'extended_longident Grammar.Entry.e)))
                (Grammar.s_token ("", "in")))
             Grammar.s_self,
           "194fe98d",
           (fun (ce : 'class_expr) _ (i : 'extended_longident) (ovf : bool) _
                _ (loc : Ploc.t) ->
              (MLast.CeLop (loc, ovf, i, ce) : 'class_expr)));
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
           "194fe98d",
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
           "194fe98d",
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
           "194fe98d",
           (fun _ (attr : 'attribute_body) _ (ct : 'class_expr)
                (loc : Ploc.t) ->
              (MLast.CeAtt (loc, ct, attr) : 'class_expr)))];
       None, None,
       [Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_nterm
                (alg_extension : 'alg_extension Grammar.Entry.e)),
           "194fe98d",
           (fun (e : 'alg_extension) (loc : Ploc.t) ->
              (MLast.CeExten (loc, e) : 'class_expr)))];
       None, None,
       [Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_nterm
                (class_expr_apply : 'class_expr_apply Grammar.Entry.e)),
           "194fe98d",
           (fun (ce : 'class_expr_apply) (loc : Ploc.t) ->
              (ce : 'class_expr)))]];
    Grammar.extension (class_expr_apply : 'class_expr_apply Grammar.Entry.e)
      None
      [Some "apply", Some Gramext.LeftA,
       [Grammar.production
          (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
             (Grammar.s_nterml (expr : 'expr Grammar.Entry.e) "label"),
           "194fe98d",
           (fun (e : 'expr) (ce : 'class_expr_apply) (loc : Ploc.t) ->
              (MLast.CeApp (loc, ce, e) : 'class_expr_apply)))];
       None, None,
       [Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_nterm
                (class_expr_simple : 'class_expr_simple Grammar.Entry.e)),
           "194fe98d",
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
           "194fe98d",
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
           "194fe98d",
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
                (longident_lident : 'longident_lident Grammar.Entry.e)),
           "194fe98d",
           (fun (cli : 'longident_lident) _ (ctcl : 'ctyp list) _
                (loc : Ploc.t) ->
              (MLast.CeCon (loc, cli, ctcl) : 'class_expr_simple)));
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
           "194fe98d",
           (fun _ (cf : 'class_structure) (cspo : 'class_self_patt option) _
                (loc : Ploc.t) ->
              (MLast.CeStr (loc, cspo, cf) : 'class_expr_simple)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_nterm
                (longident_lident : 'longident_lident Grammar.Entry.e)),
           "194fe98d",
           (fun (cli : 'longident_lident) (loc : Ploc.t) ->
              (MLast.CeCon (loc, cli, []) : 'class_expr_simple)))]];
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
                       "194fe98d",
                       (fun _ (cf : 'class_str_item) (loc : Ploc.t) ->
                          (cf : 'e__15)))])),
           "194fe98d",
           (fun (cf : 'e__15 list) (loc : Ploc.t) ->
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
           "194fe98d",
           (fun _ (t : 'ctyp) _ (p : 'patt) _ (loc : Ploc.t) ->
              (MLast.PaTyc (loc, p, t) : 'class_self_patt)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "(")))
                (Grammar.s_nterm (patt : 'patt Grammar.Entry.e)))
             (Grammar.s_token ("", ")")),
           "194fe98d",
           (fun _ (p : 'patt) _ (loc : Ploc.t) -> (p : 'class_self_patt)))]];
    Grammar.extension (class_str_item : 'class_str_item Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_nterm
                (item_extension : 'item_extension Grammar.Entry.e)),
           "194fe98d",
           (fun (e : 'item_extension) (loc : Ploc.t) ->
              (MLast.CrExten (loc, e) : 'class_str_item)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_nterm
                (floating_attribute : 'floating_attribute Grammar.Entry.e)),
           "194fe98d",
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
           "194fe98d",
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
           "194fe98d",
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
           "194fe98d",
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
           "194fe98d",
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
           "194fe98d",
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
           "194fe98d",
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
           "194fe98d",
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
                          "194fe98d",
                          (fun _ (s : 'class_str_item) (loc : Ploc.t) ->
                             (s : 'e__16)))])))
             (Grammar.s_token ("", "end")),
           "194fe98d",
           (fun _ (st : 'e__16 list) _ (loc : Ploc.t) ->
              (MLast.CrDcl (loc, st) : 'class_str_item)))]];
    Grammar.extension (as_lident : 'as_lident Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "as")))
             (Grammar.s_token ("LIDENT", "")),
           "194fe98d",
           (fun (i : string) _ (loc : Ploc.t) -> (mkident i : 'as_lident)))]];
    Grammar.extension (polyt : 'polyt Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", ":")))
             (Grammar.s_nterm (ctyp : 'ctyp Grammar.Entry.e)),
           "194fe98d", (fun (t : 'ctyp) _ (loc : Ploc.t) -> (t : 'polyt)))]];
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
           "194fe98d",
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
           "194fe98d",
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
           "194fe98d",
           (fun (e : 'expr) _ (t : 'ctyp) _ (loc : Ploc.t) ->
              (MLast.ExTyc (loc, e, t) : 'cvalue_binding)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "=")))
             (Grammar.s_nterm (expr : 'expr Grammar.Entry.e)),
           "194fe98d",
           (fun (e : 'expr) _ (loc : Ploc.t) -> (e : 'cvalue_binding)))]];
    Grammar.extension (lident : 'lident Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next Grammar.r_stop (Grammar.s_token ("LIDENT", "")),
           "194fe98d",
           (fun (i : string) (loc : Ploc.t) -> (mkident i : 'lident)))]];
    Grammar.extension (class_type : 'class_type Grammar.Entry.e) None
      [Some "top", Some Gramext.RightA,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("", "let")))
                         (Grammar.s_token ("", "open")))
                      (Grammar.s_flag (Grammar.s_token ("", "!"))))
                   (Grammar.s_nterm
                      (extended_longident :
                       'extended_longident Grammar.Entry.e)))
                (Grammar.s_token ("", "in")))
             Grammar.s_self,
           "194fe98d",
           (fun (ce : 'class_type) _ (i : 'extended_longident) (ovf : bool) _
                _ (loc : Ploc.t) ->
              (MLast.CtLop (loc, ovf, i, ce) : 'class_type)));
        Grammar.production
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
           "194fe98d",
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
           "194fe98d",
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
           "194fe98d",
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
                          "194fe98d",
                          (fun _ (csf : 'class_sig_item) (loc : Ploc.t) ->
                             (csf : 'e__17)))])))
             (Grammar.s_token ("", "end")),
           "194fe98d",
           (fun _ (csf : 'e__17 list) (cst : 'class_self_type option) _
                (loc : Ploc.t) ->
              (MLast.CtSig (loc, cst, csf) : 'class_type)))];
       Some "simple", None,
       [Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_nterm
                (alg_extension : 'alg_extension Grammar.Entry.e)),
           "194fe98d",
           (fun (e : 'alg_extension) (loc : Ploc.t) ->
              (MLast.CtExten (loc, e) : 'class_type)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "(")))
                Grammar.s_self)
             (Grammar.s_token ("", ")")),
           "194fe98d",
           (fun _ (ct : 'class_type) _ (loc : Ploc.t) -> (ct : 'class_type)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop (Grammar.s_token ("LIDENT", "")),
           "194fe98d",
           (fun (i : string) (loc : Ploc.t) ->
              (MLast.CtLid (loc, i) : 'class_type)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop
                   (Grammar.s_nterm
                      (extended_longident :
                       'extended_longident Grammar.Entry.e)))
                (Grammar.s_token ("", ".")))
             (Grammar.s_token ("LIDENT", "")),
           "194fe98d",
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
           "194fe98d",
           (fun _ (t : 'ctyp) _ (loc : Ploc.t) -> (t : 'class_self_type)))]];
    Grammar.extension (class_sig_item : 'class_sig_item Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_nterm
                (item_extension : 'item_extension Grammar.Entry.e)),
           "194fe98d",
           (fun (e : 'item_extension) (loc : Ploc.t) ->
              (MLast.CgExten (loc, e) : 'class_sig_item)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_nterm
                (floating_attribute : 'floating_attribute Grammar.Entry.e)),
           "194fe98d",
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
           "194fe98d",
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
           "194fe98d",
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
           "194fe98d",
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
           "194fe98d",
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
           "194fe98d",
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
                          "194fe98d",
                          (fun _ (s : 'class_sig_item) (loc : Ploc.t) ->
                             (s : 'e__18)))])))
             (Grammar.s_token ("", "end")),
           "194fe98d",
           (fun _ (st : 'e__18 list) _ (loc : Ploc.t) ->
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
           "194fe98d",
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
           "194fe98d",
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
           "194fe98d",
           (fun _ (cf : 'class_structure) (cspo : 'class_self_patt option)
                (ext, attrs : 'ext_attributes) _ (loc : Ploc.t) ->
              (expr_to_inline (MLast.ExObj (loc, cspo, cf)) ext attrs :
               'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "new")))
                (Grammar.s_nterm
                   (ext_attributes : 'ext_attributes Grammar.Entry.e)))
             (Grammar.s_nterm
                (longident_lident : 'longident_lident Grammar.Entry.e)),
           "194fe98d",
           (fun (cli : 'longident_lident) (ext, attrs : 'ext_attributes) _
                (loc : Ploc.t) ->
              (expr_to_inline (MLast.ExNew (loc, cli)) ext attrs : 'expr)))]];
    Grammar.extension (expr : 'expr Grammar.Entry.e)
      (Some (Gramext.Level "."))
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                (Grammar.s_nterm (hashop : 'hashop Grammar.Entry.e)))
             Grammar.s_self,
           "194fe98d",
           (fun (e2 : 'expr) (op : 'hashop) (e : 'expr) (loc : Ploc.t) ->
              (MLast.ExApp
                 (loc, MLast.ExApp (loc, MLast.ExLid (loc, op), e), e2) :
               'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                (Grammar.s_token ("", "#")))
             (Grammar.s_nterm (lident : 'lident Grammar.Entry.e)),
           "194fe98d",
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
           "194fe98d",
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
           "194fe98d",
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
           "194fe98d",
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
           "194fe98d",
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
           "194fe98d",
           (fun _ (v : bool) (ml : 'field list) _ (loc : Ploc.t) ->
              (MLast.TyObj (loc, ml, v) : 'ctyp)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "#")))
             (Grammar.s_nterm
                (extended_longident_lident :
                 'extended_longident_lident Grammar.Entry.e)),
           "194fe98d",
           (fun (cli : 'extended_longident_lident) _ (loc : Ploc.t) ->
              (MLast.TyCls (loc, cli) : 'ctyp)))]];
    Grammar.extension (field : 'field Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop
                   (Grammar.s_nterm
                      (check_not_lident_colon :
                       'check_not_lident_colon Grammar.Entry.e)))
                (Grammar.s_nterm
                   (ctyp_below_alg_attribute :
                    'ctyp_below_alg_attribute Grammar.Entry.e)))
             (Grammar.s_nterm
                (alg_attributes : 'alg_attributes Grammar.Entry.e)),
           "194fe98d",
           (fun (alg_attrs : 'alg_attributes) (t : 'ctyp_below_alg_attribute)
                _ (loc : Ploc.t) ->
              (None, t, alg_attrs : 'field)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_nterm
                            (check_lident_colon :
                             'check_lident_colon Grammar.Entry.e)))
                      (Grammar.s_token ("LIDENT", "")))
                   (Grammar.s_token ("", ":")))
                (Grammar.s_nterm
                   (ctyp_below_alg_attribute :
                    'ctyp_below_alg_attribute Grammar.Entry.e)))
             (Grammar.s_nterm
                (alg_attributes : 'alg_attributes Grammar.Entry.e)),
           "194fe98d",
           (fun (alg_attrs : 'alg_attributes) (t : 'ctyp_below_alg_attribute)
                _ (lab : string) _ (loc : Ploc.t) ->
              (Some (mkident lab), t, alg_attrs : 'field)))]];
    Grammar.extension (longident_lident : 'longident_lident Grammar.Entry.e)
      None
      [None, None,
       [Grammar.production
          (Grammar.r_next Grammar.r_stop (Grammar.s_token ("LIDENT", "")),
           "194fe98d",
           (fun (i : string) (loc : Ploc.t) ->
              (None, i : 'longident_lident)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop
                   (Grammar.s_nterm (longident : 'longident Grammar.Entry.e)))
                (Grammar.s_token ("", ".")))
             (Grammar.s_token ("LIDENT", "")),
           "194fe98d",
           (fun (i : string) _ (li : 'longident) (loc : Ploc.t) ->
              (Some li, i : 'longident_lident)))]];
    Grammar.extension
      (extended_longident_lident : 'extended_longident_lident Grammar.Entry.e)
      None
      [None, None,
       [Grammar.production
          (Grammar.r_next Grammar.r_stop (Grammar.s_token ("LIDENT", "")),
           "194fe98d",
           (fun (i : string) (loc : Ploc.t) ->
              (None, i : 'extended_longident_lident)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop
                   (Grammar.s_nterm
                      (extended_longident :
                       'extended_longident Grammar.Entry.e)))
                (Grammar.s_token ("", ".")))
             (Grammar.s_token ("LIDENT", "")),
           "194fe98d",
           (fun (i : string) _ (li : 'extended_longident) (loc : Ploc.t) ->
              (Some li, i : 'extended_longident_lident)))]];
    (* Labels *)
    Grammar.extension (ctyp : 'ctyp Grammar.Entry.e)
      (Some (Gramext.After "arrow"))
      [None, Some Gramext.NonA,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop
                (Grammar.s_token ("QUESTIONIDENTCOLON", "")))
             Grammar.s_self,
           "194fe98d",
           (fun (t : 'ctyp) (i : string) (loc : Ploc.t) ->
              (MLast.TyOlb (loc, i, t) : 'ctyp)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop
                (Grammar.s_token ("TILDEIDENTCOLON", "")))
             Grammar.s_self,
           "194fe98d",
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
           "194fe98d",
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
           "194fe98d",
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
           "194fe98d",
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
           "194fe98d",
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
           "194fe98d",
           (fun (rfl : 'poly_variant list) (loc : Ploc.t) ->
              (rfl : 'poly_variant_list)))]];
    Grammar.extension (poly_variant : 'poly_variant Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_nterm (ctyp : 'ctyp Grammar.Entry.e)),
           "194fe98d",
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
           "194fe98d",
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
           "194fe98d",
           (fun (attrs : 'alg_attributes) (i : 'ident) _ (loc : Ploc.t) ->
              (MLast.PvTag (loc, i, true, [], attrs) : 'poly_variant)))]];
    Grammar.extension (name_tag : 'name_tag Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "`")))
             (Grammar.s_nterm (ident : 'ident Grammar.Entry.e)),
           "194fe98d",
           (fun (i : 'ident) _ (loc : Ploc.t) -> (i : 'name_tag)))]];
    Grammar.extension (patt : 'patt Grammar.Entry.e)
      (Some (Gramext.Level "simple"))
      [None, None,
       [Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_nterm
                (patt_option_label : 'patt_option_label Grammar.Entry.e)),
           "194fe98d",
           (fun (p : 'patt_option_label) (loc : Ploc.t) ->
              (let _ = warning_deprecated_since_6_00 loc in p : 'patt)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop (Grammar.s_token ("TILDEIDENT", "")),
           "194fe98d",
           (fun (i : string) (loc : Ploc.t) ->
              (let _ = warning_deprecated_since_6_00 loc in
               MLast.PaLab (loc, [MLast.PaLid (loc, i), None]) :
               'patt)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop
                (Grammar.s_token ("TILDEIDENTCOLON", "")))
             Grammar.s_self,
           "194fe98d",
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
                          "194fe98d",
                          (fun (e : 'expr) _ (loc : Ploc.t) ->
                             (e : 'e__19)))])))
             (Grammar.s_token ("", "}")),
           "194fe98d",
           (fun _ (eo : 'e__19 option) (p : 'patt_tcon) _ _ (loc : Ploc.t) ->
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
           "194fe98d",
           (fun _ (lppo : 'patt_tcon_opt_eq_patt list) _ _ (loc : Ploc.t) ->
              (MLast.PaLab (loc, lppo) : 'patt)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "#")))
             (Grammar.s_nterm
                (extended_longident_lident :
                 'extended_longident_lident Grammar.Entry.e)),
           "194fe98d",
           (fun (lili : 'extended_longident_lident) _ (loc : Ploc.t) ->
              (MLast.PaTyp (loc, lili) : 'patt)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "`")))
             (Grammar.s_nterm (ident : 'ident Grammar.Entry.e)),
           "194fe98d",
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
                       "194fe98d",
                       (fun (p : 'patt) _ (loc : Ploc.t) -> (p : 'e__20)))])),
           "194fe98d",
           (fun (po : 'e__20 option) (p : 'patt_tcon) (loc : Ploc.t) ->
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
           "194fe98d",
           (fun (t : 'ctyp) _ (p : 'patt) (loc : Ploc.t) ->
              (MLast.PaTyc (loc, p, t) : 'patt_tcon)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_nterm (patt : 'patt Grammar.Entry.e)),
           "194fe98d",
           (fun (p : 'patt) (loc : Ploc.t) -> (p : 'patt_tcon)))]];
    Grammar.extension (ipatt : 'ipatt Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_nterm
                (patt_option_label : 'patt_option_label Grammar.Entry.e)),
           "194fe98d",
           (fun (p : 'patt_option_label) (loc : Ploc.t) ->
              (let _ = warning_deprecated_since_6_00 loc in p : 'ipatt)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop (Grammar.s_token ("TILDEIDENT", "")),
           "194fe98d",
           (fun (i : string) (loc : Ploc.t) ->
              (let _ = warning_deprecated_since_6_00 loc in
               MLast.PaLab (loc, [MLast.PaLid (loc, i), None]) :
               'ipatt)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop
                (Grammar.s_token ("TILDEIDENTCOLON", "")))
             Grammar.s_self,
           "194fe98d",
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
                          "194fe98d",
                          (fun (e : 'expr) _ (loc : Ploc.t) ->
                             (e : 'e__21)))])))
             (Grammar.s_token ("", "}")),
           "194fe98d",
           (fun _ (eo : 'e__21 option) (p : 'ipatt_tcon) _ _ (loc : Ploc.t) ->
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
           "194fe98d",
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
                       "194fe98d",
                       (fun (p : 'patt) _ (loc : Ploc.t) -> (p : 'e__22)))])),
           "194fe98d",
           (fun (po : 'e__22 option) (p : 'ipatt_tcon) (loc : Ploc.t) ->
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
           "194fe98d",
           (fun (t : 'ctyp) _ (p : 'ipatt) (loc : Ploc.t) ->
              (MLast.PaTyc (loc, p, t) : 'ipatt_tcon)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_nterm (ipatt : 'ipatt Grammar.Entry.e)),
           "194fe98d",
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
           "194fe98d",
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
           "194fe98d",
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
           "194fe98d",
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
           "194fe98d",
           (fun _ (e : 'expr) _ (t : 'ctyp) _ (i : string) _ _
                (loc : Ploc.t) ->
              (MLast.PaOlb
                 (loc, MLast.PaTyc (loc, MLast.PaLid (loc, i), t), Some e) :
               'patt_option_label)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_token ("QUESTIONIDENT", "")),
           "194fe98d",
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
           "194fe98d",
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
           "194fe98d",
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
           "194fe98d",
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
           "194fe98d",
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
           "194fe98d",
           (fun (i : string) (loc : Ploc.t) ->
              (let _ = warning_deprecated_since_6_00 loc in
               MLast.ExOlb (loc, MLast.PaLid (loc, i), None) :
               'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop
                (Grammar.s_token ("QUESTIONIDENTCOLON", "")))
             Grammar.s_self,
           "194fe98d",
           (fun (e : 'expr) (i : string) (loc : Ploc.t) ->
              (let _ = warning_deprecated_since_6_00 loc in
               MLast.ExOlb (loc, MLast.PaLid (loc, i), Some e) :
               'expr)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop (Grammar.s_token ("TILDEIDENT", "")),
           "194fe98d",
           (fun (i : string) (loc : Ploc.t) ->
              (let _ = warning_deprecated_since_6_00 loc in
               MLast.ExLab (loc, [MLast.PaLid (loc, i), None]) :
               'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop
                (Grammar.s_token ("TILDEIDENTCOLON", "")))
             Grammar.s_self,
           "194fe98d",
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
           "194fe98d",
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
           "194fe98d",
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
           "194fe98d",
           (fun (eo : 'fun_binding option) (p : 'ipatt_tcon) (loc : Ploc.t) ->
              (p, eo : 'ipatt_tcon_fun_binding)))]];
    Grammar.extension (expr : 'expr Grammar.Entry.e)
      (Some (Gramext.Level "simple"))
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "`")))
             (Grammar.s_nterm (ident : 'ident Grammar.Entry.e)),
           "194fe98d",
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
           "194fe98d", (fun _ (loc : Ploc.t) -> ([], Some loc : 'interf)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop
                (Grammar.s_nterm
                   (sig_item_semi : 'sig_item_semi Grammar.Entry.e)))
             Grammar.s_self,
           "194fe98d",
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
           "194fe98d",
           (fun _ (dp : 'expr option) (n : string) _ (loc : Ploc.t) ->
              ([MLast.SgDir (loc, n, dp), loc], None : 'interf)))]];
    Grammar.extension (sig_item_semi : 'sig_item_semi Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop
                (Grammar.s_nterm (sig_item : 'sig_item Grammar.Entry.e)))
             (Grammar.s_token ("", ";")),
           "194fe98d",
           (fun _ (si : 'sig_item) (loc : Ploc.t) ->
              (si, loc : 'sig_item_semi)))]];
    Grammar.extension (implem : 'implem Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next Grammar.r_stop (Grammar.s_token ("EOI", "")),
           "194fe98d", (fun _ (loc : Ploc.t) -> ([], Some loc : 'implem)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop
                (Grammar.s_nterm
                   (str_item_semi : 'str_item_semi Grammar.Entry.e)))
             Grammar.s_self,
           "194fe98d",
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
           "194fe98d",
           (fun _ (dp : 'expr option) (n : string) _ (loc : Ploc.t) ->
              ([MLast.StDir (loc, n, dp), loc], None : 'implem)))]];
    Grammar.extension (str_item_semi : 'str_item_semi Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop
                (Grammar.s_nterm (str_item : 'str_item Grammar.Entry.e)))
             (Grammar.s_token ("", ";")),
           "194fe98d",
           (fun _ (si : 'str_item) (loc : Ploc.t) ->
              (si, loc : 'str_item_semi)))]];
    Grammar.extension (top_phrase : 'top_phrase Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next Grammar.r_stop (Grammar.s_token ("EOI", "")),
           "194fe98d", (fun _ (loc : Ploc.t) -> (None : 'top_phrase)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_nterm (phrase : 'phrase Grammar.Entry.e)),
           "194fe98d",
           (fun (ph : 'phrase) (loc : Ploc.t) -> (Some ph : 'top_phrase)))]];
    Grammar.extension (use_file : 'use_file Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next Grammar.r_stop (Grammar.s_token ("EOI", "")),
           "194fe98d", (fun _ (loc : Ploc.t) -> ([], false : 'use_file)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop
                   (Grammar.s_nterm (str_item : 'str_item Grammar.Entry.e)))
                (Grammar.s_token ("", ";")))
             Grammar.s_self,
           "194fe98d",
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
           "194fe98d",
           (fun _ (dp : 'expr option) (n : string) _ (loc : Ploc.t) ->
              ([MLast.StDir (loc, n, dp)], true : 'use_file)))]];
    Grammar.extension (phrase : 'phrase Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop
                (Grammar.s_nterm (str_item : 'str_item Grammar.Entry.e)))
             (Grammar.s_token ("", ";")),
           "194fe98d",
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
           "194fe98d",
           (fun _ (dp : 'expr option) (n : string) _ (loc : Ploc.t) ->
              (MLast.StDir (loc, n, dp) : 'phrase)))]];
    Grammar.extension (expr : 'expr Grammar.Entry.e)
      (Some (Gramext.Level "simple"))
      [None, None,
       [Grammar.production
          (Grammar.r_next Grammar.r_stop (Grammar.s_token ("QUOTATION", "")),
           "194fe98d",
           (fun (x : string) (loc : Ploc.t) ->
              (let con = quotation_content x in
               Pcaml.handle_expr_quotation loc con :
               'expr)))]];
    Grammar.extension (patt : 'patt Grammar.Entry.e)
      (Some (Gramext.Level "simple"))
      [None, None,
       [Grammar.production
          (Grammar.r_next Grammar.r_stop (Grammar.s_token ("QUOTATION", "")),
           "194fe98d",
           (fun (x : string) (loc : Ploc.t) ->
              (let con = quotation_content x in
               Pcaml.handle_patt_quotation loc con :
               'patt)))]]]);;
