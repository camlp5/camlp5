(* camlp5r *)
(* pa_macro.ml,v *)
(* Copyright (c) INRIA 2007-2017 *)

#load "pa_extend.cmo";
#load "q_MLast.cmo";

(*
Added statements:

  In structure items:

     DEFINE <uident>
     DEFINE <uident> = <expression>
     DEFINE <uident> <parameters> = <expression>
     IFDEF <dexpr> THEN <structure> <else> END
     IFNDEF <dexpr> THEN <structure> <else> END

     where <else> is either:
        ELSIFDEF <dexpr> THEN <structure> <else>
        ELSIFNDEF <dexpr> THEN <structure> <else>
        ELSE <structure>
        <nothing>

  In signature items:

     DEFINE <uident>
     DEFINE <uident> = <type>
     DEFINE <uident> <parameters> = <type>
     IFDEF <dexpr> THEN <signature> <else> END
     IFNDEF <dexpr> THEN <signature> <else> END

     where <else> is either:
        ELSIFDEF <dexpr> THEN <signature> <else>
        ELSIFNDEF <dexpr> THEN <signature> <else>
        ELSE <signature>
        <nothing>

  In expressions:

     IFDEF <dexpr> THEN <expression> <else> END
     IFNDEF <dexpr> THEN <expression> <else> END
     __FILE__
     __LOCATION__

     where <else> is either:
        ELSIFDEF <dexpr> THEN <expression> <else>
        ELSIFNDEF <dexpr> THEN <expression> <else>
        ELSE <expression>

  In patterns:

     IFDEF <dexpr> THEN <pattern> ELSE <pattern> END
     IFNDEF <dexpr> THEN <pattern> ELSE <pattern> END

  In types:

     IFDEF <dexpr> THEN <type> ELSE <type> END
     IFNDEF <dexpr> THEN <type> ELSE <type> END

  In constructors declarations, record label declarations and in match cases:

     IFDEF <dexpr> THEN <item> ELSE <item> END
     IFNDEF <dexpr> THEN <item> ELSE <item> END
     IFDEF <dexpr> THEN <item> END
     IFNDEF <dexpr> THEN <item> END

  A <dexpr> is either:

     <dexpr> OR <dexpr>
     <dexpr> AND <dexpr>
     NOT <dexpr>
     ( <dexpr> )
     <uident>
     OCAML_VERSION <op> <version>

  An <op> is among: < <= = > >=
  A <version> is a version of OCaml whose dots are replaced by underscores
  and the possible subpart starting with 'plus' are removed, and prefixed
  with 'OCAML_'. E.g.:
      OCAML_3_08 for ocaml version 3.08
      OCAML_3_13_0 for ocaml version 3.13.0+dev1

  As Camlp5 options:

     -D<uident>
     -U<uident>

  After having used a DEFINE <uident> followed by "= <expression>", you
  can use it in expressions *and* in patterns. If the expression defining
  the macro cannot be used as a pattern, there is an error message if
  it is used in a pattern.

  If the expression body of a DEFINE contains the identifier EVAL, the
  expression is evaluated at compile time. Only some kinds of expressions
  are interpreted (Char.chr, Char.code, binary + and -, characters,
  integers).

  The expression __FILE__ returns the current compiled file name.
  The expression __LOCATION__ returns the current location of itself.

*)

open Pcaml;
open Printf;
open Versdep;

type macro_value =
  [ MvExpr of list string and MLast.expr
  | MvType of list string and MLast.ctyp
  | MvNone ]
;

type item_or_def 'a =
  [ SdStr of 'a
  | SdDef of string and macro_value
  | SdUnd of string
  | SdNop ]
;

value rec list_remove x =
  fun
  [ [(y, _) :: l] when y = x -> l
  | [d :: l] -> [d :: list_remove x l]
  | [] -> [] ]
;

value oversion = do {
  let v = string_copy (bytes_of_string Pcaml.ocaml_version) in
  for i = 0 to string_length v - 1 do {
    match string_get v i with
    [ '0'..'9' | 'a'..'z' | 'A'..'Z' -> ()
    | _ -> string_set v i '_' ];
  };
  bytes_to_string v
};

value oname =
  if ocaml_name = "ocaml" then []
  else [(string_uppercase ocaml_name, MvNone)]
;

value defined =
  ref
    [("CAMLP5", MvNone); ("CAMLP5_4_02", MvNone); ("CAMLP5_5_00", MvNone);
     ("CAMLP5_6_00", MvNone); ("CAMLP5_6_02_1", MvNone);
     ("CAMLP5_6_09", MvNone); ("OCAML_" ^ oversion, MvNone) :: oname]
;

value defined_version loc =
  let s = "OCAML_" in
  loop (List.rev defined.val) where rec loop =
    fun
    [ [(d, _) :: l] ->
        if String.length d > String.length s &&
           String.sub d 0 (String.length s) = s
        then d
        else loop l
    | [] -> Ploc.raise loc (Failure "no defined version") ]
;

value is_defined i =
  (i = "STRICT" && Pcaml.strict_mode.val) ||
  (i = "COMPATIBLE_WITH_OLD_OCAML" &&
   Pcaml.flag_compatible_old_versions_of_ocaml.val) ||
  List.mem_assoc i defined.val
;

value print_defined () = do {
  let deflist =
    if Pcaml.strict_mode.val then [("STRICT", MvNone) :: defined.val]
    else defined.val
  in
  List.iter
    (fun (d, v) -> do {
       print_string d;
       match v with
       [ MvExpr _ _ -> print_string " = <expr>"
       | MvType _ _ -> print_string " = <type>"
       | MvNone -> () ];
       print_newline ()
     })
    deflist;
  if Sys.interactive.val then () else exit 0
};

value loc = Ploc.dummy;

value subst mloc env =
  loop where rec loop =
    fun
    [ <:expr< let $flag:rf$ $list:pel$ in $e$ >> ->
        let pel = List.map (fun (p, e) -> (p, loop e)) pel in
        <:expr< let $flag:rf$ $list:pel$ in $loop e$ >>
    | <:expr< if $e1$ then $e2$ else $e3$ >> ->
        <:expr< if $loop e1$ then $loop e2$ else $loop e3$ >>
    | <:expr< $e1$ $e2$ >> -> <:expr< $loop e1$ $loop e2$ >>
    | <:expr< $lid:x$ >> | <:expr< $uid:x$ >> as e ->
        try <:expr< $anti:List.assoc x env$ >> with [ Not_found -> e ]
    | <:expr< ($list:x$) >> -> <:expr< ($list:List.map loop x$) >>
    | <:expr< { $list:pel$ } >> ->
        let pel = List.map (fun (p, e) -> (p, loop e)) pel in
        <:expr< { $list:pel$ } >>
    | e -> e ]
;

value substp mloc env =
  loop where rec loop =
    fun
    [ <:expr< $e1$ . $e2$ >> -> <:patt< $loop e1$ . $loop e2$ >>
    | <:expr< $e1$ $e2$ >> -> <:patt< $loop e1$ $loop e2$ >>
    | <:expr< $lid:x$ >> ->
        try <:patt< $anti:List.assoc x env$ >> with
        [ Not_found -> <:patt< $lid:x$ >> ]
    | <:expr< $uid:x$ >> ->
        try <:patt< $anti:List.assoc x env$ >> with
        [ Not_found -> <:patt< $uid:x$ >> ]
    | <:expr< $int:x$ >> -> <:patt< $int:x$ >>
    | <:expr< $chr:x$ >> -> <:patt< $chr:x$ >>
    | <:expr< $str:x$ >> -> <:patt< $str:x$ >>
    | <:expr< ($list:x$) >> -> <:patt< ($list:List.map loop x$) >>
    | <:expr< { $list:pel$ } >> ->
        let ppl = List.map (fun (p, e) -> (p, loop e)) pel in
        <:patt< { $list:ppl$ } >>
    | x ->
        Ploc.raise mloc
          (Failure
             "this macro cannot be used in a pattern (see its definition)") ]
;

value substt mloc env =
  loop where rec loop =
    fun
    [ <:ctyp< $t1$ -> $t2$ >> -> <:ctyp< $loop t1$ -> $loop t2$ >>
    | <:ctyp< $t1$ $t2$ >> -> <:ctyp< $loop t1$ $loop t2$ >>
    | <:ctyp< ($list:tl$) >> -> <:ctyp< ($list:List.map loop tl$) >>
    | <:ctyp< $lid:x$ >> | <:ctyp< $uid:x$ >> as t ->
        try List.assoc x env with [ Not_found -> t ]
    | t -> t ]
;

value cannot_eval e =
  let loc = MLast.loc_of_expr e in
  Ploc.raise loc (Stream.Error "can't eval")
;

value rec eval =
  fun
  [ <:expr< Char.chr $e$ >> ->
      match eval e with
      [ <:expr< $int:i$ >> ->
          let c = Char.escaped (Char.chr (int_of_string i)) in
         <:expr< $chr:c$ >>
      | e -> cannot_eval e ]
  | <:expr< Char.code $e$ >> ->
      match eval e with
      [ <:expr< $chr:c$ >> ->
          let i = string_of_int (Char.code (Plexing.eval_char c)) in
          <:expr< $int:i$ >>
      | e ->
          cannot_eval e ]
  | <:expr< $op$ $x$ $y$ >> ->
      let f = eval op in
      let x = eval x in
      let y = eval y in
      match (x, y) with
      [ (<:expr< $int:x$ >>, <:expr< $int:y$ >>) ->
          let x = int_of_string x in
          let y = int_of_string y in
          match f with
          [ <:expr< $lid:"+"$ >> -> <:expr< $int:string_of_int (x + y)$ >>
          | <:expr< $lid:"-"$ >> -> <:expr< $int:string_of_int (x - y)$ >>
          | <:expr< $lid:"lor"$ >> ->
              let s = sprintf "0o%o" (x lor y) in
              <:expr< $int:s$ >>
          | _ -> cannot_eval op ]
      | _ -> cannot_eval op ]
  | <:expr< $uid:x$ >> as e ->
      try
        match List.assoc x defined.val with
        [ _ -> e ]
      with
      [ Not_found -> e ]
  | <:expr< $chr:_$ >> | <:expr< $int:_$ >> | <:expr< $lid:_$ >> as e -> e
  | e -> cannot_eval e ]
;

value may_eval =
  fun
  [ <:expr< EVAL $e$ >> -> eval e
  | e -> e ]
;

value incorrect_number loc l1 l2 =
  Ploc.raise loc
    (Failure
       (sprintf "expected %d parameters; found %d" (List.length l2)
          (List.length l1)))
;

value define eo x = do {
  match eo with
  [ MvExpr [] e ->
      EXTEND
        expr: LEVEL "simple"
          [ [ UIDENT $x$ -> may_eval (Reloc.expr (fun _ -> loc) 0 e) ] ]
        ;
        patt: LEVEL "simple"
          [ [ UIDENT $x$ ->
                let p = substp loc [] e in
                Reloc.patt (fun _ -> loc) 0 p ] ]
        ;
      END
  | MvExpr sl e ->
      EXTEND
        expr: LEVEL "apply"
          [ [ UIDENT $x$; param = SELF ->
                let el =
                  match param with
                  [ <:expr< ($list:el$) >> -> el
                  | e -> [e] ]
                in
                if List.length el = List.length sl then
                  let env = List.combine sl el in
                  let e = subst loc env e in
                  may_eval (Reloc.expr (fun _ -> loc) 0 e)
                else
                  incorrect_number loc el sl ] ]
        ;
        patt: LEVEL "simple"
          [ [ UIDENT $x$; param = SELF ->
                let pl =
                  match param with
                  [ <:patt< ($list:pl$) >> -> pl
                  | p -> [p] ]
                in
                if List.length pl = List.length sl then
                  let e = may_eval (Reloc.expr (fun _ -> loc) 0 e) in
                  let env = List.combine sl pl in
                  let p = substp loc env e in
                  Reloc.patt (fun _ -> loc) 0 p
                else
                  incorrect_number loc pl sl ] ]
        ;
      END
  | MvType [] t ->
      EXTEND
        ctyp: LEVEL "simple"
          [ [ UIDENT $x$ -> t ] ]
        ;
      END
  | MvType sl t ->
      EXTEND
        ctyp: LEVEL "apply"
          [ [ UIDENT $x$; param = SELF ->
                let tl = [param] in
                if List.length tl = List.length sl then
                  let env = List.combine sl tl in
                  let t = substt loc env t in
                  t
                else
                  incorrect_number loc tl sl ] ]
        ;
      END
  | MvNone -> () ];
  defined.val := [(x, eo) :: defined.val]
};

value undef x =
  try do {
    let eo = List.assoc x defined.val in
    match eo with
    [ MvExpr [] _ -> do {
        DELETE_RULE expr: UIDENT $x$ END;
        DELETE_RULE patt: UIDENT $x$ END;
      }
    | MvExpr _ _ -> do {
        DELETE_RULE expr: UIDENT $x$; SELF END;
        DELETE_RULE patt: UIDENT $x$; SELF END;
      }
    | MvType [] _ -> do {
        DELETE_RULE ctyp: UIDENT $x$ END;
      }
    | MvType _ _ -> do {
        DELETE_RULE ctyp: UIDENT $x$; SELF END;
      }
    | MvNone -> () ];
    defined.val := list_remove x defined.val
  }
  with
  [ Not_found -> () ]
;

value apply_directive loc n dp =
  let n = Pcaml.unvala n in
  match
    try Some (Pcaml.find_directive n) with
    [ Not_found -> None ]
  with
  [ Some f -> f (Pcaml.unvala dp)
  | None ->
      let msg = sprintf "unknown directive #%s" n in
      Ploc.raise loc (Stream.Error msg) ]
;

EXTEND
  GLOBAL: expr patt str_item sig_item constructor_declaration match_case
    label_declaration;
  str_item: FIRST
    [ [ x = str_macro_def ->
          match x with
          [ SdStr sil -> do {
              let sil = Pcaml.unvala sil in
              List.iter
                (fun
                 [ MLast.StDir loc n dp -> apply_directive loc n dp
                 | _ -> () ])
                sil;
              match sil with
              [ [si] -> si
              | sil -> <:str_item< declare $list:sil$ end >> ]
            }
          | SdDef x eo -> do { define eo x; <:str_item< declare end >> }
          | SdUnd x -> do { undef x; <:str_item< declare end >> }
          | SdNop -> <:str_item< declare end >> ] ] ]
  ;
  sig_item: FIRST
    [ [ x = sig_macro_def ->
          match x with
          [ SdStr sil -> do {
              let sil = Pcaml.unvala sil in
              List.iter
                (fun
                 [ MLast.SgDir loc n dp -> apply_directive loc n dp
                 | _ -> () ])
                sil;
              match sil with
              [ [si] -> si
              | sil -> <:sig_item< declare $list:sil$ end >> ]
            }
          | SdDef x eo -> do { define eo x; <:sig_item< declare end >> }
          | SdUnd x -> do { undef x; <:sig_item< declare end >> }
          | SdNop -> <:sig_item< declare end >> ] ] ]
  ;
  str_macro_def:
    [ [ "DEFINE"; i = uident; ome = opt_macro_expr -> SdDef i ome
      | "DEFINE_TYPE"; i = uident; ome = opt_macro_type -> SdDef i ome
      | "UNDEF"; i = uident -> SdUnd i
      | "IFDEF"; e = dexpr; "THEN"; d1 = structure_or_macro;
        d2 = else_str; "END" ->
          if e then d1 else d2
      | "IFNDEF"; e = dexpr; "THEN"; d1 = structure_or_macro;
        d2 = else_str; "END" ->
          if not e then d1 else d2 ] ]
  ;
  else_str:
    [ [ "ELSIFDEF"; e = dexpr; "THEN"; d1 = structure_or_macro;
        d2 = else_str -> if e then d1 else d2
      | "ELSIFNDEF"; e = dexpr; "THEN"; d1 = structure_or_macro;
        d2 = else_str -> if not e then d1 else d2
      | "ELSE"; d1 = structure_or_macro -> d1
      | -> SdNop ] ]
  ;
  sig_macro_def:
    [ [ "DEFINE"; i = uident; omt = opt_macro_type -> SdDef i omt
      | "DEFINE_TYPE"; i = uident; omt = opt_macro_type -> SdDef i omt
      | "UNDEF"; i = uident -> SdUnd i
      | "IFDEF"; e = dexpr; "THEN"; d1 = signature_or_macro;
        d2 = else_sig; "END" ->
          if e then d1 else d2
      | "IFNDEF"; e = dexpr; "THEN"; d1 = signature_or_macro;
        d2 = else_sig; "END" ->
          if not e then d1 else d2 ] ]
  ;
  else_sig:
    [ [ "ELSIFDEF"; e = dexpr; "THEN"; d1 = signature_or_macro;
        d2 = else_sig -> if e then d1 else d2
      | "ELSIFNDEF"; e = dexpr; "THEN"; d1 = signature_or_macro;
        d2 = else_sig -> if not e then d1 else d2
      | "ELSE"; d1 = signature_or_macro -> d1
      | -> SdNop ] ]
  ;
  structure_or_macro:
    [ [ d = str_macro_def -> d
      | sil = structure -> SdStr sil ] ]
  ;
  signature_or_macro:
    [ [ d = sig_macro_def -> d
      | sil = signature -> SdStr sil ] ]
  ;
  opt_macro_expr:
    [ [ pl = macro_param; "="; e = expr -> MvExpr pl e
      | "="; e = expr -> MvExpr [] e
      | -> MvNone ] ]
  ;
  opt_macro_type:
    [ [ pl = LIST1 LIDENT; "="; t = ctyp -> MvType pl t
      | "="; t = ctyp -> MvType [] t
      | -> MvNone ] ]
  ;
  macro_param:
    [ [ sl = LIST1 LIDENT -> sl
      | "("; sl = LIST1 LIDENT SEP ","; ")" -> sl ] ]
  ;
  expr: LEVEL "top"
    [ [ "IFDEF"; e = dexpr; "THEN"; e1 = SELF; e2 = else_expr; "END" ->
          if e then e1 else e2
      | "IFNDEF"; e = dexpr; "THEN"; e1 = SELF; e2 = else_expr; "END" ->
          if not e then e1 else e2 ] ]
  ;
  else_expr:
    [ [ "ELSIFDEF"; e = dexpr; "THEN"; e1 = expr; e2 = else_expr ->
          if e then e1 else e2
      | "ELSIFNDEF"; e = dexpr; "THEN"; e1 = expr; e2 = else_expr ->
          if not e then e1 else e2
      | "ELSE"; e = expr -> e ] ]
  ;
  expr: LEVEL "simple"
    [ [ LIDENT "__FILE__" -> <:expr< $str:Ploc.file_name loc$ >>
      | LIDENT "__LOCATION__" ->
          let bp = string_of_int (Ploc.first_pos loc) in
          let ep = string_of_int (Ploc.last_pos loc) in
          <:expr< ($int:bp$, $int:ep$) >> ] ]
  ;
  patt:
    [ [ "IFDEF"; e = dexpr; "THEN"; p1 = SELF; p2 = else_patt; "END" ->
          if e then p1 else p2
      | "IFNDEF"; e = dexpr; "THEN"; p1 = SELF; p2 = else_patt; "END" ->
          if e then p2 else p1 ] ]
  ;
  else_patt:
    [ [ "ELSIFDEF"; e = dexpr; "THEN"; p1 = patt; p2 = else_patt ->
          if e then p1 else p2
      | "ELSIFNDEF"; e = dexpr; "THEN"; p1 = patt; p2 = else_patt ->
          if not e then p1 else p2
      | "ELSE"; p = patt -> p ] ]
  ;
  constructor_declaration: FIRST
    [ [ "IFDEF"; e = dexpr; "THEN"; x = SELF; "END" ->
          if e then x else Grammar.skip_item x
      | "IFDEF"; e = dexpr; "THEN"; x = SELF; "ELSE"; y = SELF; "END" ->
          if e then x else y
      | "IFNDEF"; e = dexpr; "THEN"; x = SELF; "END" ->
          if e then Grammar.skip_item x else x
      | "IFNDEF"; e = dexpr; "THEN"; x = SELF; "ELSE"; y = SELF; "END" ->
          if e then y else x ] ]
  ;
  label_declaration: FIRST
    [ [ "IFDEF"; e = dexpr; "THEN"; x = SELF; "END" ->
          if e then x else Grammar.skip_item x
      | "IFDEF"; e = dexpr; "THEN"; x = SELF; "ELSE"; y = SELF; "END" ->
          if e then x else y
      | "IFNDEF"; e = dexpr; "THEN"; x = SELF; "END" ->
          if e then Grammar.skip_item x else x
      | "IFNDEF"; e = dexpr; "THEN"; x = SELF; "ELSE"; y = SELF; "END" ->
          if e then y else x ] ]
  ;
  match_case: FIRST
    [ [ "IFDEF"; e = dexpr; "THEN"; x = SELF; y = else_match_case; "END" ->
          if e then x else y
      | "IFDEF"; e = dexpr; "THEN"; x = SELF; "END" ->
          if e then x else Grammar.skip_item x
      | "IFNDEF"; e = dexpr; "THEN"; x = SELF; y = else_match_case; "END" ->
          if not e then x else y
      | "IFNDEF"; e = dexpr; "THEN"; x = SELF; "END" ->
          if not e then x else Grammar.skip_item x ] ]
  ;
  else_match_case:
    [ RIGHTA
      [ "ELSIFDEF"; e = dexpr; "THEN"; x = match_case; y = else_match_case ->
          if e then x else y
      | "ELSIFDEF"; e = dexpr; "THEN"; x = match_case ->
          if e then x else Grammar.skip_item x
      | "ELSIFNDEF"; e = dexpr; "THEN"; x = match_case; y = else_match_case ->
          if not e then x else y
      | "ELSIFNDEF"; e = dexpr; "THEN"; x = match_case ->
          if not e then x else Grammar.skip_item x
      | "ELSE"; x = match_case -> x ] ]
  ;
  dexpr:
    [ [ x = SELF; "OR"; y = SELF -> x || y ]
    | [ x = SELF; "AND"; y = SELF -> x && y ]
    | [ "OCAML_VERSION"; f = op; y = uident -> f (defined_version loc) y ]
    | [ "NOT"; x = SELF -> not x ]
    | [ i = uident -> is_defined i
      | "("; x = SELF; ")" -> x ] ]
  ;
  op:
    [ [ "<=" -> \<=
      | "<" -> \<
      | "=" -> \=
      | "<>" -> \<>
      | ">" -> \>
      | ">=" -> \>= ] ]
  ;
  uident:
    [ [ i = UIDENT -> i ] ]
  ;
END;

Pcaml.add_option "-D" (Arg.String (define MvNone))
  "<string> Define for IFDEF instruction.";

Pcaml.add_option "-U" (Arg.String undef)
  "<string> Undefine for IFDEF instruction.";

Pcaml.add_option "-defined" (Arg.Unit print_defined)
  " Print the defined macros and exit.";
