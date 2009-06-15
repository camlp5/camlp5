(* camlp5r *)
(* $Id: pa_macro.ml,v 1.21 2007/09/06 20:48:56 deraugla Exp $ *)

(*
Added statements:

  At toplevel (structure item):

     DEFINE <uident>
     DEFINE <uident> = <expression>
     DEFINE <uident> (<parameters>) = <expression>
     IFDEF <dexpr> THEN <structure_items> END
     IFDEF <dexpr> THEN <structure_items> ELSE <structure_items> END
     IFNDEF <dexpr> THEN <structure_items> END
     IFNDEF <dexpr> THEN <structure_items> ELSE <structure_items> END

  In expressions:

     IFDEF <dexpr> THEN <expression> ELSE <expression> END
     IFNDEF <dexpr> THEN <expression> ELSE <expression> END
     __FILE__
     __LOCATION__

  In patterns:

     IFDEF <dexpr> THEN <pattern> ELSE <pattern> END
     IFNDEF <dexpr> THEN <pattern> ELSE <pattern> END

  A <dexpr> is either:

     <dexpr> OR <dexpr>
     <dexpr> AND <dexpr>
     NOT <dexpr>
     ( <dexpr> )
     <uident>

  As Camlp5 options:

     -D<uident>
     -U<uident>

  After having used a DEFINE <uident> followed by "= <expression>", you
  can use it in expressions *and* in patterns. If the expression defining
  the macro cannot be used as a pattern, there is an error message if
  it is used in a pattern.

  The expression __FILE__ returns the current compiled file name.
  The expression __LOCATION__ returns the current location of itself.

*)

#load "pa_extend.cmo";
#load "q_MLast.cmo";

open Pcaml;

type item_or_def 'a =
  [ SdStr of 'a
  | SdDef of string and option (list string * MLast.expr)
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
  let v = String.copy Pconfig.ocaml_version in
  for i = 0 to String.length v - 1 do {
    match v.[i] with
    [ '0'..'9' -> ()
    | _ -> v.[i] := '_' ];
  };
  v
};

value defined =
  ref
    [("CAMLP5", None); ("CAMLP5_4_02", None); ("OCAML_" ^ oversion, None)]
;

value is_defined i =
  (i = "STRICT" && Pcaml.strict_mode.val) ||
  List.mem_assoc i defined.val 
;

value print_defined () = do {
  List.iter
    (fun (d, v) -> do {
       print_string d;
       match v with
       [ Some _ -> print_string " = ..."
       | None -> () ];
       print_newline ()
     })
    defined.val;
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
    [ <:expr< $e1$ $e2$ >> -> <:patt< $loop e1$ $loop e2$ >>
    | <:expr< $lid:x$ >> ->
        try <:patt< $anti:List.assoc x env$ >> with
        [ Not_found -> <:patt< $lid:x$ >> ]
    | <:expr< $uid:x$ >> ->
        try <:patt< $anti:List.assoc x env$ >> with
        [ Not_found -> <:patt< $uid:x$ >> ]
    | <:expr< $int:x$ >> -> <:patt< $int:x$ >>
    | <:expr< ($list:x$) >> -> <:patt< ($list:List.map loop x$) >>
    | <:expr< { $list:pel$ } >> ->
        let ppl = List.map (fun (p, e) -> (p, loop e)) pel in
        <:patt< { $list:ppl$ } >>
    | x ->
        Ploc.raise mloc
          (Failure
             "this macro cannot be used in a pattern (see its definition)") ]
;

value incorrect_number loc l1 l2 =
  Ploc.raise loc
    (Failure
       (Printf.sprintf "expected %d parameters; found %d" (List.length l2)
          (List.length l1)))
;

value define eo x = do {
  match eo with
  [ Some ([], e) ->
      EXTEND
        expr: LEVEL "simple"
          [ [ UIDENT $x$ -> Reloc.expr (fun _ -> loc) 0 e ] ]
        ;
        patt: LEVEL "simple"
          [ [ UIDENT $x$ ->
                let p = substp loc [] e in
                Reloc.patt (fun _ -> loc) 0 p ] ]
        ;
      END
  | Some (sl, e) ->
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
                  Reloc.expr (fun _ -> loc) 0 e
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
                  let env = List.combine sl pl in
                  let p = substp loc env e in
                  Reloc.patt (fun _ -> loc) 0 p
                else
                  incorrect_number loc pl sl ] ]
        ;
      END
  | None -> () ];
  defined.val := [(x, eo) :: defined.val]
};

value undef x =
  try do {
    let eo = List.assoc x defined.val in
    match eo with
    [ Some ([], _) -> do {
        DELETE_RULE expr: UIDENT $x$ END;
        DELETE_RULE patt: UIDENT $x$ END;
      }
    | Some (_, _) -> do {
        DELETE_RULE expr: UIDENT $x$; SELF END;
        DELETE_RULE patt: UIDENT $x$; SELF END;
      }
    | None -> () ];
    defined.val := list_remove x defined.val
  }
  with
  [ Not_found -> () ]
;

EXTEND
  GLOBAL: expr patt str_item sig_item;
  str_item: FIRST
    [ [ x = str_macro_def ->
          match x with
          [ SdStr [si] -> si
          | SdStr sil -> <:str_item< declare $list:sil$ end >>
          | SdDef x eo -> do { define eo x; <:str_item< declare end >> }
          | SdUnd x -> do { undef x; <:str_item< declare end >> }
          | SdNop -> <:str_item< declare end >> ] ] ]
  ;
  sig_item: FIRST
    [ [ x = sig_macro_def ->
          match x with
          [ SdStr [si] -> si
          | SdStr sil -> <:sig_item< declare $list:sil$ end >>
          | SdDef x eo -> do { define eo x; <:sig_item< declare end >> }
          | SdUnd x -> do { undef x; <:sig_item< declare end >> }
          | SdNop -> <:sig_item< declare end >> ] ] ]
  ;
  str_macro_def:
    [ [ "DEFINE"; i = uident; def = opt_macro_value -> SdDef i def
      | "UNDEF"; i = uident -> SdUnd i
      | "IFDEF"; e = dexpr; "THEN"; d = str_item_or_macro; "END" ->
          if e then d else SdNop
      | "IFDEF"; e = dexpr; "THEN"; d1 = str_item_or_macro; "ELSE";
        d2 = str_item_or_macro; "END" ->
          if e then d1 else d2
      | "IFNDEF"; e = dexpr; "THEN"; d = str_item_or_macro; "END" ->
          if e then SdNop else d
      | "IFNDEF"; e = dexpr; "THEN"; d1 = str_item_or_macro; "ELSE";
        d2 = str_item_or_macro; "END" ->
          if e then d2 else d1 ] ]
  ;
  sig_macro_def:
    [ [ "DEFINE"; i = uident -> SdDef i None
      | "UNDEF"; i = uident -> SdUnd i
      | "IFDEF"; e = dexpr; "THEN"; d = sig_item_or_macro; "END" ->
          if e then d else SdNop
      | "IFDEF"; e = dexpr; "THEN"; d1 = sig_item_or_macro; "ELSE";
        d2 = sig_item_or_macro; "END" ->
          if e then d1 else d2
      | "IFNDEF"; e = dexpr; "THEN"; d = sig_item_or_macro; "END" ->
          if e then SdNop else d
      | "IFNDEF"; e = dexpr; "THEN"; d1 = sig_item_or_macro; "ELSE";
        d2 = sig_item_or_macro; "END" ->
          if e then d2 else d1 ] ]
  ;
  str_item_or_macro:
    [ [ d = str_macro_def -> d
      | si = LIST1 str_item -> SdStr si ] ]
  ;
  sig_item_or_macro:
    [ [ d = sig_macro_def -> d
      | si = LIST1 sig_item -> SdStr si ] ]
  ;
  opt_macro_value:
    [ [ "("; pl = LIST1 LIDENT SEP ","; ")"; "="; e = expr -> Some (pl, e)
      | "="; e = expr -> Some ([], e)
      | -> None ] ]
  ;
  expr: LEVEL "top"
    [ [ "IFDEF"; e = dexpr; "THEN"; e1 = SELF; "ELSE"; e2 = SELF; "END" ->
          if e then e1 else e2
      | "IFNDEF"; e = dexpr; "THEN"; e1 = SELF; "ELSE"; e2 = SELF; "END" ->
          if e then e2 else e1 ] ]
  ;
  expr: LEVEL "simple"
    [ [ LIDENT "__FILE__" -> <:expr< $str:Pcaml.input_file.val$ >>
      | LIDENT "__LOCATION__" ->
          let bp = string_of_int (Ploc.first_pos loc) in
          let ep = string_of_int (Ploc.last_pos loc) in
          <:expr< ($int:bp$, $int:ep$) >> ] ]
  ;
  patt:
    [ [ "IFDEF"; e = dexpr; "THEN"; p1 = SELF; "ELSE"; p2 = SELF; "END" ->
          if e then p1 else p2
      | "IFNDEF"; e = dexpr; "THEN"; p1 = SELF; "ELSE"; p2 = SELF; "END" ->
          if e then p2 else p1 ] ]
  ;
  dexpr:
    [ [ x = SELF; "OR"; y = SELF -> x || y ]
    | [ x = SELF; "AND"; y = SELF -> y && y ]
    | [ "NOT"; x = SELF -> not x ]
    | [ i = uident -> is_defined i
      | "("; x = SELF; ")" -> x ] ]
  ;
  uident:
    [ [ i = UIDENT -> i ] ]
  ;
END;

Pcaml.add_option "-D" (Arg.String (define None))
  "<string> Define for IFDEF instruction.";

Pcaml.add_option "-U" (Arg.String undef)
  "<string> Undefine for IFDEF instruction.";

Pcaml.add_option "-defined" (Arg.Unit print_defined)
  " Print the defined macros and exit.";
