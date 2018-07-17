(* camlp5r *)
(* pa_pragma.ml,v *)
(* Copyright (c) INRIA 2007-2017 *)

#load "pa_macro.cmo";
#load "q_MLast.cmo";
#qmod "ctyp,Type";

(* expressions evaluated in the context of the preprocessor *)
(* syntax at toplevel: #pragma <expr> *)

open Printf;
open Versdep;

value string_of_obj_tag x =
  if Obj.is_block (Obj.repr x) then
    let t = Obj.tag (Obj.repr x) in
    "tag = " ^ string_of_int t ^
    (if t = 0 then " size = " ^ string_of_int (Obj.size (Obj.repr x)) else "")
  else "int_val = " ^ string_of_int (Obj.magic x)
;

value not_impl loc name x =
  let desc = string_of_obj_tag x in
  Ploc.raise loc (Failure ("pa_pragma: not impl " ^ name ^ " " ^ desc))
;

module Type =
  struct
    type loc = Ploc.t;
    type t =
      [ TyAcc of loc and t and t
      | TyAny of loc
      | TyApp of loc and t and t
      | TyArr of loc and t and t
      | TyLid of loc and MLast.v string
      | TyQuo of loc and MLast.v (ref (option t))
      | TyTup of loc and MLast.v (list t)
      | TyUid of loc and MLast.v string ]
    ;
  end
;

type expr_v 'e =
  { ctyp : Type.t;
    expr : 'e;
    patt :
      (env 'e -> MLast.patt -> Type.t -> Obj.t -> option (env 'e)) ->
        env 'e -> list MLast.patt -> Obj.t -> option (env 'e) }
and bind_v 'e = { by_let : bool; valu : mutable expr_v 'e }
and env 'e = list (string * bind_v 'e);

value ty_var =
  let loc = Ploc.dummy in
  fun () -> <:ctyp< '$ref None$ >>
;

value vars = ref [];
value rec type_of_ctyp t =
  match t with
  [ MLast.TyAcc loc t1 t2 -> <:ctyp< $type_of_ctyp t1$ . $type_of_ctyp t2$ >>
  | MLast.TyAny loc -> <:ctyp< _ >>
  | MLast.TyApp loc t1 t2 -> <:ctyp< $type_of_ctyp t1$ $type_of_ctyp t2$ >>
  | MLast.TyArr loc t1 t2 -> <:ctyp< $type_of_ctyp t1$ -> $type_of_ctyp t2$ >>
  | MLast.TyLid loc s -> <:ctyp< $_lid:s$ >>
  | MLast.TyQuo loc s ->
      try List.assoc s vars.val with
      [ Not_found -> do {
          let v = ty_var () in
          vars.val := [(s, v) :: vars.val];
          v
        } ]
  | MLast.TyUid loc s -> <:ctyp< $_uid:s$ >>
  | t -> not_impl (MLast.loc_of_ctyp t) "Type.of_ctyp" t ]
;

value ty_var_name_tab = ref [];

value rec str_of_ty1 loc =
  fun
  [ <:ctyp< $t1$ -> $t2$ >> ->
      let s1 = str_of_ty2 loc t1 in
      let s2 = str_of_ty1 loc t2 in
      s1 ^ " -> " ^ s2
  | t -> str_of_ty2 loc t ]
and str_of_ty2 loc =
  fun
  [ <:ctyp< $t1$ $t2$ >> ->
      let s1 = str_of_ty2 loc t1 in
      let s2 = str_of_ty3 loc t2 in
      s1 ^ " " ^ s2
  | t -> str_of_ty3 loc t ]
and str_of_ty3 loc t =
  match t with
  [ <:ctyp< ( $list:tl$ ) >> ->
      let sl = List.map (str_of_ty1 loc) tl in
      "(" ^
      List.fold_left (fun s t -> if s = "" then t else s ^ " * " ^ t) "" sl ^
      ")"
  | <:ctyp< $t1$ . $t2$ >> -> str_of_ty1 loc t1 ^ "." ^ str_of_ty1 loc t2
  | <:ctyp< '$s$ >> ->
      match s.val with
      [ Some t -> str_of_ty3 loc t
      | None ->
          try List.assq s ty_var_name_tab.val with
          [ Not_found -> do {
              let len = List.length ty_var_name_tab.val in
              let n = "'" ^ String.make 1 (Char.chr (Char.code 'a' + len)) in
              ty_var_name_tab.val := [(s, n) :: ty_var_name_tab.val];
              n
            } ] ]
  | <:ctyp< $lid:s$ >> -> s
  | <:ctyp< $uid:s$ >> -> s
  | <:ctyp< _ >> -> "_"
  | <:ctyp< $_$ $_$ >> -> "(" ^ str_of_ty1 loc t ^ ")"
  | t -> not_impl loc "str_of_ty3" t ]
;

value rec eval_type loc t =
  match t with
  [ <:ctyp< $t1$ -> $t2$ >> ->
      <:ctyp< $eval_type loc t1$ -> $eval_type loc t2$ >>
  | <:ctyp< $t1$ . $t2$ >> ->
      <:ctyp< $eval_type loc t1$ . $eval_type loc t2$ >>
  | <:ctyp< $t1$ $t2$ >> ->
      <:ctyp< $eval_type loc t1$ $eval_type loc t2$ >>
  | <:ctyp< ( $list:tl$ ) >> ->
      <:ctyp< ( $list:List.map (eval_type loc) tl$ ) >>
  | <:ctyp< '$s$ >> ->
      match s.val with
      [ Some t -> eval_type loc t
      | None -> t ]
  | <:ctyp< $_lid:_$ >> | <:ctyp< $uid:_$ >> | <:ctyp< _ >> -> t
  | IFDEF STRICT THEN
      _ -> failwith "eval_type"
    END ]
;

value str_of_ty loc t = do {
  ty_var_name_tab.val := [];
  str_of_ty1 loc (eval_type loc t)
};

value bad_type loc expected_t found_t =
  let s1 = str_of_ty loc expected_t in
  let s2 = str_of_ty loc found_t in
  let s =
    if String.length s1 > 40 || String.length s2 > 40 then
      Printf.sprintf "\nType expected:\n  %s\nType found:\n  %s\n" s1 s2
    else
      Printf.sprintf "\n  type expected: %s\n     type found: %s\n" s1 s2
  in
  Ploc.raise loc (Stream.Error s)
;

value unbound_var loc s =
  Ploc.raise loc
    (Failure (sprintf "Variable not implemented in pa_pragma: %s" s))
;

value unbound_cons loc s =
  Ploc.raise loc
    (Failure (sprintf "Constructor not implemented in pa_pragma: %s" s))
;

value error loc s = Ploc.raise loc (Failure s);

value inst_vars = ref [];
value rec inst loc t =
  match t with
  [ <:ctyp< $t1$ -> $t2$ >> -> <:ctyp< $inst loc t1$ -> $inst loc t2$ >>
  | <:ctyp< $t1$ $t2$ >> -> <:ctyp< $inst loc t1$ $inst loc t2$ >>
  | <:ctyp< ( $list:tl$ ) >> -> <:ctyp< ( $list:List.map (inst loc) tl$ ) >>
  | <:ctyp< '$s$ >> ->
      match s.val with
      [ Some t -> inst loc t
      | None ->
          try List.assq s inst_vars.val with
          [ Not_found -> do {
              let t = ty_var () in
              inst_vars.val := [(s, t) :: inst_vars.val];
              t
            } ] ]
  | <:ctyp< $_$ . $_$ >> | <:ctyp< $lid:_$ >> -> t
  | t -> not_impl loc "instantiate" t ]
;

value instantiate loc s t = do { inst_vars.val := []; inst loc t };

value rec unify loc t1 t2 =
  match (eval_type loc t1, eval_type loc t2) with
  [ (<:ctyp< MLast.loc >>, t2) ->
      let t1 = <:ctyp< Ploc.t >> in
      unify loc t1 t2

  | (<:ctyp< $t11$ $t12$ >>, <:ctyp< $t21$ $t22$ >>) ->
      unify loc t11 t21 && unify loc t12 t22
  | (<:ctyp< $t11$ . $t12$ >>, <:ctyp< $t21$ . $t22$ >>) ->
      unify loc t11 t21 && unify loc t12 t22
  | (<:ctyp< $t11$ -> $t12$ >>, <:ctyp< $t21$ -> $t22$ >>) ->
      unify loc t11 t21 && unify loc t12 t22
  | (<:ctyp< ( $list:tl1$ ) >>, <:ctyp< ( $list:tl2$ ) >>) ->
      loop tl1 tl2 where rec loop l1 l2 =
        match (l1, l2) with
        [ ([t1 :: rest1], [t2 :: rest2]) ->
            unify loc t1 t2 && loop rest1 rest2
        | ([], []) -> True
        | _ -> False ]

  | (t1, <:ctyp< '$s$ >>) ->
      match s.val with
      [ Some t2 ->
          if unify loc t1 t2 then do { s.val := Some t1; True } else False
      | None -> do {
          let same =
            match t1 with
            [ <:ctyp< '$s1$ >> -> s1 == s
            | _ -> False ]
          in
          if not same then s.val := Some t1 else ();
          True
        } ]
  | (<:ctyp< '$s$ >>, t2) -> unify loc t2 t1

  | (<:ctyp< MLast.type_decl >>, t2) ->
      let t1 =
        <:ctyp<
          ((MLast.loc * string) *
           list (string * (bool * bool)) *
           MLast.ctyp *
           list (MLast.ctyp * MLast.ctyp)) >>
      in
      unify loc t1 t2
  | (<:ctyp< Plexing.pattern >>, t2) ->
      let t1 = <:ctyp< (string * string) >> in
      unify loc t1 t2

  | (<:ctyp< $lid:s1$ >>, <:ctyp< $lid:s2$ >>) -> s1 = s2
  | (<:ctyp< $uid:s1$ >>, <:ctyp< $uid:s2$ >>) -> s1 = s2
  | (<:ctyp< _ >>, _) -> True
  | (t1, t2) -> False ]
;

value no_patt loc eval_patt env pl param =
  error loc
    (sprintf "pattern matching not implemented for that constructor (%s)"
       (string_of_obj_tag param) ^
     "\nplease report")
;

value std_patt c eval_patt env pl param =
  match pl with
  [ [] -> if Obj.magic param = Obj.magic c then Some env else None
  | _ -> None ]
;

value rec serial eval_patt env pl tl el =
  match (pl, tl, el) with
  [ ([p :: pl], [t :: tl], [e :: el]) ->
      match eval_patt env p t e with
      [ Some env -> serial eval_patt env pl tl el
      | None -> None ]
  | ([], [], []) -> Some env
  | _ -> None ]
;

value val_tab = do {
  let ht = Hashtbl.create 1 in
  List.iter (fun (k, v) -> Hashtbl.add ht k v)
    [("::",
      fun loc ->
        let ta = ty_var () in
        let t1 = ta in
        let t2 = <:ctyp< list $ta$ >> in
        {ctyp = <:ctyp< $t1$ -> $t2$ -> list $ta$ >>;
         expr = Obj.repr (fun a l -> [a :: l]);
         patt eval_patt env pl param =
           match (pl, Obj.magic param) with
           [ ([p1; p2], [x :: l]) ->
               match eval_patt env p1 t1 x with
               [ Some env -> eval_patt env p2 t2 (Obj.repr l)
               | None -> None ]
           | _ -> None ]});
     ("<",
      fun loc ->
        let a = ty_var () in
        {ctyp = <:ctyp< $a$ -> $a$ -> bool >>;
         expr = Obj.repr \<;
         patt = no_patt loc});
     ("=",
      fun loc ->
        let t = ty_var () in
        {ctyp = <:ctyp< $t$ -> $t$ -> bool >>;
         expr = Obj.repr \=;
         patt = no_patt loc});
     ("*",
      fun loc ->
        {ctyp = <:ctyp< int -> int -> int >>;
         expr = Obj.repr \*;
         patt = no_patt loc});
     ("+",
      fun loc ->
        {ctyp = <:ctyp< int -> int -> int >>;
         expr = Obj.repr \+;
         patt = no_patt loc});
     ("-",
      fun loc ->
        {ctyp = <:ctyp< int -> int -> int >>;
         expr = Obj.repr \-;
         patt = no_patt loc});
     ("^",
      fun loc ->
        {ctyp = <:ctyp< string -> string -> string >>;
         expr = Obj.repr \^;
         patt = no_patt loc});
     ("[]",
      fun loc ->
        {ctyp = <:ctyp< list $ty_var ()$ >>;
         expr = Obj.repr [];
         patt = std_patt []});
     ("Char.chr",
      fun loc ->
        {ctyp = <:ctyp< int -> char >>;
         expr = Obj.repr Char.chr;
         patt = no_patt loc});
     ("Char.code",
      fun loc ->
        {ctyp = <:ctyp< char -> int >>;
         expr = Obj.repr Char.code;
         patt = no_patt loc});
     ("ctyp",
      fun loc ->
        {ctyp = <:ctyp< Grammar.Entry.e MLast.ctyp >>;
         expr = Obj.repr Pcaml.ctyp;
         patt = no_patt loc});
     ("Exparser.cparser",
      fun loc ->
        {ctyp =
           <:ctyp<
             MLast.loc -> option MLast.patt ->
               list
                 (list (Exparser.spat_comp * option (option MLast.expr)) *
                  option MLast.patt * MLast.expr) ->
               MLast.expr >>;
         expr = Obj.repr Exparser.cparser;
         patt = no_patt loc});
     ("Exparser.SpLhd",
      fun loc ->
        {ctyp =
           <:ctyp<
             MLast.loc -> list (list MLast.patt) -> Exparser.spat_comp >>;
         expr = Obj.repr (fun loc pll -> Exparser.SpLhd loc pll);
         patt = no_patt loc});
     ("Exparser.SpNtr",
      fun loc ->
        {ctyp =
           <:ctyp<
             MLast.loc -> MLast.patt -> MLast.expr -> Exparser.spat_comp >>;
         expr = Obj.repr (fun loc p e -> Exparser.SpNtr loc p e);
         patt = no_patt loc});
     ("Exparser.SpStr",
      fun loc ->
        {ctyp = <:ctyp< MLast.loc -> MLast.patt -> Exparser.spat_comp >>;
         expr = Obj.repr (fun loc p -> Exparser.SpStr loc p);
         patt = no_patt loc});
     ("Exparser.SpTrm",
      fun loc ->
        let t1 = <:ctyp< MLast.loc >> in
        let t2 = <:ctyp< MLast.patt >> in
        let t3 = <:ctyp< option MLast.expr >> in
        {ctyp = <:ctyp< $t1$ -> $t2$ -> $t3$ -> Exparser.spat_comp >>;
         expr = Obj.repr (fun loc p eo -> Exparser.SpTrm loc p eo);
         patt eval_patt env pl param =
           match Obj.magic param with
           [ Exparser.SpTrm loc p eo ->
               serial eval_patt env pl [t1; t2; t3]
                 [Obj.repr loc; Obj.repr p; Obj.repr eo]
           | _ -> None ]});
     ("expr",
      fun loc ->
        {ctyp = <:ctyp< Grammar.Entry.e MLast.expr >>;
         expr = Obj.repr Pcaml.expr;
         patt = no_patt loc});
     ("Failure",
      fun loc ->
        let t1 = <:ctyp< string >> in
        {ctyp = <:ctyp< $t1$ -> exn >>;
         expr = Obj.repr (fun s -> Failure s);
         patt eval_patt env pl param =
           match (pl, Obj.magic param) with
           [ ([p], Failure x) -> eval_patt env p t1 (Obj.repr x)
           | _ -> None ]});
     ("failwith",
      fun loc ->
        {ctyp = <:ctyp< string -> $ty_var ()$ >>;
         expr = Obj.repr failwith;
         patt = no_patt loc});
     ("False",
      fun loc ->
        {ctyp = <:ctyp< bool >>;
         expr = Obj.repr False;
         patt = std_patt False});
     ("flush",
      fun loc ->
        {ctyp = <:ctyp< out_channel -> unit >>;
         expr = Obj.repr flush;
         patt = no_patt loc});
     ("fst",
      fun loc ->
        let a = ty_var () in
        let b = ty_var () in
        {ctyp = <:ctyp< ($a$ * $b$) -> $a$ >>;
         expr = Obj.repr fst;
         patt = no_patt loc});
     ("Gramext.action",
      fun loc ->
        {ctyp = <:ctyp< $ty_var ()$ -> Gramext.g_action >>;
         expr = Obj.repr Gramext.action;
         patt = no_patt loc});
     ("Gramext.After",
      fun loc ->
        {ctyp = <:ctyp< string -> Gramext.position >>;
         expr = Obj.repr (fun s -> Gramext.After s);
         patt = no_patt loc});
     ("Gramext.LeftA",
      fun loc ->
        {ctyp = <:ctyp< Gramext.g_assoc >>;
         expr = Obj.repr Gramext.LeftA;
         patt = std_patt Gramext.LeftA});
     ("Gramext.Level",
      fun loc ->
        {ctyp = <:ctyp< string -> Gramext.position >>;
         expr = Obj.repr (fun s -> Gramext.Level s);
         patt = no_patt loc});
     ("Gramext.NonA",
      fun loc ->
        {ctyp = <:ctyp< Gramext.g_assoc >>;
         expr = Obj.repr Gramext.NonA;
         patt = std_patt Gramext.NonA});
     ("Gramext.RightA",
      fun loc ->
        {ctyp = <:ctyp< Gramext.g_assoc >>;
         expr = Obj.repr Gramext.RightA;
         patt = std_patt Gramext.RightA});
     ("Gramext.Slist0",
      fun loc ->
        let t = ty_var () in
        {ctyp = <:ctyp< Gramext.g_symbol $t$ -> Gramext.g_symbol $t$ >>;
         expr = Obj.repr (fun s -> Gramext.Slist0 s);
         patt = no_patt loc});
     ("Gramext.Slist1",
      fun loc ->
        let t = ty_var () in
        {ctyp = <:ctyp< Gramext.g_symbol $t$ -> Gramext.g_symbol $t$ >>;
         expr = Obj.repr (fun s -> Gramext.Slist1 s);
         patt = no_patt loc});
     ("Gramext.Slist0sep",
      fun loc ->
        let t = ty_var () in
        {ctyp =
           <:ctyp<
             Gramext.g_symbol $t$ -> Gramext.g_symbol $t$ -> bool ->
               Gramext.g_symbol $t$ >>;
         expr = Obj.repr (fun s1 s2 b -> Gramext.Slist0sep s1 s2 b);
         patt = no_patt loc});
     ("Gramext.Slist1sep",
      fun loc ->
        let t = ty_var () in
        {ctyp =
           <:ctyp<
             Gramext.g_symbol $t$ -> Gramext.g_symbol $t$ -> bool ->
               Gramext.g_symbol $t$ >>;
         expr = Obj.repr (fun s1 s2 b -> Gramext.Slist1sep s1 s2 b);
         patt = no_patt loc});
     ("Gramext.Snext",
      fun loc ->
        let a = ty_var () in
        {ctyp = <:ctyp< Gramext.g_symbol $a$ >>;
         expr = Obj.repr Gramext.Snext;
         patt = std_patt Gramext.Snext});
     ("Gramext.Snterm",
      fun loc ->
        let t = ty_var () in
        {ctyp = <:ctyp< Gramext.g_entry $t$ -> Gramext.g_symbol $t$ >>;
         expr = Obj.repr (fun e -> Gramext.Snterm e);
         patt = no_patt loc});
     ("Gramext.Sopt",
      fun loc ->
        let t = ty_var () in
        {ctyp = <:ctyp< Gramext.g_symbol $t$ -> Gramext.g_symbol $t$ >>;
         expr = Obj.repr (fun s -> Gramext.Sopt s);
         patt = no_patt loc});
     ("Gramext.srules",
      fun loc ->
        let t = ty_var () in
        {ctyp =
           <:ctyp<
             list (list (Gramext.g_symbol $t$) * Gramext.g_action) ->
               Gramext.g_symbol $t$ >>;
         expr = Obj.repr Gramext.srules;
         patt = no_patt loc});
     ("Gramext.Sself",
      fun loc ->
        {ctyp = <:ctyp< Gramext.g_symbol $ty_var ()$ >>;
         expr = Obj.repr Gramext.Sself;
         patt = std_patt Gramext.Sself});
     ("Gramext.Stoken",
      fun loc ->
        {ctyp = <:ctyp< Plexing.pattern -> Gramext.g_symbol $ty_var ()$ >>;
         expr = Obj.repr (fun tp -> Gramext.Stoken tp);
         patt = no_patt loc});
     ("Grammar.Entry.create",
      fun loc ->
        {ctyp = <:ctyp< Grammar.g -> string -> Grammar.Entry.e $ty_var ()$ >>;
         expr = Obj.repr Grammar.Entry.create;
         patt = no_patt loc});
     ("Grammar.Entry.obj",
      fun loc ->
        let t = ty_var () in
        {ctyp = <:ctyp< Grammar.Entry.e $t$ -> Gramext.g_entry token >>;
         expr = Obj.repr Grammar.Entry.obj;
         patt = no_patt loc});
     ("Grammar.extend",
      fun loc ->
        let te = ty_var () in
        {ctyp =
           <:ctyp<
             list
               (Gramext.g_entry $te$ * option Gramext.position *
                list
                  (option string * option Gramext.g_assoc *
                   list (list (Gramext.g_symbol $te$) * Gramext.g_action))) ->
             unit >>;
         expr = Obj.repr Grammar.extend;
         patt = no_patt loc});
     ("Grammar.of_entry",
      fun loc ->
        {ctyp = <:ctyp< Grammar.Entry.e $ty_var ()$ -> Grammar.g >>;
         expr = Obj.repr Grammar.of_entry;
         patt = no_patt loc});
     ("let_binding",
      fun loc ->
        {ctyp = <:ctyp< Grammar.Entry.e (MLast.patt * MLast.expr) >>;
         expr = Obj.repr Pcaml.let_binding;
         patt = no_patt loc});
     ("List.fold_left",
      fun loc ->
        let a = ty_var () in
        let b = ty_var () in
        {ctyp = <:ctyp< ($a$ -> $b$ -> $a$) -> $a$ -> list $b$ -> $a$ >>;
         expr = Obj.repr List.fold_left;
         patt = no_patt loc});
     ("List.fold_right",
      fun loc ->
        let a = ty_var () in
        let b = ty_var () in
        {ctyp = <:ctyp< ($a$ -> $b$ -> $b$) -> list $a$ -> $b$ -> $b$ >>;
         expr = Obj.repr List.fold_right;
         patt = no_patt loc});
     ("List.length",
      fun loc ->
        let a = ty_var () in
        {ctyp = <:ctyp< list $a$ -> int >>;
         expr = Obj.repr List.length;
         patt = no_patt loc});
     ("List.map",
      fun loc ->
        let a = ty_var () in
        let b = ty_var () in
        {ctyp = <:ctyp< ($a$ -> $b$) -> list $a$ -> list $b$ >>;
         expr = Obj.repr List.map;
         patt = no_patt loc});
     ("List.mem",
      fun loc ->
        let ta = ty_var () in
        {ctyp = <:ctyp< $ta$ -> list $ta$ -> bool >>;
         expr = Obj.repr List.mem;
         patt = no_patt loc});
     ("List.rev",
      fun loc ->
        let ta = ty_var () in
        {ctyp = <:ctyp< list $ta$ -> list $ta$ >>;
         expr = Obj.repr List.rev;
         patt = no_patt loc});
     ("MLast.ExAcc",
      fun loc ->
        {ctyp =
           <:ctyp< MLast.loc -> MLast.expr -> MLast.expr -> MLast.expr >>;
         expr = Obj.repr (fun loc e1 e2 -> MLast.ExAcc loc e1 e2);
         patt = no_patt loc});
     ("MLast.ExApp",
      fun loc ->
        let t1 = <:ctyp< MLast.loc >> in
        let t2 = <:ctyp< MLast.expr >> in
        let t3 = <:ctyp< MLast.expr >> in
        {ctyp = <:ctyp< $t1$ -> $t2$ -> $t3$ -> MLast.expr >>;
         expr = Obj.repr (fun loc e1 e2 -> MLast.ExApp loc e1 e2);
         patt eval_patt env pl param =
           match Obj.magic param with
           [ MLast.ExApp loc e1 e2 ->
               serial eval_patt env pl [t1; t2; t3]
                 [Obj.repr loc; Obj.repr e1; Obj.repr e2]
           | _ -> None ]});
     ("MLast.ExChr",
      fun loc ->
        {ctyp = <:ctyp< MLast.loc -> string -> MLast.expr >>;
         expr = Obj.repr (fun loc s -> MLast.ExChr loc s);
         patt = no_patt loc});
     ("MLast.ExFun",
      fun loc ->
        {ctyp =
           <:ctyp<
             MLast.loc ->
               list (MLast.patt * option MLast.expr * MLast.expr) ->
               MLast.expr >>;
         expr = Obj.repr (fun loc pel -> MLast.ExFun loc pel);
         patt = no_patt loc});
     ("MLast.ExIfe",
      fun loc ->
        {ctyp =
           <:ctyp<
             MLast.loc -> MLast.expr -> MLast.expr -> MLast.expr ->
               MLast.expr >>;
         expr = Obj.repr (fun loc e1 e2 e3 -> MLast.ExIfe loc e1 e2 e3);
         patt = no_patt loc});
     ("MLast.ExLet",
      fun loc ->
        {ctyp =
           <:ctyp<
             MLast.loc -> bool -> list (MLast.patt * MLast.expr) ->
               MLast.expr -> MLast.expr >>;
         expr = Obj.repr (fun loc rf pel e -> MLast.ExLet loc rf pel e);
         patt = no_patt loc});
     ("MLast.ExLid",
      fun loc ->
        let t1 = <:ctyp< MLast.loc >> in
        let t2 =
          IFDEF STRICT THEN <:ctyp< Ploc.vala string >>
          ELSE <:ctyp< string >> END
        in
        {ctyp = <:ctyp< $t1$ -> $t2$ -> MLast.expr >>;
         expr = Obj.repr (fun loc s -> MLast.ExLid loc s);
         patt eval_patt env pl param =
           match Obj.magic param with
           [ MLast.ExLid loc s ->
               serial eval_patt env pl [t1; t2] [Obj.repr loc; Obj.repr s]
           | _ -> None ]});
     ("MLast.ExRec",
      fun loc ->
        {ctyp =
           <:ctyp<
             MLast.loc -> list (MLast.patt * MLast.expr) ->
               option MLast.expr -> MLast.expr >>;
         expr = Obj.repr (fun loc lel eo -> MLast.ExRec loc lel eo);
         patt = no_patt loc});
     ("MLast.ExSeq",
      fun loc ->
        {ctyp = <:ctyp< MLast.loc -> list MLast.expr -> MLast.expr >>;
         expr = Obj.repr (fun loc el -> MLast.ExSeq loc el);
         patt = no_patt loc});
     ("MLast.ExStr",
      fun loc ->
        {ctyp = <:ctyp< MLast.loc -> string -> MLast.expr >>;
         expr = Obj.repr (fun loc s -> MLast.ExStr loc s);
         patt = no_patt loc});
     ("MLast.ExTry",
      fun loc ->
        {ctyp =
           <:ctyp<
             MLast.loc -> MLast.expr ->
               list (MLast.patt * option MLast.expr * MLast.expr) ->
               MLast.expr >>;
         expr = Obj.repr (fun loc e pel -> MLast.ExTry loc e pel);
         patt = no_patt loc});
     ("MLast.ExTup",
      fun loc ->
        {ctyp = <:ctyp< MLast.loc -> list MLast.expr -> MLast.expr >>;
         expr = Obj.repr (fun loc el -> MLast.ExTup loc el);
         patt = no_patt loc});
     ("MLast.ExTyc",
      fun loc ->
        {ctyp =
           <:ctyp<
             MLast.loc -> MLast.expr -> MLast.ctyp -> MLast.expr >>;
         expr = Obj.repr (fun loc e t -> MLast.ExTyc loc e t);
         patt = no_patt loc});
     ("MLast.ExUid",
      fun loc ->
        {ctyp = <:ctyp< MLast.loc -> string -> MLast.expr >>;
         expr = Obj.repr (fun loc s -> MLast.ExUid loc s);
         patt = no_patt loc});
     ("MLast.ExWhi",
      fun loc ->
        {ctyp =
           <:ctyp<
             MLast.loc -> MLast.expr -> list MLast.expr -> MLast.expr >>;
         expr = Obj.repr (fun loc e el -> MLast.ExWhi loc e el);
         patt = no_patt loc});
     ("MLast.MeStr",
      fun loc ->
        {ctyp =
           <:ctyp<
             MLast.loc -> list MLast.str_item -> MLast.module_expr >>;
         expr = Obj.repr (fun loc sil -> MLast.MeStr loc sil);
         patt = no_patt loc});
     ("MLast.MeTyc",
      fun loc ->
        {ctyp =
           <:ctyp<
             MLast.loc -> MLast.module_expr -> MLast.module_type ->
               MLast.module_expr >>;
         expr = Obj.repr (fun loc me mt -> MLast.MeTyc loc me mt);
         patt = no_patt loc});
     ("MLast.MtSig",
      fun loc ->
        {ctyp =
           <:ctyp<
             MLast.loc -> list MLast.sig_item -> MLast.module_type >>;
         expr = Obj.repr (fun loc sil -> MLast.MtSig loc sil);
         patt = no_patt loc});
     ("MLast.PaAcc",
      fun loc ->
        {ctyp =
           <:ctyp<
             MLast.loc -> MLast.patt -> MLast.patt -> MLast.patt >>;
         expr = Obj.repr (fun loc p1 p2 -> MLast.PaAcc loc p1 p2);
         patt = no_patt loc});
     ("MLast.PaAli",
      fun loc ->
        {ctyp =
           <:ctyp<
             MLast.loc -> MLast.patt -> MLast.patt -> MLast.patt >>;
         expr = Obj.repr (fun loc p1 p2 -> MLast.PaAli loc p1 p2);
         patt = no_patt loc});
     ("MLast.PaAny",
      fun loc ->
        {ctyp = <:ctyp< MLast.loc -> MLast.patt >>;
         expr = Obj.repr (fun loc -> MLast.PaAny loc);
         patt = no_patt loc});
     ("MLast.PaApp",
      fun loc ->
        {ctyp =
           <:ctyp<
             MLast.loc -> MLast.patt -> MLast.patt -> MLast.patt >>;
         expr = Obj.repr (fun loc p1 p2 -> MLast.PaApp loc p1 p2);
         patt = no_patt loc});
     ("MLast.PaChr",
      fun loc ->
        {ctyp = <:ctyp< MLast.loc -> string -> MLast.patt >>;
         expr = Obj.repr (fun loc s -> MLast.PaChr loc s);
         patt = no_patt loc});
     ("MLast.PaLid",
      fun loc ->
        {ctyp = <:ctyp< MLast.loc -> string -> MLast.patt >>;
         expr = Obj.repr (fun loc s -> MLast.PaLid loc s);
         patt = no_patt loc});
     ("MLast.PaOrp",
      fun loc ->
        {ctyp =
           <:ctyp<
             MLast.loc -> MLast.patt -> MLast.patt -> MLast.patt >>;
         expr = Obj.repr (fun loc p1 p2 -> MLast.PaOrp loc p1 p2);
         patt = no_patt loc});
     ("MLast.PaRng",
      fun loc ->
        {ctyp =
           <:ctyp<
             MLast.loc -> MLast.patt -> MLast.patt -> MLast.patt >>;
         expr = Obj.repr (fun loc p1 p2 -> MLast.PaRng loc p1 p2);
         patt = no_patt loc});
     ("MLast.PaTup",
      fun loc ->
        {ctyp = <:ctyp< MLast.loc -> list MLast.patt -> MLast.patt >>;
         expr = Obj.repr (fun loc pl -> MLast.PaTup loc pl);
         patt = no_patt loc});
     ("MLast.PaTyc",
      fun loc ->
        {ctyp =
           <:ctyp<
             MLast.loc -> MLast.patt -> MLast.ctyp -> MLast.patt >>;
         expr = Obj.repr (fun loc p t -> MLast.PaTyc loc p t);
         patt = no_patt loc});
     ("MLast.PaUid",
      fun loc ->
        {ctyp = <:ctyp< MLast.loc -> string -> MLast.patt >>;
         expr = Obj.repr (fun loc s -> MLast.PaUid loc s);
         patt = no_patt loc});
     ("MLast.SgVal",
      fun loc ->
        {ctyp =
           <:ctyp<
             MLast.loc -> string -> MLast.ctyp -> MLast.sig_item >>;
         expr = Obj.repr (fun loc s t -> MLast.SgVal loc s t);
         patt = no_patt loc});
     ("MLast.StDcl",
      fun loc ->
        {ctyp =
           <:ctyp<
             MLast.loc -> list MLast.str_item -> MLast.str_item >>;
         expr = Obj.repr (fun loc sil -> MLast.StDcl loc sil);
         patt = no_patt loc});
     ("MLast.StMod",
      fun loc ->
        {ctyp =
           <:ctyp<
             MLast.loc -> bool -> list (string * MLast.module_expr) ->
               MLast.str_item >>;
         expr = Obj.repr (fun loc rf mel -> MLast.StMod loc rf mel);
         patt = no_patt loc});
     ("MLast.StTyp",
      fun loc ->
        {ctyp =
           <:ctyp<
             MLast.loc -> bool -> list MLast.type_decl -> MLast.str_item >>;
         expr = Obj.repr (fun loc flg tdl -> MLast.StTyp loc flg tdl);
         patt = no_patt loc});
     ("MLast.StVal",
      fun loc ->
        {ctyp =
           <:ctyp<
             MLast.loc -> bool -> list (MLast.patt * MLast.expr) ->
               MLast.str_item >>;
         expr = Obj.repr (fun loc rf pel -> MLast.StVal loc rf pel);
         patt = no_patt loc});
     ("MLast.TyAcc",
      fun loc ->
        {ctyp =
           <:ctyp<
             MLast.loc -> MLast.ctyp -> MLast.ctyp -> MLast.ctyp >>;
         expr = Obj.repr (fun loc t1 t2 -> MLast.TyAcc loc t1 t2);
         patt = no_patt loc});
     ("MLast.TyAny",
      fun loc ->
        {ctyp = <:ctyp< MLast.loc -> MLast.ctyp >>;
         expr = Obj.repr (fun loc -> MLast.TyAny loc);
         patt = no_patt loc});
     ("MLast.TyApp",
      fun loc ->
        {ctyp =
           <:ctyp<
             MLast.loc -> MLast.ctyp -> MLast.ctyp -> MLast.ctyp >>;
         expr = Obj.repr (fun loc t1 t2 -> MLast.TyApp loc t1 t2);
         patt = no_patt loc});
     ("MLast.TyArr",
      fun loc ->
        {ctyp =
           <:ctyp<
             MLast.loc -> MLast.ctyp -> MLast.ctyp -> MLast.ctyp >>;
         expr = Obj.repr (fun loc t1 t2 -> MLast.TyArr loc t1 t2);
         patt = no_patt loc});
     ("MLast.TyLid",
      fun loc ->
        {ctyp = <:ctyp< MLast.loc -> string -> MLast.ctyp >>;
         expr = Obj.repr (fun loc s -> MLast.TyLid loc s);
         patt = no_patt loc});
     ("MLast.TyQuo",
      fun loc ->
        {ctyp = <:ctyp< MLast.loc -> string -> MLast.ctyp >>;
         expr = Obj.repr (fun loc s -> MLast.TyQuo loc s);
         patt = no_patt loc});
     ("MLast.TyRec",
      fun loc ->
        {ctyp =
           <:ctyp<
             MLast.loc ->
               list (MLast.loc * string * bool * MLast.ctyp) ->
               MLast.ctyp >>;
         expr = Obj.repr (fun loc ldl -> MLast.TyRec loc ldl);
         patt = no_patt loc});
     ("MLast.TyUid",
      fun loc ->
        {ctyp = <:ctyp< MLast.loc -> string -> MLast.ctyp >>;
         expr = Obj.repr (fun loc s -> MLast.TyUid loc s);
         patt = no_patt loc});
     ("module_expr",
      fun loc ->
        {ctyp = <:ctyp< Grammar.Entry.e MLast.module_expr >>;
         expr = Obj.repr Pcaml.module_expr;
         patt = no_patt loc});
     ("module_type",
      fun loc ->
        {ctyp = <:ctyp< Grammar.Entry.e MLast.module_type >>;
         expr = Obj.repr Pcaml.module_type;
         patt = no_patt loc});
     ("None",
      fun loc ->
        {ctyp = <:ctyp< option $ty_var ()$ >>;
         expr = Obj.repr None;
         patt = std_patt None});
     ("Not_found",
      fun loc ->
        {ctyp = <:ctyp< exn >>;
         expr = Obj.repr Not_found;
         patt = std_patt Not_found});
     ("patt",
      fun loc ->
        {ctyp = <:ctyp< Grammar.Entry.e MLast.patt >>;
         expr = Obj.repr Pcaml.patt;
         patt = no_patt loc});
     ("Ploc.raise",
      fun loc ->
        {ctyp = <:ctyp< Ploc.t -> exn -> _ >>;
         expr = Obj.repr Ploc.raise;
         patt = no_patt loc});
     ("Ploc.VaVal",
      fun loc ->
        let ta = ty_var () in
        {ctyp = <:ctyp< $ta$ -> Ploc.vala $ta$ >>;
         expr = Obj.repr (fun x -> Ploc.VaVal x);
         patt = no_patt loc});
     ("prerr_endline",
      fun loc ->
        {ctyp = <:ctyp< string -> unit >>;
         expr = Obj.repr prerr_endline;
         patt = no_patt loc});
     ("prerr_int",
      fun loc ->
        {ctyp = <:ctyp< int -> unit >>;
         expr = Obj.repr prerr_int;
         patt = no_patt loc});
     ("print_endline",
      fun loc ->
        {ctyp = <:ctyp< string -> unit >>;
         expr = Obj.repr print_endline;
         patt = no_patt loc});
     ("Printf.eprintf",
      fun loc ->
        let t = ty_var () in
        {ctyp = <:ctyp< format $t$ out_channel unit -> $t$ >>;
         expr = Obj.repr Printf.eprintf;
         patt = no_patt loc});
     ("raise",
      fun loc ->
        {ctyp = <:ctyp< exn -> $ty_var ()$ >>;
         expr = Obj.repr raise;
         patt = no_patt loc});
     ("sig_item",
      fun loc ->
        {ctyp = <:ctyp< Grammar.Entry.e MLast.sig_item >>;
         expr = Obj.repr Pcaml.sig_item;
         patt = no_patt loc});
     ("snd",
      fun loc ->
        let a = ty_var () in
        let b = ty_var () in
        {ctyp = <:ctyp< ($a$ * $b$) -> $b$ >>;
         expr = Obj.repr snd;
         patt = no_patt loc});
     ("Some",
      fun loc ->
        let ta = ty_var () in
        {ctyp = <:ctyp< $ta$ -> option $ta$ >>;
         expr = Obj.repr (fun x -> Some x);
         patt eval_patt env pl param =
           match (pl, Obj.magic param) with
           [ ([p], Some x) -> eval_patt env p ta (Obj.repr x)
           | _ -> None ]});
     ("stderr",
      fun loc ->
        {ctyp = <:ctyp< out_channel >>;
         expr = Obj.repr stderr;
         patt = no_patt loc});
     ("str_item",
      fun loc ->
        {ctyp = <:ctyp< Grammar.Entry.e MLast.str_item >>;
         expr = Obj.repr Pcaml.str_item;
         patt = no_patt loc});
     ("Stream.Error",
      fun loc ->
        {ctyp = <:ctyp< string -> exn >>;
         expr = Obj.repr (fun s -> Stream.Error s);
         patt = no_patt loc});
     ("Stream.of_string",
      fun loc ->
        {ctyp = <:ctyp< string -> Stream.t char >>;
         expr = Obj.repr Stream.of_string;
         patt = no_patt loc});
     ("Stream.peek",
      fun loc ->
        let ta = ty_var () in
        {ctyp = <:ctyp< Stream.t $ta$ -> option $ta$ >>;
         expr = Obj.repr Stream.peek;
         patt = no_patt loc});
     ("String.get",
      fun loc ->
        {ctyp = <:ctyp< string -> int -> char >>;
         expr = Obj.repr String.get;
         patt = no_patt loc});
     ("String.length",
      fun loc ->
        {ctyp = <:ctyp< string -> int >>;
         expr = Obj.repr String.length;
         patt = no_patt loc});
     ("String.make",
      fun loc ->
        {ctyp = <:ctyp< int -> char -> string >>;
         expr = Obj.repr String.make;
         patt = no_patt loc});
     ("String.set",
      fun loc ->
        {ctyp = <:ctyp< string -> int -> char -> unit >>;
         expr = Obj.repr string_set;
         patt = no_patt loc});
     ("String.sub",
      fun loc ->
        {ctyp = <:ctyp< string -> int -> int -> string >>;
         expr = Obj.repr String.sub;
         patt = no_patt loc});
     ("True",
      fun loc ->
        {ctyp = <:ctyp< bool >>;
         expr = Obj.repr True;
         patt = std_patt True});
     ("type_decl",
      fun loc ->
        {ctyp = <:ctyp< Grammar.Entry.e MLast.type_decl >>;
         expr = Obj.repr Pcaml.type_decl;
         patt = no_patt loc})];
  ht
};

IFDEF OCAML_VERSION <= OCAML_1_07 THEN
  value with_ctyp e t = {ctyp = t; expr = e.expr; patt = e.patt};
END;

value rec eval_expr env e =
  let loc = MLast.loc_of_expr e in
  match e with
  [ <:expr< fun [ $list:pel$ ] >> ->
      eval_fun loc env pel
  | <:expr< let $flag:rf$ $list:pel$ in $e$ >> ->
      eval_let loc env rf pel e
  | <:expr< match $e$ with [ $list:pel$ ] >> ->
      eval_match loc env e pel
  | <:expr< try $e$ with [ $list:pel$ ] >> ->
      eval_try loc env e pel
  | <:expr< if $e1$ then $e2$ else $e3$ >> ->
      let v = eval_expr env e1 in
      match v.ctyp with
      [ <:ctyp< bool >> -> eval_expr env (if Obj.magic v.expr then e2 else e3)
      | t -> bad_type (MLast.loc_of_expr e1) <:ctyp< bool >> t ]
  | <:expr< do { $list:el$ } >> ->
      loop el where rec loop =
        fun
        [ [] ->
            {ctyp = <:ctyp< unit >>; expr = Obj.repr (); patt = no_patt loc}
        | [e] -> eval_expr env e
        | [e :: el] ->
            let _ = eval_expr env e in
            loop el ]

  | <:expr< $e1$ && $e2$ >> ->
      let v1 = eval_expr env e1 in
      let t = <:ctyp< bool >> in
      if unify loc t v1.ctyp then
        if (Obj.magic v1.expr : bool) then eval_expr env e2
        else {ctyp = t; expr = Obj.repr False; patt = no_patt loc}
      else
        bad_type loc t v1.ctyp
  | <:expr< $e1$ $e2$ >> ->
      eval_expr_apply loc env e1 e2

  | <:expr< $e1$ .[ $e2$ ] := $e3$ >> ->
      eval_expr env <:expr< String.set $e1$ $e2$ $e3$ >>

  | <:expr< $e1$ .[ $e2$ ] >> ->
      eval_expr env <:expr< String.get $e1$ $e2$ >>

  | <:expr< ( $e$ : $t$ ) >> ->
      let v = eval_expr env e in
      let t = type_of_ctyp t in
      if unify loc t v.ctyp then
        let t = eval_type loc t in
        {(v) with ctyp = t}
      else
        bad_type loc t v.ctyp

  | <:expr< ( $list:el$ ) >> ->
      let vl = List.map (eval_expr env) el in
      let tl = List.map (fun v -> v.ctyp) vl in
      let xl = List.map (fun v -> v.expr) vl in
      {ctyp = <:ctyp< ( $list:tl$ ) >>; expr = Obj.repr (Array.of_list xl);
       patt = no_patt loc}

  | <:expr< $int:s$ >> ->
      {ctyp = <:ctyp< int >>; expr = Obj.repr (int_of_string s);
       patt = no_patt loc}
  | <:expr< $str:s$ >> ->
      {ctyp = <:ctyp< string >>; expr = Obj.repr (Plexing.eval_string loc s);
       patt = no_patt loc}
  | <:expr< $chr:s$ >> ->
      {ctyp = <:ctyp< char >>; expr = Obj.repr (Plexing.eval_char s);
       patt = no_patt loc}

  | <:expr< $lid:s$ >> ->
      match try Some (List.assoc s env) with [ Not_found -> None ] with
      [ Some {by_let = by_let; valu = v} ->
          if by_let then {(v) with ctyp = instantiate loc s v.ctyp} else v
      | None ->
          try Hashtbl.find val_tab s loc with
          [ Not_found -> unbound_var loc s ] ]
  | <:expr< $uid:s$ >> ->
      try Hashtbl.find val_tab s loc with [ Not_found -> unbound_var loc s ]
  | <:expr< $uid:a$ . $lid:b$ >> | <:expr< $uid:a$ . $uid:b$ >> ->
      let s = a ^ "." ^ b in
      try Hashtbl.find val_tab s loc with [ Not_found -> unbound_var loc s ]
  | <:expr< $uid:a$ . $uid:b$ . $lid:c$ >> ->
      let s = a ^ "." ^ b ^ "." ^ c in
      try Hashtbl.find val_tab s loc with [ Not_found -> unbound_var loc s ]

  | e -> not_impl loc "11/expr" e ]

and eval_match loc env e pel =
  let v = eval_expr env e in
  match eval_match_assoc_list loc env v.ctyp (ty_var ()) pel v.expr with
  [ Some v -> v
  | None ->
      raise
        (Match_failure
           (Ploc.file_name loc, Ploc.line_nb loc,
            Ploc.first_pos loc - Ploc.bol_pos loc)) ]

and eval_try loc env e pel =
  try eval_expr env e with exn ->
    let v =
      {ctyp = <:ctyp< exn >>; expr = Obj.magic exn; patt = no_patt loc}
    in
    match eval_match_assoc_list loc env v.ctyp (ty_var ()) pel v.expr with
    [ Some v -> v
    | None -> raise exn ]

and eval_let loc env rf pel e =
  if rf then do {
    let extra_env =
      loop [] pel where rec loop extra_env =
        fun
        [ [(p, e) :: pel] ->
            let extra_env =
              match p with
              [ <:patt< $lid:s$ >> ->
                  [(s, {by_let = True; valu = Obj.magic e}) :: extra_env]
              | <:patt< _ >> -> extra_env
              | p -> not_impl loc "15/patt" p ]
            in
            loop extra_env pel
        | [] -> extra_env ]
    in
    let new_env = list_rev_append extra_env env in
    List.iter
      (fun (s, bv) -> bv.valu := eval_expr new_env (Obj.magic bv.valu))
      extra_env;
    eval_expr new_env e
  }
  else
    let new_env =
      loop env pel where rec loop new_env =
        fun
        [ [(p, e) :: pel] ->
            let v = eval_expr env e in
            let new_env =
              loop new_env v p where rec loop new_env v =
                fun
                [ <:patt< ( $list:pl$ ) >> ->
                    let tl = List.map (fun _ -> <:ctyp< $ty_var ()$ >>) pl in
                    let t = <:ctyp< ( $list:tl$ ) >> in
                    if unify loc t v.ctyp then
                      let el =
                        Array.to_list (Obj.magic v.expr : array Obj.t)
                      in
                      loop2 new_env pl tl el
                      where rec loop2 new_env pl tl el =
                        match (pl, tl, el) with
                        [ ([p :: pl], [t :: tl], [e :: el]) ->
                            let new_env =
                              loop new_env
                                {ctyp = t; expr = e; patt = no_patt loc} p
                            in
                            loop2 new_env pl tl el
                        | ([], [], []) -> new_env
                        | _ -> assert False ]
                    else bad_type loc t v.ctyp
                | <:patt< $lid:s$ >> ->
                    [(s, {by_let = True; valu = v}) :: new_env]
                | <:patt< _ >> -> new_env
                | p -> not_impl loc "14/patt" p ]
            in
            loop new_env pel
        | [] -> new_env ]
    in
    eval_expr new_env e

and eval_fun loc env pel =
  let t1 = ty_var () in
  let t2 = ty_var () in
  let t = <:ctyp< $t1$ -> $t2$ >> in
  let e param =
    match eval_match_assoc_list loc env t1 t2 pel param with
    [ Some v -> v.expr
    | None ->
        raise
          (Match_failure
             (Ploc.file_name loc, Ploc.line_nb loc,
              Ploc.first_pos loc - Ploc.bol_pos loc)) ]
  in
  {ctyp = t; expr = Obj.repr e; patt = no_patt loc}

and eval_match_assoc_list loc env t1 t2 pel param =
  match pel with
  [ [pe :: pel] ->
      match eval_match_assoc loc env t1 t2 pe param with
      [ Some v -> Some v
      | None -> eval_match_assoc_list loc env t1 t2 pel param ]
  | [] -> None ]

and eval_match_assoc loc env t1 t2 (p, eo, e) param =
  match eval_patt env p t1 param with
  [ Some env ->
      let cond =
        if eo = <:vala< None >> then True
        else not_impl loc "eval_match_assoc eo = Some..." p
      in
      if cond then
        let t = eval_type loc t2 in
        let v = eval_expr env e in
        if unify loc t v.ctyp then Some {(v) with ctyp = eval_type loc t}
        else bad_type loc t v.ctyp
      else None
  | None -> None ]

and eval_patt env p tp param =
  let loc = MLast.loc_of_patt p in
  let ppl =
    loop [] p where rec loop pl =
      fun
      [ <:patt< $p1$ $p2$ >> -> loop [p2 :: pl] p1
      | <:patt< $uid:m$ . $uid:s$ >> -> Some (m ^ "." ^ s, pl)
      | <:patt< $uid:s$ >> -> Some (s, pl)
      | _ -> None ]
  in
  match ppl with
  [ Some (s, pl) ->
      match
        try Some (Hashtbl.find val_tab s loc) with [ Not_found -> None ]
      with
      [ Some pt ->
          loop (List.length pl) pt.ctyp where rec loop len t =
            if len = 0 then
              if unify loc t tp then pt.patt eval_patt env pl param
              else bad_type loc t tp
            else
              match t with
              [ <:ctyp< $_$ -> $t$ >> -> loop (len - 1) t
              | _ ->
                  error loc
                    (sprintf "Too many arguments (%d) to constructor %s\n\
                        It expects %d argument(s)."
                       (List.length pl) s (List.length pl - len)) ]
      | _ -> unbound_cons loc s ]
  | None ->
      match p with
      [ <:patt< ($p$ : $t$) >> ->
          let t = type_of_ctyp t in
          if unify loc tp t then eval_patt env p (eval_type loc tp) param
          else bad_type loc tp t
      | <:patt< ( $list:pl$ ) >> ->
          let tpl = List.map (fun _ -> ty_var ()) pl in
          let exp_tp = <:ctyp< ($list:tpl$) >> in
          if unify loc exp_tp tp && Obj.is_block param && Obj.tag param = 0 &&
             Obj.size param = List.length pl
          then
            let param_list = Array.to_list (Obj.magic param) in
            loop env param_list pl tpl where rec loop env param_list pl tpl =
              match (param_list, pl, tpl) with
              [ ([param :: param_list], [p :: pl], [tp :: tpl]) ->
                  match eval_patt env p (eval_type loc tp) param with
                  [ Some env -> loop env param_list pl tpl
                  | None -> None ]
              | ([], [], []) -> Some env
              | _ -> assert False ]
          else bad_type loc exp_tp tp

      | <:patt< $int:s$ >> ->
          let t = <:ctyp< int >> in
          if unify loc t tp then
            if int_of_string s = Obj.magic param then Some env else None
          else bad_type loc t tp
      | <:patt< $str:s$ >> ->
          let t = <:ctyp< string >> in
          if unify loc t tp then
            if s = Obj.magic param then Some env else None
          else bad_type loc t tp
      | <:patt< $lid:s$ >> ->
          let v = {ctyp = tp; expr = param; patt = no_patt loc} in
          Some [(s, {by_let = False; valu = v}) :: env]

      | <:patt< _ >> -> Some env
      | <:patt< $_$ $_$ >> -> error loc "bad apply in pattern"
      | p -> not_impl loc "1/eval_patt" p ] ]

and eval_expr_apply loc env e1 e2 =
  let v1 = eval_expr env e1 in
  let v2 = eval_expr env e2 in
  let t11 = ty_var () in
  let t12 = ty_var () in
  let tt = <:ctyp< $t11$ -> $t12$ >> in
  if unify loc v1.ctyp tt then
    let unify_ok =
      match (eval_type loc t11, eval_type loc v2.ctyp) with
      [ (<:ctyp< format $tf1$ $_$ $tf3$ >>, <:ctyp< string >>) ->
          let s = (Obj.magic v2.expr : string) in
          match try Some (String.index s '%') with [ Not_found -> None ] with
          [ Some i ->
              if i + 1 = String.length s then failwith "% at end of format"
              else
                let u =
                  match s.[i+1] with
                  [ 'd' -> unify loc <:ctyp< int -> $tf3$ >> tf1
                  | 's' -> unify loc <:ctyp< string -> $tf3$ >> tf1
                  | c -> failwith ("not impl format %" ^ String.make 1 c) ]
                in
                match
                  try Some (String.index_from s (i + 1) '%') with
                  [ Not_found -> None ]
                with
                [ Some _ -> failwith "not impl format with several %"
                | None -> u ]
          | None -> unify loc tf1 tf3 ]
      | (t1, t2) -> unify loc t1 t2 ]
    in
    if unify_ok then
      let t = eval_type loc t12 in
      {ctyp = t; expr = Obj.magic v1.expr v2.expr; patt = no_patt loc}
    else
      bad_type loc t11 v2.ctyp
  else
    bad_type loc v1.ctyp tt
;

value eval_unit_expr loc e =
  match eval_type loc (eval_expr [] e).ctyp with
  [ <:ctyp< unit >> -> ()
  | t -> bad_type loc <:ctyp< unit >> t ]
;

value pragma =
  fun
  [ Some e -> do {
      vars.val := [];
      eval_unit_expr (MLast.loc_of_expr e) e;
    }
  | None -> failwith "bad directive" ]
;

Pcaml.add_directive "pragma" pragma;
