(* camlp4r q_MLast.cmo -qmod ctyp,Type *)
(* $Id: pa_pragma.ml,v 1.37 2007/01/02 13:02:33 deraugla Exp $ *)

(* expressions evaluated in the context of the preprocessor *)
(* syntax at toplevel: #pragma <expr> *)

open Printf;

value string_of_obj_tag x =
  if Obj.is_block (Obj.repr x) then
    let t = Obj.tag (Obj.repr x) in
    "tag = " ^ string_of_int t ^
    (if t = 0 then " size = " ^ string_of_int (Obj.size (Obj.repr x)) else "")
  else "int_val = " ^ string_of_int (Obj.magic x)
;

value not_impl loc name x =
  let desc = string_of_obj_tag x in
  Stdpp.raise_with_loc loc
    (Failure ("pa_pragma: not impl " ^ name ^ " " ^ desc))
;

module Type =
  struct
    type loc = Stdpp.location;
    type t =
      [ TyAcc of loc and t and t
      | TyAny of loc
      | TyApp of loc and t and t
      | TyArr of loc and t and t
      | TyLid of loc and string
      | TyQuo of loc and ref (option t)
      | TyTup of loc and list t
      | TyUid of loc and string ]
    ;
  end
;

type expr_v =
  { ctyp : Type.t;
    expr : Obj.t;
    patt :
      (list (string * bind_v) -> MLast.patt -> Type.t -> Obj.t ->
        option (list (string * bind_v))) ->
        list (string * bind_v) -> list MLast.patt -> Obj.t ->
        option (list (string * bind_v)) }
and bind_v = { by_let : bool; valu : mutable expr_v }
;

value ty_var =
  let loc = Stdpp.dummy_loc in
  fun () -> <:ctyp< '$ref None$ >>
;

value vars = ref [];
value rec type_of_ctyp =
  fun
  [ MLast.TyAcc loc t1 t2 -> <:ctyp< $type_of_ctyp t1$ . $type_of_ctyp t2$ >>
  | MLast.TyAny loc -> <:ctyp< _ >>
  | MLast.TyApp loc t1 t2 -> <:ctyp< $type_of_ctyp t1$ $type_of_ctyp t2$ >>
  | MLast.TyArr loc t1 t2 -> <:ctyp< $type_of_ctyp t1$ -> $type_of_ctyp t2$ >>
  | MLast.TyLid loc s -> <:ctyp< $lid:s$ >>
  | MLast.TyQuo loc s ->
      try List.assoc s vars.val with
      [ Not_found -> do {
          let v = ty_var () in
          vars.val := [(s, v) :: vars.val];
          v
        } ]
  | MLast.TyUid loc s -> <:ctyp< $uid:s$ >>
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
  | <:ctyp< $lid:_$ >> | <:ctyp< $uid:_$ >> | <:ctyp< _ >> -> t ]
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
      Printf.sprintf "\nType expected:\n  %s\nType found:\n  %s\n"
        s1 s2
    else
      Printf.sprintf "\n  type expected: %s\n     type found: %s\n" s1 s2
  in
  Stdpp.raise_with_loc loc (Stream.Error s)
;

value unbound_var loc s =
  Stdpp.raise_with_loc loc (Failure (sprintf "Unbound variable: %s" s))
;

value unbound_cons loc s =
  Stdpp.raise_with_loc loc (Failure (sprintf "Unbound constructor: %s" s))
;

value error loc s =
  Stdpp.raise_with_loc loc (Failure s)
;

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
  | t -> not_impl loc "instanciate" t]
;
value instanciate loc s t = do {
  inst_vars.val := [];
  inst loc t
};

value rec unify loc t1 t2 =
  match (eval_type loc t1, eval_type loc t2) with 
  [ (<:ctyp< $t11$ $t12$ >>, <:ctyp< $t21$ $t22$ >>) ->
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
          if unify loc t1 t2 then do { s.val := Some t1; True }
          else False
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
          ((Token.location * string) *
           list (string * (bool * bool)) *
           MLast.ctyp *
           list (MLast.ctyp * MLast.ctyp)) >>
      in
      unify loc t1 t2
  | (<:ctyp< Token.pattern >>, t2) ->
      let t1 = <:ctyp< (string * string) >> in
      unify loc t1 t2

  | (<:ctyp< $lid:s1$ >>, <:ctyp< $lid:s2$ >>) -> s1 = s2
  | (<:ctyp< $uid:s1$ >>, <:ctyp< $uid:s2$ >>) -> s1 = s2
  | (<:ctyp< _ >>, _) -> True
  | (t1, t2) -> False ]
;

value val_tab = do {
  let ht = Hashtbl.create 1 in
  let loc = Token.dummy_loc in
  List.iter (fun (k, v) -> Hashtbl.add ht k v)
    [("::",
      fun () ->
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
      fun () ->
        let a = ty_var () in
        {ctyp = <:ctyp< $a$ -> $a$ -> bool >>;
         expr = Obj.repr \<;
         patt = fun []});
     ("=",
      fun () ->
        let t = ty_var () in
        {ctyp = <:ctyp< $t$ -> $t$ -> bool >>;
         expr = Obj.repr \=;
         patt = fun []});
     ("*",
      fun () ->
        {ctyp = <:ctyp< int -> int -> int >>;
         expr = Obj.repr \*;
         patt = fun []});
     ("+",
      fun () ->
        {ctyp = <:ctyp< int -> int -> int >>;
         expr = Obj.repr \+;
         patt = fun []});
     ("-",
      fun () ->
        {ctyp = <:ctyp< int -> int -> int >>;
         expr = Obj.repr \-;
         patt = fun []});
     ("^",
      fun () ->
        {ctyp = <:ctyp< string -> string -> string >>;
         expr = Obj.repr \^;
         patt = fun []});
     ("[]",
      fun () ->
        {ctyp = <:ctyp< list $ty_var ()$ >>;
         expr = Obj.repr [];
         patt eval_patt env pl param =
           match (pl, Obj.magic param) with
           [ ([], []) -> Some env
           | _ -> None ]});
     ("Char.chr",
      fun () ->
        {ctyp = <:ctyp< int -> char >>;
         expr = Obj.repr Char.chr;
         patt = fun []});
     ("Char.code",
      fun () ->
        {ctyp = <:ctyp< char -> int >>;
         expr = Obj.repr Char.code;
         patt = fun []});
     ("ctyp",
      fun () ->
        {ctyp = <:ctyp< Grammar.Entry.e MLast.ctyp >>;
         expr = Obj.repr Pcaml.ctyp;
         patt = fun []});
     ("expr",
      fun () ->
        {ctyp = <:ctyp< Grammar.Entry.e MLast.expr >>;
         expr = Obj.repr Pcaml.expr;
         patt = fun []});
     ("Failure",
      fun () ->
        let t1 = <:ctyp< string >> in
        {ctyp = <:ctyp< $t1$ -> exn >>;
         expr = Obj.repr (fun s -> Failure s);
         patt eval_patt env pl param =
           match (pl, Obj.magic param) with
           [ ([p], Failure x) -> eval_patt env p t1 (Obj.repr x)
           | _ -> None ]});
     ("False",
      fun () ->
        {ctyp = <:ctyp< bool >>;
         expr = Obj.repr False;
         patt = fun []});
     ("flush",
      fun () ->
        {ctyp = <:ctyp< out_channel -> unit >>;
         expr = Obj.repr flush;
         patt = fun []});
     ("fst",
      fun () ->
        let a = ty_var () in
        let b = ty_var () in
        {ctyp = <:ctyp< ($a$ * $b$) -> $a$ >>;
         expr = Obj.repr fst;
         patt = fun []});
     ("Gramext.action",
      fun () ->
        {ctyp = <:ctyp< $ty_var ()$ -> Gramext.g_action >>;
         expr = Obj.repr Gramext.action;
         patt = fun []});
     ("Gramext.LeftA",
      fun () ->
        {ctyp = <:ctyp< Gramext.g_assoc >>;
         expr = Obj.repr Gramext.LeftA;
         patt = fun []});
     ("Gramext.Level",
      fun () ->
        {ctyp = <:ctyp< string -> Gramext.position >>;
         expr = Obj.repr (fun s -> Gramext.Level s);
         patt = fun []});
     ("Gramext.NonA",
      fun () ->
        {ctyp = <:ctyp< Gramext.g_assoc >>;
         expr = Obj.repr Gramext.NonA;
         patt = fun []});
     ("Gramext.RightA",
      fun () ->
        {ctyp = <:ctyp< Gramext.g_assoc >>;
         expr = Obj.repr Gramext.RightA;
         patt = fun []});
     ("Gramext.Slist0",
      fun () ->
        let t = ty_var () in
        {ctyp = <:ctyp< Gramext.g_symbol $t$ -> Gramext.g_symbol $t$ >>;
         expr = Obj.repr (fun s -> Gramext.Slist0 s);
         patt = fun []});
     ("Gramext.Slist1",
      fun () ->
        let t = ty_var () in
        {ctyp = <:ctyp< Gramext.g_symbol $t$ -> Gramext.g_symbol $t$ >>;
         expr = Obj.repr (fun s -> Gramext.Slist1 s);
         patt = fun []});
     ("Gramext.Slist0sep",
      fun () ->
        let t = ty_var () in
        {ctyp =
           <:ctyp<
             Gramext.g_symbol $t$ -> Gramext.g_symbol $t$ ->
               Gramext.g_symbol $t$ >>;
         expr = Obj.repr (fun s1 s2 -> Gramext.Slist0sep s1 s2);
         patt = fun []});
     ("Gramext.Slist1sep",
      fun () ->
        let t = ty_var () in
        {ctyp =
           <:ctyp<
             Gramext.g_symbol $t$ -> Gramext.g_symbol $t$ ->
               Gramext.g_symbol $t$ >>;
         expr = Obj.repr (fun s1 s2 -> Gramext.Slist1sep s1 s2);
         patt = fun []});
     ("Gramext.Snext",
      fun () ->
        let a = ty_var () in
        {ctyp = <:ctyp< Gramext.g_symbol $a$ >>;
         expr = Obj.repr Gramext.Snext;
         patt = fun []});
     ("Gramext.Snterm",
      fun () ->
        let t = ty_var () in
        {ctyp = <:ctyp< Gramext.g_entry $t$ -> Gramext.g_symbol $t$ >>;
         expr = Obj.repr (fun e -> Gramext.Snterm e);
         patt = fun []});
     ("Gramext.Sopt",
      fun () ->
        let t = ty_var () in
        {ctyp = <:ctyp< Gramext.g_symbol $t$ -> Gramext.g_symbol $t$ >>;
         expr = Obj.repr (fun s -> Gramext.Sopt s);
         patt = fun []});
     ("Gramext.srules",
      fun () ->
        let t = ty_var () in
        {ctyp =
           <:ctyp<
             list (list (Gramext.g_symbol $t$) * Gramext.g_action) ->
               Gramext.g_symbol $t$ >>;
         expr = Obj.repr Gramext.srules;
         patt = fun []});
     ("Gramext.Sself",
      fun () ->
        {ctyp = <:ctyp< Gramext.g_symbol $ty_var ()$ >>;
         expr = Obj.repr Gramext.Sself;
         patt = fun []});
     ("Gramext.Stoken",
      fun () ->
        {ctyp = <:ctyp< Token.pattern -> Gramext.g_symbol $ty_var ()$ >>;
         expr = Obj.repr (fun tp -> Gramext.Stoken tp);
         patt = fun []});
     ("Grammar.Entry.create",
      fun () ->
        {ctyp = <:ctyp< Grammar.g -> string -> Grammar.Entry.e $ty_var ()$ >>;
         expr = Obj.repr Grammar.Entry.create;
         patt = fun []});
     ("Grammar.Entry.obj",
      fun () ->
        let t = ty_var () in
        {ctyp = <:ctyp< Grammar.Entry.e $t$ -> Gramext.g_entry token >>;
         expr = Obj.repr Grammar.Entry.obj;
         patt = fun []});
     ("Grammar.extend",
      fun () ->
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
         patt = fun []});
     ("Grammar.of_entry",
      fun () ->
        {ctyp = <:ctyp< Grammar.Entry.e $ty_var ()$ -> Grammar.g >>;
         expr = Obj.repr Grammar.of_entry;
         patt = fun []});
     ("let_binding",
      fun () ->
        {ctyp = <:ctyp< Grammar.Entry.e (MLast.patt * MLast.expr) >>;
         expr = Obj.repr Pcaml.let_binding;
         patt = fun []});
     ("List.fold_left",
      fun () ->
        let a = ty_var () in
        let b = ty_var () in
        {ctyp = <:ctyp< ($a$ -> $b$ -> $a$) -> $a$ -> list $b$ -> $a$ >>;
         expr = Obj.repr List.fold_left;
         patt = fun []});
     ("List.fold_right",
      fun () ->
        let a = ty_var () in
        let b = ty_var () in
        {ctyp = <:ctyp< ($a$ -> $b$ -> $b$) -> list $a$ -> $b$ -> $b$ >>;
         expr = Obj.repr List.fold_right;
         patt = fun []});
     ("List.length",
      fun () ->
        let a = ty_var () in
        {ctyp = <:ctyp< list $a$ -> int >>;
         expr = Obj.repr List.length;
         patt = fun []});
     ("List.map",
      fun () ->
        let a = ty_var () in
        let b = ty_var () in
        {ctyp = <:ctyp< ($a$ -> $b$) -> list $a$ -> list $b$ >>;
         expr = Obj.repr List.map;
         patt = fun []});
     ("MLast.ExAcc",
      fun () ->
        {ctyp =
           <:ctyp< Token.location -> MLast.expr -> MLast.expr -> MLast.expr >>;
         expr = Obj.repr (fun loc e1 e2 -> MLast.ExAcc loc e1 e2);
         patt = fun []});
     ("MLast.ExApp",
      fun () ->
        {ctyp =
           <:ctyp< Token.location -> MLast.expr -> MLast.expr -> MLast.expr >>;
         expr = Obj.repr (fun loc e1 e2 -> MLast.ExApp loc e1 e2);
         patt = fun []});
     ("MLast.ExFun",
      fun () ->
        {ctyp =
           <:ctyp<
             Token.location ->
               list (MLast.patt * option MLast.expr * MLast.expr) ->
               MLast.expr >>;
         expr = Obj.repr (fun loc pel -> MLast.ExFun loc pel);
         patt = fun []});
     ("MLast.ExIfe",
      fun () ->
        {ctyp =
           <:ctyp<
             Token.location -> MLast.expr -> MLast.expr -> MLast.expr ->
               MLast.expr >>;
         expr = Obj.repr (fun loc e1 e2 e3 -> MLast.ExIfe loc e1 e2 e3);
         patt = fun []});
     ("MLast.ExLet",
      fun () ->
        {ctyp =
           <:ctyp<
             Token.location -> bool -> list (MLast.patt * MLast.expr) ->
               MLast.expr -> MLast.expr >>;
         expr = Obj.repr (fun loc rf pel e -> MLast.ExLet loc rf pel e);
         patt = fun []});
     ("MLast.ExLid",
      fun () ->
        {ctyp = <:ctyp< Token.location -> string -> MLast.expr >>;
         expr = Obj.repr (fun loc s -> MLast.ExLid loc s);
         patt = fun []});
     ("MLast.ExRec",
      fun () ->
        {ctyp =
           <:ctyp<
             Token.location -> list (MLast.patt * MLast.expr) ->
               option MLast.expr -> MLast.expr >>;
         expr = Obj.repr (fun loc lel eo -> MLast.ExRec loc lel eo);
         patt = fun []});
     ("MLast.ExTup",
      fun () ->
        {ctyp = <:ctyp< Token.location -> list MLast.expr -> MLast.expr >>;
         expr = Obj.repr (fun loc el -> MLast.ExTup loc el);
         patt = fun []});
     ("MLast.ExTyc",
      fun () ->
        {ctyp =
           <:ctyp<
             Token.location -> MLast.expr -> MLast.ctyp -> MLast.expr >>;
         expr = Obj.repr (fun loc e t -> MLast.ExTyc loc e t);
         patt = fun []});
     ("MLast.ExUid",
      fun () ->
        {ctyp = <:ctyp< Token.location -> string -> MLast.expr >>;
         expr = Obj.repr (fun loc s -> MLast.ExUid loc s);
         patt = fun []});
     ("MLast.MeStr",
      fun () ->
        {ctyp =
           <:ctyp<
             Token.location -> list MLast.str_item -> MLast.module_expr >>;
         expr = Obj.repr (fun loc sil -> MLast.MeStr loc sil);
         patt = fun []});
     ("MLast.MeTyc",
      fun () ->
        {ctyp =
           <:ctyp<
             Token.location -> MLast.module_expr -> MLast.module_type ->
               MLast.module_expr >>;
         expr = Obj.repr (fun loc me mt -> MLast.MeTyc loc me mt);
         patt = fun []});
     ("MLast.MtSig",
      fun () ->
        {ctyp =
           <:ctyp<
             Token.location -> list MLast.sig_item -> MLast.module_type >>;
         expr = Obj.repr (fun loc sil -> MLast.MtSig loc sil);
         patt = fun []});
     ("MLast.PaAny",
      fun () ->
        {ctyp = <:ctyp< Token.location -> MLast.patt >>;
         expr = Obj.repr (fun loc -> MLast.PaAny loc);
         patt = fun []});
     ("MLast.PaChr",
      fun () ->
        {ctyp = <:ctyp< Token.location -> string -> MLast.patt >>;
         expr = Obj.repr (fun loc s -> MLast.PaChr loc s);
         patt = fun []});
     ("MLast.PaLid",
      fun () ->
        {ctyp = <:ctyp< Token.location -> string -> MLast.patt >>;
         expr = Obj.repr (fun loc s -> MLast.PaLid loc s);
         patt = fun []});
     ("MLast.PaOrp",
      fun () ->
        {ctyp =
           <:ctyp<
             Token.location -> MLast.patt -> MLast.patt -> MLast.patt >>;
         expr = Obj.repr (fun loc p1 p2 -> MLast.PaOrp loc p1 p2);
         patt = fun []});
     ("MLast.PaRng",
      fun () ->
        {ctyp =
           <:ctyp<
             Token.location -> MLast.patt -> MLast.patt -> MLast.patt >>;
         expr = Obj.repr (fun loc p1 p2 -> MLast.PaRng loc p1 p2);
         patt = fun []});
     ("MLast.PaTup",
      fun () ->
        {ctyp = <:ctyp< Token.location -> list MLast.patt -> MLast.patt >>;
         expr = Obj.repr (fun loc pl -> MLast.PaTup loc pl);
         patt = fun []});
     ("MLast.PaTyc",
      fun () ->
        {ctyp =
           <:ctyp<
             Token.location -> MLast.patt -> MLast.ctyp -> MLast.patt >>;
         expr = Obj.repr (fun loc p t -> MLast.PaTyc loc p t);
         patt = fun []});
     ("MLast.PaUid",
      fun () ->
        {ctyp = <:ctyp< Token.location -> string -> MLast.patt >>;
         expr = Obj.repr (fun loc s -> MLast.PaUid loc s);
         patt = fun []});
     ("MLast.SgVal",
      fun () ->
        {ctyp =
           <:ctyp<
             Token.location -> string -> MLast.ctyp -> MLast.sig_item >>;
         expr = Obj.repr (fun loc s t -> MLast.SgVal loc s t);
         patt = fun []});
     ("MLast.StDcl",
      fun () ->
        {ctyp =
           <:ctyp<
             Token.location -> list MLast.str_item -> MLast.str_item >>;
         expr = Obj.repr (fun loc sil -> MLast.StDcl loc sil);
         patt = fun []});
     ("MLast.StMod",
      fun () ->
        {ctyp =
           <:ctyp<
             Token.location -> bool -> list (string * MLast.module_expr) ->
               MLast.str_item >>;
         expr = Obj.repr (fun loc rf mel -> MLast.StMod loc rf mel);
         patt = fun []});
     ("MLast.StTyp",
      fun () ->
        {ctyp =
           <:ctyp<
             Token.location -> list MLast.type_decl -> MLast.str_item >>;
         expr = Obj.repr (fun loc tdl -> MLast.StTyp loc tdl);
         patt = fun []});
     ("MLast.StVal",
      fun () ->
        {ctyp =
           <:ctyp<
             Token.location -> bool -> list (MLast.patt * MLast.expr) ->
               MLast.str_item >>;
         expr = Obj.repr (fun loc rf pel -> MLast.StVal loc rf pel);
         patt = fun []});
     ("MLast.TyAny",
      fun () ->
        {ctyp = <:ctyp< Token.location -> MLast.ctyp >>;
         expr = Obj.repr (fun loc -> MLast.TyAny loc);
         patt = fun []});
     ("MLast.TyArr",
      fun () ->
        {ctyp =
           <:ctyp<
             Token.location -> MLast.ctyp -> MLast.ctyp -> MLast.ctyp >>;
         expr = Obj.repr (fun loc t1 t2 -> MLast.TyArr loc t1 t2);
         patt = fun []});
     ("MLast.TyLid",
      fun () ->
        {ctyp = <:ctyp< Token.location -> string -> MLast.ctyp >>;
         expr = Obj.repr (fun loc s -> MLast.TyLid loc s);
         patt = fun []});
     ("MLast.TyQuo",
      fun () ->
        {ctyp = <:ctyp< Token.location -> string -> MLast.ctyp >>;
         expr = Obj.repr (fun loc s -> MLast.TyQuo loc s);
         patt = fun []});
     ("MLast.TyRec",
      fun () ->
        {ctyp =
           <:ctyp<
             Token.location ->
               list (Token.location * string * bool * MLast.ctyp) ->
               MLast.ctyp >>;
         expr = Obj.repr (fun loc ldl -> MLast.TyRec loc ldl);
         patt = fun []});
     ("module_expr",
      fun () ->
        {ctyp = <:ctyp< Grammar.Entry.e MLast.module_expr >>;
         expr = Obj.repr Pcaml.module_expr;
         patt = fun []});
     ("module_type",
      fun () ->
        {ctyp = <:ctyp< Grammar.Entry.e MLast.module_type >>;
         expr = Obj.repr Pcaml.module_type;
         patt = fun []});
     ("None",
      fun () ->
        {ctyp = <:ctyp< option $ty_var ()$ >>;
         expr = Obj.repr None;
         patt eval_patt env pl param =
           match (pl, Obj.magic param) with
           [ ([], None) -> Some env
           | _ -> None ]});
     ("Not_found",
      fun () ->
        {ctyp = <:ctyp< exn >>;
         expr = Obj.repr Not_found;
         patt eval_patt env pl param =
           match (pl, Obj.magic param) with
           [ ([], Not_found) -> Some env
           | _ -> None ]});
     ("patt",
      fun () ->
        {ctyp = <:ctyp< Grammar.Entry.e MLast.patt >>;
         expr = Obj.repr Pcaml.patt;
         patt = fun []});
     ("prerr_endline",
      fun () ->
        {ctyp = <:ctyp< string -> unit >>;
         expr = Obj.repr prerr_endline;
         patt = fun []});
     ("prerr_int",
      fun () ->
        {ctyp = <:ctyp< int -> unit >>;
         expr = Obj.repr prerr_int;
         patt = fun []});
     ("print_endline",
      fun () ->
        {ctyp = <:ctyp< string -> unit >>;
         expr = Obj.repr print_endline;
         patt = fun []});
     ("Printf.eprintf",
      fun () ->
        let t = ty_var () in
        {ctyp = <:ctyp< format $t$ out_channel unit -> $t$ >>;
         expr = Obj.repr Printf.eprintf;
         patt = fun []});
     ("raise",
      fun () ->
        {ctyp = <:ctyp< exn -> $ty_var ()$ >>;
         expr = Obj.repr raise;
         patt = fun []});
     ("sig_item",
      fun () ->
        {ctyp = <:ctyp< Grammar.Entry.e MLast.sig_item >>;
         expr = Obj.repr Pcaml.sig_item;
         patt = fun []});
     ("snd",
      fun () ->
        let a = ty_var () in
        let b = ty_var () in
        {ctyp = <:ctyp< ($a$ * $b$) -> $b$ >>;
         expr = Obj.repr snd;
         patt = fun []});
     ("Some",
      fun () ->
        let ta = ty_var () in
        {ctyp = <:ctyp< $ta$ -> option $ta$ >>;
         expr = Obj.repr (fun x -> Some x);
         patt eval_patt env pl param =
           match (pl, Obj.magic param) with
           [ ([p], Some x) -> eval_patt env p ta (Obj.repr x)
           | _ -> None ]});
     ("stderr",
      fun () ->
        {ctyp = <:ctyp< out_channel >>;
         expr = Obj.repr stderr;
         patt = fun []});
     ("Stdpp.raise_with_loc",
      fun () ->
        {ctyp = <:ctyp< Token.location -> exn -> _ >>;
         expr = Obj.repr Stdpp.raise_with_loc;
         patt = fun []});
     ("str_item",
      fun () ->
        {ctyp = <:ctyp< Grammar.Entry.e MLast.str_item >>;
         expr = Obj.repr Pcaml.str_item;
         patt = fun []});
     ("Stream.Error",
      fun () ->
        {ctyp = <:ctyp< string -> exn >>;
         expr = Obj.repr (fun s -> Stream.Error s);
         patt = fun []});
     ("Stream.of_string",
      fun () ->
        {ctyp = <:ctyp< string -> Stream.t char >>;
         expr = Obj.repr Stream.of_string;
         patt = fun []});
     ("Stream.peek",
      fun () ->
        let ta = ty_var () in
        {ctyp = <:ctyp< Stream.t $ta$ -> option $ta$ >>;
         expr = Obj.repr Stream.peek;
         patt = fun []});
     ("String.get",
      fun () ->
        {ctyp = <:ctyp< string -> int -> char >>;
         expr = Obj.repr String.get;
         patt = fun []});
     ("String.length",
      fun () ->
        {ctyp = <:ctyp< string -> int >>;
         expr = Obj.repr String.length;
         patt = fun []});
     ("String.make",
      fun () ->
        {ctyp = <:ctyp< int -> char -> string >>;
         expr = Obj.repr String.make;
         patt = fun []});
     ("String.set",
      fun () ->
        {ctyp = <:ctyp< string -> int -> char -> unit >>;
         expr = Obj.repr String.set;
         patt = fun []});
     ("String.sub",
      fun () ->
        {ctyp = <:ctyp< string -> int -> int -> string >>;
         expr = Obj.repr String.sub;
         patt = fun []});
     ("True",
      fun () ->
        {ctyp = <:ctyp< bool >>;
         expr = Obj.repr True;
         patt = fun []});
     ("type_declaration",
      fun () ->
        {ctyp = <:ctyp< Grammar.Entry.e MLast.type_decl >>;
         expr = Obj.repr Pcaml.type_declaration;
         patt = fun []})];
  ht
};

value rec eval_expr env e =
  let loc = MLast.loc_of_expr e in
  match e with
  [ <:expr< fun [ $list:pel$ ] >> ->
      eval_fun loc env pel
  | <:expr< let $opt:rf$ $list:pel$ in $e$ >> ->
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
        [ [] -> {ctyp = <:ctyp< unit >>; expr = Obj.repr (); patt = fun []}
        | [e] -> eval_expr env e
        | [e :: el] ->
            let _ = eval_expr env e in
            loop el ]

  | <:expr< $e1$ && $e2$ >> ->
      let v1 = eval_expr env e1 in
      let t = <:ctyp< bool >> in
      if unify loc t v1.ctyp then
        if (Obj.magic v1.expr : bool) then eval_expr env e2
        else {ctyp = t; expr = Obj.repr False; patt = fun []}
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
       patt = fun []}

  | <:expr< $int:s$ >> ->
      {ctyp = <:ctyp< int >>; expr = Obj.repr (int_of_string s);
       patt = fun []}
  | <:expr< $str:s$ >> ->
      {ctyp = <:ctyp< string >>; expr = Obj.repr (Token.eval_string loc s);
       patt = fun []}
  | <:expr< $chr:s$ >> ->
      {ctyp = <:ctyp< char >>; expr = Obj.repr (Token.eval_char s);
       patt = fun []}

  | <:expr< $lid:s$ >> ->
      match try Some (List.assoc s env) with [ Not_found -> None ] with
      [ Some {by_let = by_let; valu = v} ->
          if by_let then {(v) with ctyp = instanciate loc s v.ctyp} else v
      | None ->
          try Hashtbl.find val_tab s () with
          [ Not_found -> unbound_var loc s ] ]
  | <:expr< $uid:s$ >> ->
      try Hashtbl.find val_tab s () with [ Not_found -> unbound_var loc s ]
  | <:expr< $uid:a$ . $lid:b$ >> | <:expr< $uid:a$ . $uid:b$ >> ->
      let s = a ^ "." ^ b in
      try Hashtbl.find val_tab s () with [ Not_found -> unbound_var loc s ]
  | <:expr< $uid:a$ . $uid:b$ . $lid:c$ >> ->
      let s = a ^ "." ^ b ^ "." ^ c in
      try Hashtbl.find val_tab s () with [ Not_found -> unbound_var loc s ]

  | e -> not_impl loc "11/expr" e ]

and eval_match loc env e pel =
  let v = eval_expr env e in
  match eval_match_assoc_list loc env v.ctyp (ty_var ()) pel v.expr with
  [ Some v -> v
  | None ->
      raise
        (Match_failure
           (Pcaml.input_file.val, Stdpp.line_nb loc,
            Stdpp.first_pos loc - Stdpp.bol_pos loc)) ]

and eval_try loc env e pel =
  try eval_expr env e with exn ->
    let v = {ctyp = <:ctyp< exn >>; expr = Obj.magic exn; patt = fun []} in
    match eval_match_assoc_list loc env v.ctyp (ty_var ()) pel v.expr with
    [ Some v -> v
    | None -> raise exn ]

and eval_let loc env rf pel e =
  if rf then do {
    let extra_env =
      loop [] pel where rec loop extra_env =
        fun
        [ [(p, e) :: pel] ->
            match p with
            [ <:patt< $lid:s$ >> ->
                [(s, {by_let = True; valu = Obj.magic e}) :: extra_env]
            | <:patt< _ >> -> extra_env
            | p -> not_impl loc "15/patt" p ]
        | [] -> extra_env ]
    in
    let new_env = List.rev_append extra_env env in
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
                              loop new_env {ctyp = t; expr = e; patt = fun []}
                                p
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
             (Pcaml.input_file.val, Stdpp.line_nb loc,
              Stdpp.first_pos loc - Stdpp.bol_pos loc)) ]
  in
  {ctyp = t; expr = Obj.repr e; patt = fun []}

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
        if eo = None then True
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
      | p -> (p, pl) ]
  in
  match ppl with
  [ (<:patt< $uid:s$ >>, pl) ->
      match
        try Some (Hashtbl.find val_tab s ()) with [ Not_found -> None ]
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
                    (sprintf
                       "Too many arguments (%d) to constructor %s\n\
                        It expects %d argument(s)."
                       (List.length pl) s (List.length pl - len)) ]
      | _ -> unbound_cons loc s ]
  | (_, [_ :: _]) -> error loc "not a constructor"
  | (p, []) ->
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
      | <:patt< $lid:s$ >> ->
          let v = {ctyp = tp; expr = param; patt = fun []} in
          Some [(s, {by_let = False; valu = v}) :: env]

      | <:patt< _ >> -> Some env
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
      {ctyp = t; expr = Obj.magic v1.expr v2.expr; patt = fun []}
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
