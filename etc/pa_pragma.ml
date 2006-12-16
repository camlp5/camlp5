(* camlp4r q_MLast.cmo -qmod ctyp,Type *)
(* $Id: pa_pragma.ml,v 1.3 2006/12/16 14:27:17 deraugla Exp $ *)

open Printf;

value not_impl loc name x =
  let desc =
    if Obj.is_block (Obj.repr x) then
      "tag = " ^ string_of_int (Obj.tag (Obj.repr x))
    else "int_val = " ^ string_of_int (Obj.magic x)
  in
  Stdpp.raise_with_loc loc (Failure ("Main: not impl " ^ name ^ " " ^ desc))
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

type typed 'a = { ctyp : Type.t; item : 'a };
type expr_v = typed Obj.t;

value ty_var =
  let loc = Stdpp.dummy_loc in
  fun () -> <:ctyp< '$ref None$ >>
;

value vars = ref [];
value rec type_of_ctyp =
  fun
  [ MLast.TyAcc loc t1 t2 -> <:ctyp< $type_of_ctyp t1$ . $type_of_ctyp t2$ >>
  | MLast.TyApp loc t1 t2 -> <:ctyp< $type_of_ctyp t1$ $type_of_ctyp t2$ >>
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

value rec str_of_ty loc =
  fun
  [ <:ctyp< $t1$ -> $t2$ >> ->
      let s1 = str_of_ty2 loc t1 in
      let s2 = str_of_ty loc t2 in
      s1 ^ " -> " ^ s2
  | t -> str_of_ty2 loc t ]
and str_of_ty2 loc =
  fun
  [ <:ctyp< ( $list:tl$ ) >> ->
      let sl = List.map (str_of_ty loc) tl in
      "(" ^
      List.fold_left (fun s t -> if s = "" then t else s ^ " * " ^ t) "" sl ^
      ")"
  | <:ctyp< $t1$ . $t2$ >> -> str_of_ty loc t1 ^ "." ^ str_of_ty loc t2
  | <:ctyp< '$s$ >> ->
      match s.val with
      [ Some t -> str_of_ty2 loc t
      | None -> "'a?" ]
  | <:ctyp< $lid:s$ >> -> s
  | <:ctyp< $uid:s$ >> -> s
  | t -> not_impl loc "str_of_ty2" t ]
;

value bad_type loc expected_t found_t =
  Stdpp.raise_with_loc loc
    (Failure
       (sprintf "Type expected %s; type found = %s"
          (str_of_ty loc expected_t) (str_of_ty loc found_t)))
;

value unbound_var loc s =
  Stdpp.raise_with_loc loc (Failure (sprintf "Unbound variable: %s" s))
;

value rec unify loc t1 t2 =
  match (t1, t2) with
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
      | None -> do { s.val := Some t1; True } ]
  | (<:ctyp< '$s$ >>, t2) -> unify loc t2 t1

  | (<:ctyp< $_$ $_$ >>, t2) -> not_impl loc "2/unify" t2
  | (<:ctyp< Token.pattern >>, <:ctyp< (string * string) >>) -> True
  | (<:ctyp< $lid:s1$ >>, <:ctyp< $lid:s2$ >>) -> s1 = s2
  | (<:ctyp< $uid:s1$ >>, <:ctyp< $uid:s2$ >>) -> s1 = s2
  | (<:ctyp< _ >>, _) -> True
  | (t1, t2) -> False ]
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
  | <:ctyp< $lid:_$ >> | <:ctyp< $uid:_$ >> -> t
  | <:ctyp< _ >> -> <:ctyp< _ >> ]
;

value rec eval_expr loc env =
  fun
  [ <:expr< $e1$ $e2$ >> -> eval_expr_apply loc env e1 e2
  | <:expr< fun [ $list:pel$ ] >> -> eval_expr_fun loc env pel

  | <:expr< Gramext.Stoken >> ->
      let t = <:ctyp< Token.pattern -> Gramext.g_symbol $ty_var ()$ >> in
      {ctyp = t; item = Obj.repr (fun tp -> Gramext.Stoken tp)}
  | <:expr< Gramext . Sself >> ->
      let t = <:ctyp< Gramext.g_symbol $ty_var ()$ >> in
      {ctyp = t; item = Obj.repr Gramext.Sself}
  | <:expr< Gramext.action >> ->
      let t = <:ctyp< $ty_var ()$ -> Gramext.g_action >> in
      {ctyp = t; item = Obj.repr Gramext.action}
  | <:expr< Grammar.Entry.obj >> ->
      let t = <:ctyp< Grammar.Entry.e _ -> Gramext.g_entry token >> in
      {ctyp = t; item = Obj.repr Grammar.Entry.obj}
  | <:expr< Grammar.extend >> ->
      let t =
        let te = ty_var () in
        <:ctyp<
          list
            (Gramext.g_entry $te$ * option Gramext.position *
             list
               (option string * option Gramext.g_assoc *
                list (list (Gramext.g_symbol $te$) * Gramext.g_action))) ->
          unit >>
      in
      {ctyp = t; item = Obj.repr Grammar.extend}
  | <:expr< MLast.ExIfe >> ->
      let t =
        <:ctyp<
          Token.location -> MLast.expr -> MLast.expr -> MLast.expr ->
            MLast.expr >>
      in
      let e loc e1 e2 e3 = MLast.ExIfe loc e1 e2 e3 in
      {ctyp = t; item = Obj.repr e}

  | <:expr< ( $e$ : $t$ ) >> ->
      let v = eval_expr loc env e in
      let t = type_of_ctyp t in
      if unify loc t v.ctyp then
        let t = eval_type loc t in
        {ctyp = t; item = v.item}
      else bad_type loc t v.ctyp

  | <:expr< ( $list:el$ ) >> ->
      let vl = List.map (eval_expr loc env) el in
      let tl = List.map (fun v -> v.ctyp) vl in
      let xl = List.map (fun v -> v.item) vl in
      {ctyp = <:ctyp< ( $list:tl$ ) >>; item = Obj.repr (Array.of_list xl)}

  | <:expr< $lid:s$ >> ->
      match try Some (List.assoc s env) with [ Not_found -> None ] with
      [ Some v -> v
      | None ->
          match s with
          [ "expr" ->
              {ctyp = <:ctyp< Grammar.Entry.e MLast.expr >>;
               item = Obj.repr Pcaml.expr}
          | _ -> unbound_var loc s ] ]

  | <:expr< $uid:"::"$ >> ->
      let t = ty_var () in
      let t = <:ctyp< $t$ -> list $t$ -> list $t$ >> in
      {ctyp = t; item = Obj.repr (fun a l -> [a :: l])}
  | <:expr< None >> ->
      {ctyp = <:ctyp< option $ty_var ()$ >>; item = Obj.repr None}
  | <:expr< [] >> ->
      {ctyp = <:ctyp< list $ty_var ()$ >>; item = Obj.repr []}

  | <:expr< Grammar. $lid:s$ >> -> not_impl loc ("expr access Grammar." ^ s) 0
  | <:expr< Gramext . $uid:s$ >> -> not_impl loc ("4/expr Gramext." ^ s) 0
  | <:expr< Gramext . $lid:s$ >> -> not_impl loc ("8/expr access " ^ s) 0
  | <:expr< MLast . $uid:s$ >> -> not_impl loc ("9/expr access = " ^ s) 0
  | <:expr< $uid:s$ . $e2$ >> -> not_impl loc ("7/expr access = " ^ s) e2
  | <:expr< Grammar. $uid:s$ . $e3$ >> -> not_impl loc ("Grammar." ^ s) e3
  | <:expr< $uid:s$ . $e2$ . $e3$ >> -> not_impl loc ("2/expr access " ^ s) e2
  | <:expr< $e1$ . $e2$ . $e3$ >> -> not_impl loc "2/expr access" e1
  | <:expr< $e1$ . $e2$ >> -> not_impl loc "expr access" e1
  | <:expr< $uid:s$ >> -> not_impl loc ("1/expr uid = " ^ s) 0
  | <:expr< $str:s$ >> -> {ctyp = <:ctyp< string >>; item = Obj.repr s}

  | e -> not_impl loc "11/expr" e ]

and eval_expr_fun loc env pel =
  let t1 = ty_var () in
  let t2 = ty_var () in
  let t = <:ctyp< $t1$ -> $t2$ >> in
  let e param = (eval_match_assoc_list loc env t1 t2 pel param).item in
  {ctyp = t; item = Obj.repr e}

and eval_match_assoc_list loc env t1 t2 pel param =
  match pel with
  [ [pe :: pel] ->
      match eval_match_assoc loc env t1 t2 pe param with
      [ Some v -> v
      | None -> eval_match_assoc_list loc env t1 t2 pel param ]
  | [] ->
      raise
        (Match_failure
           (Pcaml.input_file.val, Stdpp.line_nb loc,
            Stdpp.first_pos loc - Stdpp.bol_pos loc)) ]

and eval_match_assoc loc env t1 t2 (p, eo, e) param =
  match eval_patt loc p env t1 param with
  [ Some env ->
      let cond =
        if eo = None then True
        else not_impl loc "eval_match_assoc eo = Some..." p
      in
      if cond then
        let t = eval_type loc t2 in
        let v = eval_expr loc env e in
        if unify loc t v.ctyp then
          Some {ctyp = eval_type loc t; item = v.item}
        else bad_type loc t v.ctyp
      else None
  | None -> None ]

and eval_patt loc p env t1 param =
  match p with
  [ <:patt< ($p$ : $t$) >> ->
      let t = type_of_ctyp t in
      if unify loc t1 t then eval_patt loc p env (eval_type loc t1) param
      else bad_type loc t1 t
  | <:patt< $lid:s$ >> ->
      let v = {ctyp = t1; item = param} in
      Some [(s, v) :: env]
  | <:patt< _ >> -> Some env
  | p -> not_impl loc "1/eval_patt" p ]

and eval_expr_apply loc env e1 e2 =
  let v1 = eval_expr loc env e1 in
  let v2 = eval_expr loc env e2 in
  let t11 = ty_var () in
  let t12 = ty_var () in
  if unify loc v1.ctyp <:ctyp< $t11$ -> $t12$ >> then
    if unify loc (eval_type loc t11) v2.ctyp then
      let t = eval_type loc t12 in
      {ctyp = t; item = Obj.magic v1.item v2.item}
    else bad_type loc v1.ctyp v2.ctyp
  else bad_type loc v1.ctyp v2.ctyp
;

value eval_unit_expr loc e =
  match (eval_expr loc [] e).ctyp with
  [ <:ctyp< unit >> -> ()
  | t -> not_impl loc "expr not unit" t ]
;

value pragma =
  fun
  [ Some e -> eval_unit_expr (MLast.loc_of_expr e) e
  | None -> failwith "bad directive" ]
;

Pcaml.add_directive "pragma" pragma;
