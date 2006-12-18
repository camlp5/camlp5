(* camlp4r q_MLast.cmo -qmod ctyp,Type *)
(* $Id: pa_pragma.ml,v 1.14 2006/12/18 11:37:45 deraugla Exp $ *)

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

value inst_vars = ref [];
value rec inst loc t =
  match t with
  [ <:ctyp< $t1$ -> $t2$ >> -> <:ctyp< $inst loc t1$ -> $inst loc t2$ >>
  | <:ctyp< $t1$ $t2$ >> -> <:ctyp< $inst loc t1$ $inst loc t2$ >>
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

  | (<:ctyp< Token.pattern >>, <:ctyp< (string * string) >>) -> True
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
        let t = ty_var () in
        {ctyp = <:ctyp< $t$ -> list $t$ -> list $t$ >>;
         item = Obj.repr (fun a l -> [a :: l])});
     ("=",
      fun () ->
        let t = ty_var () in
        {ctyp = <:ctyp< $t$ -> $t$ -> bool >>;
         item = Obj.repr \=});
     ("+",
      fun () ->
        {ctyp = <:ctyp< int -> int -> int >>;
         item = Obj.repr \+});
     ("[]",
      fun () ->
        {ctyp = <:ctyp< list $ty_var ()$ >>;
         item = Obj.repr []});
     ("ctyp",
      fun () ->
        {ctyp = <:ctyp< Grammar.Entry.e MLast.ctyp >>;
         item = Obj.repr Pcaml.ctyp});
     ("expr",
      fun () ->
        {ctyp = <:ctyp< Grammar.Entry.e MLast.expr >>;
         item = Obj.repr Pcaml.expr});
     ("Failure",
      fun () ->
        {ctyp = <:ctyp< string -> exn >>;
         item = Obj.repr (fun s -> Failure s)});
     ("flush",
      fun () ->
        {ctyp = <:ctyp< out_channel -> unit >>;
         item = Obj.repr flush});
     ("Gramext.action",
      fun () ->
        {ctyp = <:ctyp< $ty_var ()$ -> Gramext.g_action >>;
         item = Obj.repr Gramext.action});
     ("Gramext.LeftA",
      fun () ->
        {ctyp = <:ctyp< Gramext.g_assoc >>;
         item = Obj.repr Gramext.LeftA});
     ("Gramext.Level",
      fun () ->
        {ctyp = <:ctyp< string -> Gramext.position >>;
         item = Obj.repr (fun s -> Gramext.Level s)});
     ("Gramext.NonA",
      fun () ->
        {ctyp = <:ctyp< Gramext.g_assoc >>;
         item = Obj.repr Gramext.NonA});
     ("Gramext.RightA",
      fun () ->
        {ctyp = <:ctyp< Gramext.g_assoc >>;
         item = Obj.repr Gramext.RightA});
     ("Gramext.Slist0",
      fun () ->
        let t = ty_var () in
        {ctyp = <:ctyp< Gramext.g_symbol $t$ -> Gramext.g_symbol $t$ >>;
         item = Obj.repr (fun s -> Gramext.Slist0 s)});
     ("Gramext.Slist1",
      fun () ->
        let t = ty_var () in
        {ctyp = <:ctyp< Gramext.g_symbol $t$ -> Gramext.g_symbol $t$ >>;
         item = Obj.repr (fun s -> Gramext.Slist1 s)});
     ("Gramext.Slist0sep",
      fun () ->
        let t = ty_var () in
        {ctyp =
           <:ctyp<
             Gramext.g_symbol $t$ -> Gramext.g_symbol $t$ ->
               Gramext.g_symbol $t$ >>;
         item = Obj.repr (fun s1 s2 -> Gramext.Slist0sep s1 s2)});
     ("Gramext.Slist1sep",
      fun () ->
        let t = ty_var () in
        {ctyp =
           <:ctyp<
             Gramext.g_symbol $t$ -> Gramext.g_symbol $t$ ->
               Gramext.g_symbol $t$ >>;
         item = Obj.repr (fun s1 s2 -> Gramext.Slist1sep s1 s2)});
     ("Gramext.Snterm",
      fun () ->
        let t = ty_var () in
        {ctyp = <:ctyp< Gramext.g_entry $t$ -> Gramext.g_symbol $t$ >>;
         item = Obj.repr (fun e -> Gramext.Snterm e)});
     ("Gramext.Sopt",
      fun () ->
        let t = ty_var () in
        {ctyp = <:ctyp< Gramext.g_symbol $t$ -> Gramext.g_symbol $t$ >>;
         item = Obj.repr (fun s -> Gramext.Sopt s)});
     ("Gramext.srules",
      fun () ->
        let t = ty_var () in
        {ctyp =
           <:ctyp<
             list (list (Gramext.g_symbol $t$) * Gramext.g_action) ->
               Gramext.g_symbol $t$ >>;
         item = Obj.repr Gramext.srules});
     ("Gramext.Sself",
      fun () ->
        {ctyp = <:ctyp< Gramext.g_symbol $ty_var ()$ >>;
         item = Obj.repr Gramext.Sself});
     ("Gramext.Stoken",
      fun () ->
        {ctyp = <:ctyp< Token.pattern -> Gramext.g_symbol $ty_var ()$ >>;
         item = Obj.repr (fun tp -> Gramext.Stoken tp)});
     ("Grammar.Entry.create",
      fun () ->
        {ctyp = <:ctyp< Grammar.g -> string -> Grammar.Entry.e $ty_var ()$ >>;
         item = Obj.repr Grammar.Entry.create});
     ("Grammar.Entry.obj",
      fun () ->
        let t = ty_var () in
        {ctyp = <:ctyp< Grammar.Entry.e $t$ -> Gramext.g_entry token >>;
         item = Obj.repr Grammar.Entry.obj});
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
         item = Obj.repr Grammar.extend});
     ("Grammar.of_entry",
      fun () ->
        {ctyp = <:ctyp< Grammar.Entry.e $ty_var ()$ -> Grammar.g >>;
         item = Obj.repr Grammar.of_entry});
     ("let_binding",
      fun () ->
        {ctyp = <:ctyp< Grammar.Entry.e (MLast.patt * MLast.expr) >>;
         item = Obj.repr Pcaml.let_binding});
     ("MLast.ExApp",
      fun () ->
        {ctyp =
           <:ctyp< Token.location -> MLast.expr -> MLast.expr -> MLast.expr >>;
         item = Obj.repr (fun loc e1 e2 -> MLast.ExApp loc e1 e2)});
     ("MLast.ExIfe",
      fun () ->
        {ctyp =
           <:ctyp<
             Token.location -> MLast.expr -> MLast.expr -> MLast.expr ->
               MLast.expr >>;
         item = Obj.repr (fun loc e1 e2 e3 -> MLast.ExIfe loc e1 e2 e3)});
     ("MLast.ExLid",
      fun () ->
        {ctyp = <:ctyp< Token.location -> string -> MLast.expr >>;
         item = Obj.repr (fun loc s -> MLast.ExLid loc s)});
     ("MLast.ExTup",
      fun () ->
        {ctyp = <:ctyp< Token.location -> list MLast.expr -> MLast.expr >>;
         item = Obj.repr (fun loc el -> MLast.ExTup loc el)});
     ("MLast.ExUid",
      fun () ->
        {ctyp = <:ctyp< Token.location -> string -> MLast.expr >>;
         item = Obj.repr (fun loc s -> MLast.ExUid loc s)});
     ("MLast.PaLid",
      fun () ->
        {ctyp = <:ctyp< Token.location -> string -> MLast.patt >>;
         item = Obj.repr (fun loc s -> MLast.PaLid loc s)});
     ("module_expr",
      fun () ->
        {ctyp = <:ctyp< Grammar.Entry.e MLast.module_expr >>;
         item = Obj.repr Pcaml.module_expr});
     ("module_type",
      fun () ->
        {ctyp = <:ctyp< Grammar.Entry.e MLast.module_type >>;
         item = Obj.repr Pcaml.module_type});
     ("None",
      fun () ->
        {ctyp = <:ctyp< option $ty_var ()$ >>;
         item = Obj.repr None});
     ("prerr_endline",
      fun () ->
        {ctyp = <:ctyp< string -> unit >>;
         item = Obj.repr prerr_endline});
     ("print_endline",
      fun () ->
        {ctyp = <:ctyp< string -> unit >>;
         item = Obj.repr print_endline});
     ("Printf.eprintf",
      fun () ->
        let t = ty_var () in
        {ctyp = <:ctyp< format $t$ out_channel unit -> $t$ >>;
         item = Obj.repr Printf.eprintf});
     ("raise",
      fun () ->
        {ctyp = <:ctyp< exn -> $ty_var ()$ >>;
         item = Obj.repr raise});
     ("sig_item",
      fun () ->
        {ctyp = <:ctyp< Grammar.Entry.e MLast.sig_item >>;
         item = Obj.repr Pcaml.sig_item});
     ("Some",
      fun () ->
        let t = ty_var () in
        {ctyp = <:ctyp< $t$ -> option $t$ >>;
         item = Obj.repr (fun x -> Some x)});
     ("patt",
      fun () ->
        {ctyp = <:ctyp< Grammar.Entry.e MLast.patt >>;
         item = Obj.repr Pcaml.patt});
     ("stderr",
      fun () ->
        {ctyp = <:ctyp< out_channel >>;
         item = Obj.repr stderr});
     ("str_item",
      fun () ->
        {ctyp = <:ctyp< Grammar.Entry.e MLast.str_item >>;
         item = Obj.repr Pcaml.str_item});
     ("True",
      fun () ->
        {ctyp = <:ctyp< bool >>;
         item = Obj.repr True});
     ("type_declaration",
      fun () ->
        {ctyp = <:ctyp< Grammar.Entry.e MLast.type_decl >>;
         item = Obj.repr Pcaml.type_declaration})];
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
  | <:expr< if $e1$ then $e2$ else $e3$ >> ->
      let v = eval_expr env e1 in
      match v.ctyp with
      [ <:ctyp< bool >> -> eval_expr env (if Obj.magic v.item then e2 else e3)
      | t -> bad_type (MLast.loc_of_expr e1) <:ctyp< bool >> t ]
  | <:expr< do { $list:el$ } >> ->
      loop el where rec loop =
        fun
        [ [] -> {ctyp = <:ctyp< unit >>; item = Obj.repr ()}
        | [e] -> eval_expr env e
        | [e :: el] ->
            let _ = eval_expr env e in
            loop el ]

  | <:expr< $e1$ $e2$ >> ->
      eval_expr_apply loc env e1 e2

  | <:expr< ( $e$ : $t$ ) >> ->
      let v = eval_expr env e in
      let t = type_of_ctyp t in
      if unify loc t v.ctyp then
        let t = eval_type loc t in
        {ctyp = t; item = v.item}
      else
        bad_type loc t v.ctyp

  | <:expr< ( $list:el$ ) >> ->
      let vl = List.map (eval_expr env) el in
      let tl = List.map (fun v -> v.ctyp) vl in
      let xl = List.map (fun v -> v.item) vl in
      {ctyp = <:ctyp< ( $list:tl$ ) >>; item = Obj.repr (Array.of_list xl)}

  | <:expr< $str:s$ >> ->
      {ctyp = <:ctyp< string >>; item = Obj.repr (Token.eval_string loc s)}
  | <:expr< $int:s$ >> ->
      {ctyp = <:ctyp< int >>; item = Obj.repr (int_of_string s)}

  | <:expr< $lid:s$ >> ->
      match try Some (List.assoc s env) with [ Not_found -> None ] with
      [ Some (by_let, v) ->
          if by_let then {(v) with ctyp = instanciate loc s v.ctyp}
          else v
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
  eval_match_assoc_list loc env (ty_var ()) v.ctyp pel v.item

and eval_let loc env rf pel e =
  let new_env =
    loop env pel where rec loop new_env =
      fun
      [ [(p, e) :: pel] ->
          let v = eval_expr env e in
          let new_env =
            match p with
            [ <:patt< $lid:s$ >> -> [(s, (True, v)) :: new_env]
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
        let v = eval_expr env e in
        if unify loc t v.ctyp then
          Some {ctyp = eval_type loc t; item = v.item}
        else
          bad_type loc t v.ctyp
      else None
  | None -> None ]

and eval_patt loc p env tp param =
  match p with
  [ <:patt< ($p$ : $t$) >> ->
      let t = type_of_ctyp t in
      if unify loc tp t then eval_patt loc p env (eval_type loc tp) param
      else bad_type loc tp t
  | <:patt< $lid:s$ >> ->
      let v = {ctyp = tp; item = param} in
      Some [(s, (False, v)) :: env]
  | <:patt< $uid:s$ >> ->
      match
        try Some (Hashtbl.find val_tab s ()) with [ Not_found -> None ]
      with
      [ Some v ->
          if unify loc tp v.ctyp then
            if param = v.item then Some env else None
          else bad_type loc tp v.ctyp
      | None -> unbound_cons loc s ]
  | <:patt< _ >> -> Some env
  | p -> not_impl loc "1/eval_patt" p ]

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
          let s = (Obj.magic v2.item : string) in
          match try Some (String.index s '%') with [ Not_found -> None ] with
          [ Some i -> failwith ("not impl format " ^ s)
          | None -> unify loc tf1 tf3 ]
      | (t1, t2) -> unify loc t1 t2 ]
    in
    if unify_ok then
      let t = eval_type loc t12 in
      {ctyp = t; item = Obj.magic v1.item v2.item}
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
