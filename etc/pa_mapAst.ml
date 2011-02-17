(* camlp5r *)
(* $Id: pa_mapAst.ml,v 6.6 2011/02/17 09:17:06 deraugla Exp $ *)

(*
   meta/camlp5r etc/pa_mapAst.cmo etc/pr_r.cmo -impl main/mLast.mli
*)

#load "pa_extend.cmo";
#load "q_MLast.cmo";

Pcaml.strict_mode.val := True;

value param_f = "f";
value field_of_constr = String.uncapitalize;

value patt_of_type loc n t =
  let x = "x" ^ string_of_int n in
  let p = <:patt< $lid:x$ >> in
  match t with
  [ <:ctyp< loc >> -> (<:patt< loc >>, n)
  | _ -> (p, n + 1) ]
;

value expr_param_of_type loc n t =
  let x = "x" ^ string_of_int n in
  let e = <:expr< $lid:x$ >> in
  match t with
  [ <:ctyp< loc >> -> (<:expr< loc >>, n)
  | _ -> (e, n + 1) ]
;

value rec expr_of_type gtn use_self loc t =
  match t with
  [ <:ctyp< $lid:tn$ >> ->
      if tn = gtn then Some (<:expr< self >>, True)
      else if List.mem tn ["bool"; "string"; "type_var"] then None
      else Some (<:expr< $lid:tn$ $lid:param_f$ >>, use_self)
  | <:ctyp< ($list:tl$) >> ->
      let (rev_pl, _) =
        List.fold_left
          (fun (rev_pl, n) t ->
             let (p, n) = patt_of_type loc n t in
             ([p :: rev_pl], n))
          ([], 1) tl
      in
      let (rev_el, _, use_self) =
        List.fold_left
          (fun (rev_el, n, use_self) t ->
             let (e, n, use_self) =
               match t with
               [ <:ctyp< loc >> ->
                   (<:expr< $lid:param_f$.mloc loc >>, n, use_self)
               | _ ->
                   let x = "x" ^ string_of_int n in
                   let e = <:expr< $lid:x$ >> in
                   let (e, use_self) =
                     match expr_of_type gtn use_self loc t with
                     [ Some (f, use_self) -> (<:expr< $f$ $e$ >>, use_self)
                     | None -> (e, use_self) ]
                   in
                   (e, n + 1, use_self) ]
             in
             ([e :: rev_el], n, use_self))
          ([], 1, use_self) tl
      in
      let p = <:patt< ($list:List.rev rev_pl$) >> in
      let e = <:expr< ($list:List.rev rev_el$) >> in
      Some (<:expr< fun $p$ -> $e$ >>, use_self)
  | <:ctyp< $t1$ $t2$ >> ->
      match expr_of_type gtn use_self loc t2 with
      [ Some (e, use_self) ->
          let f =
            match t1 with
            [ <:ctyp< list >> -> <:expr< List.map >>
            | <:ctyp< option >> -> <:expr< option_map >>
            | <:ctyp< Ploc.vala >> -> <:expr< vala_map >>
            | <:ctyp< $lid:n$ >> ->
                <:expr< $lid:n^"_map"$ $lid:param_f$.mloc >>
            | _ -> <:expr< error >> ]
          in
          Some (<:expr< $f$ $e$ >>, use_self)
      | None -> None ]
  | _ ->
      Some (<:expr< error >>, use_self) ]
;

value expr_of_cons_decl gtn use_self (loc, c, tl, rto) =
  let tl = Pcaml.unvala tl in
  let (p, _) =
    let p = <:patt< $_uid:c$ >> in
    List.fold_left
      (fun (p1, n) t ->
         let (p2, n) =
           match t with
           [ <:ctyp< loc >> -> (<:patt< loc >>, n)
           | _ ->
               let x = "x" ^ string_of_int n in
               (<:patt< $lid:x$ >>, n + 1) ]
         in
         (<:patt< $p1$ $p2$ >>, n))
      (p, 1) tl
  in
  let c = Pcaml.unvala c in
  let e = <:expr< $lid:param_f$.$lid:field_of_constr c$ >> in
  let (e, use_self) =
    match c with
    [ "ExAnt" ->
         let e =
           <:expr<
             let new_mloc loc1 =
               $lid:param_f$.anti_loc ($lid:param_f$.mloc loc) loc loc1
             in
             expr {($lid:param_f$) with mloc = new_mloc} x1 >>
         in
         (e, use_self)
    | "PaAnt" ->
         let e =
           <:expr<
             let new_mloc loc1 =
               $lid:param_f$.anti_loc ($lid:param_f$.mloc loc) loc loc1
             in
             patt {($lid:param_f$) with mloc = new_mloc} x1 >>
         in
         (e, use_self)
    | _ ->
        let (e, _, use_self) =
          List.fold_left
            (fun (e1, n, use_self) t ->
               let x = "x" ^ string_of_int n in
               let e = <:expr< $lid:x$ >> in
               let (e2, n, use_self) =
                 match t with
                 [ <:ctyp< loc >> ->
                     (<:expr< $lid:param_f$.mloc loc >>, n, use_self)
                 | _ ->
                     let (e, use_self) =
                       match expr_of_type gtn use_self loc t with
                       [ Some (f, use_self) -> (<:expr< $f$ $e$ >>, use_self)
                       | None -> (e, use_self) ]
                     in
                     (e, n + 1, use_self) ]
               in
               (<:expr< $e1$ $e2$ >>, n, use_self))
            (e, 1, use_self) tl
        in
        (e, use_self) ]
  in
  ((p, <:vala< None >>, e), use_self)
;

value apply loc f e =
  match f with
  [ <:expr< fun $p1$ -> $e1$ >> -> <:expr< let $p1$ = $e$ in $e1$ >>
  | _ -> <:expr< $f$ $e$ >> ]
;

value expr_of_type_decl loc tn td =
  match td.MLast.tdDef with
  [ <:ctyp< [ $list:cdl$ ] >> ->
      let (pwel, use_self) =
        List.fold_right
          (fun cd (pwel, use_self) ->
             let (pwe, use_self) = expr_of_cons_decl tn use_self cd in
             ([pwe :: pwel], use_self))
          cdl ([], False)
      in
      (<:expr< fun [ $list:pwel$ ] >>, use_self)
  | <:ctyp< { $list:ldl$ } >> ->
      let lel =
        List.map
          (fun (loc, l, mf, t) ->
             let e = <:expr< x.$lid:l$ >> in
             let e =
               match expr_of_type "" False loc t with
               [ Some (f, _) -> apply loc f e
               | None -> e ]
             in
             (<:patt< $lid:l$ >>, e))
          ldl
      in
      (<:expr< fun x -> {$list:lel$} >>, False)
  | _ -> (<:expr< 0 >>, False) ]
;

value type_of_map_field loc t tl = do {
  List.fold_right
    (fun t1 t2 ->
       let t1 =
         tr_vala t1 where rec tr_vala =
           fun
           [ <:ctyp:< Ploc.vala $t$ >> -> <:ctyp< v $tr_vala t$ >>
           | <:ctyp:< $t1$ $t2$ >> -> <:ctyp< $t1$ $tr_vala t2$ >>
           | <:ctyp:< ($list:tl$) >> ->
               <:ctyp< ($list:List.map tr_vala tl$) >>
           | t -> t ]
       in
       <:ctyp< $t1$ → $t2$ >>)
    tl t
};

value ldl_of_td tdl =
  fun
  [ <:type_decl< $_tp:ls$ $_list:ltv$ = $_priv:b$ $t$ $_list:ltt$ >> ->
      match t with
      [ <:ctyp< [$list:cdl$] >> ->
          let tn =
            let ls = Pcaml.unvala ls in
            let s = Pcaml.unvala (snd ls) in
            let loc = fst ls in
            <:ctyp< $lid:s$ >>
          in
          List.fold_left
            (fun tdl (loc, c, tl, rto) ->
               let f = field_of_constr (Pcaml.unvala c) in
               let t = type_of_map_field loc tn (Pcaml.unvala tl) in
               let td = (loc, f, False, t) in
               [td :: tdl])
            tdl cdl
      | _ ->
          tdl ] ]
;

value expr_of_map_field loc c tl = do {
  let (rev_pl, _) =
    List.fold_left
      (fun (rev_pl, n) t ->
         let (p, n) = patt_of_type loc n t in
         ([p :: rev_pl], n))
      ([], 1) tl
  in
  let (rev_el, _) =
    List.fold_left
      (fun (rev_el, n) t ->
         let (e, n) = expr_param_of_type loc n t in
         ([e :: rev_el], n))
      ([], 1) tl
  in
  let e =
    List.fold_right (fun e1 e2 -> <:expr< $e2$ $e1$ >>) rev_el
      <:expr< $uid:c$ >>
  in
  List.fold_left (fun e p -> <:expr< fun $p$ -> $e$ >>) e rev_pl
};

value lel_of_td tdl =
  fun
  [ <:type_decl< $_tp:ls$ $_list:ltv$ = $_priv:b$ $t$ $_list:ltt$ >> ->
      match t with
      [ <:ctyp< [$list:cdl$] >> ->
          List.fold_left
            (fun tdl (loc, c, tl, rto) ->
               let c = Pcaml.unvala c in
               let f = field_of_constr c in
               let e = expr_of_map_field loc c (Pcaml.unvala tl) in
               let td = (<:patt< $lid:f$ >>, e) in
               [td :: tdl])
            tdl cdl
      | _ ->
          tdl ] ]
;

value gen_mapast loc tdl =
  match tdl with
  [ [{MLast.tdNam = <:vala< (_, <:vala< "ctyp" >>) >>} :: _] ->
      let td =
        let rev_ldl = List.fold_left ldl_of_td [] tdl in
        let ld_loc = (loc, "mloc", False, <:ctyp< loc → loc >>) in
        let ld_anti_loc =
          (loc, "anti_loc", False, <:ctyp< loc → loc → loc → loc >>)
        in
        let rev_ldl = [ld_anti_loc; ld_loc :: rev_ldl] in
        let td =
          let ls = (loc, <:vala< "map_f" >>) in
          <:type_decl< $tp:ls$ = {$list:List.rev rev_ldl$} >>
        in
        <:str_item< type $list:[td]$ >>
      in
      let vd =
        let rev_pel = List.fold_left lel_of_td [] tdl in
        let pe_loc = (<:patt< mloc >>, <:expr< fun loc -> loc >>) in
        let pe_anti_loc =
          (<:patt< anti_loc >>, <:expr< fun qloc loc loc1 -> qloc >>)
        in
        let rev_pel = [pe_anti_loc; pe_loc :: rev_pel] in
        let loc = Ploc.with_comment loc "\n" in
        <:str_item< value rec def = {$list:List.rev rev_pel$} >>
      in
      let pel =
        List.map
          (fun td ->
             let tn = Pcaml.unvala (snd (Pcaml.unvala td.MLast.tdNam)) in
             let (e, use_self) = expr_of_type_decl loc tn td in
             let e =
               if use_self then <:expr< self where rec self = $e$ >>
               else e
             in
             let e = <:expr< fun $lid:param_f$ -> $e$ >> in
             (<:patt< $lid:tn$ >>, e))
          tdl
      in
      let vm =
        let loc = Ploc.with_comment loc "\n" in
        <:str_item< value rec $list:pel$ >>
      in
      <:str_item< declare $list:[td; vd; vm]$ end >>
  | _ -> <:str_item< type $list:tdl$ >> ]
;

open Pcaml;

Grammar.warning_verbose.val := False;

EXTEND
  str_item:
    [ [ "type"; tdl = LIST1 type_decl SEP "and" -> gen_mapast loc tdl ] ]
  ;
END;
