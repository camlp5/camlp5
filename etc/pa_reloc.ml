(* camlp5r *)
(* pa_reloc.ml,v *)

(*
   meta/camlp5r etc/pa_reloc.cmo etc/pr_r.cmo -impl main/mLast.mli
*)

#load "pa_extend.cmo";
#load "q_MLast.cmo";

Pcaml.strict_mode.val := True;

value patt_of_type gtn loc n t =
  let x = "x" ^ string_of_int n in
  let p = <:patt< $lid:x$ >> in
  match t with
  [ <:ctyp< loc >> -> (<:patt< loc >>, n)
  | _ -> (p, n + 1) ]
;

value rec expr_of_type gtn use_self loc t =
  match t with
  [ <:ctyp< $lid:tn$ >> ->
      if tn = gtn then Some (<:expr< self >>, True)
      else if List.mem tn ["bool"; "string"; "type_var"] then None
      else if tn = "loc" then Some (<:expr< floc >>, use_self)
      else Some (<:expr< $lid:tn$ floc sh >>, use_self)
  | <:ctyp< ($list:tl$) >> ->
      let (rev_pl, _) =
        List.fold_left
          (fun (rev_pl, n) t ->
             let (p, n) = patt_of_type gtn loc n t in
             ([p :: rev_pl], n))
          ([], 1) tl
      in
      let (rev_el, _, use_self) =
        List.fold_left
          (fun (rev_el, n, use_self) t ->
             let (e, n, use_self) =
               match t with
               [ <:ctyp< loc >> -> (<:expr< floc loc >>, n, use_self)
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
            | <:ctyp< $lid:n$ >> -> <:expr< $lid:n^"_map"$ floc >>
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
  let e = <:expr< $_uid:c$ >> in
  let (e, use_self) =
    match Pcaml.unvala c with
    [ "ExAnt" ->
         let e =
           <:expr<
             let new_floc loc1 = anti_loc (floc loc) sh loc loc1 in
             expr new_floc sh x1 >>
         in
         (e, use_self)
    | "PaAnt" ->
         let e =
           <:expr<
             let new_floc loc1 = anti_loc (floc loc) sh loc loc1 in
             patt new_floc sh x1 >>
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
                 [ <:ctyp< loc >> -> (<:expr< loc >>, n, use_self)
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
        let e = <:expr< let loc = floc loc in $e$ >> in
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
             let (pwe, use_self) =
               expr_of_cons_decl tn use_self cd
             in
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

value gen_reloc loc tdl =
  match tdl with
  [ [{MLast.tdNam = <:vala< (_, <:vala< "ctyp" >>) >>} :: _] ->
      let pel =
        List.map
          (fun td ->
             let tn = Pcaml.unvala (snd (Pcaml.unvala td.MLast.tdNam)) in
             let (e, use_self) = expr_of_type_decl loc tn td in
             let e =
               if use_self then <:expr< self where rec self = $e$ >>
               else e
             in
             let e = <:expr< fun floc sh -> $e$ >> in
             (<:patt< $lid:tn$ >>, e))
          tdl
      in
      <:str_item< value rec $list:pel$ >>
  | _ -> <:str_item< type $list:tdl$ >> ]
;

Grammar.warning_verbose.val := False;

EXTEND
  Pcaml.str_item:
    [ [ "type"; tdl = LIST1 Pcaml.type_decl SEP "and" -> gen_reloc loc tdl ] ]
  ;
END;
