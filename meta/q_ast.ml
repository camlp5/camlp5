(* camlp5r pa_macro.cmo pa_extend.cmo q_MLast.cmo *)
(* $Id: q_ast.ml,v 1.77 2007/09/15 19:35:16 deraugla Exp $ *)
(* Copyright (c) INRIA 2007 *)

(* Experimental AST quotations while running the normal parser and
   its possible extensions and meta-ifying the nodes. Antiquotations
   work only in "strict" mode. *)

value not_impl f x =
  let desc =
    if Obj.is_block (Obj.repr x) then
      "tag = " ^ string_of_int (Obj.tag (Obj.repr x))
    else "int_val = " ^ string_of_int (Obj.magic x)
  in
  failwith ("q_ast.ml: " ^ f ^ ", not impl: " ^ desc)
;

value call_with r v f a =
  let saved = r.val in
  try do {
    r.val := v;
    let b = f a in
    r.val := saved;
    b
  }
  with e -> do { r.val := saved; raise e }
;

value eval_anti entry loc typ str =
  let loc =
    let sh =
      if typ = "" then String.length "$"
      else
        String.length "$" + String.length typ + String.length ":"
    in
    let len = String.length str in
    Ploc.sub loc sh len
  in
  let r =
    try
      call_with Plexer.force_antiquot_loc False
        (Grammar.Entry.parse entry) (Stream.of_string str)
    with
    [ Ploc.Exc loc1 exc ->
        let shift = Ploc.first_pos loc in
        let loc =
          Ploc.make
            (Ploc.line_nb loc + Ploc.line_nb loc1 - 1)
            (if Ploc.line_nb loc1 = 1 then Ploc.bol_pos loc
             else shift + Ploc.bol_pos loc1)
            (shift + Ploc.first_pos loc1,
             shift + Ploc.last_pos loc1)
          in
          raise (Ploc.Exc loc exc) ]
  in
  (loc, r)
;

value get_anti_loc s =
  try
    let i = String.index s ':' in
    let (j, len) =
      loop (i + 1) where rec loop j =
        if j = String.length s then (i, 0)
        else
          match s.[j] with
          [ ':' -> (j, j - i - 1)
          | 'a'..'z' | 'A'..'Z' | '0'..'9' | '_' -> loop (j + 1)
          | _ -> (i, 0) ]
    in
    let kind = String.sub s (i + 1) len in
    let loc =
      let k = String.index s ',' in
      let bp = int_of_string (String.sub s 0 k) in
      let ep = int_of_string (String.sub s (k + 1) (i - k - 1)) in
      Ploc.make_unlined (bp, ep)
    in
    Some (loc, kind, String.sub s (j + 1) (String.length s - j - 1))
  with
  [ Not_found | Failure _ -> None ]
;

module Meta =
  struct
    open MLast;
    value loc = Ploc.dummy;
    value ln () = <:expr< $lid:Ploc.name.val$ >>;
    value e_vala elem =
      IFNDEF STRICT THEN
        fun e -> elem e
      ELSE
        fun
        [ Ploc.VaAnt s ->
            match get_anti_loc s with
            [ Some (loc, typ, str) ->
                let (loc, r) = eval_anti Pcaml.expr_eoi loc typ str in
                if typ <> "" && typ.[0] = 'a' then <:expr< $anti:r$ >>
                else <:expr< Ploc.VaVal $anti:r$ >>
            | None -> assert False ]
        | Ploc.VaVal v -> <:expr< Ploc.VaVal $elem v$ >> ]
      END
    ;
    value p_vala elem =
      IFNDEF STRICT THEN
        fun p -> elem p
      ELSE
        fun
        [ Ploc.VaAnt s ->
            match get_anti_loc s with
            [ Some (loc, typ, str) ->
                let (loc, r) = eval_anti Pcaml.patt_eoi loc typ str in
                if typ <> "" && typ.[0] = 'a' then <:patt< $anti:r$ >>
                else <:patt< Ploc.VaVal $anti:r$ >>
            | None -> assert False ]
        | Ploc.VaVal v -> <:patt< Ploc.VaVal $elem v$ >> ]
      END
    ;
    value e_xtr_or_anti loc f s =
      match get_anti_loc s with
      [ Some (loc, typ, str) ->
          match typ with
          [ "" ->
              let (loc, r) = eval_anti Pcaml.expr_eoi loc "" str in
              <:expr< $anti:r$ >>
          | "anti" ->
              let (loc, r) = eval_anti Pcaml.expr_eoi loc "anti" str in
              f <:expr< $anti:r$ >>
          | _ -> assert False ]
      | _ -> assert False ]
    ;
    value p_xtr_or_anti loc f s =
      match get_anti_loc s with
      [ Some (loc, typ, str) ->
          match typ with
          [ "" ->
              let (loc, r) = eval_anti Pcaml.patt_eoi loc "" str in
              <:patt< $anti:r$ >>
          | "anti" ->
              let (loc, r) = eval_anti Pcaml.patt_eoi loc "anti" str in
              f <:patt< $anti:r$ >>
          | _ -> assert False ]
      | _ -> assert False ]
    ;
    value e_xtr loc s =
      match get_anti_loc s with
      [ Some (loc, typ, str) ->
          match typ with
          [ "" ->
              let (loc, r) = eval_anti Pcaml.expr_eoi loc "" str in
              <:expr< $anti:r$ >>
          | _ -> assert False ]
      | _ -> assert False ]
    ;
    value p_xtr loc s =
      match get_anti_loc s with
      [ Some (loc, typ, str) ->
          match typ with
          [ "" ->
              let (loc, r) = eval_anti Pcaml.patt_eoi loc "" str in
              <:patt< $anti:r$ >>
          | _ -> assert False ]
      | _ -> assert False ]
    ;
    value e_list elem el =
      loop el where rec loop el =
        match el with
        [ [] -> <:expr< [] >>
        | [e :: el] -> <:expr< [$elem e$ :: $loop el$] >> ]
    ;
    value p_list elem el =
      loop el where rec loop el =
        match el with
        [ [] -> <:patt< [] >>
        | [e :: el] -> <:patt< [$elem e$ :: $loop el$] >> ]
    ;
    value e_option elem oe =
      match oe with
      [ None -> <:expr< None >>
      | Some e -> <:expr< Some $elem e$ >> ]
    ;
    value p_option elem oe =
      match oe with
      [ None -> <:patt< None >>
      | Some e -> <:patt< Some $elem e$ >> ]
    ;
    value e_bool b = if b then <:expr< True >> else <:expr< False >>;
    value p_bool b = if b then <:patt< True >> else <:patt< False >>;
    value e_string s = <:expr< $str:s$ >>;
    value p_string s = <:patt< $str:s$ >>;
    value e_node con el =
      List.fold_left (fun e1 e2 -> <:expr< $e1$ $e2$ >>)
        <:expr< MLast.$uid:con$ $ln ()$ >> el
    ;
    value p_node con pl =
      List.fold_left (fun p1 p2 -> <:patt< $p1$ $p2$ >>)
        <:patt< MLast.$uid:con$ _ >> pl
    ;
    value rec e_ctyp = 
      fun
      [ TyAcc _ t1 t2 -> e_node "TyAcc" [e_ctyp t1; e_ctyp t2]
      | TyAli _ t1 t2 -> e_node "TyAli" [e_ctyp t1; e_ctyp t2] 
      | TyArr _ t1 t2 -> e_node "TyArr" [e_ctyp t1; e_ctyp t2]
      | TyAny _ -> e_node "TyAny" []
      | TyApp _ t1 t2 -> e_node "TyApp" [e_ctyp t1; e_ctyp t2]
      | TyCls _ ls -> e_node "TyCls" [e_vala (e_list e_string) ls]
      | TyLab _ i t -> e_node "TyLab" [e_vala e_string i; e_ctyp t]
      | TyLid _ s -> e_node "TyLid" [e_vala e_string s]
      | TyMan _ t1 t2 -> e_node "TyMan" [e_ctyp t1; e_ctyp t2]
      | TyObj _ lm v ->
          e_node "TyObj"
            [e_vala
               (e_list (fun (s, t) -> <:expr< ($e_string s$, $e_ctyp t$) >>))
               lm;
             e_vala e_bool v]
      | TyOlb _ i t -> e_node "TyOlb" [e_vala e_string i; e_ctyp t]
      | TyPol _ lv t -> e_node "TyPol" [e_vala (e_list e_string) lv; e_ctyp t]
      | TyQuo _ s -> e_node "TyQuo" [e_vala e_string s]
      | TyRec _ lld ->
          let lld =
            e_vala
              (e_list
                 (fun (loc, lab, mf, t) ->
                    <:expr< ($ln ()$, $str:lab$, $e_bool mf$, $e_ctyp t$) >>))
              lld
          in
          e_node "TyRec" [lld]
      | TySum _ lcd ->
          let lcd =
            e_vala
              (e_list
                 (fun (loc, lab, lt) ->
                    let lt = e_vala (e_list e_ctyp) lt in
                    <:expr< ($ln ()$, $e_vala e_string lab$, $lt$) >>))
              lcd
          in
          e_node "TySum" [lcd]
      | TyTup _ tl -> e_node "TyTup" [e_vala (e_list e_ctyp) tl]
      | TyUid _ s -> e_node "TyUid" [e_vala e_string s]
      | TyVrn _ lpv ools ->
          e_node "TyVrn"
            [e_vala (e_list e_poly_variant) lpv;
             e_option (e_option (e_vala (e_list e_string))) ools]
      | IFDEF STRICT THEN
          TyXtr loc s _ -> e_xtr loc s
        END ]
    and p_ctyp =
      fun
      [ TyAcc _ t1 t2 -> p_node "TyAcc" [p_ctyp t1; p_ctyp t2]
      | TyAli _ t1 t2 -> p_node "TyAli" [p_ctyp t1; p_ctyp t2] 
      | TyArr _ t1 t2 -> p_node "TyArr" [p_ctyp t1; p_ctyp t2]
      | TyAny _ -> p_node "TyAny" []
      | TyApp _ t1 t2 -> p_node "TyApp" [p_ctyp t1; p_ctyp t2]
      | TyCls _ ls -> p_node "TyCls" [p_vala (p_list p_string) ls]
      | TyLab _ i t -> p_node "TyLab" [p_vala p_string i; p_ctyp t]
      | TyLid _ s -> p_node "TyLid" [p_vala p_string s]
      | TyMan _ t1 t2 -> p_node "TyMan" [p_ctyp t1; p_ctyp t2]
      | TyObj _ lm v ->
          p_node "TyObj"
            [p_vala
               (p_list (fun (s, t) -> <:patt< ($p_string s$, $p_ctyp t$) >>))
               lm;
             p_vala p_bool v]
      | TyOlb _ i t -> p_node "TyOlb" [p_vala p_string i; p_ctyp t]
      | TyPol _ lv t -> p_node "TyPol" [p_vala (p_list p_string) lv; p_ctyp t]
      | TyQuo _ s -> p_node "TyQuo" [p_vala p_string s]
      | TyRec _ lld ->
          let lld =
            p_vala
              (p_list
                 (fun (loc, lab, mf, t) ->
                    <:patt< (_, $str:lab$, $p_bool mf$, $p_ctyp t$) >>))
              lld
          in
          p_node "TyRec" [lld]
      | TySum _ lcd ->
          let lcd =
            p_vala
              (p_list
                 (fun (loc, lab, lt) ->
                    let lt = p_vala (p_list p_ctyp) lt in
                    <:patt< (_, $p_vala p_string lab$, $lt$) >>))
              lcd
          in
          p_node "TySum" [lcd]
      | TyTup _ tl -> p_node "TyTup" [p_vala (p_list p_ctyp) tl]
      | TyUid _ s -> p_node "TyUid" [p_vala p_string s]
      | TyVrn _ lpv ools ->
          p_node "TyVrn"
            [p_vala (p_list p_poly_variant) lpv;
             p_option (p_option (p_vala (p_list p_string))) ools]
      | IFDEF STRICT THEN
          TyXtr loc s _ -> p_xtr loc s
        END ]
    and e_poly_variant =
      fun
      [ PvTag s a lt ->
          let s = e_vala e_string s in
          let a = e_vala e_bool a in
          let lt = e_vala (e_list e_ctyp) lt in
          <:expr< MLast.PvTag $s$ $a$ $lt$ >>
      | PvInh t ->
          <:expr< MLast.PvInh $e_ctyp t$ >> ]
    and p_poly_variant =
      fun
      [ x -> not_impl "p_poly_variant" x ]
    ;
    value e_class_infos a =
      fun
      [ x -> not_impl "e_class_infos" x ]
    ;
    value e_type_var =
      fun
      [ x -> not_impl "e_type_var" x ]
    ;
    value rec e_patt =
      fun
      [ PaAcc _ p1 p2 -> e_node "PaAcc" [e_patt p1; e_patt p2]
      | PaAli _ p1 p2 -> e_node "PaAli" [e_patt p1; e_patt p2]
      | PaAny _ -> e_node "PaAny" []
      | PaApp _ p1 p2 -> e_node "PaApp" [e_patt p1; e_patt p2]
      | PaArr _ pl -> e_node "PaArr" [e_vala (e_list e_patt) pl]
      | PaChr _ s -> e_node "PaChr" [e_vala e_string s]
      | PaInt _ s k -> e_node "PaInt" [e_vala e_string s; e_string k]
      | PaFlo _ s -> e_node "PaFlo" [e_vala e_string s]
      | PaLab _ s p -> e_node "PaLab" [e_vala e_string s; e_option e_patt p]
      | PaLid _ s -> e_node "PaLid" [e_vala e_string s]
      | PaOlb _ s opeo ->
          e_node "PaOlb"
            [e_vala e_string s;
             e_option
               (fun (p, oe) ->
                  <:expr< ($e_patt p$, $e_vala (e_option e_expr) oe$) >>)
               opeo]
      | PaOrp _ p1 p2 -> e_node "PaOrp" [e_patt p1; e_patt p2]
      | PaRec _ lpe ->
          let lpe =
            e_vala
              (e_list (fun (p, e) -> <:expr< ($e_patt p$, $e_patt e$) >>)) lpe
          in
          e_node "PaRec" [lpe]
      | PaRng _ p1 p2 -> e_node "PaRng" [e_patt p1; e_patt p2]
      | PaStr _ s -> e_node "PaStr" [e_vala e_string s]
      | PaTup _ pl -> e_node "PaTup" [e_vala (e_list e_patt) pl]
      | PaTyc _ p t -> e_node "PaTyc" [e_patt p; e_ctyp t]
      | PaTyp _ ls -> e_node "PaTyp" [e_vala (e_list e_string) ls]
      | PaUid _ s -> e_node "PaUid" [e_vala e_string s]
      | PaVrn _ s -> e_node "PaVrn" [e_vala e_string s]
      | IFDEF STRICT THEN
          PaXtr loc s _ -> e_xtr_or_anti loc (fun r -> e_node "PaAnt" [r]) s
        END
      | x -> not_impl "e_patt" x ]
    and p_patt =
      fun
      [ PaAcc _ p1 p2 -> p_node "PaAcc" [p_patt p1; p_patt p2]
      | PaAli _ p1 p2 -> p_node "PaAli" [p_patt p1; p_patt p2]
      | PaChr _ s -> p_node "PaChr" [p_vala p_string s]
      | PaLid _ s -> p_node "PaLid" [p_vala p_string s]
      | PaTup _ pl -> p_node "PaTup" [p_vala (p_list p_patt) pl]
      | IFDEF STRICT THEN
          PaXtr loc s _ -> p_xtr_or_anti loc (fun r -> p_node "PaAnt" [r]) s
        END
      | x -> not_impl "p_patt" x ]
    and e_expr =
      fun
      [ ExAcc _ e1 e2 -> e_node "ExAcc" [e_expr e1; e_expr e2]
      | ExAnt _ _ as e -> e
      | ExApp _ e1 e2 -> e_node "ExApp" [e_expr e1; e_expr e2]
      | ExAre _ e1 e2 -> e_node "ExAre" [e_expr e1; e_expr e2]
      | ExArr _ el -> e_node "ExArr" [e_vala (e_list e_expr) el]
      | ExAss _ e1 e2 -> e_node "ExAss" [e_expr e1; e_expr e2]
      | ExAsr _ e -> e_node "ExAsr" [e_expr e]
      | ExBae _ e el -> e_node "ExBae" [e_expr e; e_vala (e_list e_expr) el]
      | ExChr _ s -> e_node "ExChr" [e_vala e_string s]
      | ExCoe _ e ot t ->
          e_node "ExCoe" [e_expr e; e_option e_ctyp ot; e_ctyp t]
      | ExIfe _ e1 e2 e3 -> e_node "ExIfe" [e_expr e1; e_expr e2; e_expr e3]
      | ExInt _ s k -> e_node "ExInt" [e_vala e_string s; e_string k]
      | ExFlo _ s -> e_node "ExFlo" [e_vala e_string s]
      | ExFor _ i e1 e2 df el ->
          let i = e_vala e_string i in
          let df = e_vala e_bool df in
          let el = e_vala (e_list e_expr) el in
          e_node "ExFor" [i; e_expr e1; e_expr e2; df; el]
      | ExFun _ pwel ->
          let pwel =
            e_vala
              (e_list
                (fun (p, oe, e) ->
                   <:expr< ($e_patt p$, $e_option e_expr oe$, $e_expr e$) >>))
              pwel
          in
          e_node "ExFun" [pwel]
      | ExLab _ s oe -> e_node "ExLab" [e_vala e_string s; e_option e_expr oe]
      | ExLaz _ e -> e_node "ExLaz" [e_expr e]
      | ExLet _ rf lpe e ->
          let rf = e_vala e_bool rf in
          let lpe =
            e_vala
              (e_list (fun (p, e) -> <:expr< ($e_patt p$, $e_expr e$) >>)) lpe
          in
          e_node "ExLet" [rf; lpe; e_expr e]
      | ExLid _ s -> e_node "ExLid" [e_vala e_string s]
      | ExLmd _ i me e ->
          let i = e_vala e_string i in
          let me = e_module_expr me in
          e_node "ExLmd" [i; me; e_expr e]
      | ExMat _ e pwel ->
          let pwel =
            e_vala
              (e_list
                 (fun (p, oe, e) ->
                    let oe = e_option e_expr oe in
                    <:expr< ($e_patt p$, $oe$, $e_expr e$) >>))
              pwel
          in
          e_node "ExMat" [e_expr e; pwel]
      | ExNew _ ls -> e_node "ExNew" [e_vala (e_list e_string) ls]
      | ExObj _ op lcsi ->
          e_node "ExObj"
            [e_vala (e_option e_patt) op;
             e_vala (e_list e_class_str_item) lcsi]
      | ExOlb _ s oe ->
          e_node "ExOlb" [e_vala e_string s; e_option e_expr oe]
      | ExOvr _ lse ->
          e_node "ExOvr"
            [e_vala
               (e_list (fun (s, e) -> <:expr< ($e_string s$, $e_expr e$) >>))
               lse]
      | ExRec _ lpe oe ->
          let lpe =
            e_vala
              (e_list (fun (p, e) -> <:expr< ($e_patt p$, $e_expr e$) >>)) lpe
          in
          let oe = e_option e_expr oe in
          e_node "ExRec" [lpe; oe]
      | ExSeq _ el -> e_node "ExSeq" [e_vala (e_list e_expr) el]
      | ExSnd _ e s -> e_node "ExSnd" [e_expr e; e_vala e_string s]
      | ExSte _ e1 e2 -> e_node "ExSte" [e_expr e1; e_expr e2]
      | ExStr _ s -> e_node "ExStr" [e_vala e_string s]
      | ExTry _ e pwel ->
          let pwel =
            e_vala
              (e_list
                 (fun (p, oe, e) ->
                    <:expr< ($e_patt p$, $e_option e_expr oe$, $e_expr e$) >>))
              pwel
          in
          e_node "ExTry" [e_expr e; pwel]
      | ExTup _ el -> e_node "ExTup" [e_vala (e_list e_expr) el]
      | ExTyc _ e t -> e_node "ExTyc" [e_expr e; e_ctyp t]
      | ExUid _ s -> e_node "ExUid" [e_vala e_string s]
      | ExVrn _ s -> e_node "ExVrn" [e_vala e_string s]
      | ExWhi _ e el -> e_node "ExWhi" [e_expr e; e_vala (e_list e_expr) el]
      | IFDEF STRICT THEN
          ExXtr loc s _ -> e_xtr_or_anti loc (fun r -> e_node "ExAnt" [r]) s
        END ]
    and p_expr =
      fun
      [ ExAcc _ e1 e2 -> p_node "ExAcc" [p_expr e1; p_expr e2]
      | ExApp _ e1 e2 -> p_node "ExApp" [p_expr e1; p_expr e2]
      | ExIfe _ e1 e2 e3 -> p_node "ExIfe" [p_expr e1; p_expr e2; p_expr e3]
      | ExInt _ s k -> p_node "ExInt" [p_vala p_string s; p_string k]
      | ExFlo _ s -> p_node "ExFlo" [p_vala p_string s]
      | ExLet _ rf lpe e ->
          let rf = p_vala p_bool rf in
          let lpe =
            p_vala
              (p_list (fun (p, e) -> <:patt< ($p_patt p$, $p_expr e$) >>)) lpe
          in
          p_node "ExLet" [rf; lpe; p_expr e]
      | ExRec _ lpe oe ->
          let lpe =
            p_vala
              (p_list (fun (p, e) -> <:patt< ($p_patt p$, $p_expr e$) >>)) lpe
          in
          let oe = p_option p_expr oe in
          p_node "ExRec" [lpe; oe]
      | ExLid _ s -> p_node "ExLid" [p_vala p_string s]
      | ExStr _ s -> p_node "ExStr" [p_vala p_string s]
      | ExTup _ el -> p_node "ExTup" [p_vala (p_list p_expr) el]
      | ExUid _ s -> p_node "ExUid" [p_vala p_string s]
      | IFDEF STRICT THEN
          ExXtr loc s _ -> p_xtr_or_anti loc (fun r -> p_node "ExAnt" [r]) s
        END
      | x -> not_impl "p_expr" x ]
    and e_module_type =
      fun
      [ MtAcc _ mt1 mt2 ->
          e_node "MtAcc" [e_module_type mt1; e_module_type mt2]
      | MtApp _ mt1 mt2 ->
          e_node "MtApp" [e_module_type mt1; e_module_type mt2]
      | MtFun _ s mt1 mt2 ->
          e_node "MtFun"
            [e_vala e_string s; e_module_type mt1; e_module_type mt2]
      | MtLid _ s -> e_node "MtLid" [e_vala e_string s]
      | MtQuo _ s -> e_node "MtQuo" [e_vala e_string s]
      | MtSig _ sil -> e_node "MtSig" [e_vala (e_list e_sig_item) sil]
      | MtUid _ s -> e_node "MtUid" [e_vala e_string s]
      | MtWit _ mt lwc ->
          e_node "MtWit" [e_module_type mt; e_vala (e_list e_with_constr) lwc]
      | IFDEF STRICT THEN
          MtXtr loc s _ -> e_xtr loc s
        END ]
    and p_module_type =
      fun
      [ x -> not_impl "p_module_type" x ]
    and e_sig_item =
      fun
      [ SgCls _ cd ->
          e_node "SgCls" [e_vala (e_list (e_class_infos e_class_type)) cd]
      | SgClt _ ctd ->
          e_node "SgClt" [e_vala (e_list (e_class_infos e_class_type)) ctd]
      | SgDcl _ lsi ->
          e_node "SgDcl" [e_vala (e_list e_sig_item) lsi]
      | SgDir _ n dp ->
          e_node "SgDir" [e_vala e_string n; e_vala (e_option e_expr) dp]
      | SgExc _ s lt ->
          let s = e_vala e_string s in
          let lt = e_vala (e_list e_ctyp) lt in
          e_node "SgExc" [s; lt]
      | SgExt _ s t ls ->
          let ls = e_vala (e_list e_string) ls in
          e_node "SgExt" [e_vala e_string s; e_ctyp t; ls]
      | SgInc _ mt -> e_node "SgInc" [e_module_type mt]
      | SgMod _ rf lsmt ->
          let lsmt =
            e_vala
              (e_list
                 (fun (s, mt) ->
                    <:expr< ($e_string s$, $e_module_type mt$) >>))
              lsmt
          in
          e_node "SgMod" [e_vala e_bool rf; lsmt]
      | SgMty _ s mt -> e_node "SgMty" [e_vala e_string s; e_module_type mt]
      | SgOpn _ sl -> e_node "SgOpn" [e_vala (e_list e_string) sl]
      | SgTyp _ ltd -> e_node "SgTyp" [e_vala (e_list e_type_decl) ltd]
      | SgVal _ s t -> e_node "SgVal" [e_vala e_string s; e_ctyp t]
      | x -> not_impl "e_sig_item" x ]
    and p_sig_item =
      fun
      [ (* SgVal _ s t -> p_node "SgVal" [p_string s; p_ctyp t]
      | *) x -> not_impl "p_sig_item" x ]
    and e_with_constr =
      fun
      [ WcTyp _ li ltp pf t ->
          let li = e_vala (e_list e_string) li in
          let ltp = e_vala (e_list e_type_var) ltp in
          let pf = e_vala e_bool pf in
          let t = e_ctyp t in
          e_node "WcTyp" [li; ltp; pf; t]
      | WcMod _ li me ->
          let li = e_vala (e_list e_string) li in
          let me = e_module_expr me in
          e_node "WcMod" [li; me] ]
    and p_with_constr =
      fun
      [ x -> not_impl "p_with_constr" x ]
    and e_module_expr =
      fun
      [ MeAcc _ me1 me2 ->
          e_node "MeAcc" [e_module_expr me1; e_module_expr me2]
      | MeApp _ me1 me2 ->
          e_node "MeApp" [e_module_expr me1; e_module_expr me2]
      | MeFun _ s mt me ->
          e_node "MeFun"
            [e_vala e_string s; e_module_type mt; e_module_expr me]
      | MeStr _ lsi -> e_node "MeStr" [e_vala (e_list e_str_item) lsi]
      | MeTyc _ me mt -> e_node "MeTyc" [e_module_expr me; e_module_type mt]
      | MeUid _ s -> e_node "MeUid" [e_vala e_string s]
      | IFDEF STRICT THEN
          MeXtr loc s _ -> e_xtr loc s
        END ]
    and p_module_expr =
      fun
      [ x -> not_impl "p_module_expr" x ]
    and e_str_item =
      fun
      [ StCls _ cd ->
          e_node "StCls" [e_vala (e_list (e_class_infos e_class_expr)) cd]
      | StClt _ ctd ->
          e_node "StClt" [e_vala (e_list (e_class_infos e_class_type)) ctd]
      | StDcl _ lsi ->
          e_node "StDcl" [e_vala (e_list e_str_item) lsi]
      | StDir _ n dp ->
          e_node "StDir" [e_vala e_string n; e_vala (e_option e_expr) dp]
      | StExc _ s lt ls ->
          let s = e_vala e_string s in
          let lt = e_vala (e_list e_ctyp) lt in
          let ls = e_vala (e_list e_string) ls in
          e_node "StExc" [s; lt; ls]
      | StExp _ e -> e_node "StExp" [e_expr e]
      | StExt _ s t ls ->
          let ls = e_vala (e_list e_string) ls in
          e_node "StExt" [e_vala e_string s; e_ctyp t; ls]
      | StInc _ me -> e_node "StInc" [e_module_expr me]
      | StMod _ rf lsme ->
          let lsme =
            e_vala
              (e_list
                 (fun (s, me) ->
                    <:expr< ($e_string s$, $e_module_expr me$) >>))
              lsme
          in
          e_node "StMod" [e_vala e_bool rf; lsme]
      | StMty _ s mt -> e_node "StMty" [e_vala e_string s; e_module_type mt]
      | StOpn _ sl -> e_node "StOpn" [e_vala (e_list e_string) sl]
      | StTyp _ ltd -> e_node "StTyp" [e_vala (e_list e_type_decl) ltd]
      | StVal _ rf lpe ->
          let lpe =
            e_vala
              (e_list (fun (p, e) -> <:expr< ($e_patt p$, $e_expr e$) >>))
              lpe
          in
          e_node "StVal" [e_vala e_bool rf; lpe]
      | x -> not_impl "e_str_item" x ]
    and p_str_item =
      fun
      [ x -> not_impl "p_str_item" x ]
    and e_type_decl =
      fun
      [ x -> not_impl "e_type_decl" x ]
    and e_class_type =
      fun
      [ CtCon _ ls lt ->
          e_node "CtCon"
            [e_vala (e_list e_string) ls; e_vala (e_list e_ctyp) lt]
      | CtFun _ t ct -> e_node "CtFun" [e_ctyp t; e_class_type ct]
      | CtSig _ ot lcsi ->
          e_node "CtSig"
            [e_vala (e_option e_ctyp) ot;
             e_vala (e_list e_class_sig_item) lcsi]
      | IFDEF STRICT THEN
          CtXtr loc s _ -> e_xtr loc s
        END ]
    and p_class_type =
      fun
      [ x -> not_impl "p_class_type" x ]
    and e_class_sig_item =
      fun
      [ CgCtr _ t1 t2 -> e_node "CgCtr" [e_ctyp t1; e_ctyp t2]
      | CgDcl _ lcsi -> e_node "CgDcl" [e_vala (e_list e_class_sig_item) lcsi]
      | CgInh _ ct -> e_node "CgInh" [e_class_type ct]
      | CgMth _ s mf t ->
          e_node "CgMth" [e_vala e_string s; e_vala e_bool mf; e_ctyp t]
      | CgVal _ s mf t ->
          e_node "CgVal" [e_vala e_string s; e_vala e_bool mf; e_ctyp t]
      | CgVir _ s mf t ->
          e_node "CgVir" [e_vala e_string s; e_vala e_bool mf; e_ctyp t] ]
    and p_class_sig_item =
      fun
      [ x -> not_impl "p_class_sig_item" x ]
    and e_class_expr =
      fun
      [ CeApp _ ce e -> e_node "CeApp" [e_class_expr ce; e_expr e]
      | CeCon _ c l ->
          let c = e_vala (e_list e_string) c in
          e_node "CeCon" [c; e_vala (e_list e_ctyp) l]
      | CeFun _ p ce -> e_node "CeFun" [e_patt p; e_class_expr ce]
      | CeLet _ rf lb ce ->
          e_node "CeLet"
            [e_vala e_bool rf;
             e_vala
               (e_list (fun (p, e) -> <:expr< ($e_patt p$, $e_expr e$) >>))
               lb;
             e_class_expr ce]
      | CeStr _ ocsp lcsi ->
          let ocsp = e_vala (e_option e_patt) ocsp in
          let lcsi = e_vala (e_list e_class_str_item) lcsi in
          e_node "CeStr" [ocsp; lcsi]
      | CeTyc _ ce ct -> e_node "CeTyc" [e_class_expr ce; e_class_type ct]
      | IFDEF STRICT THEN
          CeXtr loc s _ -> e_xtr loc s
        END ]
    and p_class_expr =
      fun
      [ x -> not_impl "p_class_expr" x ]
    and e_class_str_item =
      fun
      [ CrCtr _ t1 t2 -> e_node "CrCtr" [e_ctyp t1; e_ctyp t2]
      | CrDcl _ lcsi -> e_node "CrDcl" [e_vala (e_list e_class_str_item) lcsi]
      | CrInh _ ce os ->
          e_node "CrInh" [e_class_expr ce; e_vala (e_option e_string) os]
      | CrIni _ e -> e_node "CrIni" [e_expr e]
      | CrMth _ s pf e ot ->
          e_node "CrMth"
            [e_vala e_string s; e_vala e_bool pf; e_expr e;
             e_vala (e_option e_ctyp) ot]
      | CrVal _ s rf e ->
          e_node "CrVal" [e_vala e_string s; e_vala e_bool rf; e_expr e]
      | CrVir _ s pf t ->
          e_node "CrVir" [e_vala e_string s; e_vala e_bool pf; e_ctyp t] ]
    and p_class_str_item =
      fun
      [ x -> not_impl "p_class_str_item" x ]
    ;
  end
;

value expr_eoi = Grammar.Entry.create Pcaml.gram "expr";
value patt_eoi = Grammar.Entry.create Pcaml.gram "patt";
value ctyp_eoi = Grammar.Entry.create Pcaml.gram "type";
value str_item_eoi = Grammar.Entry.create Pcaml.gram "str_item";
value sig_item_eoi = Grammar.Entry.create Pcaml.gram "sig_item";
value module_expr_eoi = Grammar.Entry.create Pcaml.gram "module_expr";
value module_type_eoi = Grammar.Entry.create Pcaml.gram "module_type";
value with_constr_eoi = Grammar.Entry.create Pcaml.gram "with_constr";
value poly_variant_eoi = Grammar.Entry.create Pcaml.gram "poly_variant";
value class_expr_eoi = Grammar.Entry.create Pcaml.gram "class_expr";
value class_type_eoi = Grammar.Entry.create Pcaml.gram "class_type";
value class_str_item_eoi = Grammar.Entry.create Pcaml.gram "class_str_item";
value class_sig_item_eoi = Grammar.Entry.create Pcaml.gram "class_sig_item";

EXTEND
  expr_eoi: [ [ x = Pcaml.expr; EOI -> x ] ];
  patt_eoi: [ [ x = Pcaml.patt; EOI -> x ] ];
  ctyp_eoi: [ [ x = Pcaml.ctyp; EOI -> x ] ];
  sig_item_eoi: [ [ x = Pcaml.sig_item; EOI -> x ] ];
  str_item_eoi: [ [ x = Pcaml.str_item; EOI -> x ] ];
  module_expr_eoi: [ [ x = Pcaml.module_expr; EOI -> x ] ];
  module_type_eoi: [ [ x = Pcaml.module_type; EOI -> x ] ];
  with_constr_eoi: [ [ x = Pcaml.with_constr; EOI -> x ] ];
  poly_variant_eoi: [ [ x = Pcaml.poly_variant; EOI -> x ] ];
  class_expr_eoi: [ [ x = Pcaml.class_expr; EOI -> x ] ];
  class_type_eoi: [ [ x = Pcaml.class_type; EOI -> x ] ];
  class_str_item_eoi: [ [ x = Pcaml.class_str_item; EOI -> x ] ];
  class_sig_item_eoi: [ [ x = Pcaml.class_sig_item; EOI -> x ] ];
END;

IFDEF STRICT THEN
  let ipatt = Grammar.Entry.find Pcaml.expr "ipatt" in
  EXTEND
    Pcaml.expr: LAST
      [ [ s = ANTIQUOT_LOC "" -> MLast.ExXtr loc s None
        | s = ANTIQUOT_LOC "anti" -> MLast.ExXtr loc s None ] ]
    ;
    Pcaml.patt: LAST
      [ [ s = ANTIQUOT_LOC "" -> MLast.PaXtr loc s None
        | s = ANTIQUOT_LOC "anti" -> MLast.PaXtr loc s None ] ]
    ;
    ipatt: LAST
      [ [ s = ANTIQUOT_LOC "" -> Obj.repr (MLast.PaXtr loc s None) ] ]
    ;
    Pcaml.ctyp: LAST
      [ [ s = ANTIQUOT_LOC -> MLast.TyXtr loc s None ] ]
    ;
    Pcaml.str_item: LAST
      [ [ s = ANTIQUOT_LOC "exp" ->
            let e =
              match get_anti_loc s with
              [ Some (loc, _, str) ->
                  let (loc, r) = eval_anti Pcaml.expr_eoi loc "exp" str in
                  <:expr< $anti:r$ >>
              | None -> assert False ]
            in
            MLast.StExp loc e ] ]
    ;
    Pcaml.module_expr: LAST
      [ [ s = ANTIQUOT_LOC -> MLast.MeXtr loc s None ] ]
    ;
    Pcaml.module_type: LAST
      [ [ s = ANTIQUOT_LOC -> MLast.MtXtr loc s None ] ]
    ;
    Pcaml.class_expr: LAST
      [ [ s = ANTIQUOT_LOC -> MLast.CeXtr loc s None ] ]
    ;
    Pcaml.class_type: LAST
      [ [ s = ANTIQUOT_LOC -> MLast.CtXtr loc s None ] ]
    ;
  END
END;

value check_anti_loc s kind =
  try
    let i = String.index s ':' in
    let (j, len) =
      loop (i + 1) where rec loop j =
        if j = String.length s then (i, 0)
        else
          match s.[j] with
          [ ':' -> (j, j - i - 1)
          | 'a'..'z' | 'A'..'Z' | '0'..'9' | '_' -> loop (j + 1)
          | _ -> (i, 0) ]
    in
    if String.sub s (i + 1) len = kind then
      let loc =
        let k = String.index s ',' in
        let bp = int_of_string (String.sub s 0 k) in
        let ep = int_of_string (String.sub s (k + 1) (i - k - 1)) in
        Ploc.make_unlined (bp, ep)
      in
      (loc, String.sub s (j + 1) (String.length s - j - 1))
    else raise Stream.Failure
  with
  [ Not_found | Failure _ -> raise Stream.Failure ]
;

value check_anti_loc2 s =
  try
    let i = String.index s ':' in
    let (j, len) =
      loop (i + 1) where rec loop j =
        if j = String.length s then (i, 0)
        else
          match s.[j] with
          [ ':' -> (j, j - i - 1)
          | 'a'..'z' | 'A'..'Z' | '0'..'9' | '_' -> loop (j + 1)
          | _ -> (i, 0) ]
    in
    String.sub s (i + 1) len
  with
  [ Not_found | Failure _ -> raise Stream.Failure ]
;

let lex = Grammar.glexer Pcaml.gram in
let tok_match = lex.Plexing.tok_match in
lex.Plexing.tok_match :=
  fun
  [("ANTIQUOT_LOC", p_prm) ->
      fun
      [ ("ANTIQUOT_LOC", prm) ->
          let kind = check_anti_loc2 prm in
          if kind = p_prm then prm
          else raise Stream.Failure
      | _ -> raise Stream.Failure ]
  | ("V INT", "") ->
      fun
      [ ("ANTIQUOT_LOC", prm) ->
          let kind = check_anti_loc2 prm in
          if kind = "aint" || kind = "int" then prm
          else raise Stream.Failure
      | _ -> raise Stream.Failure ]
  | ("V INT_l", "") ->
      fun
      [ ("ANTIQUOT_LOC", prm) ->
          let kind = check_anti_loc2 prm in
          if kind = "aint32" || kind = "int32" then prm
          else raise Stream.Failure
      | _ -> raise Stream.Failure ]
  | ("V INT_L", "") ->
      fun
      [ ("ANTIQUOT_LOC", prm) ->
          let kind = check_anti_loc2 prm in
          if kind = "aint64" || kind = "int64" then prm
          else raise Stream.Failure
      | _ -> raise Stream.Failure ]
  | ("V INT_n", "") ->
      fun
      [ ("ANTIQUOT_LOC", prm) ->
          let kind = check_anti_loc2 prm in
          if kind = "anativeint" || kind = "nativeint" then prm
          else raise Stream.Failure
      | _ -> raise Stream.Failure ]
  | ("V FLOAT", "") ->
      fun
      [ ("ANTIQUOT_LOC", prm) ->
          let kind = check_anti_loc2 prm in
          if kind = "aflo" || kind = "flo" then prm
          else raise Stream.Failure
      | _ -> raise Stream.Failure ]
  | ("V LIDENT", "") ->
      fun
      [ ("ANTIQUOT_LOC", prm) ->
          let kind = check_anti_loc2 prm in
          if kind = "alid" || kind = "lid" then prm
          else raise Stream.Failure
      | _ -> raise Stream.Failure ]
  | ("V UIDENT", "") ->
      fun
      [ ("ANTIQUOT_LOC", prm) ->
          let kind = check_anti_loc2 prm in
          if kind = "auid" || kind = "uid" then prm
          else raise Stream.Failure
      | _ -> raise Stream.Failure ]
  | ("V STRING", "") ->
      fun
      [ ("ANTIQUOT_LOC", prm) ->
          let kind = check_anti_loc2 prm in
          if kind = "astr" || kind = "str" then prm
          else raise Stream.Failure
      | _ -> raise Stream.Failure ]
  | ("V CHAR", "") ->
      fun
      [ ("ANTIQUOT_LOC", prm) ->
          let kind = check_anti_loc2 prm in
          if kind = "achr" || kind = "chr" then prm
          else raise Stream.Failure
      | _ -> raise Stream.Failure ]
  | ("V LIST", "") ->
      fun
      [ ("ANTIQUOT_LOC", prm) ->
          let kind = check_anti_loc2 prm in
          if kind = "alist" || kind = "list" then prm
          else raise Stream.Failure
      | _ -> raise Stream.Failure ]
  | ("V OPT", "") ->
      fun
      [ ("ANTIQUOT_LOC", prm) ->
          let kind = check_anti_loc2 prm in
          if kind = "aopt" || kind = "opt" then prm
          else raise Stream.Failure
      | _ -> raise Stream.Failure ]
  | ("V FLAG", "") ->
      fun
      [ ("ANTIQUOT_LOC", prm) ->
          let kind = check_anti_loc2 prm in
          if kind = "aflag" || kind = "flag" then prm
          else raise Stream.Failure
      | _ -> raise Stream.Failure ]
  | tok -> tok_match tok ]
;

(* reinit the entry functions to take the new tok_match into account *)
Grammar.iter_entry Grammar.reinit_entry_functions
  (Grammar.Entry.obj Pcaml.expr);

value apply_entry e me mp =
  let f s =
    call_with Plexer.force_antiquot_loc True
      (Grammar.Entry.parse e) (Stream.of_string s)
  in
  let expr s = me (f s) in
  let patt s = mp (f s) in
  Quotation.ExAst (expr, patt)
;

List.iter
  (fun (q, f) -> Quotation.add q f)
  [("expr", apply_entry expr_eoi Meta.e_expr Meta.p_expr);
   ("patt", apply_entry patt_eoi Meta.e_patt Meta.p_patt);
   ("ctyp", apply_entry ctyp_eoi Meta.e_ctyp Meta.p_ctyp);
   ("str_item", apply_entry str_item_eoi Meta.e_str_item Meta.p_str_item);
   ("sig_item", apply_entry sig_item_eoi Meta.e_sig_item Meta.p_sig_item);
   ("module_expr",
    apply_entry module_expr_eoi Meta.e_module_expr Meta.p_module_expr);
   ("module_type",
    apply_entry module_type_eoi Meta.e_module_type Meta.p_module_type);
   ("with_constr",
    apply_entry with_constr_eoi Meta.e_with_constr Meta.p_with_constr);
   ("poly_variant",
    apply_entry poly_variant_eoi Meta.e_poly_variant Meta.p_poly_variant);
   ("class_expr",
    apply_entry class_expr_eoi Meta.e_class_expr Meta.p_class_expr);
   ("class_type",
    apply_entry class_type_eoi Meta.e_class_type Meta.p_class_type);
   ("class_str_item",
    apply_entry class_str_item_eoi Meta.e_class_str_item
      Meta.p_class_str_item);
   ("class_sig_item",
    apply_entry class_sig_item_eoi Meta.e_class_sig_item
      Meta.p_class_sig_item)]
;

do {
  let expr_eoi = Grammar.Entry.create Pcaml.gram "expr_eoi" in
  EXTEND
    expr_eoi:
      [ [ a = ANTIQUOT_LOC; EOI ->
            let loc = Ploc.make_unlined (0, 0) in
            if Pcaml.strict_mode.val then
              let a =
                let i = String.index a ':' in
                let i = String.index_from a (i + 1) ':' in
                let a = String.sub a (i + 1) (String.length a - i - 1) in
                Grammar.Entry.parse Pcaml.expr_eoi (Stream.of_string a)
              in
              <:expr< Ploc.VaAnt $anti:a$ >>
            else <:expr< failwith "antiquot" >>
        | e = Pcaml.expr; EOI ->
            let loc = Ploc.make_unlined (0, 0) in
            if Pcaml.strict_mode.val then <:expr< Ploc.VaVal $anti:e$ >>
            else <:expr< $anti:e$ >> ] ]
    ;
  END;
  let expr s =
    call_with Plexer.force_antiquot_loc True
      (Grammar.Entry.parse expr_eoi) (Stream.of_string s)
  in
  let patt s =
    let p =
      call_with Plexer.force_antiquot_loc True
        (Grammar.Entry.parse Pcaml.patt_eoi) (Stream.of_string s)
    in
    let loc = Ploc.make_unlined (0, 0) in
    if Pcaml.strict_mode.val then <:patt< Ploc.VaVal $anti:p$ >>
    else <:patt< $anti:p$ >>
  in
  Quotation.add "vala" (Quotation.ExAst (expr, patt));
};
