(* camlp5r pa_macro.cmo pa_extend.cmo q_MLast.cmo *)
(* $Id: q_ast.ml,v 1.83 2007/09/17 23:32:31 deraugla Exp $ *)
(* Copyright (c) INRIA 2007 *)

(* AST quotations with works by running the language parser (and its possible
   extensions) and meta-ifying the nodes. Works completely only in "strict"
   mode. In "transitional" mode, not all antiquotations are available. *)

value not_impl f x =
  let desc =
    if Obj.is_block (Obj.repr x) then
      "tag = " ^ string_of_int (Obj.tag (Obj.repr x))
    else "int_val = " ^ string_of_int (Obj.magic x)
  in
  failwith ("q_ast.ml: " ^ f ^ ", not impl: " ^ desc)
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
      Ploc.call_with Plexer.force_antiquot_loc False
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

module type MetaSig =
  sig
    type t = 'abstract;
    value loc_v : unit -> t;
    value node : string -> list t -> t;
    value node_no_loc : string -> list t -> t;
    value list : ('a -> t) -> list 'a -> t;
    value option : ('a -> t) -> option 'a -> t;
    value vala : ('a -> t) -> MLast.v 'a -> t;
    value bool : bool -> t;
    value string : string -> t;
    value tuple : list t -> t;
    value of_expr : MLast.expr -> t;
    value xtr : Ploc.t -> string -> t;
    value xtr_or_anti : Ploc.t -> (t -> t) -> string -> t;
  end
;

module Meta_make (C : MetaSig) =
  struct
    open MLast;
    value rec ctyp = 
      fun
      [ TyAcc _ t1 t2 -> C.node "TyAcc" [ctyp t1; ctyp t2]
      | TyAli _ t1 t2 -> C.node "TyAli" [ctyp t1; ctyp t2] 
      | TyArr _ t1 t2 -> C.node "TyArr" [ctyp t1; ctyp t2]
      | TyAny _ -> C.node "TyAny" []
      | TyApp _ t1 t2 -> C.node "TyApp" [ctyp t1; ctyp t2]
      | TyCls _ ls -> C.node "TyCls" [C.vala (C.list C.string) ls]
      | TyLab _ i t -> C.node "TyLab" [C.vala C.string i; ctyp t]
      | TyLid _ s -> C.node "TyLid" [C.vala C.string s]
      | TyMan _ t1 t2 -> C.node "TyMan" [ctyp t1; ctyp t2]
      | TyObj _ lm v ->
          C.node "TyObj"
            [C.vala (C.list (fun (s, t) -> C.tuple [C.string s; ctyp t]))
               lm;
             C.vala C.bool v]
      | TyOlb _ i t -> C.node "TyOlb" [C.vala C.string i; ctyp t]
      | TyPol _ lv t ->
          C.node "TyPol" [C.vala (C.list C.string) lv; ctyp t]
      | TyQuo _ s -> C.node "TyQuo" [C.vala C.string s]
      | TyRec _ lld ->
          let lld =
            C.vala
              (C.list
                 (fun (loc, lab, mf, t) ->
                    C.tuple
                      [C.loc_v (); C.string lab; C.bool mf; ctyp t]))
              lld
          in
          C.node "TyRec" [lld]
      | TySum _ lcd ->
          let lcd =
            C.vala
              (C.list
                 (fun (loc, lab, lt) ->
                    let lt = C.vala (C.list ctyp) lt in
                    C.tuple [C.loc_v (); C.vala C.string lab; lt]))
              lcd
          in
          C.node "TySum" [lcd]
      | TyTup _ tl -> C.node "TyTup" [C.vala (C.list ctyp) tl]
      | TyUid _ s -> C.node "TyUid" [C.vala C.string s]
      | TyVrn _ lpv ools ->
          C.node "TyVrn"
            [C.vala (C.list poly_variant) lpv;
             C.option (C.option (C.vala (C.list C.string))) ools]
      | IFDEF STRICT THEN
          TyXtr loc s _ -> C.xtr loc s
        END ]
    and poly_variant =
      fun
      [ PvTag s a lt ->
          let s = C.vala C.string s in
          let a = C.vala C.bool a in
          let lt = C.vala (C.list ctyp) lt in
          C.node_no_loc "PvTag" [s; a; lt]
      | PvInh t ->
          C.node_no_loc "PvInh" [ctyp t] ]
    ;
    value type_var (s, (plus, minus)) =
      C.tuple [C.vala C.string s; C.tuple [C.bool plus; C.bool minus]]
    ;
    value e_class_infos a =
      fun
      [ x -> not_impl "e_class_infos" x ]
    ;
    value rec patt =
      fun
      [ PaAcc _ p1 p2 -> C.node "PaAcc" [patt p1; patt p2]
      | PaAli _ p1 p2 -> C.node "PaAli" [patt p1; patt p2]
      | PaAny _ -> C.node "PaAny" []
      | PaApp _ p1 p2 -> C.node "PaApp" [patt p1; patt p2]
      | PaArr _ pl -> C.node "PaArr" [C.vala (C.list patt) pl]
      | PaChr _ s -> C.node "PaChr" [C.vala C.string s]
      | PaInt _ s k -> C.node "PaInt" [C.vala C.string s; C.string k]
      | PaFlo _ s -> C.node "PaFlo" [C.vala C.string s]
      | PaLab _ s p ->
          C.node "PaLab" [C.vala C.string s; C.option patt p]
      | PaLid _ s -> C.node "PaLid" [C.vala C.string s]
      | PaOlb _ s opeo ->
          C.node "PaOlb"
            [C.vala C.string s;
             C.option
               (fun (p, oe) ->
                  C.tuple [patt p; C.vala (C.option expr) oe])
               opeo]
      | PaOrp _ p1 p2 -> C.node "PaOrp" [patt p1; patt p2]
      | PaRec _ lpe ->
          let lpe =
            C.vala
              (C.list (fun (p, e) -> C.tuple [patt p; patt e])) lpe
          in
          C.node "PaRec" [lpe]
      | PaRng _ p1 p2 -> C.node "PaRng" [patt p1; patt p2]
      | PaStr _ s -> C.node "PaStr" [C.vala C.string s]
      | PaTup _ pl -> C.node "PaTup" [C.vala (C.list patt) pl]
      | PaTyc _ p t -> C.node "PaTyc" [patt p; ctyp t]
      | PaTyp _ ls -> C.node "PaTyp" [C.vala (C.list C.string) ls]
      | PaUid _ s -> C.node "PaUid" [C.vala C.string s]
      | PaVrn _ s -> C.node "PaVrn" [C.vala C.string s]
      | IFDEF STRICT THEN
          PaXtr loc s _ -> C.xtr_or_anti loc (fun r -> C.node "PaAnt" [r]) s
        END
      | x -> not_impl "patt" x ]
    and expr =
      fun
      [ ExAcc _ e1 e2 -> C.node "ExAcc" [expr e1; expr e2]
      | ExAnt _ _ as e -> C.of_expr e
      | ExApp _ e1 e2 -> C.node "ExApp" [expr e1; expr e2]
      | ExAre _ e1 e2 -> C.node "ExAre" [expr e1; expr e2]
      | ExArr _ el -> C.node "ExArr" [C.vala (C.list expr) el]
      | ExAss _ e1 e2 -> C.node "ExAss" [expr e1; expr e2]
      | ExAsr _ e -> C.node "ExAsr" [expr e]
      | ExBae _ e el -> C.node "ExBae" [expr e; C.vala (C.list expr) el]
      | ExChr _ s -> C.node "ExChr" [C.vala C.string s]
      | ExCoe _ e ot t ->
          C.node "ExCoe" [expr e; C.option ctyp ot; ctyp t]
      | ExIfe _ e1 e2 e3 -> C.node "ExIfe" [expr e1; expr e2; expr e3]
      | ExInt _ s k -> C.node "ExInt" [C.vala C.string s; C.string k]
      | ExFlo _ s -> C.node "ExFlo" [C.vala C.string s]
      | ExFor _ i e1 e2 df el ->
          let i = C.vala C.string i in
          let df = C.vala C.bool df in
          let el = C.vala (C.list expr) el in
          C.node "ExFor" [i; expr e1; expr e2; df; el]
      | ExFun _ pwel ->
          let pwel =
            C.vala
              (C.list
                (fun (p, oe, e) ->
                   C.tuple [patt p; C.vala (C.option expr) oe; expr e]))
              pwel
          in
          C.node "ExFun" [pwel]
      | ExLab _ s oe ->
          C.node "ExLab" [C.vala C.string s; C.option expr oe]
      | ExLaz _ e -> C.node "ExLaz" [expr e]
      | ExLet _ rf lpe e ->
          let rf = C.vala C.bool rf in
          let lpe =
            C.vala
              (C.list (fun (p, e) -> C.tuple [patt p; expr e])) lpe
          in
          C.node "ExLet" [rf; lpe; expr e]
      | ExLid _ s -> C.node "ExLid" [C.vala C.string s]
      | ExLmd _ i me e ->
          let i = C.vala C.string i in
          let me = module_expr me in
          C.node "ExLmd" [i; me; expr e]
      | ExMat _ e pwel ->
          let pwel =
            C.vala
              (C.list
                 (fun (p, oe, e) ->
                    C.tuple [patt p; C.vala (C.option expr) oe; expr e]))
              pwel
          in
          C.node "ExMat" [expr e; pwel]
      | ExNew _ ls -> C.node "ExNew" [C.vala (C.list C.string) ls]
      | ExObj _ op lcsi ->
          C.node "ExObj"
            [C.vala (C.option patt) op;
             C.vala (C.list class_str_item) lcsi]
      | ExOlb _ s oe ->
          C.node "ExOlb" [C.vala C.string s; C.option expr oe]
      | ExOvr _ lse ->
          C.node "ExOvr"
            [C.vala (C.list (fun (s, e) -> C.tuple [C.string s; expr e]))
               lse]
      | ExRec _ lpe oe ->
          let lpe =
            C.vala
              (C.list (fun (p, e) -> C.tuple [patt p; expr e])) lpe
          in
          let oe = C.option expr oe in
          C.node "ExRec" [lpe; oe]
      | ExSeq _ el -> C.node "ExSeq" [C.vala (C.list expr) el]
      | ExSnd _ e s -> C.node "ExSnd" [expr e; C.vala C.string s]
      | ExSte _ e1 e2 -> C.node "ExSte" [expr e1; expr e2]
      | ExStr _ s -> C.node "ExStr" [C.vala C.string s]
      | ExTry _ e pwel ->
          let pwel =
            C.vala
              (C.list
                 (fun (p, oe, e) ->
                    C.tuple [patt p; C.vala (C.option expr) oe; expr e]))
              pwel
          in
          C.node "ExTry" [expr e; pwel]
      | ExTup _ el -> C.node "ExTup" [C.vala (C.list expr) el]
      | ExTyc _ e t -> C.node "ExTyc" [expr e; ctyp t]
      | ExUid _ s -> C.node "ExUid" [C.vala C.string s]
      | ExVrn _ s -> C.node "ExVrn" [C.vala C.string s]
      | ExWhi _ e el -> C.node "ExWhi" [expr e; C.vala (C.list expr) el]
      | IFDEF STRICT THEN
          ExXtr loc s _ -> C.xtr_or_anti loc (fun r -> C.node "ExAnt" [r]) s
        END ]
    and module_type =
      fun
      [ MtAcc _ mt1 mt2 ->
          C.node "MtAcc" [module_type mt1; module_type mt2]
      | MtApp _ mt1 mt2 ->
          C.node "MtApp" [module_type mt1; module_type mt2]
      | MtFun _ s mt1 mt2 ->
          C.node "MtFun"
            [C.vala C.string s; module_type mt1; module_type mt2]
      | MtLid _ s -> C.node "MtLid" [C.vala C.string s]
      | MtQuo _ s -> C.node "MtQuo" [C.vala C.string s]
      | MtSig _ sil -> C.node "MtSig" [C.vala (C.list sig_item) sil]
      | MtUid _ s -> C.node "MtUid" [C.vala C.string s]
      | MtWit _ mt lwc ->
          C.node "MtWit"
            [module_type mt; C.vala (C.list with_constr) lwc]
      | IFDEF STRICT THEN
          MtXtr loc s _ -> C.xtr loc s
        END ]
    and sig_item =
      fun
      [ SgCls _ cd ->
          C.node "SgCls" [C.vala (C.list (e_class_infos class_type)) cd]
      | SgClt _ ctd ->
          C.node "SgClt" [C.vala (C.list (e_class_infos class_type)) ctd]
      | SgDcl _ lsi ->
          C.node "SgDcl" [C.vala (C.list sig_item) lsi]
      | SgDir _ n dp ->
          C.node "SgDir" [C.vala C.string n; C.vala (C.option expr) dp]
      | SgExc _ s lt ->
          let s = C.vala C.string s in
          let lt = C.vala (C.list ctyp) lt in
          C.node "SgExc" [s; lt]
      | SgExt _ s t ls ->
          let ls = C.vala (C.list C.string) ls in
          C.node "SgExt" [C.vala C.string s; ctyp t; ls]
      | SgInc _ mt -> C.node "SgInc" [module_type mt]
      | SgMod _ rf lsmt ->
          let lsmt =
            C.vala
              (C.list
                 (fun (s, mt) -> C.tuple [C.string s; module_type mt]))
              lsmt
          in
          C.node "SgMod" [C.vala C.bool rf; lsmt]
      | SgMty _ s mt -> C.node "SgMty" [C.vala C.string s; module_type mt]
      | SgOpn _ sl -> C.node "SgOpn" [C.vala (C.list C.string) sl]
      | SgTyp _ ltd -> C.node "SgTyp" [C.vala (C.list e_type_decl) ltd]
      | SgVal _ s t -> C.node "SgVal" [C.vala C.string s; ctyp t]
      | x -> not_impl "sig_item" x ]
    and with_constr =
      fun
      [ WcTyp _ li ltp pf t ->
          let li = C.vala (C.list C.string) li in
          let ltp = C.vala (C.list type_var) ltp in
          let pf = C.vala C.bool pf in
          let t = ctyp t in
          C.node "WcTyp" [li; ltp; pf; t]
      | WcMod _ li me ->
          let li = C.vala (C.list C.string) li in
          let me = module_expr me in
          C.node "WcMod" [li; me] ]
    and module_expr =
      fun
      [ MeAcc _ me1 me2 ->
          C.node "MeAcc" [module_expr me1; module_expr me2]
      | MeApp _ me1 me2 ->
          C.node "MeApp" [module_expr me1; module_expr me2]
      | MeFun _ s mt me ->
          C.node "MeFun"
            [C.vala C.string s; module_type mt; module_expr me]
      | MeStr _ lsi -> C.node "MeStr" [C.vala (C.list str_item) lsi]
      | MeTyc _ me mt -> C.node "MeTyc" [module_expr me; module_type mt]
      | MeUid _ s -> C.node "MeUid" [C.vala C.string s]
      | IFDEF STRICT THEN
          MeXtr loc s _ -> C.xtr loc s
        END ]
    and str_item =
      fun
      [ StCls _ cd ->
          C.node "StCls" [C.vala (C.list (e_class_infos class_expr)) cd]
      | StClt _ ctd ->
          C.node "StClt" [C.vala (C.list (e_class_infos class_type)) ctd]
      | StDcl _ lsi ->
          C.node "StDcl" [C.vala (C.list str_item) lsi]
      | StDir _ n dp ->
          C.node "StDir" [C.vala C.string n; C.vala (C.option expr) dp]
      | StExc _ s lt ls ->
          let s = C.vala C.string s in
          let lt = C.vala (C.list ctyp) lt in
          let ls = C.vala (C.list C.string) ls in
          C.node "StExc" [s; lt; ls]
      | StExp _ e -> C.node "StExp" [expr e]
      | StExt _ s t ls ->
          let ls = C.vala (C.list C.string) ls in
          C.node "StExt" [C.vala C.string s; ctyp t; ls]
      | StInc _ me -> C.node "StInc" [module_expr me]
      | StMod _ rf lsme ->
          let lsme =
            C.vala
              (C.list
                 (fun (s, me) -> C.tuple [C.string s; module_expr me]))
              lsme
          in
          C.node "StMod" [C.vala C.bool rf; lsme]
      | StMty _ s mt ->
          C.node "StMty" [C.vala C.string s; module_type mt]
      | StOpn _ sl -> C.node "StOpn" [C.vala (C.list C.string) sl]
      | StTyp _ ltd -> C.node "StTyp" [C.vala (C.list e_type_decl) ltd]
      | StVal _ rf lpe ->
          let lpe =
            C.vala (C.list (fun (p, e) -> C.tuple [patt p; expr e]))
              lpe
          in
          C.node "StVal" [C.vala C.bool rf; lpe]
      | x -> not_impl "str_item" x ]
    and e_type_decl =
      fun
      [ x -> not_impl "e_type_decl" x ]
    and class_type =
      fun
      [ CtCon _ ls lt ->
          C.node "CtCon"
            [C.vala (C.list C.string) ls; C.vala (C.list ctyp) lt]
      | CtFun _ t ct -> C.node "CtFun" [ctyp t; class_type ct]
      | CtSig _ ot lcsi ->
          C.node "CtSig"
            [C.vala (C.option ctyp) ot;
             C.vala (C.list class_sig_item) lcsi]
      | IFDEF STRICT THEN
          CtXtr loc s _ -> C.xtr loc s
        END ]
    and class_sig_item =
      fun
      [ CgCtr _ t1 t2 -> C.node "CgCtr" [ctyp t1; ctyp t2]
      | CgDcl _ lcsi ->
          C.node "CgDcl" [C.vala (C.list class_sig_item) lcsi]
      | CgInh _ ct -> C.node "CgInh" [class_type ct]
      | CgMth _ s mf t ->
          C.node "CgMth" [C.vala C.string s; C.vala C.bool mf; ctyp t]
      | CgVal _ s mf t ->
          C.node "CgVal" [C.vala C.string s; C.vala C.bool mf; ctyp t]
      | CgVir _ s mf t ->
          C.node "CgVir" [C.vala C.string s; C.vala C.bool mf; ctyp t] ]
    and class_expr =
      fun
      [ CeApp _ ce e -> C.node "CeApp" [class_expr ce; expr e]
      | CeCon _ c l ->
          let c = C.vala (C.list C.string) c in
          C.node "CeCon" [c; C.vala (C.list ctyp) l]
      | CeFun _ p ce -> C.node "CeFun" [patt p; class_expr ce]
      | CeLet _ rf lb ce ->
          C.node "CeLet"
            [C.vala C.bool rf;
             C.vala (C.list (fun (p, e) -> C.tuple [patt p; expr e]))
               lb;
             class_expr ce]
      | CeStr _ ocsp lcsi ->
          let ocsp = C.vala (C.option patt) ocsp in
          let lcsi = C.vala (C.list class_str_item) lcsi in
          C.node "CeStr" [ocsp; lcsi]
      | CeTyc _ ce ct -> C.node "CeTyc" [class_expr ce; class_type ct]
      | IFDEF STRICT THEN
          CeXtr loc s _ -> C.xtr loc s
        END ]
    and class_str_item =
      fun
      [ CrCtr _ t1 t2 -> C.node "CrCtr" [ctyp t1; ctyp t2]
      | CrDcl _ lcsi -> C.node "CrDcl" [C.vala (C.list class_str_item) lcsi]
      | CrInh _ ce os ->
          C.node "CrInh" [class_expr ce; C.vala (C.option C.string) os]
      | CrIni _ e -> C.node "CrIni" [expr e]
      | CrMth _ s pf e ot ->
          C.node "CrMth"
            [C.vala C.string s; C.vala C.bool pf; expr e;
             C.vala (C.option ctyp) ot]
      | CrVal _ s rf e ->
          C.node "CrVal" [C.vala C.string s; C.vala C.bool rf; expr e]
      | CrVir _ s pf t ->
          C.node "CrVir" [C.vala C.string s; C.vala C.bool pf; ctyp t] ]
    ;
  end
;

module Meta_E =
  Meta_make
    (struct
       type t = MLast.expr;
       value loc = Ploc.dummy;
       value loc_v () = <:expr< $lid:Ploc.name.val$ >>;
       value node con el =
         List.fold_left (fun e1 e2 -> <:expr< $e1$ $e2$ >>)
           <:expr< MLast.$uid:con$ $loc_v ()$ >> el
       ;
       value node_no_loc con el =
         List.fold_left (fun e1 e2 -> <:expr< $e1$ $e2$ >>)
           <:expr< MLast.$uid:con$  >> el
       ;
       value list elem el =
         loop el where rec loop el =
           match el with
           [ [] -> <:expr< [] >>
           | [e :: el] -> <:expr< [$elem e$ :: $loop el$] >> ]
       ;
       value option elem oe =
         match oe with
         [ None -> <:expr< None >>
         | Some e -> <:expr< Some $elem e$ >> ]
       ;
       value vala elem =
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
       value bool b = if b then <:expr< True >> else <:expr< False >>;
       value string s = <:expr< $str:s$ >>;
       value tuple el = <:expr< ($list:el$) >>;
       value of_expr e = e;
       value xtr loc s =
         match get_anti_loc s with
         [ Some (loc, typ, str) ->
             match typ with
             [ "" ->
                 let (loc, r) = eval_anti Pcaml.expr_eoi loc "" str in
                 <:expr< $anti:r$ >>
             | _ -> assert False ]
         | _ -> assert False ]
       ;
       value xtr_or_anti loc f s =
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
     end)
;

module Meta_P =
  Meta_make
    (struct
       type t = MLast.patt;
       value loc = Ploc.dummy;
       value loc_v () = <:patt< _ >>;
       value node con pl =
         List.fold_left (fun p1 p2 -> <:patt< $p1$ $p2$ >>)
           <:patt< MLast.$uid:con$ _ >> pl
       ;
       value node_no_loc con pl =
         List.fold_left (fun p1 p2 -> <:patt< $p1$ $p2$ >>)
           <:patt< MLast.$uid:con$ >> pl
       ;
       value list elem el =
         loop el where rec loop el =
           match el with
           [ [] -> <:patt< [] >>
           | [e :: el] -> <:patt< [$elem e$ :: $loop el$] >> ]
       ;
       value option elem oe =
         match oe with
         [ None -> <:patt< None >>
         | Some e -> <:patt< Some $elem e$ >> ]
       ;
       value vala elem =
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
       value bool b = if b then <:patt< True >> else <:patt< False >>;
       value string s = <:patt< $str:s$ >>;
       value tuple pl = <:patt< ($list:pl$) >>;
       value of_expr _ = assert False;
       value xtr loc s =
         match get_anti_loc s with
         [ Some (loc, typ, str) ->
             match typ with
             [ "" ->
                 let (loc, r) = eval_anti Pcaml.patt_eoi loc "" str in
                 <:patt< $anti:r$ >>
             | _ -> assert False ]
         | _ -> assert False ]
       ;
       value xtr_or_anti loc f s =
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
     end)
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
    Ploc.call_with Plexer.force_antiquot_loc True
      (Grammar.Entry.parse e) (Stream.of_string s)
  in
  let expr s = me (f s) in
  let patt s = mp (f s) in
  Quotation.ExAst (expr, patt)
;

List.iter
  (fun (q, f) -> Quotation.add q f)
  [("expr", apply_entry expr_eoi Meta_E.expr Meta_P.expr);
   ("patt", apply_entry patt_eoi Meta_E.patt Meta_P.patt);
   ("ctyp", apply_entry ctyp_eoi Meta_E.ctyp Meta_P.ctyp);
   ("str_item", apply_entry str_item_eoi Meta_E.str_item Meta_P.str_item);
   ("sig_item", apply_entry sig_item_eoi Meta_E.sig_item Meta_P.sig_item);
   ("module_expr",
    apply_entry module_expr_eoi Meta_E.module_expr Meta_P.module_expr);
   ("module_type",
    apply_entry module_type_eoi Meta_E.module_type Meta_P.module_type);
   ("with_constr",
    apply_entry with_constr_eoi Meta_E.with_constr Meta_P.with_constr);
   ("poly_variant",
    apply_entry poly_variant_eoi Meta_E.poly_variant Meta_P.poly_variant);
   ("class_expr",
    apply_entry class_expr_eoi Meta_E.class_expr Meta_P.class_expr);
   ("class_type",
    apply_entry class_type_eoi Meta_E.class_type Meta_P.class_type);
   ("class_str_item",
    apply_entry class_str_item_eoi Meta_E.class_str_item
      Meta_P.class_str_item);
   ("class_sig_item",
    apply_entry class_sig_item_eoi Meta_E.class_sig_item
      Meta_P.class_sig_item)]
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
    Ploc.call_with Plexer.force_antiquot_loc True
      (Grammar.Entry.parse expr_eoi) (Stream.of_string s)
  in
  let patt s =
    let p =
      Ploc.call_with Plexer.force_antiquot_loc True
        (Grammar.Entry.parse Pcaml.patt_eoi) (Stream.of_string s)
    in
    let loc = Ploc.make_unlined (0, 0) in
    if Pcaml.strict_mode.val then <:patt< Ploc.VaVal $anti:p$ >>
    else <:patt< $anti:p$ >>
  in
  Quotation.add "vala" (Quotation.ExAst (expr, patt));
};
