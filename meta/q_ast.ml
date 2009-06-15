(* camlp5r pa_macro.cmo *)
(* $Id: q_ast.ml,v 1.51 2007/09/10 17:19:30 deraugla Exp $ *)
(* Copyright (c) INRIA 2007 *)

(* Experimental AST quotations while running the normal parser and
   its possible extensions and meta-ifying the nodes. Antiquotations
   work only in "strict" mode. *)

#load "pa_extend.cmo";
#load "q_MLast.cmo";

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

(*
(* upper bound of tags of all syntax tree nodes *)
value anti_tag = 100;

value make_anti loc t s = do {
  let r = Obj.new_block anti_tag 3 in
  Obj.set_field r 0 (Obj.repr (loc : Ploc.t));
  Obj.set_field r 1 (Obj.repr (t : string));
  Obj.set_field r 2 (Obj.repr (s : string));
  Obj.magic r
};

value get_anti v =
  if Obj.tag (Obj.repr v) = anti_tag && Obj.size (Obj.repr v) = 3 then
    let loc : Ploc.t = Obj.magic (Obj.field (Obj.repr v) 0) in
    let t : string = Obj.magic (Obj.field (Obj.repr v) 1) in
    let s : string = Obj.magic (Obj.field (Obj.repr v) 2) in
    Some (loc, t, s)
  else None
;
*)

value make_anti loc t s = failwith "not impl: make_anti";
value get_anti v = None;

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
            let asit = s.[0] = 'a' in
            let s = String.sub s 1 (String.length s - 1) in
            match get_anti_loc s with
            [ Some (loc, typ, str) ->
                let (loc, r) = eval_anti Pcaml.expr_eoi loc typ str in
                if asit then <:expr< $anti:r$ >>
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
            let asit = s.[0] = 'a' in
            let s = String.sub s 1 (String.length s - 1) in
            match get_anti_loc s with
            [ Some (loc, typ, str) ->
                let (loc, r) = eval_anti Pcaml.patt_eoi loc typ str in
                if asit then <:patt< $anti:r$ >>
                else <:patt< Ploc.VaVal $anti:r$ >>
            | None -> assert False ]
        | Ploc.VaVal v -> <:patt< Ploc.VaVal $elem v$ >> ]
      END
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
      match get_anti oe with
      [ Some (loc, typ, str) ->
          let (loc, r) = eval_anti Pcaml.patt_eoi loc typ str in
          <:patt< $anti:r$ >>
      | None ->
          match oe with
          [ None -> <:patt< None >>
          | Some e -> <:patt< Some $elem e$ >> ] ]
    ;
    value e_bool b =
      match get_anti b with
      [ Some (loc, typ, str) ->
          let (loc, r) = eval_anti Pcaml.expr_eoi loc typ str in
          <:expr< $anti:r$ >>
      | None -> if b then <:expr< True >> else <:expr< False >> ]
    ;
    value p_bool b =
      match get_anti b with
      [ Some (loc, typ, str) ->
          let (loc, r) = eval_anti Pcaml.patt_eoi loc typ str in
          <:patt< $anti:r$ >>
      | None -> if b then <:patt< True >> else <:patt< False >> ]
    ;
    value e_string s = <:expr< $str:s$ >>;
    value p_string s =
      match get_anti s with
      [ Some (loc, typ, str) ->
          let (loc, r) = eval_anti Pcaml.patt_eoi loc typ str in
          <:patt< $anti:r$ >>
      | None -> <:patt< $str:s$ >> ]
    ;
    value e_ctyp t = 
      let ln = ln () in
      loop t where rec loop t =
        match t with
        [ TyAcc _ t1 t2 -> <:expr< MLast.TyAcc $ln$ $loop t1$ $loop t2$ >>
        | TyArr _ t1 t2 -> <:expr< MLast.TyArr $ln$ $loop t1$ $loop t2$ >>
        | TyAny _ -> <:expr< MLast.TyAny $ln$ >>
        | TyApp _ t1 t2 -> <:expr< MLast.TyApp $ln$ $loop t1$ $loop t2$ >> 
        | TyLid _ s -> <:expr< MLast.TyLid $ln$ $e_vala e_string s$ >>
        | TyQuo _ s -> <:expr< MLast.TyQuo $ln$ $e_vala e_string s$ >>
(*
        | TyRec _ lld ->
            let lld =
              e_vala
                (e_list
                   (fun (loc, lab, mf, t) ->
                      <:expr< ($ln$, $str:lab$, $e_bool mf$, $loop t$) >>))
                lld
            in
            <:expr< MLast.TyRec $ln$ $lld$ >>
*)
        | TyTup _ tl -> <:expr< MLast.TyTup $ln$ $e_vala (e_list loop) tl$ >>
        | TyUid _ s -> <:expr< MLast.TyUid $ln$ $e_vala e_string s$ >>
        | IFDEF STRICT THEN
            TyXtr loc s _ ->
              let (loc, r) = eval_anti Pcaml.expr_eoi loc "" s in
              <:expr< $anti:r$ >>
          END
        | x -> not_impl "e_ctyp" x ]
    ;
    value p_ctyp =
      loop where rec loop =
        fun
        [ TyArr _ t1 t2 -> <:patt< MLast.TyArr _ $loop t1$ $loop t2$ >>
        | TyApp _ t1 t2 -> <:patt< MLast.TyApp _ $loop t1$ $loop t2$ >>
        | TyLid _ s -> <:patt< MLast.TyLid _ $p_vala p_string s$ >>
        | TyTup _ tl -> <:patt< MLast.TyTup _ $p_vala (p_list loop) tl$ >>
        | TyUid _ s -> <:patt< MLast.TyUid _ $p_vala p_string s$ >>
        | IFDEF STRICT THEN
            TyXtr loc s _ ->
              let (loc, r) = eval_anti Pcaml.patt_eoi loc "" s in
              <:patt< $anti:r$ >>
          END
        | x -> not_impl "p_ctyp" x ]
    ;
(*
    value e_type_decl =
      fun
      [ x -> not_impl "e_type_decl" x ]
    ;
*)
    value e_patt p =
      let ln = ln () in
      loop p where rec loop =
        fun
        [ PaAcc _ p1 p2 -> <:expr< MLast.PaAcc $ln$ $loop p1$ $loop p2$ >>
        | PaAli _ p1 p2 -> <:expr< MLast.PaAli $ln$ $loop p1$ $loop p2$ >>
        | PaAny _ -> <:expr< MLast.PaAny $ln$ >>
        | PaApp _ p1 p2 -> <:expr< MLast.PaApp $ln$ $loop p1$ $loop p2$ >>
        | PaChr _ s -> <:expr< MLast.PaChr $ln$ $e_vala e_string s$ >>
        | PaInt _ s k ->
            <:expr< MLast.PaInt $ln$ $e_vala e_string s$ $str:k$ >>
        | PaFlo _ s -> <:expr< MLast.PaFlo $ln$ $e_vala e_string s$ >>
        | PaLid _ s -> <:expr< MLast.PaLid $ln$ $e_vala e_string s$ >>
        | PaOrp _ p1 p2 -> <:expr< MLast.PaOrp $ln$ $loop p1$ $loop p2$ >>
        | PaRec _ lpe ->
            let lpe =
              e_vala
                (e_list (fun (p, e) -> <:expr< ($loop p$, $loop e$) >>)) lpe
            in
            <:expr< MLast.PaRec $ln$ $lpe$ >>
        | PaRng _ p1 p2 -> <:expr< MLast.PaRng $ln$ $loop p1$ $loop p2$ >>
        | PaStr _ s -> <:expr< MLast.PaStr $ln$ $e_string s$ >>
        | PaTup _ pl -> <:expr< MLast.PaTup $ln$ $e_vala (e_list loop) pl$ >>
        | PaTyc _ p t -> <:expr< MLast.PaTyc $ln$ $loop p$ $e_ctyp t$ >>
        | PaUid _ s -> <:expr< MLast.PaUid $ln$ $e_vala e_string s$ >>
        | IFDEF STRICT THEN
            PaXtr loc s _ ->
              let asit = s.[0] = 'a' in
              let s = String.sub s 1 (String.length s - 1) in
              if asit then
                let (loc, r) = eval_anti Pcaml.expr_eoi loc "" s in
                <:expr< $anti:r$ >>
              else
                let (loc, r) = eval_anti Pcaml.expr_eoi loc "anti" s in
                let r = <:expr< $anti:r$ >> in
                <:expr< MLast.PaAnt loc $r$ >>
          END
        | x -> not_impl "e_patt" x ]
    ;
    value p_patt =
      loop where rec loop =
        fun
        [ PaAcc _ p1 p2 -> <:patt< MLast.PaAcc _ $loop p1$ $loop p2$ >>
        | PaAli _ p1 p2 -> <:patt< MLast.PaAli _ $loop p1$ $loop p2$ >>
        | PaChr _ s -> <:patt< MLast.PaChr _ $p_vala p_string s$ >>
        | PaLid _ s -> <:patt< MLast.PaLid _ $p_vala p_string s$ >>
        | PaTup _ pl -> <:patt< MLast.PaTup _ $p_vala (p_list loop) pl$ >>
        | IFDEF STRICT THEN
            PaXtr loc s _ ->
              let asit = s.[0] = 'a' in
              let s = String.sub s 1 (String.length s - 1) in
              if asit then
                let (loc, r) = eval_anti Pcaml.patt_eoi loc "" s in
                <:patt< $anti:r$ >>
              else
                let (loc, r) = eval_anti Pcaml.patt_eoi loc "anti" s in
                let r = <:patt< $anti:r$ >> in
                <:patt< MLast.PaAnt loc $r$ >>
          END
        | x -> not_impl "p_patt" x ]
    ;
    value e_expr e =
      let ln = ln () in
      loop e where rec loop =
        fun
        [ ExAcc _ e1 e2 -> <:expr< MLast.ExAcc $ln$ $loop e1$ $loop e2$ >>
        | ExApp _ e1 e2 -> <:expr< MLast.ExApp $ln$ $loop e1$ $loop e2$ >>
(*
        | ExArr _ el -> <:expr< MLast.ExArr $ln$ $e_list loop el$ >>
*)
        | ExChr _ s -> <:expr< MLast.ExChr $ln$ $e_vala e_string s$ >>
        | ExIfe _ e1 e2 e3 ->
            <:expr< MLast.ExIfe $ln$ $loop e1$ $loop e2$ $loop e3$ >>
        | ExInt _ s k ->
            <:expr< MLast.ExInt $ln$ $e_vala e_string s$ $str:k$ >>
        | ExFlo _ s -> <:expr< MLast.ExFlo $ln$ $e_vala e_string s$ >>
        | ExFun _ pwel ->
            let pwel =
              e_list
                (fun (p, oe, e) ->
                   <:expr< ($e_patt p$, $e_option loop oe$, $loop e$) >>)
                pwel
            in
            <:expr< MLast.ExFun $ln$ $pwel$ >>
        | ExLet _ rf lpe e ->
            let rf = e_vala e_bool rf in
            let lpe =
              e_vala
                (e_list (fun (p, e) -> <:expr< ($e_patt p$, $loop e$) >>)) lpe
            in
            <:expr< MLast.ExLet $ln$ $rf$ $lpe$ $loop e$ >>
        | ExLid _ s -> <:expr< MLast.ExLid $ln$ $e_vala e_string s$ >>
        | ExMat _ e pwel ->
            let pwel =
              e_list
                (fun (p, oe, e) ->
                   <:expr< ($e_patt p$, $e_option loop oe$, $loop e$) >>)
                pwel
            in
            <:expr< MLast.ExMat $ln$ $loop e$ $pwel$ >>
        | ExRec _ lpe oe ->
            let lpe =
              e_vala
                (e_list (fun (p, e) -> <:expr< ($e_patt p$, $loop e$) >>)) lpe
            in
            let oe = e_option loop oe in
            <:expr< MLast.ExRec $ln$ $lpe$ $oe$ >>
        | ExSeq _ el -> <:expr< MLast.ExSeq $ln$ $e_vala (e_list loop) el$ >>
        | ExStr _ s -> <:expr< MLast.ExStr $ln$ $e_vala e_string s$ >>
        | ExTup _ el -> <:expr< MLast.ExTup $ln$ $e_vala (e_list loop) el$ >>
        | ExTyc _ e t -> <:expr< MLast.ExTyc $ln$ $loop e$ $e_ctyp t$ >>
        | ExUid _ s -> <:expr< MLast.ExUid $ln$ $e_vala e_string s$ >>
        | IFDEF STRICT THEN
            ExXtr loc s _ ->
              let asit = s.[0] = 'a' in
              let s = String.sub s 1 (String.length s - 1) in
              if asit then
                let (loc, r) = eval_anti Pcaml.expr_eoi loc "" s in
                <:expr< $anti:r$ >>
              else
                let (loc, r) = eval_anti Pcaml.expr_eoi loc "anti" s in
                let r = <:expr< $anti:r$ >> in
                <:expr< MLast.ExAnt loc $r$ >>
          END
        | x -> not_impl "e_expr" x ]
    ;
    value p_expr e =
      loop e where rec loop =
        fun
        [ ExAcc _ e1 e2 -> <:patt< MLast.ExAcc _ $loop e1$ $loop e2$ >>
        | ExApp _ e1 e2 -> <:patt< MLast.ExApp _ $loop e1$ $loop e2$ >>
        | ExIfe _ e1 e2 e3 ->
            <:patt< MLast.ExIfe _ $loop e1$ $loop e2$ $loop e3$ >>
        | ExInt _ s k -> <:patt< MLast.ExInt _ $p_vala p_string s$ $str:k$ >>
        | ExFlo _ s -> <:patt< MLast.ExFlo _ $p_vala p_string s$ >>
        | ExLet _ rf lpe e ->
            let rf = p_vala p_bool rf in
            let lpe =
              p_vala
                (p_list (fun (p, e) -> <:patt< ($p_patt p$, $loop e$) >>)) lpe
            in
            <:patt< MLast.ExLet _ $rf$ $lpe$ $loop e$ >>
        | ExRec _ lpe oe ->
            let lpe =
              p_vala
                (p_list (fun (p, e) -> <:patt< ($p_patt p$, $loop e$) >>)) lpe
            in
            let oe = p_option loop oe in
            <:patt< MLast.ExRec _ $lpe$ $oe$ >>
        | ExLid _ s -> <:patt< MLast.ExLid _ $p_vala p_string s$ >>
        | ExStr _ s -> <:patt< MLast.ExStr _ $p_vala p_string s$ >>
        | ExTup _ el -> <:patt< MLast.ExTup _ $p_vala (p_list loop) el$ >>
        | ExUid _ s -> <:patt< MLast.ExUid _ $p_vala p_string s$ >>
        | IFDEF STRICT THEN
            ExXtr loc s _ ->
              let asit = s.[0] = 'a' in
              let s = String.sub s 1 (String.length s - 1) in
              if asit then
                let (loc, r) = eval_anti Pcaml.patt_eoi loc "" s in
                <:patt< $anti:r$ >>
              else
                let (loc, r) = eval_anti Pcaml.patt_eoi loc "anti" s in
                let r = <:patt< $anti:r$ >> in
                <:patt< MLast.ExAnt loc $r$ >>
          END
        | x -> not_impl "p_expr" x ]
    ;
    value e_sig_item si =
      let ln = ln () in
      loop si where rec loop =
        fun
        [ SgDcl _ lsi ->
            <:expr< MLast.SgDcl $ln$ $e_vala (e_list loop) lsi$ >>
(*
        | SgVal _ s t -> <:expr< MLast.SgVal $ln ()$ $e_string s$ $e_ctyp t$ >>
*)
        | x -> not_impl "e_sig_item" x ]
    ;
(*
    value e_module_type mt =
      let ln = ln () in
      loop mt where rec loop =
        fun
        [ MtUid _ s -> <:expr< MLast.MtUid $ln$ $e_string s$ >>
        | x -> not_impl "e_module_type" x ]
    ;
*)
    value rec e_str_item si =
      let ln = ln () in
      loop si where rec loop =
        fun
        [ StDcl _ lsi ->
            <:expr< MLast.StDcl $ln$ $e_vala (e_list loop) lsi$ >>
(*
        | StExc _ s lt ls ->
            let ls =
              match eval_antiquot_patch expr_eoi ls with
              [ Some (loc, r) -> <:expr< $anti:r$ >>
              | None -> e_list e_string ls ]
            in
            <:expr< MLast.StExc $ln$ $e_string s$ $e_list e_ctyp lt$ $ls$ >>
        | StExp _ e -> <:expr< MLast.StExp $ln$ $e_expr e$ >>
        | StExt _ s t ls ->
            let ls = e_list e_string ls in
            <:expr< MLast.StExt $ln$ $e_string s$ $e_ctyp t$ $ls$ >>
        | StInc _ me -> <:expr< MLast.StInc $ln$ $e_module_expr me$ >>
        | StMod _ rf lsme ->
            let lsme =
              e_list
                (fun (s, me) -> <:expr< ($e_string s$, $e_module_expr me$) >>)
                lsme
            in
            <:expr< MLast.StMod $ln$ $e_vala e_bool rf$ $lsme$ >>
        | StMty _ s mt ->
            <:expr< MLast.StMty $ln$ $e_string s$ $e_module_type mt$ >>
        | StOpn _ sl ->
            <:expr< MLast.StOpn $ln$ $e_list e_string sl$ >>
        | StTyp _ ltd ->
            <:expr< MLast.StTyp $ln$ $e_list e_type_decl ltd$ >>
*)
        | StVal _ rf lpe ->
            let lpe =
              e_list (fun (p, e) -> <:expr< ($e_patt p$, $e_expr e$) >>) lpe
            in
            <:expr< MLast.StVal $ln$ $e_vala e_bool rf$ $lpe$ >>
        | x -> not_impl "e_str_item" x ]
    and p_str_item =
      fun
      [ x -> not_impl "p_str_item" x ]
    and e_module_expr me =
(*
      let ln = ln () in
*)
      loop me where rec loop =
        fun
        [ (* MeAcc _ me1 me2 ->
            <:expr< MLast.MeAcc $ln$ $loop me1$ $loop me2$ >>
        | MeApp _ me1 me2 ->
            <:expr< MLast.MeApp $ln$ $loop me1$ $loop me2$ >>
        | MeFun _ s mt me ->
            let mt = e_module_type mt in
            <:expr< MLast.MeFun $ln$ $e_string s$ $mt$ $loop me$ >>
        | MeStr _ lsi -> <:expr< MLast.MeStr $ln$ $e_list e_str_item lsi$ >>
        | MeTyc _ me mt ->
            let mt = e_module_type mt in
            <:expr< MLast.MeTyc $ln$ $loop me$ $mt$ >>
        | MeUid _ s -> <:expr< MLast.MeUid $ln$ $e_string s$ >>
        | *) x -> not_impl "e_module_expr" x ]
    and p_module_expr =
      fun
      [ x -> not_impl "p_module_expr" x ]
    ;
    value p_sig_item =
      fun
      [ (* SgVal _ s t -> <:patt< MLast.SgVal _ $p_string s$ $p_ctyp t$ >>
      | *) x -> not_impl "p_sig_item" x ]
    ;
  end
;

value expr_eoi = Grammar.Entry.create Pcaml.gram "expr";
value patt_eoi = Grammar.Entry.create Pcaml.gram "patt";
value ctyp_eoi = Grammar.Entry.create Pcaml.gram "type";
value str_item_eoi = Grammar.Entry.create Pcaml.gram "str_item";
value sig_item_eoi = Grammar.Entry.create Pcaml.gram "sig_item";
value module_expr_eoi = Grammar.Entry.create Pcaml.gram "module_expr";

EXTEND
  expr_eoi: [ [ x = Pcaml.expr; EOI -> x ] ];
  patt_eoi: [ [ x = Pcaml.patt; EOI -> x ] ];
  ctyp_eoi: [ [ x = Pcaml.ctyp; EOI -> x ] ];
  sig_item_eoi: [ [ x = Pcaml.sig_item; EOI -> x ] ];
  str_item_eoi: [ [ x = Pcaml.str_item; EOI -> x ] ];
  module_expr_eoi: [ [ x = Pcaml.module_expr; EOI -> x ] ];
END;

IFDEF STRICT THEN
  let ipatt = Grammar.Entry.find Pcaml.expr "ipatt" in
  EXTEND
    Pcaml.expr: LAST
      [ [ s = ANTIQUOT_LOC "" -> MLast.ExXtr loc ("a" ^ s) None
        | s = ANTIQUOT_LOC "anti" -> MLast.ExXtr loc ("b" ^ s) None ] ]
    ;
    Pcaml.patt: LAST
      [ [ s = ANTIQUOT_LOC "" -> MLast.PaXtr loc ("a" ^ s) None
        | s = ANTIQUOT_LOC "anti" -> MLast.PaXtr loc ("b" ^ s) None ] ]
    ;
    ipatt: LAST
      [ [ s = ANTIQUOT_LOC "" -> Obj.repr (MLast.PaXtr loc ("a" ^ s) None) ] ]
    ;
    Pcaml.ctyp: LAST
      [ [ s = ANTIQUOT_LOC -> MLast.TyXtr loc s None ] ]
    ;
  (*
    Pcaml.str_item: LAST
      [ [ s = ANTIQUOT_LOC "exp" ->
            let e = MLast.ExAnt loc (MLast.ExLid loc s) in
            MLast.StExp loc e ] ]
    ;
    Pcaml.module_expr: LAST
      [ [ s = ANTIQUOT_LOC -> MLast.MeUid loc s ] ]
    ;
    Pcaml.module_type: LAST
      [ [ s = ANTIQUOT_LOC -> MLast.MtUid loc s ] ]
    ;
  *)
  END
END;

(*
let mod_ident = Grammar.Entry.find Pcaml.str_item "mod_ident" in
EXTEND
  mod_ident: FIRST
    [ [ s = ANTIQUOT_LOC "" -> Obj.repr s ] ]
  ;
END;

value check_anti s kind =
  if String.length s > String.length kind then
    if String.sub s 0 (String.length kind + 1) = kind ^ ":" then s
    else raise Stream.Failure
  else raise Stream.Failure
;
*)

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

value check_and_make_anti prm typ =
  let (loc, str) = check_anti_loc prm typ in
  make_anti loc typ str
;

(* Need adding in grammar.ml in Slist* cases:
      let pa = parser_of_token entry ("LIST", "") in
   and
      [: a = pa :] -> a
   in their parsers. Same for OPT and FLAG. *)

let lex = Grammar.glexer Pcaml.gram in
let tok_match = lex.Plexing.tok_match in
lex.Plexing.tok_match :=
  fun
  [("ANTIQUOT_LOC", p_prm) ->
      fun
      [ ("ANTIQUOT_LOC", prm) -> snd (check_anti_loc prm p_prm)
      | _ -> raise Stream.Failure ]
  | ("V INT", "") ->
      fun
      [ ("ANTIQUOT_LOC", prm) ->
          let kind = check_anti_loc2 prm in
          if kind = "aint" then "a" ^ prm
          else if kind = "int" then "b" ^ prm
          else raise Stream.Failure
      | _ -> raise Stream.Failure ]
  | ("V FLOAT", "") ->
      fun
      [ ("ANTIQUOT_LOC", prm) ->
          let kind = check_anti_loc2 prm in
          if kind = "aflo" then "a" ^ prm
          else if kind = "flo" then "b" ^ prm
          else raise Stream.Failure
      | _ -> raise Stream.Failure ]
  | ("V LIDENT", "") ->
      fun
      [ ("ANTIQUOT_LOC", prm) ->
          let kind = check_anti_loc2 prm in
          if kind = "alid" then "a" ^ prm
          else if kind = "lid" then "b" ^ prm
          else raise Stream.Failure
      | _ -> raise Stream.Failure ]
  | ("V UIDENT", "") ->
      fun
      [ ("ANTIQUOT_LOC", prm) ->
          let kind = check_anti_loc2 prm in
          if kind = "auid" then "a" ^ prm
          else if kind = "uid" then "b" ^ prm
          else raise Stream.Failure
      | _ -> raise Stream.Failure ]
  | ("V STRING", "") ->
      fun
      [ ("ANTIQUOT_LOC", prm) ->
          let kind = check_anti_loc2 prm in
          if kind = "astr" then "a" ^ prm
          else if kind = "str" then "b" ^ prm
          else raise Stream.Failure
      | _ -> raise Stream.Failure ]
  | ("V CHAR", "") ->
      fun
      [ ("ANTIQUOT_LOC", prm) ->
          let kind = check_anti_loc2 prm in
          if kind = "achr" then "a" ^ prm
          else if kind = "chr" then "b" ^ prm
          else raise Stream.Failure
      | _ -> raise Stream.Failure ]
(*
  | ("V SELF", "") ->
      fun
      [ ("ANTIQUOT_LOC", prm) ->
          let kind = check_anti_loc2 prm in
          if kind = "" then prm else raise Stream.Failure
      | _ -> raise Stream.Failure ]
*)
  | ("V LIST", "") ->
      fun
      [ ("ANTIQUOT_LOC", prm) ->
          let kind = check_anti_loc2 prm in
          if kind = "alist" then "a" ^ prm
          else if kind = "list" then "b" ^ prm
          else raise Stream.Failure
      | _ -> raise Stream.Failure ]
(*
  | ("OPT", "") ->
      fun
      [ ("ANTIQUOT_LOC", prm) -> check_and_make_anti prm "opt"
      | _ -> raise Stream.Failure ]
*)
  | ("V FLAG", "") ->
      fun
      [ ("ANTIQUOT_LOC", prm) ->
          let kind = check_anti_loc2 prm in
          if kind = "aflag" then "a" ^ prm
          else if kind = "flag" then "b" ^ prm
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
    apply_entry module_expr_eoi Meta.e_module_expr Meta.p_module_expr)]
;
