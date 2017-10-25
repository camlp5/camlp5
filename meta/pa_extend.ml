(* camlp5r *)
(* pa_extend.ml,v *)
(* Copyright (c) INRIA 2007-2017 *)

#load "pa_macro.cmo";
#load "pa_extend.cmo";
#load "q_MLast.cmo";

value split_ext = ref False;

Pcaml.add_option "-split_ext" (Arg.Set split_ext)
  "Split EXTEND by using functions.";

type loc = Ploc.t;

type a_entry 'e 'p =
  { ae_loc : loc;
    ae_name : (string * 'e);
    ae_pos : option 'e;
    ae_levels : list (a_level 'e 'p) }
and a_level 'e 'p =
  { al_loc : loc;
    al_label : option string;
    al_assoc : option 'e;
    al_rules : a_rules 'e 'p }
and a_rules 'e 'p =
  { au_loc : loc;
    au_rules : list (a_rule 'e 'p) }
and a_rule 'e 'p =
  { ar_loc : loc;
    ar_psymbols : list (a_psymbol 'e 'p);
    ar_action : option 'e }
and a_psymbol 'e 'p =
  { ap_loc : loc;
    ap_patt : option 'p;
    ap_symb : a_symbol 'e 'p }
and a_symbol 'e 'p =
  [ ASflag of loc and a_symbol 'e 'p
  | ASkeyw of loc and a_string 'e
  | ASlist of loc and lmin_len and a_symbol 'e 'p and
      option (a_symbol 'e 'p * bool)
  | ASnext of loc
  | ASnterm of loc and (string * 'e) and option string
  | ASopt of loc and a_symbol 'e 'p
  | ASfold of loc and string and string and 'e and 'e and a_symbol 'e 'p
      and option (a_symbol 'e 'p)
  | ASquot of loc and a_symbol 'e 'p
  | ASrules of loc and a_rules 'e 'p
  | ASself of loc
  | AScut of loc
  | AStok of loc and string and option (a_string 'e)
  | ASvala of loc and a_symbol 'e 'p and list string
  | ASvala2 of loc and a_symbol 'e 'p and list string
      and option (string * 'e) ]
and a_string 'e =
  [ ATstring of loc and string
  | ATexpr of loc and 'e ]
and lmin_len =
  [ LML_0 | LML_1 ]
;

type name 'e = { expr : 'e; tvar : string; loc : loc };

type styp =
  [ STlid of loc and string
  | STapp of loc and styp and styp
  | STquo of loc and string
  | STself of loc and string
  | STtyp of MLast.ctyp
  | STnone
  | STvala of loc and styp ]
;

type text 'e 'p =
  [ TXfacto of loc and text 'e 'p
  | TXmeta of loc and string and list (text 'e 'p) and 'e and styp
  | TXlist of loc and lmin_len and text 'e 'p and option (text 'e 'p * bool)
  | TXnext of loc
  | TXnterm of loc and name 'e and option string
  | TXopt of loc and text 'e 'p
  | TXflag of loc and text 'e 'p
  | TXrules of loc and string and list (rule 'e 'p)
  | TXself of loc
  | TXtok of loc and string and 'e
  | TXcut of loc
  | TXvala of loc and list string and text 'e 'p ]
and entry 'e 'p =
  { name : name 'e; pos : option 'e; levels : list (level 'e 'p) }
and level 'e 'p =
  { label : option string; assoc : option 'e; rules : list (rule 'e 'p) }
and rule 'e 'p = { prod : list (psymbol 'e 'p); action : option 'e }
and psymbol 'e 'p = { pattern : option 'p; symbol : symbol 'e 'p }
and symbol 'e 'p = { used : list string; text : text 'e 'p; styp : styp };

type used = [ Unused | UsedScanned | UsedNotScanned ];

value option_map f =
  fun
  [ Some x -> Some (f x)
  | None -> None ]
;

value mark_used modif ht n =
  try
    let rll = Hashtbl.find_all ht n in
    List.iter
      (fun (r, _) ->
         if r.val == Unused then do {
           r.val := UsedNotScanned;
           modif.val := True
         }
         else ())
      rll
  with
  [ Not_found -> () ]
;

value rec mark_symbol modif ht symb =
  List.iter (fun e -> mark_used modif ht e) symb.used
;

value check_use nl el = do {
  let ht = Hashtbl.create 301 in
  let modif = ref False in
  List.iter
    (fun e ->
       let u =
         match e.name.expr with
         [ <:expr< $lid:_$ >> -> Unused
         | _ -> UsedNotScanned ]
       in
       Hashtbl.add ht e.name.tvar (ref u, e))
    el;
  List.iter
    (fun n ->
       try
         let rll = Hashtbl.find_all ht n.tvar in
         List.iter (fun (r, _) -> r.val := UsedNotScanned) rll
       with _ -> ())
    nl;
  modif.val := True;
  while modif.val do {
    modif.val := False;
    Hashtbl.iter
      (fun s (r, e) ->
         if r.val = UsedNotScanned then do {
           r.val := UsedScanned;
           List.iter
             (fun level ->
                let rules = level.rules in
                List.iter
                  (fun rule ->
                     List.iter (fun ps -> mark_symbol modif ht ps.symbol)
                       rule.prod)
                  rules)
             e.levels
         }
         else ())
      ht
  };
  Hashtbl.iter
    (fun s (r, e) ->
       if r.val = Unused then
         Pcaml.warning.val e.name.loc ("Unused local entry \"" ^ s ^ "\"")
       else ())
    ht
};

value locate n = <:expr< $n.expr$ >>;

value new_type_var =
  let i = ref 0 in
  fun () -> do { incr i; "e__" ^ string_of_int i.val }
;

value used_of_rule_list rl =
  List.fold_left
    (fun nl r -> List.fold_left (fun nl s -> s.symbol.used @ nl) nl r.prod) []
    rl
;

value retype_rule_list_without_patterns loc rl =
  try
    List.map
      (fun
       [ {prod = [{pattern = None; symbol = s}]; action = None} ->
           {prod = [{pattern = Some <:patt< x >>; symbol = s}];
            action = Some <:expr< x >>}
       | {prod = []; action = Some _} as r -> r
       | _ -> raise Exit ])
      rl
  with
  [ Exit -> rl ]
;

value rec make_list loc f =
  fun
  [ [] -> <:expr< [] >>
  | [x :: l] -> <:expr< [ $f x$ :: $make_list loc f l$ ] >> ]
;

value quotify = ref False;
value meta_action = ref False;

module MetaAction =
  struct
    value not_impl f x =
      let desc =
        if Obj.is_block (Obj.repr x) then
          "tag = " ^ string_of_int (Obj.tag (Obj.repr x))
        else "int_val = " ^ string_of_int (Obj.magic x)
      in
      failwith ("pa_extend.ml: " ^ f ^ ", not impl: " ^ desc)
    ;
    value loc = Ploc.dummy;
    value mlist f l = make_list loc f l;
    value moption mf =
      fun
      [ None -> <:expr< None >>
      | Some x -> <:expr< Some $mf x$ >> ]
    ;
    value mbool =
      fun
      [ False -> <:expr< False >>
      | True -> <:expr< True >> ]
    ;
    value mstring s = <:expr< $str:s$ >>;
    value mstring_escaped s = <:expr< $str:String.escaped s$ >>;
    value mvala f s =
      IFNDEF STRICT THEN f s
      ELSE
        match s with
        [ Ploc.VaVal s -> <:expr< Ploc.VaVal $f s$ >>
        | _ -> assert False ]
      END
    ;
    value mloc = <:expr< Ploc.dummy >>;
    value rec mexpr =
      fun
      [ MLast.ExAcc loc e1 e2 ->
          <:expr< MLast.ExAcc $mloc$ $mexpr e1$ $mexpr e2$ >>
      | MLast.ExApp loc e1 e2 ->
          <:expr< MLast.ExApp $mloc$ $mexpr e1$ $mexpr e2$ >>
      | MLast.ExAsr loc e ->
          <:expr< MLast.ExAsr $mloc$ $mexpr e$ >>
      | MLast.ExChr loc s -> <:expr< MLast.ExChr $mloc$ $mvala mstring s$ >>
      | MLast.ExFun loc pwel ->
          <:expr< MLast.ExFun $mloc$ $mvala (mlist mpwe) pwel$ >>
      | MLast.ExIfe loc e1 e2 e3 ->
          <:expr< MLast.ExIfe $mloc$ $mexpr e1$ $mexpr e2$ $mexpr e3$ >>
      | MLast.ExInt loc s c ->
          <:expr< MLast.ExInt $mloc$ $mvala mstring s$ $str:c$ >>
      | MLast.ExFlo loc s -> <:expr< MLast.ExFlo $mloc$ $mvala mstring s$ >>
      | MLast.ExLet loc rf pel e ->
          let rf = mvala mbool rf in
          <:expr< MLast.ExLet $mloc$ $rf$ $mvala (mlist mpe) pel$ $mexpr e$ >>
      | MLast.ExLid loc s -> <:expr< MLast.ExLid $mloc$ $mvala mstring s$ >>
      | MLast.ExMat loc e pwel ->
          <:expr< MLast.ExMat $mloc$ $mexpr e$ $mvala (mlist mpwe) pwel$ >>
      | MLast.ExRec loc pel eo ->
          let pel = mvala (mlist mpe) pel in
          <:expr< MLast.ExRec $mloc$ $pel$ $moption mexpr eo$ >>
      | MLast.ExSeq loc el ->
          <:expr< MLast.ExSeq $mloc$ $mvala (mlist mexpr) el$ >>
      | MLast.ExSte loc e1 e2 ->
          <:expr< MLast.ExSte $mloc$ $mexpr e1$ $mexpr e2$ >>
      | MLast.ExStr loc s ->
          <:expr< MLast.ExStr $mloc$ $mvala mstring_escaped s$ >>
      | MLast.ExTry loc e pwel ->
          <:expr< MLast.ExTry $mloc$ $mexpr e$ $mvala (mlist mpwe) pwel$ >>
      | MLast.ExTup loc el ->
          <:expr< MLast.ExTup $mloc$ $mvala (mlist mexpr) el$ >>
      | MLast.ExTyc loc e t ->
          <:expr< MLast.ExTyc $mloc$ $mexpr e$ $mctyp t$ >>
      | MLast.ExUid loc s -> <:expr< MLast.ExUid $mloc$ $mvala mstring s$ >>
      | x -> not_impl "mexpr" x ]
    and mpatt =
      fun
      [ MLast.PaAcc loc p1 p2 ->
          <:expr< MLast.PaAcc $mloc$ $mpatt p1$ $mpatt p2$ >>
      | MLast.PaAny loc -> <:expr< MLast.PaAny $mloc$ >>
      | MLast.PaApp loc p1 p2 ->
          <:expr< MLast.PaApp $mloc$ $mpatt p1$ $mpatt p2$ >>
      | MLast.PaInt loc s c ->
          <:expr< MLast.PaInt $mloc$ $mvala mstring s$ $str:c$ >>
      | MLast.PaLid loc s -> <:expr< MLast.PaLid $mloc$ $mvala mstring s$ >>
      | MLast.PaOrp loc p1 p2 ->
          <:expr< MLast.PaOrp $mloc$ $mpatt p1$ $mpatt p2$ >>
      | MLast.PaStr loc s ->
          <:expr< MLast.PaStr $mloc$ $mvala mstring_escaped s$ >>
      | MLast.PaTup loc pl ->
          <:expr< MLast.PaTup $mloc$ $mvala (mlist mpatt) pl$ >>
      | MLast.PaTyc loc p t ->
          <:expr< MLast.PaTyc $mloc$ $mpatt p$ $mctyp t$ >>
      | MLast.PaUid loc s -> <:expr< MLast.PaUid $mloc$ $mvala mstring s$ >>
      | x -> not_impl "mpatt" x ]
    and mctyp =
      fun
      [ MLast.TyAcc loc t1 t2 ->
          <:expr< MLast.TyAcc $mloc$ $mctyp t1$ $mctyp t2$ >>
      | MLast.TyApp loc t1 t2 ->
          <:expr< MLast.TyApp $mloc$ $mctyp t1$ $mctyp t2$ >>
      | MLast.TyLid loc s -> <:expr< MLast.TyLid $mloc$ $mvala mstring s$ >>
      | MLast.TyQuo loc s -> <:expr< MLast.TyQuo $mloc$ $mvala mstring s$ >>
      | MLast.TyTup loc tl ->
          <:expr< MLast.TyTup $mloc$ $mvala (mlist mctyp) tl$ >>
      | MLast.TyUid loc s -> <:expr< MLast.TyUid $mloc$ $mvala mstring s$ >>
      | x -> not_impl "mctyp" x ]
    and mpe (p, e) = <:expr< ($mpatt p$, $mexpr e$) >>
    and mpwe (p, w, e) =
      <:expr< ($mpatt p$, $mvala (moption mexpr) w$, $mexpr e$) >>;
  end
;

value mklistexp loc =
  loop True where rec loop top =
    fun
    [ [] -> <:expr< [] >>
    | [e1 :: el] ->
        let loc =
          if top then loc else Ploc.encl (MLast.loc_of_expr e1) loc
        in
        <:expr< [$e1$ :: $loop False el$] >> ]
;

value mklistpat loc =
  loop True where rec loop top =
    fun
    [ [] -> <:patt< [] >>
    | [p1 :: pl] ->
        let loc =
          if top then loc else Ploc.encl (MLast.loc_of_patt p1) loc
        in
        <:patt< [$p1$ :: $loop False pl$] >> ]
;

value rec expr_fa al =
  fun
  [ <:expr< $f$ $a$ >> -> expr_fa [a :: al] f
  | f -> (f, al) ]
;

value assoc_anti = [("ANTIQUOT_LOC", "ANTIQUOT")];

value anti_str psl =
  match psl with
  [ [{symbol = {text = TXtok _ x <:expr< $str:s$ >>}}] ->
      if List.exists (fun (_, y) -> x = y) assoc_anti then s else ""
  | _ -> "" ]
;

value anti_anti n =
  if n <> "" && (n.[0] = '~' || n.[0] = '?') then
    String.make 1 n.[0] ^ "_" ^ String.sub n 1 (String.length n - 1)
  else "_" ^ n
;

value is_anti_anti n =
  n <> "" && n.[0] = '_' ||
  String.length n > 1 && (n.[0] = '~' || n.[0] = '?') && n.[1] = '_'
;

value anti_of_tok =
  fun
  [ "CHAR" -> ["chr"]
  | "FLOAT" -> ["flo"]
  | "INT" -> ["int"]
  | "INT_l" -> ["int32"]
  | "INT_L" -> ["int64"]
  | "INT_n" -> ["nativeint"]
  | "LIDENT" -> ["lid"; ""]
  | "QUESTIONIDENT" -> ["?"]
  | "QUESTIONIDENTCOLON" -> ["?:"]
  | "STRING" -> ["str"]
  | "TILDEIDENT" -> ["~"]
  | "TILDEIDENTCOLON" -> ["~:"]
  | "UIDENT" -> ["uid"; ""]
  | s -> [] ]
;

value is_not_translated_function f =
  f = "warning_deprecated_since_6_00"
;

value quot_expr psl e =
  loop e where rec loop e =
    let loc = MLast.loc_of_expr e in
    match e with
    [ <:expr< None >> -> <:expr< Qast.Option None >>
    | <:expr< Some $e$ >> -> <:expr< Qast.Option (Some $loop e$) >>
    | <:expr< False >> -> <:expr< Qast.Bool False >>
    | <:expr< True >> -> <:expr< Qast.Bool True >>
    | <:expr< Ploc.VaAnt $e$ >> ->
        let s = anti_str psl in
        let e = <:expr< Qast.VaAnt $str:s$ loc $loop e$ >> in
        if is_anti_anti s then e else <:expr< Qast.VaVal $e$ >>
    | <:expr< Ploc.VaVal $e$ >> -> <:expr< Qast.VaVal $loop e$ >>
    | <:expr< () >> -> e
    | <:expr< Qast.Bool $_$ >> -> e
    | <:expr< Qast.List $_$ >> -> e
    | <:expr< Qast.Option $_$ >> -> e
    | <:expr< Qast.Str $_$ >> -> e
    | <:expr< Qast.VaAnt $_$ $_$ $_$ >> -> e
    | <:expr< Qast.VaVal $_$ >> -> e
    | <:expr< [] >> -> <:expr< Qast.List [] >>
    | <:expr< [$e$] >> -> <:expr< Qast.List [$loop e$] >>
    | <:expr< [$e1$ :: $e2$] >> -> <:expr< Qast.Cons $loop e1$ $loop e2$ >>
    | <:expr< $_$ $_$ >> ->
        let (f, al) = expr_fa [] e in
        match f with
        [ <:expr< $uid:c$ >> ->
            let al = List.map loop al in
            <:expr< Qast.Node $str:c$ $mklistexp loc al$ >>
        | <:expr< MLast.$uid:c$ >> ->
            let al = List.map loop al in
            <:expr< Qast.Node $str:c$ $mklistexp loc al$ >>
        | <:expr< $uid:m$.$uid:c$ >> ->
            let al = List.map loop al in
            <:expr< Qast.Node $str:m ^ "." ^ c$ $mklistexp loc al$ >>
        | <:expr< $lid:f$ >> ->
            if is_not_translated_function f then e
            else
              let al = List.map loop al in
              List.fold_left (fun f e -> <:expr< $f$ $e$ >>)
                <:expr< $lid:f$ >> al
        | _ -> e ]
    | <:expr< {$list:pel$} >> ->
        try
          let lel =
            List.map
              (fun (p, e) ->
                 let lab =
                   match p with
                   [ <:patt< $lid:c$ >> -> <:expr< $str:c$ >>
                   | <:patt< $_$.$lid:c$ >> -> <:expr< $str:c$ >>
                   | _ -> raise Not_found ]
                 in
                 <:expr< ($lab$, $loop e$) >>)
              pel
          in
          <:expr< Qast.Record $mklistexp loc lel$>>
        with
        [ Not_found -> e ]
    | <:expr< $lid:s$ >> ->
        if s = Ploc.name.val then <:expr< Qast.Loc >> else e
    | <:expr< MLast.$uid:s$ >> -> <:expr< Qast.Node $str:s$ [] >>
    | <:expr< $uid:m$.$uid:s$ >> -> <:expr< Qast.Node $str:m ^ "." ^ s$ [] >>
    | <:expr< $uid:s$ >> -> <:expr< Qast.Node $str:s$ [] >>
    | <:expr< $str:s$ >> -> <:expr< Qast.Str $str:s$ >>
    | <:expr< ($list:el$) >> ->
        let el = List.map loop el in
        <:expr< Qast.Tuple $mklistexp loc el$ >>
    | <:expr< let $flag:r$ $list:pel$ in $e$ >> ->
        let pel = List.map (fun (p, e) -> (p, loop e)) pel in
        <:expr< let $flag:r$ $list:pel$ in $loop e$ >>
    | _ -> e ]
;

value symgen = "xx";

value pname_of_ptuple pl =
  List.fold_left
    (fun pname p ->
       match p with
       [ <:patt< $lid:s$ >> -> pname ^ s
       | _ -> pname ])
    "" pl
;

value quotify_action psl act =
  let e = quot_expr psl act in
  List.fold_left
    (fun e ps ->
       match ps.pattern with
       [ Some <:patt< ($list:pl$) >> ->
           let loc = Ploc.dummy in
           let pname = pname_of_ptuple pl in
           let (pl1, el1) =
             let (l, _) =
               List.fold_left
                 (fun (l, cnt) _ ->
                    ([symgen ^ string_of_int cnt :: l], cnt + 1))
                 ([], 1) pl
             in
             let l = List.rev l in
             (List.map (fun s -> <:patt< $lid:s$ >>) l,
              List.map (fun s -> <:expr< $lid:s$ >>) l)
           in
           <:expr<
              let ($list:pl$) =
                match $lid:pname$ with
                [ Qast.Tuple $mklistpat loc pl1$ -> ($list:el1$)
                | _ -> match () with [] ]
              in $e$ >>
       | _ -> e ])
    e psl
;

value rec make_ctyp styp tvar =
  match styp with
  [ STlid loc s -> <:ctyp< $lid:s$ >>
  | STapp loc t1 t2 -> <:ctyp< $make_ctyp t1 tvar$ $make_ctyp t2 tvar$ >>
  | STquo loc s -> <:ctyp< '$s$ >>
  | STself loc x ->
      if tvar = "" then
        Ploc.raise loc
          (Stream.Error ("'" ^ x ^ "' illegal in anonymous entry level"))
      else <:ctyp< '$tvar$ >>
  | STtyp t -> t
  | STnone -> failwith "make_ctyp: internal error"
  | STvala loc t -> <:ctyp< Ploc.vala $make_ctyp t tvar$ >> ]
;

value text_of_action loc psl rtvar act tvar =
  let locid = <:patt< $lid:Ploc.name.val$ >> in
  let act =
    match act with
    [ Some act -> if quotify.val then quotify_action psl act else act
    | None -> <:expr< () >> ]
  in
  let e = <:expr< fun [ ($locid$ : Ploc.t) -> ($act$ : '$rtvar$) ] >> in
  let txt =
    List.fold_left
      (fun txt ps ->
         match ps.symbol.styp with
         | STnone -> txt
         | st ->
             match ps.pattern with
             [ None -> <:expr< fun _ -> $txt$ >>
             | Some p ->
                 let t = make_ctyp st tvar in
                 let p =
                   match p with
                   [ <:patt< ($list:pl$) >> when quotify.val ->
                       <:patt< $lid:pname_of_ptuple pl$ >>
                   | _ -> p ]
                 in
                 <:expr< fun ($p$ : $t$) -> $txt$ >> ]
             end)
      e psl
  in
  let txt =
    if meta_action.val then <:expr< Obj.magic $MetaAction.mexpr txt$ >>
    else txt
  in
  <:expr< $txt$ >>
;

value srules loc t rl tvar =
  List.map
    (fun r ->
       let sl = List.map (fun ps -> ps.symbol.text) r.prod in
       let ac = text_of_action loc r.prod t r.action tvar in
       (sl, ac))
    rl
;

value is_cut =
  fun
  [ TXcut _ -> True
  | _ -> False ]
;

value rec make_expr gmod tvar =
  fun
  [ TXfacto loc t -> <:expr< $uid:gmod$.s_facto $make_expr gmod tvar t$ >>
  | TXmeta loc n tl e t ->
      let el =
        List.fold_right
          (fun t el -> <:expr< [$make_expr gmod "" t$ :: $el$] >>) tl
          <:expr< [] >>
      in
      <:expr<
        $uid:gmod$.s_meta $str:n$ $el$ (Obj.repr ($e$ : $make_ctyp t tvar$)) >>
  | TXlist loc min t ts ->
      let txt = make_expr gmod "" t in
      match (min, ts) with
      [ (LML_0, None) -> <:expr< $uid:gmod$.s_list0 $txt$ >>
      | (LML_1, None) -> <:expr< $uid:gmod$.s_list1 $txt$ >>
      | (LML_0, Some (s, b)) ->
          let x = make_expr gmod tvar s in
          let b = if b then <:expr< True >> else <:expr< False >> in
          <:expr< $uid:gmod$.s_list0sep $txt$ $x$ $b$ >>
      | (LML_1, Some (s, b)) ->
          let x = make_expr gmod tvar s in
          let b = if b then <:expr< True >> else <:expr< False >> in
          <:expr< $uid:gmod$.s_list1sep $txt$ $x$ $b$ >> ]
  | TXnext loc -> <:expr< $uid:gmod$.s_next >>
  | TXnterm loc n lev ->
      match lev with
      [ Some lab ->
          <:expr<
             $uid:gmod$.s_nterml
               ($n.expr$ : $uid:gmod$.Entry.e '$n.tvar$)
               $str:lab$ >>
      | None ->
          if n.tvar = tvar then <:expr< $uid:gmod$.s_self >>
          else
            <:expr<
               $uid:gmod$.s_nterm
                 ($n.expr$ : $uid:gmod$.Entry.e '$n.tvar$) >> ]
  | TXopt loc t -> <:expr< $uid:gmod$.s_opt $make_expr gmod "" t$ >>
  | TXflag loc t -> <:expr< $uid:gmod$.s_flag $make_expr gmod "" t$ >>
  | TXrules loc s rl ->
      let rl = srules loc s rl "" in
      <:expr< $uid:gmod$.s_rules $make_expr_rules loc gmod rl ""$ >>
  | TXself loc -> <:expr< $uid:gmod$.s_self >>
  | TXcut loc -> assert False
  | TXtok loc s e -> <:expr< $uid:gmod$.s_token ($str:s$, $e$) >>
  | TXvala loc al t ->
      let al = make_list loc (fun s -> <:expr< $str:s$ >>) al in
      <:expr< $uid:gmod$.s_vala $al$ $make_expr gmod "" t$ >> ]
and make_expr_rules loc gmod rl tvar =
  List.fold_left
    (fun txt (sl, ac) ->
       let sl =
         List.fold_left
           (fun txt t ->
              if is_cut t then <:expr< $uid:gmod$.r_cut $txt$ >>
              else
                let x = make_expr gmod tvar t in
                <:expr< $uid:gmod$.r_next $txt$ $x$ >>)
           <:expr< $uid:gmod$.r_stop >> sl
       in
       <:expr< [$uid:gmod$.production ($sl$, $ac$) :: $txt$] >>)
    <:expr< [] >> rl
;

value rec ident_of_expr =
  fun
  [ <:expr< $lid:s$ >> -> s
  | <:expr< $uid:s$ >> -> s
  | <:expr< $e1$ . $e2$ >> -> ident_of_expr e1 ^ "__" ^ ident_of_expr e2
  | _ -> failwith "internal error in pa_extend" ]
;

value mk_name loc e = {expr = e; tvar = ident_of_expr e; loc = loc};
value mk_name2 (i, e) =
  let loc = MLast.loc_of_expr e in
  {expr = e; tvar = i; loc = loc}
;

value slist loc min sep symb =
  let t =
    match sep with
    [ Some (s, b) -> Some (s.text, b)
    | None -> None ]
  in
  TXlist loc min symb.text t
;

value sfold loc n foldfun f e s =
  let styp = STquo loc (new_type_var ()) in
  let e = <:expr< Extfold.$lid:foldfun$ $f$ $e$ >> in
  let t = STapp loc (STapp loc (STtyp <:ctyp< Extfold.t _ >>) s.styp) styp in
  {used = s.used; text = TXmeta loc n [s.text] e t; styp = styp}
;

value sfoldsep loc n foldfun f e s sep =
  let styp = STquo loc (new_type_var ()) in
  let e = <:expr< Extfold.$lid:foldfun$ $f$ $e$ >> in
  let t =
    STapp loc (STapp loc (STtyp <:ctyp< Extfold.tsep _ >>) s.styp) styp
  in
  {used = s.used @ sep.used; text = TXmeta loc n [s.text; sep.text] e t;
   styp = styp}
;

value mk_psymbol p s t =
  let symb = {used = []; text = s; styp = t} in
  {pattern = Some p; symbol = symb}
;

value ss2 loc ls oe s =
  let qast_f a =
    match s.styp with
    [ STlid loc "bool" -> <:expr< Qast.Bool $a$ >>
    | STlid loc "string" -> <:expr< Qast.Str $a$ >>
    | STapp loc (STlid _ "list") t ->
        let a =
          match t with
          [ STlid _ "string" -> <:expr< List.map (fun a -> Qast.Str a) $a$ >>
          | _ -> a ]
        in
        <:expr< Qast.List $a$ >>
    | STapp loc (STlid _ "option") t -> <:expr< Qast.Option $a$ >>
    | STquo _ _ -> a
    | t -> MetaAction.not_impl "ss2" s.styp ]
  in
  let t = new_type_var () in
  let text =
    let rl =
      match oe with
      [ Some (i, e) ->
          let r =
            let ps =
              let text =
                let name = mk_name2 (i, e) in
                TXnterm loc name None
              in
              let styp = STquo loc i in
              let s = {used = []; text = text; styp = styp} in
              {pattern = Some <:patt< a >>; symbol = s}
            in
            let act = <:expr< a >> in
            {prod = [ps]; action = Some act}
          in
          [r]
      | None -> [] ]
    in
    let rl =
      let r2 =
        let ps = {pattern = Some <:patt< a >>; symbol = s} in
        let act = <:expr< Qast.VaVal $qast_f <:expr< a >>$>> in
        {prod = [ps]; action = Some act}
      in
      [r2 :: rl]
    in
    let rl =
      List.fold_right
        (fun a rl ->
           let r1 =
             let ps =
               let text = TXtok loc "ANTIQUOT" <:expr< $str:a$ >> in
               let styp = STlid loc "string" in
               let s = {used = []; text = text; styp = styp} in
               {pattern = Some <:patt< a >>; symbol = s}
             in
             let act = <:expr< Qast.VaVal (Qast.VaAnt $str:a$ loc a) >> in
             {prod = [ps]; action = Some act}
           in
           let r2 =
             let a = anti_anti a in
             let ps =
               let text = TXtok loc "ANTIQUOT" <:expr< $str:a$ >> in
               let styp = STlid loc "string" in
               let s = {used = []; text = text; styp = styp} in
               {pattern = Some <:patt< a >>; symbol = s}
             in
             let act = <:expr< Qast.VaAnt $str:a$ loc a >> in
             {prod = [ps]; action = Some act}
           in
           [r1; r2 :: rl])
        ls rl
    in
    TXfacto loc (TXrules loc t rl)
  in
  let used =
    match oe with
    [ Some e -> [fst e :: s.used]
    | None -> s.used ]
  in
  {used = used; text = text; styp = STquo loc t}
;

value string_of_a =
  fun
  [ ATstring loc s -> <:expr< $str:s$ >>
  | ATexpr _ e -> e ]
;

value rec symbol_of_a =
  fun
  [ ASflag loc s ->
      let s = symbol_of_a s in
      let text = TXflag loc s.text in
      let styp = STlid loc "bool" in
      {used = s.used; text = text; styp = styp}
  | ASfold loc n foldfun f e s sep ->
      let s = symbol_of_a s in
      match sep with
      [ Some sep -> sfoldsep loc n foldfun f e s (symbol_of_a sep)
      | None -> sfold loc n foldfun f e s ]
  | ASkeyw loc s ->
      let text = TXtok loc "" (string_of_a s) in
      {used = []; text = text; styp = STlid loc "string"}
  | ASlist loc min s sep ->
      let s = symbol_of_a s in
      let sep = option_map (fun (sep, b) -> (symbol_of_a sep, b)) sep in
      let used =
        match sep with
        [ Some (symb, _) -> symb.used @ s.used
        | None -> s.used ]
      in
      let text = slist loc min sep s in
      let styp = STapp loc (STlid loc "list") s.styp in
      {used = used; text = text; styp = styp}
  | ASnext loc -> {used = []; text = TXnext loc; styp = STself loc "NEXT"}
  | ASnterm loc (i, n) lev ->
      let name = mk_name2 (i, n) in
      let text = TXnterm loc name lev in
      let styp = STquo loc i in
      {used = [i]; text = text; styp = styp}
  | ASopt loc s ->
      let s = symbol_of_a s in
      let text = TXopt loc s.text in
      let styp = STapp loc (STlid loc "option") s.styp in
      {used = s.used; text = text; styp = styp}
  | ASquot loc s -> symbol_of_a s
  | ASrules loc rl ->
      let rl = rules_of_a rl in
      let t = new_type_var () in
      {used = used_of_rule_list rl; text = TXrules loc t rl;
       styp = STquo loc t}
  | ASself loc ->
      {used = []; text = TXself loc; styp = STself loc "SELF"}
  | AScut loc ->
      {used = []; text = TXcut loc; styp = STnone}
  | AStok loc s p ->
      let e =
        match p with
        [ Some e -> string_of_a e
        | None -> <:expr< "" >> ]
      in
      let text = TXtok loc s e in
      {used = []; text = text; styp = STlid loc "string"}
  | ASvala loc s ls ->
      if quotify.val then
        match s with
        [ AStok _ _ (Some _) -> symbol_of_a s
        | _ ->
            let ls =
              if ls = [] then
                match s with
                [ ASflag _ _ -> ["flag"; "opt"]
                | ASlist _ _ _ _ -> ["list"]
                | ASopt _ _ -> ["opt"]
                | AStok _ s _ -> anti_of_tok s
                | _ -> [] ]
              else ls
            in
            let oe =
              match s with
              [ AStok _ s _ ->
                  match s with
                  [ "QUESTIONIDENT" -> Some ("a_qi", <:expr< a_qi >>)
                  | "QUESTIONIDENTCOLON" -> Some ("a_qic", <:expr< a_qic >>)
                  | "TILDEIDENT" -> Some ("a_ti", <:expr< a_ti >>)
                  | "TILDEIDENTCOLON" -> Some ("a_tic", <:expr< a_tic >>)
                  | _ -> None ]
              | _ -> None ]
            in
            let s = Ploc.call_with quotify False symbol_of_a s in
            ss2 loc ls oe s ]
      else
        let s = symbol_of_a s in
        let (text, styp) =
          if not Pcaml.strict_mode.val then (s.text, s.styp)
          else (TXvala loc ls s.text, STvala loc s.styp)
        in
        {used = s.used; text = text; styp = styp}
  | ASvala2 loc s ls oe ->
      match s with
      [ AStok _ _ (Some _) -> symbol_of_a s
      | s ->
          let ls =
            if ls = [] then
              match s with
              [ ASflag _ _ -> ["flag"; "opt"]
              | ASlist _ _ _ _ -> ["list"]
              | ASopt _ _ -> ["opt"]
              | AStok _ s _ -> anti_of_tok s
              | _ -> [] ]
            else ls
          in
          let s = symbol_of_a s in
          ss2 loc ls oe s ] ]
and psymbol_of_a ap =
  {pattern = ap.ap_patt; symbol = symbol_of_a ap.ap_symb}
and rules_of_a au =
  let rl = List.map rule_of_a au.au_rules in
  retype_rule_list_without_patterns au.au_loc rl
and rule_of_a ar =
  {prod = List.map psymbol_of_a ar.ar_psymbols; action = ar.ar_action}
;

value level_of_a alv =
  let rl = rules_of_a alv.al_rules in
  {label = alv.al_label; assoc = alv.al_assoc; rules = rl}
;

value entry_of_a ae =
  {name = mk_name2 ae.ae_name; pos = ae.ae_pos;
   levels = List.map level_of_a ae.ae_levels}
;

value expr_of_delete_rule loc gmod n sl =
  let n = mk_name2 n in
  let sl = List.map symbol_of_a sl in
  let sl =
    List.fold_left
      (fun e s ->
        if is_cut s.text then <:expr< $uid:gmod$.r_cut $e$ >>
        else <:expr< $uid:gmod$.r_next $e$ $make_expr gmod "" s.text$ >>)
      <:expr< $uid:gmod$.r_stop >> sl
  in
  (<:expr< $n.expr$ >>, sl)
;

value text_of_entry loc gmod e =
  let ent =
    let x = e.name in
    let loc = e.name.loc in
    <:expr< ($x.expr$ : $uid:gmod$.Entry.e '$x.tvar$) >>
  in
  let loc = Ploc.with_comment loc "" in
  let pos =
    match e.pos with
    [ Some pos -> <:expr< Some $pos$ >>
    | None -> <:expr< None >> ]
  in
  let txt =
    List.fold_right
      (fun level txt ->
         let lab =
           match level.label with
           [ Some lab -> <:expr< Some $str:lab$ >>
           | None -> <:expr< None >> ]
         in
         let ass =
           match level.assoc with
           [ Some ass -> <:expr< Some $ass$ >>
           | None -> <:expr< None >> ]
         in
         let txt =
           let rl = srules loc e.name.tvar level.rules e.name.tvar in
           let e = make_expr_rules loc gmod rl e.name.tvar in
           <:expr< [($lab$, $ass$, $e$) :: $txt$] >>
         in
         txt)
      e.levels <:expr< [] >>
  in
  (ent, pos, txt)
;

value let_in_of_extend loc gmod functor_version gl el args =
  match gl with
  [ Some ([n1 :: _] as nl) -> do {
      check_use nl el;
      let ll =
        let same_tvar e n = e.name.tvar = n.tvar in
        List.fold_right
          (fun e ll ->
             match e.name.expr with
             [ <:expr< $lid:_$ >> ->
                 if List.exists (same_tvar e) nl then ll
                 else if List.exists (same_tvar e) ll then ll
                 else [e.name :: ll]
             | _ -> ll ])
          el []
      in
      let globals =
        List.map
          (fun {expr = e; tvar = x; loc = loc} ->
             (<:patt< _ >>, <:expr< ($e$ : $uid:gmod$.Entry.e '$x$) >>))
          nl
      in
      let locals =
        List.map
          (fun {expr = e; tvar = x; loc = loc} ->
             let i =
               match e with
               [ <:expr< $lid:i$ >> -> i
               | _ -> failwith "internal error in pa_extend" ]
             in
             (<:patt< $lid:i$ >>,
              <:expr<
                (grammar_entry_create $str:i$ : $uid:gmod$.Entry.e '$x$)
              >>))
          ll
      in
      let e =
        if ll = [] then args
        else if functor_version then
          <:expr<
            let grammar_entry_create = $uid:gmod$.Entry.create in
            let $list:locals$ in $args$ >>
        else
          <:expr<
            let grammar_entry_create s =
              $uid:gmod$.create_local_entry ($uid:gmod$.of_entry $locate n1$)
                s
            in
            let $list:locals$ in $args$ >>
      in
      <:expr< let $list:globals$ in $e$ >>
    }
  | _ -> args ]
;

value text_of_extend loc gmod gl el f =
  let el = List.map entry_of_a el in
  let gl = option_map (List.map mk_name2) gl in
  let iloc = Ploc.with_comment loc "" in
  if split_ext.val then
    let args =
      let loc = iloc in
      List.map
        (fun e ->
           let (ent, pos, txt) = text_of_entry e.name.loc gmod e in
           let e = <:expr< ($ent$, $pos$, $txt$) >> in
           <:expr< let aux () = $f$ [$e$] in aux () >>)
        el
    in
    let args =
      let loc = iloc in
      <:expr< do { $list:args$ } >>
    in
    let_in_of_extend loc gmod False gl el args
  else
    let args =
      let loc = iloc in
      List.fold_right
        (fun e el ->
           let (ent, pos, txt) = text_of_entry e.name.loc gmod e in
           let e =
             let loc = e.name.loc in
             <:expr< $uid:gmod$.extension $ent$ $pos$ $txt$ >>
           in
           <:expr< [$e$ :: $el$] >>)
        el <:expr< [] >>
    in
    let args = let_in_of_extend iloc gmod False gl el args in
    <:expr< $f$ $args$ >>
;

value text_of_functorial_extend loc gmod gl el =
  let el = List.map entry_of_a el in
  let gl = option_map (List.map mk_name2) gl in
  let args =
    let el =
      List.map
        (fun e ->
           let (ent, pos, txt) = text_of_entry e.name.loc gmod e in
           let e = <:expr< $uid:gmod$.safe_extend $ent$ $pos$ $txt$ >> in
           if split_ext.val then <:expr< let aux () = $e$ in aux () >> else e)
        el
    in
    match el with
    [ [e] -> e
    | _ -> <:expr< do { $list:el$ } >> ]
  in
  let_in_of_extend loc gmod True gl el args
;

open Pcaml;
value symbol = Grammar.Entry.create gram "symbol";
value semi_sep =
  if syntax_name.val = "Scheme" then
    Grammar.Entry.of_parser gram "'/'" (parser [: `("", "/") :] -> ())
  else
    Grammar.Entry.of_parser gram "';'" (parser [: `("", ";") :] -> ())
;

EXTEND
  GLOBAL: expr symbol;
  expr: AFTER "top"
    [ [ "EXTEND"; /; e = extend_body; "END" -> e
      | "GEXTEND"; /; e = gextend_body; "END" -> e
      | "DELETE_RULE"; /; e = delete_rule_body; "END" -> e
      | "GDELETE_RULE"; /; e = gdelete_rule_body; "END" -> e ] ]
  ;
  extend_body:
    [ [ f = efunction; sl = OPT global;
        el = LIST1 [ e = entry; semi_sep -> e ] ->
          text_of_extend loc "Grammar" sl el f ] ]
  ;
  gextend_body:
    [ [ g = UIDENT; sl = OPT global;
        el = LIST1 [ e = entry; semi_sep -> e ] ->
          text_of_functorial_extend loc g sl el ] ]
  ;
  delete_rule_body:
    [ [ n = name; ":"; sl = LIST1 symbol SEP semi_sep ->
          let (e, b) = expr_of_delete_rule loc "Grammar" n sl in
          <:expr< Grammar.safe_delete_rule $e$ $b$ >> ] ]
  ;
  gdelete_rule_body:
    [ [ g = UIDENT; n = name; ":"; sl = LIST1 symbol SEP semi_sep ->
          let (e, b) = expr_of_delete_rule loc g n sl in
          <:expr< $uid:g$.safe_delete_rule $e$ $b$ >> ] ]
  ;
  efunction:
    [ [ UIDENT "FUNCTION"; ":"; f = qualid; semi_sep -> snd f
      | -> <:expr< Grammar.safe_extend >> ] ]
  ;
  global:
    [ [ UIDENT "GLOBAL"; ":"; sl = LIST1 name; semi_sep -> sl ] ]
  ;
  entry:
    [ [ n = name; ":"; pos = OPT position; ll = level_list ->
          {ae_loc = loc; ae_name = n; ae_pos = pos; ae_levels = ll} ] ]
  ;
  position:
    [ [ UIDENT "FIRST" -> <:expr< Gramext.First >>
      | UIDENT "LAST" -> <:expr< Gramext.Last >>
      | UIDENT "BEFORE"; n = string ->
          <:expr< Gramext.Before $string_of_a n$ >>
      | UIDENT "AFTER"; n = string ->
          <:expr< Gramext.After $string_of_a n$ >>
      | UIDENT "LIKE"; n = string ->
          <:expr< Gramext.Like $string_of_a n$ >>
      | UIDENT "LEVEL"; n = string ->
          <:expr< Gramext.Level $string_of_a n$ >> ] ]
  ;
  level_list:
    [ [ "["; ll = LIST0 level SEP "|"; "]" -> ll ] ]
  ;
  level:
    [ [ lab = OPT STRING; ass = OPT assoc; rules = rule_list ->
          {al_loc = loc; al_label = lab; al_assoc = ass; al_rules = rules} ] ]
  ;
  assoc:
    [ [ UIDENT "LEFTA" -> <:expr< Gramext.LeftA >>
      | UIDENT "RIGHTA" -> <:expr< Gramext.RightA >>
      | UIDENT "NONA" -> <:expr< Gramext.NonA >> ] ]
  ;
  rule_list:
    [ [ "["; "]" -> {au_loc = loc; au_rules = []}
      | "["; rules = LIST1 rule SEP "|"; "]" ->
          {au_loc = loc; au_rules = rules} ] ]
  ;
  rule:
    [ [ psl = LIST0 psymbol SEP semi_sep; "->"; act = expr ->
          {ar_loc = loc; ar_psymbols = psl; ar_action = Some act}
      | psl = LIST0 psymbol SEP semi_sep ->
          {ar_loc = loc; ar_psymbols = psl; ar_action = None} ] ]
  ;
  psymbol:
    [ [ p = LIDENT; "="; s = symbol ->
          {ap_loc = loc; ap_patt = Some <:patt< $lid:p$ >>; ap_symb = s}
      | i = LIDENT; lev = OPT [ UIDENT "LEVEL"; s = STRING -> s ] ->
          let n = <:expr< $lid:i$ >> in
          {ap_loc = loc; ap_patt = None; ap_symb = ASnterm loc (i, n) lev}
      | p = pattern; "="; s = symbol ->
          {ap_loc = loc; ap_patt = Some p; ap_symb = s}
      | s = symbol ->
          {ap_loc = loc; ap_patt = None; ap_symb = s} ] ]
  ;
  sep_opt_sep:
    [ [ sep = UIDENT "SEP"; t = symbol; b = FLAG [ UIDENT "OPT_SEP" ] ->
          (t, b) ] ]
  ;
  symbol:
    [ "top" NONA
      [ UIDENT "LIST0"; s = SELF; sep = OPT sep_opt_sep ->
          ASlist loc LML_0 s sep
      | UIDENT "LIST1"; s = SELF; sep = OPT sep_opt_sep ->
          ASlist loc LML_1 s sep
      | UIDENT "OPT"; s = SELF ->
          ASopt loc s
      | UIDENT "FLAG"; s = SELF ->
          ASflag loc s ]
    | "vala"
      [ UIDENT "V"; UIDENT "SELF"; al = LIST0 STRING ->
          let s = ASself loc in
          ASvala loc s al
      | UIDENT "V"; UIDENT "NEXT"; al = LIST0 STRING ->
          let s = ASnext loc in
          ASvala loc s al
      | UIDENT "V"; x = UIDENT; al = LIST0 STRING ->
          let s = AStok loc x None in
          ASvala loc s al
      | UIDENT "V"; s = NEXT; al = LIST0 STRING ->
          ASvala loc s al ]
    | "simple"
      [ UIDENT "SELF" ->
          ASself loc
      | UIDENT "NEXT" ->
          ASnext loc
      | "["; rl = LIST0 rule SEP "|"; "]" ->
          ASrules loc {au_loc = loc; au_rules = rl}
      | x = UIDENT ->
          AStok loc x None
      | x = UIDENT; e = string ->
          AStok loc x (Some e)
      | e = string ->
          ASkeyw loc e
      | i = UIDENT; "."; e = qualid;
        lev = OPT [ UIDENT "LEVEL"; s = STRING -> s ] ->
          let v = <:expr< $uid:i$.$snd e$ >> in
          ASnterm loc (i ^ "__" ^ fst e, v) lev
      | n = name; lev = OPT [ UIDENT "LEVEL"; s = STRING -> s ] ->
          ASnterm loc n lev
      | "/" ->
          AScut loc
      | "("; s_t = SELF; ")" -> s_t ] ]
  ;
  pattern:
    [ [ i = LIDENT -> <:patt< $lid:i$ >>
      | "_" -> <:patt< _ >>
      | "("; p = SELF; ")" -> <:patt< $p$ >>
      | "("; p = SELF; ","; pl = patterns_comma; ")" ->
          <:patt< ( $list:[p :: pl]$ ) >> ] ]
  ;
  patterns_comma:
    [ [ pl = SELF; ","; p = pattern -> pl @ [p] ]
    | [ p = pattern -> [p] ] ]
  ;
  name:
    [ [ e = qualid -> e ] ]
  ;
  qualid:
    [ [ e1 = SELF; "."; e2 = SELF ->
          (fst e1 ^ "__" ^ fst e2, <:expr< $snd e1$ . $snd e2$ >>) ]
    | [ i = UIDENT ->
          (i, <:expr< $uid:i$ >>)
      | i = LIDENT ->
          (i, <:expr< $lid:i$ >>) ] ]
  ;
  string:
    [ [ s = STRING -> ATstring loc s
      | "$"; e = expr; "$" -> ATexpr loc e ] ]
  ;
END;

Pcaml.add_option "-quotify" (Arg.Set quotify) "Generate code for quotations";
Pcaml.add_option "-meta_action" (Arg.Set meta_action) "Undocumented";
