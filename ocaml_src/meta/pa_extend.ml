(* camlp5r *)
(* pa_extend.ml,v *)
(* Copyright (c) INRIA 2007-2017 *)

(* #load "pa_macro.cmo" *)
(* #load "pa_extend.cmo" *)
(* #load "q_MLast.cmo" *)

let split_ext = ref false;;

Pcaml.add_option "-split_ext" (Arg.Set split_ext)
  "Split EXTEND by using functions.";;

type loc = Ploc.t;;

type ('e, 'p) a_entry =
  { ae_loc : loc;
    ae_name : string * 'e;
    ae_pos : 'e option;
    ae_levels : ('e, 'p) a_level list }
and ('e, 'p) a_level =
  { al_loc : loc;
    al_label : string option;
    al_assoc : 'e option;
    al_rules : ('e, 'p) a_rules }
and ('e, 'p) a_rules = { au_loc : loc; au_rules : ('e, 'p) a_rule list }
and ('e, 'p) a_rule =
  { ar_loc : loc;
    ar_psymbols : ('e, 'p) a_psymbol list;
    ar_action : 'e option }
and ('e, 'p) a_psymbol =
  { ap_loc : loc; ap_patt : 'p option; ap_symb : ('e, 'p) a_symbol }
and ('e, 'p) a_symbol =
    ASflag of loc * ('e, 'p) a_symbol
  | ASkeyw of loc * 'e a_string
  | ASlist of
      loc * lmin_len * ('e, 'p) a_symbol * (('e, 'p) a_symbol * bool) option
  | ASnext of loc
  | ASnterm of loc * (string * 'e) * string option
  | ASopt of loc * ('e, 'p) a_symbol
  | ASquot of loc * ('e, 'p) a_symbol
  | ASrules of loc * ('e, 'p) a_rules
  | ASself of loc
  | AScut of loc
  | AStok of loc * string * 'e a_string option
  | ASvala of loc * ('e, 'p) a_symbol * string list
  | ASvala2 of loc * ('e, 'p) a_symbol * string list * (string * 'e) option
and 'e a_string =
    ATstring of loc * string
  | ATexpr of loc * 'e
and lmin_len = LML_0 | LML_1;;

type 'e name = { expr : 'e; tvar : string; loc : loc };;

type styp =
    STlid of loc * string
  | STapp of loc * styp * styp
  | STquo of loc * string
  | STself of loc * string
  | STtyp of MLast.ctyp
  | STnone
  | STvala of loc * styp
;;

type ('e, 'p) text =
    TXfacto of loc * ('e, 'p) text
  | TXlist of loc * lmin_len * ('e, 'p) text * (('e, 'p) text * bool) option
  | TXnext of loc
  | TXnterm of loc * 'e name * string option
  | TXopt of loc * ('e, 'p) text
  | TXflag of loc * ('e, 'p) text
  | TXrules of loc * string * ('e, 'p) rule list
  | TXself of loc
  | TXtok of loc * string * 'e
  | TXcut of loc
  | TXvala of loc * string list * ('e, 'p) text
and ('e, 'p) entry =
  { name : 'e name; pos : 'e option; levels : ('e, 'p) level list }
and ('e, 'p) level =
  { label : string option; assoc : 'e option; rules : ('e, 'p) rule list }
and ('e, 'p) rule = { prod : ('e, 'p) psymbol list; action : 'e option }
and ('e, 'p) psymbol = { pattern : 'p option; symbol : ('e, 'p) symbol }
and ('e, 'p) symbol =
  { used : string list; text : ('e, 'p) text; styp : styp }
;;

type used = Unused | UsedScanned | UsedNotScanned;;

let option_map f =
  function
    Some x -> Some (f x)
  | None -> None
;;

let mark_used modif ht n =
  try
    let rll = Hashtbl.find_all ht n in
    List.iter
      (fun (r, _) ->
         if !r == Unused then begin r := UsedNotScanned; modif := true end)
      rll
  with Not_found -> ()
;;

let rec mark_symbol modif ht symb =
  List.iter (fun e -> mark_used modif ht e) symb.used
;;

let check_use nl el =
  let ht = Hashtbl.create 301 in
  let modif = ref false in
  List.iter
    (fun e ->
       let u =
         match e.name.expr with
           MLast.ExLid (_, _) -> Unused
         | _ -> UsedNotScanned
       in
       Hashtbl.add ht e.name.tvar (ref u, e))
    el;
  List.iter
    (fun n ->
       try
         let rll = Hashtbl.find_all ht n.tvar in
         List.iter (fun (r, _) -> r := UsedNotScanned) rll
       with _ -> ())
    nl;
  modif := true;
  while !modif do
    modif := false;
    Hashtbl.iter
      (fun s (r, e) ->
         if !r = UsedNotScanned then
           begin
             r := UsedScanned;
             List.iter
               (fun level ->
                  let rules = level.rules in
                  List.iter
                    (fun rule ->
                       List.iter (fun ps -> mark_symbol modif ht ps.symbol)
                         rule.prod)
                    rules)
               e.levels
           end)
      ht
  done;
  Hashtbl.iter
    (fun s (r, e) ->
       if !r = Unused then
         !(Pcaml.warning) e.name.loc ("Unused local entry \"" ^ s ^ "\""))
    ht
;;

let locate n = n.expr;;

let new_type_var =
  let i = ref 0 in fun () -> incr i; "e__" ^ string_of_int !i
;;

let used_of_rule_list rl =
  List.fold_left
    (fun nl r -> List.fold_left (fun nl s -> s.symbol.used @ nl) nl r.prod) []
    rl
;;

let retype_rule_list_without_patterns loc rl =
  try
    List.map
      (function
         {prod = [{pattern = None; symbol = s}]; action = None} ->
           {prod = [{pattern = Some (MLast.PaLid (loc, "x")); symbol = s}];
            action = Some (MLast.ExLid (loc, "x"))}
       | {prod = []; action = Some _} as r -> r
       | _ -> raise Exit)
      rl
  with Exit -> rl
;;

let rec make_list loc f =
  function
    [] -> MLast.ExLong (loc, MLast.LiUid (loc, "[]"))
  | x :: l ->
      MLast.ExApp
        (loc,
         MLast.ExApp (loc, MLast.ExLong (loc, MLast.LiUid (loc, "::")), f x),
         make_list loc f l)
;;

let quotify = ref false;;
let meta_action = ref false;;

module MetaAction =
  struct
    let not_impl f x =
      let desc =
        if Obj.is_block (Obj.repr x) then
          "tag = " ^ string_of_int (Obj.tag (Obj.repr x))
        else "int_val = " ^ string_of_int (Obj.magic x)
      in
      failwith ("pa_extend.ml: " ^ f ^ ", not impl: " ^ desc)
    ;;
    let loc = Ploc.dummy;;
    let mlist f l = make_list loc f l;;
    let moption mf =
      function
        None -> MLast.ExLong (loc, MLast.LiUid (loc, "None"))
      | Some x ->
          MLast.ExApp
            (loc, MLast.ExLong (loc, MLast.LiUid (loc, "Some")), mf x)
    ;;
    let mbool =
      function
        false -> MLast.ExLong (loc, MLast.LiUid (loc, "False"))
      | true -> MLast.ExLong (loc, MLast.LiUid (loc, "True"))
    ;;
    let mstring s = MLast.ExStr (loc, s);;
    let mstring_escaped s = MLast.ExStr (loc, String.escaped s);;
    let mvala f s = f s;;
    let mloc =
      MLast.ExFle
        (loc, MLast.ExLong (loc, MLast.LiUid (loc, "Ploc")), (None, "dummy"))
    ;;
    let rec mexpr =
      function
        MLast.ExLong (loc, li) ->
          MLast.ExApp
            (loc,
             MLast.ExApp
               (loc,
                MLast.ExLong
                  (loc,
                   MLast.LiAcc (loc, MLast.LiUid (loc, "MLast"), "ExLong")),
                mloc),
             mlongid li)
      | MLast.ExOpen (loc, li, e) ->
          MLast.ExApp
            (loc,
             MLast.ExApp
               (loc,
                MLast.ExApp
                  (loc,
                   MLast.ExLong
                     (loc,
                      MLast.LiAcc
                        (loc, MLast.LiUid (loc, "MLast"), "ExOpen")),
                   mloc),
                mlongid li),
             mexpr e)
      | MLast.ExFle (loc, e, lili) ->
          MLast.ExApp
            (loc,
             MLast.ExApp
               (loc,
                MLast.ExApp
                  (loc,
                   MLast.ExLong
                     (loc,
                      MLast.LiAcc (loc, MLast.LiUid (loc, "MLast"), "ExFle")),
                   mloc),
                mexpr e),
             mvala mlongid_lident lili)
      | MLast.ExApp (loc, e1, e2) ->
          MLast.ExApp
            (loc,
             MLast.ExApp
               (loc,
                MLast.ExApp
                  (loc,
                   MLast.ExLong
                     (loc,
                      MLast.LiAcc (loc, MLast.LiUid (loc, "MLast"), "ExApp")),
                   mloc),
                mexpr e1),
             mexpr e2)
      | MLast.ExAsr (loc, e) ->
          MLast.ExApp
            (loc,
             MLast.ExApp
               (loc,
                MLast.ExLong
                  (loc,
                   MLast.LiAcc (loc, MLast.LiUid (loc, "MLast"), "ExAsr")),
                mloc),
             mexpr e)
      | MLast.ExChr (loc, s) ->
          MLast.ExApp
            (loc,
             MLast.ExApp
               (loc,
                MLast.ExLong
                  (loc,
                   MLast.LiAcc (loc, MLast.LiUid (loc, "MLast"), "ExChr")),
                mloc),
             mvala mstring s)
      | MLast.ExFun (loc, pwel) ->
          MLast.ExApp
            (loc,
             MLast.ExApp
               (loc,
                MLast.ExLong
                  (loc,
                   MLast.LiAcc (loc, MLast.LiUid (loc, "MLast"), "ExFun")),
                mloc),
             mvala (mlist mpwe) pwel)
      | MLast.ExIfe (loc, e1, e2, e3) ->
          MLast.ExApp
            (loc,
             MLast.ExApp
               (loc,
                MLast.ExApp
                  (loc,
                   MLast.ExApp
                     (loc,
                      MLast.ExLong
                        (loc,
                         MLast.LiAcc
                           (loc, MLast.LiUid (loc, "MLast"), "ExIfe")),
                      mloc),
                   mexpr e1),
                mexpr e2),
             mexpr e3)
      | MLast.ExInt (loc, s, c) ->
          MLast.ExApp
            (loc,
             MLast.ExApp
               (loc,
                MLast.ExApp
                  (loc,
                   MLast.ExLong
                     (loc,
                      MLast.LiAcc (loc, MLast.LiUid (loc, "MLast"), "ExInt")),
                   mloc),
                mvala mstring s),
             MLast.ExStr (loc, c))
      | MLast.ExLab (loc, peoptl) ->
          MLast.ExApp
            (loc,
             MLast.ExApp
               (loc,
                MLast.ExLong
                  (loc,
                   MLast.LiAcc (loc, MLast.LiUid (loc, "MLast"), "ExLab")),
                mloc),
             mvala (mlist mpeopt) peoptl)
      | MLast.ExFlo (loc, s) ->
          MLast.ExApp
            (loc,
             MLast.ExApp
               (loc,
                MLast.ExLong
                  (loc,
                   MLast.LiAcc (loc, MLast.LiUid (loc, "MLast"), "ExFlo")),
                mloc),
             mvala mstring s)
      | MLast.ExLet (loc, rf, pel, e) ->
          let rf = mvala mbool rf in
          MLast.ExApp
            (loc,
             MLast.ExApp
               (loc,
                MLast.ExApp
                  (loc,
                   MLast.ExApp
                     (loc,
                      MLast.ExLong
                        (loc,
                         MLast.LiAcc
                           (loc, MLast.LiUid (loc, "MLast"), "ExLet")),
                      mloc),
                   rf),
                mvala (mlist mpea) pel),
             mexpr e)
      | MLast.ExLid (loc, s) ->
          MLast.ExApp
            (loc,
             MLast.ExApp
               (loc,
                MLast.ExLong
                  (loc,
                   MLast.LiAcc (loc, MLast.LiUid (loc, "MLast"), "ExLid")),
                mloc),
             mvala mstring s)
      | MLast.ExMat (loc, e, pwel) ->
          MLast.ExApp
            (loc,
             MLast.ExApp
               (loc,
                MLast.ExApp
                  (loc,
                   MLast.ExLong
                     (loc,
                      MLast.LiAcc (loc, MLast.LiUid (loc, "MLast"), "ExMat")),
                   mloc),
                mexpr e),
             mvala (mlist mpwe) pwel)
      | MLast.ExRec (loc, pel, eo) ->
          let pel = mvala (mlist mpe) pel in
          MLast.ExApp
            (loc,
             MLast.ExApp
               (loc,
                MLast.ExApp
                  (loc,
                   MLast.ExLong
                     (loc,
                      MLast.LiAcc (loc, MLast.LiUid (loc, "MLast"), "ExRec")),
                   mloc),
                pel),
             moption mexpr eo)
      | MLast.ExSeq (loc, el) ->
          MLast.ExApp
            (loc,
             MLast.ExApp
               (loc,
                MLast.ExLong
                  (loc,
                   MLast.LiAcc (loc, MLast.LiUid (loc, "MLast"), "ExSeq")),
                mloc),
             mvala (mlist mexpr) el)
      | MLast.ExSte (loc, s, e1, e2) ->
          MLast.ExApp
            (loc,
             MLast.ExApp
               (loc,
                MLast.ExApp
                  (loc,
                   MLast.ExApp
                     (loc,
                      MLast.ExLong
                        (loc,
                         MLast.LiAcc
                           (loc, MLast.LiUid (loc, "MLast"), "ExSte")),
                      mvala mstring s),
                   mloc),
                mexpr e1),
             mvala (mlist mexpr) e2)
      | MLast.ExStr (loc, s) ->
          MLast.ExApp
            (loc,
             MLast.ExApp
               (loc,
                MLast.ExLong
                  (loc,
                   MLast.LiAcc (loc, MLast.LiUid (loc, "MLast"), "ExStr")),
                mloc),
             mvala mstring_escaped s)
      | MLast.ExTry (loc, e, pwel) ->
          MLast.ExApp
            (loc,
             MLast.ExApp
               (loc,
                MLast.ExApp
                  (loc,
                   MLast.ExLong
                     (loc,
                      MLast.LiAcc (loc, MLast.LiUid (loc, "MLast"), "ExTry")),
                   mloc),
                mexpr e),
             mvala (mlist mpwe) pwel)
      | MLast.ExTup (loc, el) ->
          MLast.ExApp
            (loc,
             MLast.ExApp
               (loc,
                MLast.ExLong
                  (loc,
                   MLast.LiAcc (loc, MLast.LiUid (loc, "MLast"), "ExTup")),
                mloc),
             mvala (mlist mexpr) el)
      | MLast.ExTyc (loc, e, t) ->
          MLast.ExApp
            (loc,
             MLast.ExApp
               (loc,
                MLast.ExApp
                  (loc,
                   MLast.ExLong
                     (loc,
                      MLast.LiAcc (loc, MLast.LiUid (loc, "MLast"), "ExTyc")),
                   mloc),
                mexpr e),
             mctyp t)
      | x -> not_impl "mexpr" x
    and mpatt =
      function
        MLast.PaPfx (loc, li, p) ->
          MLast.ExApp
            (loc,
             MLast.ExApp
               (loc,
                MLast.ExApp
                  (loc,
                   MLast.ExLong
                     (loc,
                      MLast.LiAcc (loc, MLast.LiUid (loc, "MLast"), "PaPfx")),
                   mloc),
                mlongid li),
             mpatt p)
      | MLast.PaLong (loc, li, []) ->
          MLast.ExApp
            (loc,
             MLast.ExApp
               (loc,
                MLast.ExApp
                  (loc,
                   MLast.ExLong
                     (loc,
                      MLast.LiAcc
                        (loc, MLast.LiUid (loc, "MLast"), "PaLong")),
                   mloc),
                mlongid li),
             MLast.ExApp
               (loc,
                MLast.ExLong
                  (loc,
                   MLast.LiAcc (loc, MLast.LiUid (loc, "Ploc"), "VaVal")),
                MLast.ExLong (loc, MLast.LiUid (loc, "[]"))))
      | MLast.PaLong (loc, li, _) -> assert false
      | MLast.PaAny loc ->
          MLast.ExApp
            (loc,
             MLast.ExLong
               (loc, MLast.LiAcc (loc, MLast.LiUid (loc, "MLast"), "PaAny")),
             mloc)
      | MLast.PaApp (loc, p1, p2) ->
          MLast.ExApp
            (loc,
             MLast.ExApp
               (loc,
                MLast.ExApp
                  (loc,
                   MLast.ExLong
                     (loc,
                      MLast.LiAcc (loc, MLast.LiUid (loc, "MLast"), "PaApp")),
                   mloc),
                mpatt p1),
             mpatt p2)
      | MLast.PaInt (loc, s, c) ->
          MLast.ExApp
            (loc,
             MLast.ExApp
               (loc,
                MLast.ExApp
                  (loc,
                   MLast.ExLong
                     (loc,
                      MLast.LiAcc (loc, MLast.LiUid (loc, "MLast"), "PaInt")),
                   mloc),
                mvala mstring s),
             MLast.ExStr (loc, c))
      | MLast.PaLid (loc, s) ->
          MLast.ExApp
            (loc,
             MLast.ExApp
               (loc,
                MLast.ExLong
                  (loc,
                   MLast.LiAcc (loc, MLast.LiUid (loc, "MLast"), "PaLid")),
                mloc),
             mvala mstring s)
      | MLast.PaOrp (loc, p1, p2) ->
          MLast.ExApp
            (loc,
             MLast.ExApp
               (loc,
                MLast.ExApp
                  (loc,
                   MLast.ExLong
                     (loc,
                      MLast.LiAcc (loc, MLast.LiUid (loc, "MLast"), "PaOrp")),
                   mloc),
                mpatt p1),
             mpatt p2)
      | MLast.PaStr (loc, s) ->
          MLast.ExApp
            (loc,
             MLast.ExApp
               (loc,
                MLast.ExLong
                  (loc,
                   MLast.LiAcc (loc, MLast.LiUid (loc, "MLast"), "PaStr")),
                mloc),
             mvala mstring_escaped s)
      | MLast.PaTup (loc, pl) ->
          MLast.ExApp
            (loc,
             MLast.ExApp
               (loc,
                MLast.ExLong
                  (loc,
                   MLast.LiAcc (loc, MLast.LiUid (loc, "MLast"), "PaTup")),
                mloc),
             mvala (mlist mpatt) pl)
      | MLast.PaTyc (loc, p, t) ->
          MLast.ExApp
            (loc,
             MLast.ExApp
               (loc,
                MLast.ExApp
                  (loc,
                   MLast.ExLong
                     (loc,
                      MLast.LiAcc (loc, MLast.LiUid (loc, "MLast"), "PaTyc")),
                   mloc),
                mpatt p),
             mctyp t)
      | x -> not_impl "mpatt" x
    and mlongid =
      function
        MLast.LiApp (loc, me1, me2) ->
          MLast.ExApp
            (loc,
             MLast.ExApp
               (loc,
                MLast.ExApp
                  (loc,
                   MLast.ExLong
                     (loc,
                      MLast.LiAcc (loc, MLast.LiUid (loc, "MLast"), "LiApp")),
                   mloc),
                mlongid me1),
             mlongid me2)
      | MLast.LiAcc (loc, me1, uid) ->
          MLast.ExApp
            (loc,
             MLast.ExApp
               (loc,
                MLast.ExApp
                  (loc,
                   MLast.ExLong
                     (loc,
                      MLast.LiAcc (loc, MLast.LiUid (loc, "MLast"), "LiAcc")),
                   mloc),
                mlongid me1),
             mvala mstring uid)
      | MLast.LiUid (loc, s) ->
          MLast.ExApp
            (loc,
             MLast.ExApp
               (loc,
                MLast.ExLong
                  (loc,
                   MLast.LiAcc (loc, MLast.LiUid (loc, "MLast"), "LiUid")),
                mloc),
             mvala mstring s)
      | x -> not_impl "mlongid" x
    and mlongid_lident =
      function
        Some li, id ->
          MLast.ExTup
            (loc,
             [MLast.ExApp
                (loc, MLast.ExLong (loc, MLast.LiUid (loc, "Some")),
                 mvala mlongid li);
              mvala mstring id])
      | None, id ->
          MLast.ExTup
            (loc,
             [MLast.ExLong (loc, MLast.LiUid (loc, "None"));
              mvala mstring id])
    and mctyp =
      function
        MLast.TyAcc (loc, m1, t2) ->
          MLast.ExApp
            (loc,
             MLast.ExApp
               (loc,
                MLast.ExApp
                  (loc,
                   MLast.ExLong
                     (loc,
                      MLast.LiAcc (loc, MLast.LiUid (loc, "MLast"), "TyAcc")),
                   mloc),
                mlongid m1),
             mvala mstring t2)
      | MLast.TyApp (loc, t1, t2) ->
          MLast.ExApp
            (loc,
             MLast.ExApp
               (loc,
                MLast.ExApp
                  (loc,
                   MLast.ExLong
                     (loc,
                      MLast.LiAcc (loc, MLast.LiUid (loc, "MLast"), "TyApp")),
                   mloc),
                mctyp t1),
             mctyp t2)
      | MLast.TyLid (loc, s) ->
          MLast.ExApp
            (loc,
             MLast.ExApp
               (loc,
                MLast.ExLong
                  (loc,
                   MLast.LiAcc (loc, MLast.LiUid (loc, "MLast"), "TyLid")),
                mloc),
             mvala mstring s)
      | MLast.TyQuo (loc, s) ->
          MLast.ExApp
            (loc,
             MLast.ExApp
               (loc,
                MLast.ExLong
                  (loc,
                   MLast.LiAcc (loc, MLast.LiUid (loc, "MLast"), "TyQuo")),
                mloc),
             mvala mstring s)
      | MLast.TyTup (loc, tl) ->
          MLast.ExApp
            (loc,
             MLast.ExApp
               (loc,
                MLast.ExLong
                  (loc,
                   MLast.LiAcc (loc, MLast.LiUid (loc, "MLast"), "TyTup")),
                mloc),
             mvala (mlist mctyp) tl)
      | x -> not_impl "mctyp" x
    and mpea (p, e, attrs) =
      assert ([] = Pcaml.unvala attrs);
      MLast.ExTup
        (loc,
         [mpatt p; mexpr e;
          MLast.ExApp
            (loc,
             MLast.ExLong
               (loc, MLast.LiAcc (loc, MLast.LiUid (loc, "Ploc"), "VaVal")),
             MLast.ExLong (loc, MLast.LiUid (loc, "[]")))])
    and mpe (p, e) = MLast.ExTup (loc, [mpatt p; mexpr e])
    and mpwe (p, w, e) =
      MLast.ExTup (loc, [mpatt p; mvala (moption mexpr) w; mexpr e])
    and mpeopt (p, eopt) =
      MLast.ExTup (loc, [mpatt p; mvala (moption mexpr) eopt])
    ;;
  end
;;

let mklistexp loc =
  let rec loop top =
    function
      [] -> MLast.ExLong (loc, MLast.LiUid (loc, "[]"))
    | e1 :: el ->
        let loc = if top then loc else Ploc.encl (MLast.loc_of_expr e1) loc in
        MLast.ExApp
          (loc,
           MLast.ExApp (loc, MLast.ExLong (loc, MLast.LiUid (loc, "::")), e1),
           loop false el)
  in
  loop true
;;

let mklistpat loc =
  let rec loop top =
    function
      [] -> MLast.PaLong (loc, MLast.LiUid (loc, "[]"), [])
    | p1 :: pl ->
        let loc = if top then loc else Ploc.encl (MLast.loc_of_patt p1) loc in
        MLast.PaApp
          (loc,
           MLast.PaApp
             (loc, MLast.PaLong (loc, MLast.LiUid (loc, "::"), []), p1),
           loop false pl)
  in
  loop true
;;

let rec expr_fa al =
  function
    MLast.ExApp (_, f, a) -> expr_fa (a :: al) f
  | f -> f, al
;;

let assoc_anti = ["ANTIQUOT_LOC", "ANTIQUOT"];;

let anti_str psl =
  match psl with
    [{symbol = {text = TXtok (_, x, MLast.ExStr (_, s))}}] ->
      if List.exists (fun (_, y) -> x = y) assoc_anti then s else ""
  | _ -> ""
;;

let anti_anti n =
  if n <> "" && (n.[0] = '~' || n.[0] = '?') then
    String.make 1 n.[0] ^ "_" ^ String.sub n 1 (String.length n - 1)
  else "_" ^ n
;;

let is_anti_anti n =
  n <> "" && n.[0] = '_' ||
  String.length n > 1 && (n.[0] = '~' || n.[0] = '?') && n.[1] = '_'
;;

let anti_of_tok =
  function
    "CHAR" -> ["chr"]
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
  | s -> []
;;

let is_not_translated_function f = f = "warning_deprecated_since_6_00";;

let quot_expr psl e =
  let rec loop e =
    let loc = MLast.loc_of_expr e in
    match e with
      MLast.ExLong (_, MLast.LiUid (_, "None")) ->
        MLast.ExApp
          (loc,
           MLast.ExLong
             (loc, MLast.LiAcc (loc, MLast.LiUid (loc, "Qast"), "Option")),
           MLast.ExLong (loc, MLast.LiUid (loc, "None")))
    | MLast.ExApp (_, MLast.ExLong (_, MLast.LiUid (_, "Some")), e) ->
        MLast.ExApp
          (loc,
           MLast.ExLong
             (loc, MLast.LiAcc (loc, MLast.LiUid (loc, "Qast"), "Option")),
           MLast.ExApp
             (loc, MLast.ExLong (loc, MLast.LiUid (loc, "Some")), loop e))
    | MLast.ExLong (_, MLast.LiUid (_, "False")) ->
        MLast.ExApp
          (loc,
           MLast.ExLong
             (loc, MLast.LiAcc (loc, MLast.LiUid (loc, "Qast"), "Bool")),
           MLast.ExLong (loc, MLast.LiUid (loc, "False")))
    | MLast.ExLong (_, MLast.LiUid (_, "True")) ->
        MLast.ExApp
          (loc,
           MLast.ExLong
             (loc, MLast.LiAcc (loc, MLast.LiUid (loc, "Qast"), "Bool")),
           MLast.ExLong (loc, MLast.LiUid (loc, "True")))
    | MLast.ExApp
        (_,
         MLast.ExLong (_, MLast.LiAcc (_, MLast.LiUid (_, "Ploc"), "VaAnt")),
         e) ->
        let s = anti_str psl in
        let e =
          MLast.ExApp
            (loc,
             MLast.ExApp
               (loc,
                MLast.ExApp
                  (loc,
                   MLast.ExLong
                     (loc,
                      MLast.LiAcc (loc, MLast.LiUid (loc, "Qast"), "VaAnt")),
                   MLast.ExStr (loc, s)),
                MLast.ExLid (loc, "loc")),
             loop e)
        in
        if is_anti_anti s then e
        else
          MLast.ExApp
            (loc,
             MLast.ExLong
               (loc, MLast.LiAcc (loc, MLast.LiUid (loc, "Qast"), "VaVal")),
             e)
    | MLast.ExApp
        (_,
         MLast.ExLong (_, MLast.LiAcc (_, MLast.LiUid (_, "Ploc"), "VaVal")),
         e) ->
        MLast.ExApp
          (loc,
           MLast.ExLong
             (loc, MLast.LiAcc (loc, MLast.LiUid (loc, "Qast"), "VaVal")),
           loop e)
    | MLast.ExLong (_, MLast.LiUid (_, "()")) -> e
    | MLast.ExApp
        (_,
         MLast.ExLong (_, MLast.LiAcc (_, MLast.LiUid (_, "Qast"), "Bool")),
         _) ->
        e
    | MLast.ExApp
        (_,
         MLast.ExLong (_, MLast.LiAcc (_, MLast.LiUid (_, "Qast"), "List")),
         _) ->
        e
    | MLast.ExApp
        (_,
         MLast.ExLong (_, MLast.LiAcc (_, MLast.LiUid (_, "Qast"), "Option")),
         _) ->
        e
    | MLast.ExApp
        (_, MLast.ExLong (_, MLast.LiAcc (_, MLast.LiUid (_, "Qast"), "Str")),
         _) ->
        e
    | MLast.ExApp
        (_,
         MLast.ExApp
           (_,
            MLast.ExApp
              (_,
               MLast.ExLong
                 (_, MLast.LiAcc (_, MLast.LiUid (_, "Qast"), "VaAnt")),
               _),
            _),
         _) ->
        e
    | MLast.ExApp
        (_,
         MLast.ExLong (_, MLast.LiAcc (_, MLast.LiUid (_, "Qast"), "VaVal")),
         _) ->
        e
    | MLast.ExLong (_, MLast.LiUid (_, "[]")) ->
        MLast.ExApp
          (loc,
           MLast.ExLong
             (loc, MLast.LiAcc (loc, MLast.LiUid (loc, "Qast"), "List")),
           MLast.ExLong (loc, MLast.LiUid (loc, "[]")))
    | MLast.ExApp
        (_, MLast.ExApp (_, MLast.ExLong (_, MLast.LiUid (_, "::")), e),
         MLast.ExLong (_, MLast.LiUid (_, "[]"))) ->
        MLast.ExApp
          (loc,
           MLast.ExLong
             (loc, MLast.LiAcc (loc, MLast.LiUid (loc, "Qast"), "List")),
           MLast.ExApp
             (loc,
              MLast.ExApp
                (loc, MLast.ExLong (loc, MLast.LiUid (loc, "::")), loop e),
              MLast.ExLong (loc, MLast.LiUid (loc, "[]"))))
    | MLast.ExApp
        (_, MLast.ExApp (_, MLast.ExLong (_, MLast.LiUid (_, "::")), e1),
         e2) ->
        MLast.ExApp
          (loc,
           MLast.ExApp
             (loc,
              MLast.ExLong
                (loc, MLast.LiAcc (loc, MLast.LiUid (loc, "Qast"), "Cons")),
              loop e1),
           loop e2)
    | MLast.ExApp (_, _, _) ->
        let (f, al) = expr_fa [] e in
        begin match f with
          MLast.ExLong (_, MLast.LiUid (_, c)) ->
            let al = List.map loop al in
            MLast.ExApp
              (loc,
               MLast.ExApp
                 (loc,
                  MLast.ExLong
                    (loc,
                     MLast.LiAcc (loc, MLast.LiUid (loc, "Qast"), "Node")),
                  MLast.ExStr (loc, c)),
               mklistexp loc al)
        | MLast.ExLong (_, MLast.LiAcc (_, MLast.LiUid (_, "MLast"), c)) ->
            let al = List.map loop al in
            MLast.ExApp
              (loc,
               MLast.ExApp
                 (loc,
                  MLast.ExLong
                    (loc,
                     MLast.LiAcc (loc, MLast.LiUid (loc, "Qast"), "Node")),
                  MLast.ExStr (loc, c)),
               mklistexp loc al)
        | MLast.ExLong (_, MLast.LiAcc (_, MLast.LiUid (_, m), c)) ->
            let al = List.map loop al in
            MLast.ExApp
              (loc,
               MLast.ExApp
                 (loc,
                  MLast.ExLong
                    (loc,
                     MLast.LiAcc (loc, MLast.LiUid (loc, "Qast"), "Node")),
                  MLast.ExStr (loc, m ^ "." ^ c)),
               mklistexp loc al)
        | MLast.ExLid (_, f) ->
            if is_not_translated_function f then e
            else
              let al = List.map loop al in
              List.fold_left (fun f e -> MLast.ExApp (loc, f, e))
                (MLast.ExLid (loc, f)) al
        | _ -> e
        end
    | MLast.ExRec (_, pel, None) ->
        begin try
          let lel =
            List.map
              (fun (p, e) ->
                 let lab =
                   match p with
                     MLast.PaLid (_, c) -> MLast.ExStr (loc, c)
                   | MLast.PaPfx (_, _, MLast.PaLid (_, c)) ->
                       MLast.ExStr (loc, c)
                   | _ -> raise Not_found
                 in
                 MLast.ExTup (loc, [lab; loop e]))
              pel
          in
          MLast.ExApp
            (loc,
             MLast.ExLong
               (loc, MLast.LiAcc (loc, MLast.LiUid (loc, "Qast"), "Record")),
             mklistexp loc lel)
        with Not_found -> e
        end
    | MLast.ExLid (_, s) ->
        if s = !(Ploc.name) then
          MLast.ExLong
            (loc, MLast.LiAcc (loc, MLast.LiUid (loc, "Qast"), "Loc"))
        else e
    | MLast.ExLong (_, MLast.LiAcc (_, MLast.LiUid (_, "MLast"), s)) ->
        MLast.ExApp
          (loc,
           MLast.ExApp
             (loc,
              MLast.ExLong
                (loc, MLast.LiAcc (loc, MLast.LiUid (loc, "Qast"), "Node")),
              MLast.ExStr (loc, s)),
           MLast.ExLong (loc, MLast.LiUid (loc, "[]")))
    | MLast.ExLong (_, MLast.LiAcc (_, MLast.LiUid (_, m), s)) ->
        MLast.ExApp
          (loc,
           MLast.ExApp
             (loc,
              MLast.ExLong
                (loc, MLast.LiAcc (loc, MLast.LiUid (loc, "Qast"), "Node")),
              MLast.ExStr (loc, m ^ "." ^ s)),
           MLast.ExLong (loc, MLast.LiUid (loc, "[]")))
    | MLast.ExLong (_, MLast.LiUid (_, s)) ->
        MLast.ExApp
          (loc,
           MLast.ExApp
             (loc,
              MLast.ExLong
                (loc, MLast.LiAcc (loc, MLast.LiUid (loc, "Qast"), "Node")),
              MLast.ExStr (loc, s)),
           MLast.ExLong (loc, MLast.LiUid (loc, "[]")))
    | MLast.ExStr (_, s) ->
        MLast.ExApp
          (loc,
           MLast.ExLong
             (loc, MLast.LiAcc (loc, MLast.LiUid (loc, "Qast"), "Str")),
           MLast.ExStr (loc, s))
    | MLast.ExTup (_, el) ->
        let el = List.map loop el in
        MLast.ExApp
          (loc,
           MLast.ExLong
             (loc, MLast.LiAcc (loc, MLast.LiUid (loc, "Qast"), "Tuple")),
           mklistexp loc el)
    | MLast.ExLet (_, r, pel, e) ->
        let pel = List.map (fun (p, e, attrs) -> p, loop e, attrs) pel in
        MLast.ExLet (loc, r, pel, loop e)
    | _ -> e
  in
  loop e
;;

let symgen = "xx";;

let pname_of_ptuple pl =
  List.fold_left
    (fun pname p ->
       match p with
         MLast.PaLid (_, s) -> pname ^ s
       | _ -> pname)
    "" pl
;;

let quotify_action psl act =
  let e = quot_expr psl act in
  List.fold_left
    (fun e ps ->
       match ps.pattern with
         Some (MLast.PaTup (_, pl)) ->
           let loc = Ploc.dummy in
           let pname = pname_of_ptuple pl in
           let (pl1, el1) =
             let (l, _) =
               List.fold_left
                 (fun (l, cnt) _ ->
                    (symgen ^ string_of_int cnt) :: l, cnt + 1)
                 ([], 1) pl
             in
             let l = List.rev l in
             List.map (fun s -> MLast.PaLid (loc, s)) l,
             List.map (fun s -> MLast.ExLid (loc, s)) l
           in
           MLast.ExLet
             (loc, false,
              [MLast.PaTup (loc, pl),
               MLast.ExMat
                 (loc, MLast.ExLid (loc, pname),
                  [MLast.PaApp
                     (loc,
                      MLast.PaLong
                        (loc,
                         MLast.LiAcc
                           (loc, MLast.LiUid (loc, "Qast"), "Tuple"),
                         []),
                      mklistpat loc pl1),
                   None, MLast.ExTup (loc, el1);
                   MLast.PaAny loc, None,
                   MLast.ExMat
                     (loc, MLast.ExLong (loc, MLast.LiUid (loc, "()")), [])]),
               []],
              e)
       | _ -> e)
    e psl
;;

let rec make_ctyp styp tvar =
  match styp with
    STlid (loc, s) -> MLast.TyLid (loc, s)
  | STapp (loc, t1, t2) ->
      MLast.TyApp (loc, make_ctyp t1 tvar, make_ctyp t2 tvar)
  | STquo (loc, s) -> MLast.TyQuo (loc, s)
  | STself (loc, x) ->
      if tvar = "" then
        Ploc.raise loc
          (Stream.Error ("'" ^ x ^ "' illegal in anonymous entry level"))
      else MLast.TyQuo (loc, tvar)
  | STtyp t -> t
  | STnone -> failwith "make_ctyp: internal error"
  | STvala (loc, t) ->
      MLast.TyApp
        (loc, MLast.TyAcc (loc, MLast.LiUid (loc, "Ploc"), "vala"),
         make_ctyp t tvar)
;;

let text_of_action loc psl rtvar act tvar =
  let locid = MLast.PaLid (loc, !(Ploc.name)) in
  let act =
    match act with
      Some act -> if !quotify then quotify_action psl act else act
    | None -> MLast.ExLong (loc, MLast.LiUid (loc, "()"))
  in
  let e =
    MLast.ExFun
      (loc,
       [MLast.PaTyc
          (loc, locid, MLast.TyAcc (loc, MLast.LiUid (loc, "Ploc"), "t")),
        None, MLast.ExTyc (loc, act, MLast.TyQuo (loc, rtvar))])
  in
  let txt =
    List.fold_left
      (fun txt ps ->
         match ps.symbol.styp with
           STnone -> txt
         | st ->
             match ps.pattern with
               None -> MLast.ExFun (loc, [MLast.PaAny loc, None, txt])
             | Some p ->
                 let t = make_ctyp st tvar in
                 let p =
                   match p with
                     MLast.PaTup (_, pl) when !quotify ->
                       MLast.PaLid (loc, pname_of_ptuple pl)
                   | _ -> p
                 in
                 MLast.ExFun (loc, [MLast.PaTyc (loc, p, t), None, txt]))
      e psl
  in
  let txt =
    if !meta_action then
      MLast.ExApp
        (loc,
         MLast.ExFle
           (loc, MLast.ExLong (loc, MLast.LiUid (loc, "Obj")),
            (None, "magic")),
         MetaAction.mexpr txt)
    else txt
  in
  txt
;;

let srules loc t rl tvar =
  List.map
    (fun r ->
       let sl = List.map (fun ps -> ps.symbol.text) r.prod in
       let ac = text_of_action loc r.prod t r.action tvar in sl, ac)
    rl
;;

let is_cut =
  function
    TXcut _ -> true
  | _ -> false
;;

let rec make_expr gmod tvar =
  function
    TXfacto (loc, t) ->
      MLast.ExApp
        (loc,
         MLast.ExFle
           (loc, MLast.ExLong (loc, MLast.LiUid (loc, gmod)),
            (None, "s_facto")),
         make_expr gmod tvar t)
  | TXlist (loc, min, t, ts) ->
      let txt = make_expr gmod "" t in
      begin match min, ts with
        LML_0, None ->
          MLast.ExApp
            (loc,
             MLast.ExFle
               (loc, MLast.ExLong (loc, MLast.LiUid (loc, gmod)),
                (None, "s_list0")),
             txt)
      | LML_1, None ->
          MLast.ExApp
            (loc,
             MLast.ExFle
               (loc, MLast.ExLong (loc, MLast.LiUid (loc, gmod)),
                (None, "s_list1")),
             txt)
      | LML_0, Some (s, b) ->
          let x = make_expr gmod tvar s in
          let b =
            if b then MLast.ExLong (loc, MLast.LiUid (loc, "True"))
            else MLast.ExLong (loc, MLast.LiUid (loc, "False"))
          in
          MLast.ExApp
            (loc,
             MLast.ExApp
               (loc,
                MLast.ExApp
                  (loc,
                   MLast.ExFle
                     (loc, MLast.ExLong (loc, MLast.LiUid (loc, gmod)),
                      (None, "s_list0sep")),
                   txt),
                x),
             b)
      | LML_1, Some (s, b) ->
          let x = make_expr gmod tvar s in
          let b =
            if b then MLast.ExLong (loc, MLast.LiUid (loc, "True"))
            else MLast.ExLong (loc, MLast.LiUid (loc, "False"))
          in
          MLast.ExApp
            (loc,
             MLast.ExApp
               (loc,
                MLast.ExApp
                  (loc,
                   MLast.ExFle
                     (loc, MLast.ExLong (loc, MLast.LiUid (loc, gmod)),
                      (None, "s_list1sep")),
                   txt),
                x),
             b)
      end
  | TXnext loc ->
      MLast.ExFle
        (loc, MLast.ExLong (loc, MLast.LiUid (loc, gmod)), (None, "s_next"))
  | TXnterm (loc, n, lev) ->
      begin match lev with
        Some lab ->
          MLast.ExApp
            (loc,
             MLast.ExApp
               (loc,
                MLast.ExFle
                  (loc, MLast.ExLong (loc, MLast.LiUid (loc, gmod)),
                   (None, "s_nterml")),
                MLast.ExTyc
                  (loc, n.expr,
                   MLast.TyApp
                     (loc,
                      MLast.TyAcc
                        (loc,
                         MLast.LiAcc (loc, MLast.LiUid (loc, gmod), "Entry"),
                         "e"),
                      MLast.TyQuo (loc, n.tvar)))),
             MLast.ExStr (loc, lab))
      | None ->
          if n.tvar = tvar then
            MLast.ExFle
              (loc, MLast.ExLong (loc, MLast.LiUid (loc, gmod)),
               (None, "s_self"))
          else
            MLast.ExApp
              (loc,
               MLast.ExFle
                 (loc, MLast.ExLong (loc, MLast.LiUid (loc, gmod)),
                  (None, "s_nterm")),
               MLast.ExTyc
                 (loc, n.expr,
                  MLast.TyApp
                    (loc,
                     MLast.TyAcc
                       (loc,
                        MLast.LiAcc (loc, MLast.LiUid (loc, gmod), "Entry"),
                        "e"),
                     MLast.TyQuo (loc, n.tvar))))
      end
  | TXopt (loc, t) ->
      MLast.ExApp
        (loc,
         MLast.ExFle
           (loc, MLast.ExLong (loc, MLast.LiUid (loc, gmod)),
            (None, "s_opt")),
         make_expr gmod "" t)
  | TXflag (loc, t) ->
      MLast.ExApp
        (loc,
         MLast.ExFle
           (loc, MLast.ExLong (loc, MLast.LiUid (loc, gmod)),
            (None, "s_flag")),
         make_expr gmod "" t)
  | TXrules (loc, s, rl) ->
      let rl = srules loc s rl "" in
      MLast.ExApp
        (loc,
         MLast.ExFle
           (loc, MLast.ExLong (loc, MLast.LiUid (loc, gmod)),
            (None, "s_rules")),
         make_expr_rules loc gmod rl "")
  | TXself loc ->
      MLast.ExFle
        (loc, MLast.ExLong (loc, MLast.LiUid (loc, gmod)), (None, "s_self"))
  | TXcut loc -> assert false
  | TXtok (loc, s, e) ->
      MLast.ExApp
        (loc,
         MLast.ExFle
           (loc, MLast.ExLong (loc, MLast.LiUid (loc, gmod)),
            (None, "s_token")),
         MLast.ExTup (loc, [MLast.ExStr (loc, s); e]))
  | TXvala (loc, al, t) ->
      let al = make_list loc (fun s -> MLast.ExStr (loc, s)) al in
      MLast.ExApp
        (loc,
         MLast.ExApp
           (loc,
            MLast.ExFle
              (loc, MLast.ExLong (loc, MLast.LiUid (loc, gmod)),
               (None, "s_vala")),
            al),
         make_expr gmod "" t)
and make_expr_rules loc gmod rl tvar =
  List.fold_left
    (fun txt (sl, ac) ->
       let sl =
         List.fold_left
           (fun txt t ->
              if is_cut t then
                MLast.ExApp
                  (loc,
                   MLast.ExFle
                     (loc, MLast.ExLong (loc, MLast.LiUid (loc, gmod)),
                      (None, "r_cut")),
                   txt)
              else
                let x = make_expr gmod tvar t in
                MLast.ExApp
                  (loc,
                   MLast.ExApp
                     (loc,
                      MLast.ExFle
                        (loc, MLast.ExLong (loc, MLast.LiUid (loc, gmod)),
                         (None, "r_next")),
                      txt),
                   x))
           (MLast.ExFle
              (loc, MLast.ExLong (loc, MLast.LiUid (loc, gmod)),
               (None, "r_stop")))
           sl
       in
       let hash =
         Printf.sprintf "%08x"
           (Hashtbl.hash (Reloc.expr (fun _ -> Ploc.dummy) 0 ac))
       in
       MLast.ExApp
         (loc,
          MLast.ExApp
            (loc, MLast.ExLong (loc, MLast.LiUid (loc, "::")),
             MLast.ExApp
               (loc,
                MLast.ExFle
                  (loc, MLast.ExLong (loc, MLast.LiUid (loc, gmod)),
                   (None, "production")),
                MLast.ExTup (loc, [sl; MLast.ExStr (loc, hash); ac]))),
          txt))
    (MLast.ExLong (loc, MLast.LiUid (loc, "[]"))) rl
;;

let rec ident_of_longid =
  function
    MLast.LiUid (_, s) -> s
  | MLast.LiAcc (_, li, s) -> ident_of_longid li ^ "__" ^ s
  | li ->
      Ploc.raise (MLast.loc_of_longid li)
        (Failure "ident_of_longid: internal error in pa_extend")
;;

let rec ident_of_expr =
  function
    MLast.ExLid (_, s) -> s
  | MLast.ExLong (_, MLast.LiUid (_, s)) -> s
  | MLast.ExLong (_, li) -> ident_of_longid li
  | e ->
      Ploc.raise (MLast.loc_of_expr e)
        (Failure "ident_of_expr: internal error in pa_extend")
;;

let mk_name loc e = {expr = e; tvar = ident_of_expr e; loc = loc};;
let mk_name2 (i, e) =
  let loc = MLast.loc_of_expr e in {expr = e; tvar = i; loc = loc}
;;

let slist loc min sep symb =
  let t =
    match sep with
      Some (s, b) -> Some (s.text, b)
    | None -> None
  in
  TXlist (loc, min, symb.text, t)
;;

let mk_psymbol p s t =
  let symb = {used = []; text = s; styp = t} in
  {pattern = Some p; symbol = symb}
;;

let ss2 loc ls oe s =
  let qast_f a =
    match s.styp with
      STlid (loc, "bool") ->
        MLast.ExApp
          (loc,
           MLast.ExLong
             (loc, MLast.LiAcc (loc, MLast.LiUid (loc, "Qast"), "Bool")),
           a)
    | STlid (loc, "string") ->
        MLast.ExApp
          (loc,
           MLast.ExLong
             (loc, MLast.LiAcc (loc, MLast.LiUid (loc, "Qast"), "Str")),
           a)
    | STapp (loc, STlid (_, "list"), t) ->
        let a =
          match t with
            STlid (_, "string") ->
              MLast.ExApp
                (loc,
                 MLast.ExApp
                   (loc,
                    MLast.ExFle
                      (loc, MLast.ExLong (loc, MLast.LiUid (loc, "List")),
                       (None, "map")),
                    MLast.ExFun
                      (loc,
                       [MLast.PaLid (loc, "a"), None,
                        MLast.ExApp
                          (loc,
                           MLast.ExLong
                             (loc,
                              MLast.LiAcc
                                (loc, MLast.LiUid (loc, "Qast"), "Str")),
                           MLast.ExLid (loc, "a"))])),
                 a)
          | _ -> a
        in
        MLast.ExApp
          (loc,
           MLast.ExLong
             (loc, MLast.LiAcc (loc, MLast.LiUid (loc, "Qast"), "List")),
           a)
    | STapp (loc, STlid (_, "option"), t) ->
        MLast.ExApp
          (loc,
           MLast.ExLong
             (loc, MLast.LiAcc (loc, MLast.LiUid (loc, "Qast"), "Option")),
           a)
    | STquo (_, _) -> a
    | t -> MetaAction.not_impl "ss2" s.styp
  in
  let t = new_type_var () in
  let text =
    let rl =
      match oe with
        Some (i, e) ->
          let r =
            let ps =
              let text =
                let name = mk_name2 (i, e) in TXnterm (loc, name, None)
              in
              let styp = STquo (loc, i) in
              let s = {used = []; text = text; styp = styp} in
              {pattern = Some (MLast.PaLid (loc, "a")); symbol = s}
            in
            let act = MLast.ExLid (loc, "a") in
            {prod = [ps]; action = Some act}
          in
          [r]
      | None -> []
    in
    let rl =
      let r2 =
        let ps = {pattern = Some (MLast.PaLid (loc, "a")); symbol = s} in
        let act =
          MLast.ExApp
            (loc,
             MLast.ExLong
               (loc, MLast.LiAcc (loc, MLast.LiUid (loc, "Qast"), "VaVal")),
             qast_f (MLast.ExLid (loc, "a")))
        in
        {prod = [ps]; action = Some act}
      in
      r2 :: rl
    in
    let rl =
      List.fold_right
        (fun a rl ->
           let r1 =
             let ps =
               let text = TXtok (loc, "ANTIQUOT", MLast.ExStr (loc, a)) in
               let styp = STlid (loc, "string") in
               let s = {used = []; text = text; styp = styp} in
               {pattern = Some (MLast.PaLid (loc, "a")); symbol = s}
             in
             let act =
               MLast.ExApp
                 (loc,
                  MLast.ExLong
                    (loc,
                     MLast.LiAcc (loc, MLast.LiUid (loc, "Qast"), "VaVal")),
                  MLast.ExApp
                    (loc,
                     MLast.ExApp
                       (loc,
                        MLast.ExApp
                          (loc,
                           MLast.ExLong
                             (loc,
                              MLast.LiAcc
                                (loc, MLast.LiUid (loc, "Qast"), "VaAnt")),
                           MLast.ExStr (loc, a)),
                        MLast.ExLid (loc, "loc")),
                     MLast.ExLid (loc, "a")))
             in
             {prod = [ps]; action = Some act}
           in
           let r2 =
             let a = anti_anti a in
             let ps =
               let text = TXtok (loc, "ANTIQUOT", MLast.ExStr (loc, a)) in
               let styp = STlid (loc, "string") in
               let s = {used = []; text = text; styp = styp} in
               {pattern = Some (MLast.PaLid (loc, "a")); symbol = s}
             in
             let act =
               MLast.ExApp
                 (loc,
                  MLast.ExApp
                    (loc,
                     MLast.ExApp
                       (loc,
                        MLast.ExLong
                          (loc,
                           MLast.LiAcc
                             (loc, MLast.LiUid (loc, "Qast"), "VaAnt")),
                        MLast.ExStr (loc, a)),
                     MLast.ExLid (loc, "loc")),
                  MLast.ExLid (loc, "a"))
             in
             {prod = [ps]; action = Some act}
           in
           r1 :: r2 :: rl)
        ls rl
    in
    TXfacto (loc, TXrules (loc, t, rl))
  in
  let used =
    match oe with
      Some e -> fst e :: s.used
    | None -> s.used
  in
  {used = used; text = text; styp = STquo (loc, t)}
;;

let string_of_a =
  function
    ATstring (loc, s) -> MLast.ExStr (loc, s)
  | ATexpr (_, e) -> e
;;

let rec symbol_of_a =
  function
    ASflag (loc, s) ->
      let s = symbol_of_a s in
      let text = TXflag (loc, s.text) in
      let styp = STlid (loc, "bool") in
      {used = s.used; text = text; styp = styp}
  | ASkeyw (loc, s) ->
      let text = TXtok (loc, "", string_of_a s) in
      {used = []; text = text; styp = STlid (loc, "string")}
  | ASlist (loc, min, s, sep) ->
      let s = symbol_of_a s in
      let sep = option_map (fun (sep, b) -> symbol_of_a sep, b) sep in
      let used =
        match sep with
          Some (symb, _) -> symb.used @ s.used
        | None -> s.used
      in
      let text = slist loc min sep s in
      let styp = STapp (loc, STlid (loc, "list"), s.styp) in
      {used = used; text = text; styp = styp}
  | ASnext loc -> {used = []; text = TXnext loc; styp = STself (loc, "NEXT")}
  | ASnterm (loc, (i, n), lev) ->
      let name = mk_name2 (i, n) in
      let text = TXnterm (loc, name, lev) in
      let styp = STquo (loc, i) in {used = [i]; text = text; styp = styp}
  | ASopt (loc, s) ->
      let s = symbol_of_a s in
      let text = TXopt (loc, s.text) in
      let styp = STapp (loc, STlid (loc, "option"), s.styp) in
      {used = s.used; text = text; styp = styp}
  | ASquot (loc, s) -> symbol_of_a s
  | ASrules (loc, rl) ->
      let rl = rules_of_a rl in
      let t = new_type_var () in
      {used = used_of_rule_list rl; text = TXrules (loc, t, rl);
       styp = STquo (loc, t)}
  | ASself loc -> {used = []; text = TXself loc; styp = STself (loc, "SELF")}
  | AScut loc -> {used = []; text = TXcut loc; styp = STnone}
  | AStok (loc, s, p) ->
      let e =
        match p with
          Some e -> string_of_a e
        | None -> MLast.ExStr (loc, "")
      in
      let text = TXtok (loc, s, e) in
      {used = []; text = text; styp = STlid (loc, "string")}
  | ASvala (loc, s, ls) ->
      if !quotify then
        match s with
          AStok (_, _, Some _) -> symbol_of_a s
        | _ ->
            let ls =
              if ls = [] then
                match s with
                  ASflag (_, _) -> ["flag"; "opt"]
                | ASlist (_, _, _, _) -> ["list"]
                | ASopt (_, _) -> ["opt"]
                | AStok (_, s, _) -> anti_of_tok s
                | _ -> []
              else ls
            in
            let oe =
              match s with
                AStok (_, s, _) ->
                  begin match s with
                    "QUESTIONIDENT" ->
                      Some ("a_qi", MLast.ExLid (loc, "a_qi"))
                  | "QUESTIONIDENTCOLON" ->
                      Some ("a_qic", MLast.ExLid (loc, "a_qic"))
                  | "TILDEIDENT" -> Some ("a_ti", MLast.ExLid (loc, "a_ti"))
                  | "TILDEIDENTCOLON" ->
                      Some ("a_tic", MLast.ExLid (loc, "a_tic"))
                  | _ -> None
                  end
              | _ -> None
            in
            let s = Ploc.call_with quotify false symbol_of_a s in
            ss2 loc ls oe s
      else
        let s = symbol_of_a s in
        let (text, styp) =
          if not !(Pcaml.strict_mode) then s.text, s.styp
          else TXvala (loc, ls, s.text), STvala (loc, s.styp)
        in
        {used = s.used; text = text; styp = styp}
  | ASvala2 (loc, s, ls, oe) ->
      match s with
        AStok (_, _, Some _) -> symbol_of_a s
      | s ->
          let ls =
            if ls = [] then
              match s with
                ASflag (_, _) -> ["flag"; "opt"]
              | ASlist (_, _, _, _) -> ["list"]
              | ASopt (_, _) -> ["opt"]
              | AStok (_, s, _) -> anti_of_tok s
              | _ -> []
            else ls
          in
          let s = symbol_of_a s in ss2 loc ls oe s
and psymbol_of_a ap = {pattern = ap.ap_patt; symbol = symbol_of_a ap.ap_symb}
and rules_of_a au =
  let rl = List.map rule_of_a au.au_rules in
  retype_rule_list_without_patterns au.au_loc rl
and rule_of_a ar =
  {prod = List.map psymbol_of_a ar.ar_psymbols; action = ar.ar_action}
;;

let level_of_a alv =
  let rl = rules_of_a alv.al_rules in
  {label = alv.al_label; assoc = alv.al_assoc; rules = rl}
;;

let entry_of_a ae =
  {name = mk_name2 ae.ae_name; pos = ae.ae_pos;
   levels = List.map level_of_a ae.ae_levels}
;;

let expr_of_delete_rule loc gmod n sl =
  let n = mk_name2 n in
  let sl = List.map symbol_of_a sl in
  let sl =
    List.fold_left
      (fun e s ->
         if is_cut s.text then
           MLast.ExApp
             (loc,
              MLast.ExFle
                (loc, MLast.ExLong (loc, MLast.LiUid (loc, gmod)),
                 (None, "r_cut")),
              e)
         else
           MLast.ExApp
             (loc,
              MLast.ExApp
                (loc,
                 MLast.ExFle
                   (loc, MLast.ExLong (loc, MLast.LiUid (loc, gmod)),
                    (None, "r_next")),
                 e),
              make_expr gmod "" s.text))
      (MLast.ExFle
         (loc, MLast.ExLong (loc, MLast.LiUid (loc, gmod)), (None, "r_stop")))
      sl
  in
  n.expr, sl
;;

let text_of_entry loc gmod e =
  let ent =
    let x = e.name in
    let loc = e.name.loc in
    MLast.ExTyc
      (loc, x.expr,
       MLast.TyApp
         (loc,
          MLast.TyAcc
            (loc, MLast.LiAcc (loc, MLast.LiUid (loc, gmod), "Entry"), "e"),
          MLast.TyQuo (loc, x.tvar)))
  in
  let loc = Ploc.with_comment loc "" in
  let pos =
    match e.pos with
      Some pos ->
        MLast.ExApp (loc, MLast.ExLong (loc, MLast.LiUid (loc, "Some")), pos)
    | None -> MLast.ExLong (loc, MLast.LiUid (loc, "None"))
  in
  let txt =
    List.fold_right
      (fun level txt ->
         let lab =
           match level.label with
             Some lab ->
               MLast.ExApp
                 (loc, MLast.ExLong (loc, MLast.LiUid (loc, "Some")),
                  MLast.ExStr (loc, lab))
           | None -> MLast.ExLong (loc, MLast.LiUid (loc, "None"))
         in
         let ass =
           match level.assoc with
             Some ass ->
               MLast.ExApp
                 (loc, MLast.ExLong (loc, MLast.LiUid (loc, "Some")), ass)
           | None -> MLast.ExLong (loc, MLast.LiUid (loc, "None"))
         in
         let txt =
           let rl = srules loc e.name.tvar level.rules e.name.tvar in
           let e = make_expr_rules loc gmod rl e.name.tvar in
           MLast.ExApp
             (loc,
              MLast.ExApp
                (loc, MLast.ExLong (loc, MLast.LiUid (loc, "::")),
                 MLast.ExTup (loc, [lab; ass; e])),
              txt)
         in
         txt)
      e.levels (MLast.ExLong (loc, MLast.LiUid (loc, "[]")))
  in
  ent, pos, txt
;;

let let_in_of_extend loc gmod functor_version gl el args =
  match gl with
    Some (n1 :: _ as nl) ->
      check_use nl el;
      let ll =
        let same_tvar e n = e.name.tvar = n.tvar in
        List.fold_right
          (fun e ll ->
             match e.name.expr with
               MLast.ExLid (_, _) ->
                 if List.exists (same_tvar e) nl then ll
                 else if List.exists (same_tvar e) ll then ll
                 else e.name :: ll
             | _ -> ll)
          el []
      in
      let globals =
        List.map
          (fun {expr = e; tvar = x; loc = loc} ->
             MLast.PaAny loc,
             MLast.ExTyc
               (loc, e,
                MLast.TyApp
                  (loc,
                   MLast.TyAcc
                     (loc,
                      MLast.LiAcc (loc, MLast.LiUid (loc, gmod), "Entry"),
                      "e"),
                   MLast.TyQuo (loc, x))),
             [])
          nl
      in
      let locals =
        List.map
          (fun {expr = e; tvar = x; loc = loc} ->
             let i =
               match e with
                 MLast.ExLid (_, i) -> i
               | _ -> failwith "internal error in pa_extend"
             in
             MLast.PaLid (loc, i),
             MLast.ExTyc
               (loc,
                MLast.ExApp
                  (loc, MLast.ExLid (loc, "grammar_entry_create"),
                   MLast.ExStr (loc, i)),
                MLast.TyApp
                  (loc,
                   MLast.TyAcc
                     (loc,
                      MLast.LiAcc (loc, MLast.LiUid (loc, gmod), "Entry"),
                      "e"),
                   MLast.TyQuo (loc, x))),
             [])
          ll
      in
      let e =
        if ll = [] then args
        else if functor_version then
          MLast.ExLet
            (loc, false,
             [MLast.PaLid (loc, "grammar_entry_create"),
              MLast.ExFle
                (loc,
                 MLast.ExLong
                   (loc, MLast.LiAcc (loc, MLast.LiUid (loc, gmod), "Entry")),
                 (None, "create")),
              []],
             MLast.ExLet (loc, false, locals, args))
        else
          MLast.ExLet
            (loc, false,
             [MLast.PaLid (loc, "grammar_entry_create"),
              MLast.ExFun
                (loc,
                 [MLast.PaLid (loc, "s"), None,
                  MLast.ExApp
                    (loc,
                     MLast.ExApp
                       (loc,
                        MLast.ExFle
                          (loc, MLast.ExLong (loc, MLast.LiUid (loc, gmod)),
                           (None, "create_local_entry")),
                        MLast.ExApp
                          (loc,
                           MLast.ExFle
                             (loc,
                              MLast.ExLong (loc, MLast.LiUid (loc, gmod)),
                              (None, "of_entry")),
                           locate n1)),
                     MLast.ExLid (loc, "s"))]),
              []],
             MLast.ExLet (loc, false, locals, args))
      in
      MLast.ExLet (loc, false, globals, e)
  | _ -> args
;;

let text_of_extend loc gmod gl el f =
  let el = List.map entry_of_a el in
  let gl = option_map (List.map mk_name2) gl in
  let iloc = Ploc.with_comment loc "" in
  if !split_ext then
    let args =
      let loc = iloc in
      List.map
        (fun e ->
           let (ent, pos, txt) = text_of_entry e.name.loc gmod e in
           let e = MLast.ExTup (loc, [ent; pos; txt]) in
           MLast.ExLet
             (loc, false,
              [MLast.PaLid (loc, "aux"),
               MLast.ExFun
                 (loc,
                  [MLast.PaLong (loc, MLast.LiUid (loc, "()"), []), None,
                   MLast.ExApp
                     (loc, f,
                      MLast.ExApp
                        (loc,
                         MLast.ExApp
                           (loc, MLast.ExLong (loc, MLast.LiUid (loc, "::")),
                            e),
                         MLast.ExLong (loc, MLast.LiUid (loc, "[]"))))]),
               []],
              MLast.ExApp
                (loc, MLast.ExLid (loc, "aux"),
                 MLast.ExLong (loc, MLast.LiUid (loc, "()")))))
        el
    in
    let args = let loc = iloc in MLast.ExSeq (loc, args) in
    let_in_of_extend loc gmod false gl el args
  else
    let args =
      let loc = iloc in
      List.fold_right
        (fun e el ->
           let (ent, pos, txt) = text_of_entry e.name.loc gmod e in
           let e =
             let loc = e.name.loc in
             MLast.ExApp
               (loc,
                MLast.ExApp
                  (loc,
                   MLast.ExApp
                     (loc,
                      MLast.ExFle
                        (loc, MLast.ExLong (loc, MLast.LiUid (loc, gmod)),
                         (None, "extension")),
                      ent),
                   pos),
                txt)
           in
           MLast.ExApp
             (loc,
              MLast.ExApp
                (loc, MLast.ExLong (loc, MLast.LiUid (loc, "::")), e),
              el))
        el (MLast.ExLong (loc, MLast.LiUid (loc, "[]")))
    in
    let args = let_in_of_extend iloc gmod false gl el args in
    MLast.ExApp (loc, f, args)
;;

let text_of_functorial_extend loc gmod gl el =
  let el = List.map entry_of_a el in
  let gl = option_map (List.map mk_name2) gl in
  let args =
    let el =
      List.map
        (fun e ->
           let (ent, pos, txt) = text_of_entry e.name.loc gmod e in
           let e =
             MLast.ExApp
               (loc,
                MLast.ExApp
                  (loc,
                   MLast.ExApp
                     (loc,
                      MLast.ExFle
                        (loc, MLast.ExLong (loc, MLast.LiUid (loc, gmod)),
                         (None, "safe_extend")),
                      ent),
                   pos),
                txt)
           in
           if !split_ext then
             MLast.ExLet
               (loc, false,
                [MLast.PaLid (loc, "aux"),
                 MLast.ExFun
                   (loc,
                    [MLast.PaLong (loc, MLast.LiUid (loc, "()"), []), None,
                     e]),
                 []],
                MLast.ExApp
                  (loc, MLast.ExLid (loc, "aux"),
                   MLast.ExLong (loc, MLast.LiUid (loc, "()"))))
           else e)
        el
    in
    match el with
      [e] -> e
    | _ -> MLast.ExSeq (loc, el)
  in
  let_in_of_extend loc gmod true gl el args
;;

let longname_of_raw_qualid (l, id) = String.concat "__" (l @ [id]);;

let expr_of_raw_qualid loc (l, id) =
  match l with
    _ :: _ ->
      let li = Asttools.longident_of_string_list loc l in
      let vid = id in MLast.ExFle (loc, MLast.ExLong (loc, li), (None, vid))
  | [] -> MLast.ExLid (loc, id)
;;

open Pcaml;;
let symbol = Grammar.Entry.create gram "symbol";;
let rule = Grammar.Entry.create gram "rule";;
let rule_list = Grammar.Entry.create gram "rule_list";;
let level_list = Grammar.Entry.create gram "level_list";;
let level = Grammar.Entry.create gram "level";;
let semi_sep =
  if !syntax_name = "Scheme" then
    Grammar.Entry.of_parser gram "'/'"
      (fun (strm__ : _ Stream.t) ->
         match Stream.peek strm__ with
           Some ("", "/") -> Stream.junk strm__; ()
         | _ -> raise Stream.Failure)
  else
    Grammar.Entry.of_parser gram "';'"
      (fun (strm__ : _ Stream.t) ->
         match Stream.peek strm__ with
           Some ("", ";") -> Stream.junk strm__; ()
         | _ -> raise Stream.Failure)
;;

Grammar.safe_extend
  (let _ = (expr : 'expr Grammar.Entry.e)
   and _ = (symbol : 'symbol Grammar.Entry.e)
   and _ = (rule : 'rule Grammar.Entry.e)
   and _ = (rule_list : 'rule_list Grammar.Entry.e)
   and _ = (level : 'level Grammar.Entry.e)
   and _ = (level_list : 'level_list Grammar.Entry.e) in
   let grammar_entry_create s =
     Grammar.create_local_entry (Grammar.of_entry expr) s
   in
   let extend_body : 'extend_body Grammar.Entry.e =
     grammar_entry_create "extend_body"
   and gextend_body : 'gextend_body Grammar.Entry.e =
     grammar_entry_create "gextend_body"
   and delete_rule_body : 'delete_rule_body Grammar.Entry.e =
     grammar_entry_create "delete_rule_body"
   and gdelete_rule_body : 'gdelete_rule_body Grammar.Entry.e =
     grammar_entry_create "gdelete_rule_body"
   and efunction : 'efunction Grammar.Entry.e =
     grammar_entry_create "efunction"
   and global : 'global Grammar.Entry.e = grammar_entry_create "global"
   and entry : 'entry Grammar.Entry.e = grammar_entry_create "entry"
   and position : 'position Grammar.Entry.e = grammar_entry_create "position"
   and assoc : 'assoc Grammar.Entry.e = grammar_entry_create "assoc"
   and psymbol : 'psymbol Grammar.Entry.e = grammar_entry_create "psymbol"
   and sep_opt_sep : 'sep_opt_sep Grammar.Entry.e =
     grammar_entry_create "sep_opt_sep"
   and pattern : 'pattern Grammar.Entry.e = grammar_entry_create "pattern"
   and patterns_comma : 'patterns_comma Grammar.Entry.e =
     grammar_entry_create "patterns_comma"
   and name : 'name Grammar.Entry.e = grammar_entry_create "name"
   and qualid : 'qualid Grammar.Entry.e = grammar_entry_create "qualid"
   and raw_qualid : 'raw_qualid Grammar.Entry.e =
     grammar_entry_create "raw_qualid"
   and string : 'string Grammar.Entry.e = grammar_entry_create "string" in
   [Grammar.extension (expr : 'expr Grammar.Entry.e)
      (Some (Gramext.After "top"))
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_cut
                   (Grammar.r_next Grammar.r_stop
                      (Grammar.s_token ("", "GDELETE_RULE"))))
                (Grammar.s_nterm
                   (gdelete_rule_body : 'gdelete_rule_body Grammar.Entry.e)))
             (Grammar.s_token ("", "END")),
           "194fe98d",
           (fun _ (e : 'gdelete_rule_body) _ (loc : Ploc.t) -> (e : 'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_cut
                   (Grammar.r_next Grammar.r_stop
                      (Grammar.s_token ("", "DELETE_RULE"))))
                (Grammar.s_nterm
                   (delete_rule_body : 'delete_rule_body Grammar.Entry.e)))
             (Grammar.s_token ("", "END")),
           "194fe98d",
           (fun _ (e : 'delete_rule_body) _ (loc : Ploc.t) -> (e : 'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_cut
                   (Grammar.r_next Grammar.r_stop
                      (Grammar.s_token ("", "GEXTEND"))))
                (Grammar.s_nterm
                   (gextend_body : 'gextend_body Grammar.Entry.e)))
             (Grammar.s_token ("", "END")),
           "194fe98d",
           (fun _ (e : 'gextend_body) _ (loc : Ploc.t) -> (e : 'expr)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_cut
                   (Grammar.r_next Grammar.r_stop
                      (Grammar.s_token ("", "EXTEND"))))
                (Grammar.s_nterm
                   (extend_body : 'extend_body Grammar.Entry.e)))
             (Grammar.s_token ("", "END")),
           "194fe98d",
           (fun _ (e : 'extend_body) _ (loc : Ploc.t) -> (e : 'expr)))]];
    Grammar.extension (extend_body : 'extend_body Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop
                   (Grammar.s_nterm (efunction : 'efunction Grammar.Entry.e)))
                (Grammar.s_opt
                   (Grammar.s_nterm (global : 'global Grammar.Entry.e))))
             (Grammar.s_list1
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_nterm
                               (entry : 'entry Grammar.Entry.e)))
                         (Grammar.s_nterm
                            (semi_sep : 'semi_sep Grammar.Entry.e)),
                       "194fe98d",
                       (fun _ (e : 'entry) (loc : Ploc.t) -> (e : 'e__1)))])),
           "194fe98d",
           (fun (el : 'e__1 list) (sl : 'global option) (f : 'efunction)
                (loc : Ploc.t) ->
              (text_of_extend loc "Grammar" sl el f : 'extend_body)))]];
    Grammar.extension (gextend_body : 'gextend_body Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop
                   (Grammar.s_token ("UIDENT", "")))
                (Grammar.s_opt
                   (Grammar.s_nterm (global : 'global Grammar.Entry.e))))
             (Grammar.s_list1
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_nterm
                               (entry : 'entry Grammar.Entry.e)))
                         (Grammar.s_nterm
                            (semi_sep : 'semi_sep Grammar.Entry.e)),
                       "194fe98d",
                       (fun _ (e : 'entry) (loc : Ploc.t) -> (e : 'e__2)))])),
           "194fe98d",
           (fun (el : 'e__2 list) (sl : 'global option) (g : string)
                (loc : Ploc.t) ->
              (text_of_functorial_extend loc g sl el : 'gextend_body)))]];
    Grammar.extension (delete_rule_body : 'delete_rule_body Grammar.Entry.e)
      None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop
                   (Grammar.s_nterm (name : 'name Grammar.Entry.e)))
                (Grammar.s_token ("", ":")))
             (Grammar.s_list1sep
                (Grammar.s_nterm (symbol : 'symbol Grammar.Entry.e))
                (Grammar.s_nterm (semi_sep : 'semi_sep Grammar.Entry.e))
                false),
           "194fe98d",
           (fun (sl : 'symbol list) _ (n : 'name) (loc : Ploc.t) ->
              (let (e, b) = expr_of_delete_rule loc "Grammar" n sl in
               MLast.ExApp
                 (loc,
                  MLast.ExApp
                    (loc,
                     MLast.ExFle
                       (loc, MLast.ExLong (loc, MLast.LiUid (loc, "Grammar")),
                        (None, "safe_delete_rule")),
                     e),
                  b) :
               'delete_rule_body)))]];
    Grammar.extension (gdelete_rule_body : 'gdelete_rule_body Grammar.Entry.e)
      None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next Grammar.r_stop
                      (Grammar.s_token ("UIDENT", "")))
                   (Grammar.s_nterm (name : 'name Grammar.Entry.e)))
                (Grammar.s_token ("", ":")))
             (Grammar.s_list1sep
                (Grammar.s_nterm (symbol : 'symbol Grammar.Entry.e))
                (Grammar.s_nterm (semi_sep : 'semi_sep Grammar.Entry.e))
                false),
           "194fe98d",
           (fun (sl : 'symbol list) _ (n : 'name) (g : string)
                (loc : Ploc.t) ->
              (let (e, b) = expr_of_delete_rule loc g n sl in
               MLast.ExApp
                 (loc,
                  MLast.ExApp
                    (loc,
                     MLast.ExFle
                       (loc, MLast.ExLong (loc, MLast.LiUid (loc, g)),
                        (None, "safe_delete_rule")),
                     e),
                  b) :
               'gdelete_rule_body)))]];
    Grammar.extension (efunction : 'efunction Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_stop, "194fe98d",
           (fun (loc : Ploc.t) ->
              (MLast.ExFle
                 (loc, MLast.ExLong (loc, MLast.LiUid (loc, "Grammar")),
                  (None, "safe_extend")) :
               'efunction)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next Grammar.r_stop
                      (Grammar.s_token ("UIDENT", "FUNCTION")))
                   (Grammar.s_token ("", ":")))
                (Grammar.s_nterm (qualid : 'qualid Grammar.Entry.e)))
             (Grammar.s_nterm (semi_sep : 'semi_sep Grammar.Entry.e)),
           "194fe98d",
           (fun _ (f : 'qualid) _ _ (loc : Ploc.t) ->
              (snd f : 'efunction)))]];
    Grammar.extension (global : 'global Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next Grammar.r_stop
                      (Grammar.s_token ("UIDENT", "GLOBAL")))
                   (Grammar.s_token ("", ":")))
                (Grammar.s_list1
                   (Grammar.s_nterm (name : 'name Grammar.Entry.e))))
             (Grammar.s_nterm (semi_sep : 'semi_sep Grammar.Entry.e)),
           "194fe98d",
           (fun _ (sl : 'name list) _ _ (loc : Ploc.t) -> (sl : 'global)))]];
    Grammar.extension (entry : 'entry Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next Grammar.r_stop
                      (Grammar.s_nterm (name : 'name Grammar.Entry.e)))
                   (Grammar.s_token ("", ":")))
                (Grammar.s_opt
                   (Grammar.s_nterm (position : 'position Grammar.Entry.e))))
             (Grammar.s_nterm (level_list : 'level_list Grammar.Entry.e)),
           "194fe98d",
           (fun (ll : 'level_list) (pos : 'position option) _ (n : 'name)
                (loc : Ploc.t) ->
              ({ae_loc = loc; ae_name = n; ae_pos = pos; ae_levels = ll} :
               'entry)))]];
    Grammar.extension (position : 'position Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop
                (Grammar.s_token ("UIDENT", "LEVEL")))
             (Grammar.s_nterm (string : 'string Grammar.Entry.e)),
           "194fe98d",
           (fun (n : 'string) _ (loc : Ploc.t) ->
              (MLast.ExApp
                 (loc,
                  MLast.ExLong
                    (loc,
                     MLast.LiAcc
                       (loc, MLast.LiUid (loc, "Gramext"), "Level")),
                  string_of_a n) :
               'position)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop
                (Grammar.s_token ("UIDENT", "LIKE")))
             (Grammar.s_nterm (string : 'string Grammar.Entry.e)),
           "194fe98d",
           (fun (n : 'string) _ (loc : Ploc.t) ->
              (MLast.ExApp
                 (loc,
                  MLast.ExLong
                    (loc,
                     MLast.LiAcc (loc, MLast.LiUid (loc, "Gramext"), "Like")),
                  string_of_a n) :
               'position)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop
                (Grammar.s_token ("UIDENT", "AFTER")))
             (Grammar.s_nterm (string : 'string Grammar.Entry.e)),
           "194fe98d",
           (fun (n : 'string) _ (loc : Ploc.t) ->
              (MLast.ExApp
                 (loc,
                  MLast.ExLong
                    (loc,
                     MLast.LiAcc
                       (loc, MLast.LiUid (loc, "Gramext"), "After")),
                  string_of_a n) :
               'position)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop
                (Grammar.s_token ("UIDENT", "BEFORE")))
             (Grammar.s_nterm (string : 'string Grammar.Entry.e)),
           "194fe98d",
           (fun (n : 'string) _ (loc : Ploc.t) ->
              (MLast.ExApp
                 (loc,
                  MLast.ExLong
                    (loc,
                     MLast.LiAcc
                       (loc, MLast.LiUid (loc, "Gramext"), "Before")),
                  string_of_a n) :
               'position)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop (Grammar.s_token ("UIDENT", "LAST")),
           "194fe98d",
           (fun _ (loc : Ploc.t) ->
              (MLast.ExLong
                 (loc,
                  MLast.LiAcc (loc, MLast.LiUid (loc, "Gramext"), "Last")) :
               'position)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_token ("UIDENT", "FIRST")),
           "194fe98d",
           (fun _ (loc : Ploc.t) ->
              (MLast.ExLong
                 (loc,
                  MLast.LiAcc (loc, MLast.LiUid (loc, "Gramext"), "First")) :
               'position)))]];
    Grammar.extension (level_list : 'level_list Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "[")))
                (Grammar.s_list0sep
                   (Grammar.s_nterm (level : 'level Grammar.Entry.e))
                   (Grammar.s_token ("", "|")) false))
             (Grammar.s_token ("", "]")),
           "194fe98d",
           (fun _ (ll : 'level list) _ (loc : Ploc.t) ->
              (ll : 'level_list)))]];
    Grammar.extension (level : 'level Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop
                   (Grammar.s_opt (Grammar.s_token ("STRING", ""))))
                (Grammar.s_opt
                   (Grammar.s_nterm (assoc : 'assoc Grammar.Entry.e))))
             (Grammar.s_nterm (rule_list : 'rule_list Grammar.Entry.e)),
           "194fe98d",
           (fun (rules : 'rule_list) (ass : 'assoc option)
                (lab : string option) (loc : Ploc.t) ->
              ({al_loc = loc; al_label = lab; al_assoc = ass;
                al_rules = rules} :
               'level)))]];
    Grammar.extension (assoc : 'assoc Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next Grammar.r_stop (Grammar.s_token ("UIDENT", "NONA")),
           "194fe98d",
           (fun _ (loc : Ploc.t) ->
              (MLast.ExLong
                 (loc,
                  MLast.LiAcc (loc, MLast.LiUid (loc, "Gramext"), "NonA")) :
               'assoc)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_token ("UIDENT", "RIGHTA")),
           "194fe98d",
           (fun _ (loc : Ploc.t) ->
              (MLast.ExLong
                 (loc,
                  MLast.LiAcc (loc, MLast.LiUid (loc, "Gramext"), "RightA")) :
               'assoc)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_token ("UIDENT", "LEFTA")),
           "194fe98d",
           (fun _ (loc : Ploc.t) ->
              (MLast.ExLong
                 (loc,
                  MLast.LiAcc (loc, MLast.LiUid (loc, "Gramext"), "LeftA")) :
               'assoc)))]];
    Grammar.extension (rule_list : 'rule_list Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "[")))
                (Grammar.s_list1sep
                   (Grammar.s_nterm (rule : 'rule Grammar.Entry.e))
                   (Grammar.s_token ("", "|")) false))
             (Grammar.s_token ("", "]")),
           "194fe98d",
           (fun _ (rules : 'rule list) _ (loc : Ploc.t) ->
              ({au_loc = loc; au_rules = rules} : 'rule_list)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "[")))
             (Grammar.s_token ("", "]")),
           "194fe98d",
           (fun _ _ (loc : Ploc.t) ->
              ({au_loc = loc; au_rules = []} : 'rule_list)))]];
    Grammar.extension (rule : 'rule Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_list0sep
                (Grammar.s_nterm (psymbol : 'psymbol Grammar.Entry.e))
                (Grammar.s_nterm (semi_sep : 'semi_sep Grammar.Entry.e))
                false),
           "194fe98d",
           (fun (psl : 'psymbol list) (loc : Ploc.t) ->
              ({ar_loc = loc; ar_psymbols = psl; ar_action = None} : 'rule)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop
                   (Grammar.s_list0sep
                      (Grammar.s_nterm (psymbol : 'psymbol Grammar.Entry.e))
                      (Grammar.s_nterm (semi_sep : 'semi_sep Grammar.Entry.e))
                      false))
                (Grammar.s_token ("", "->")))
             (Grammar.s_nterm (expr : 'expr Grammar.Entry.e)),
           "194fe98d",
           (fun (act : 'expr) _ (psl : 'psymbol list) (loc : Ploc.t) ->
              ({ar_loc = loc; ar_psymbols = psl; ar_action = Some act} :
               'rule)))]];
    Grammar.extension (psymbol : 'psymbol Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_nterm (symbol : 'symbol Grammar.Entry.e)),
           "194fe98d",
           (fun (s : 'symbol) (loc : Ploc.t) ->
              ({ap_loc = loc; ap_patt = None; ap_symb = s} : 'psymbol)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop
                   (Grammar.s_nterm (pattern : 'pattern Grammar.Entry.e)))
                (Grammar.s_token ("", "=")))
             (Grammar.s_nterm (symbol : 'symbol Grammar.Entry.e)),
           "194fe98d",
           (fun (s : 'symbol) _ (p : 'pattern) (loc : Ploc.t) ->
              ({ap_loc = loc; ap_patt = Some p; ap_symb = s} : 'psymbol)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("LIDENT", "")))
             (Grammar.s_opt
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("UIDENT", "LEVEL")))
                         (Grammar.s_token ("STRING", "")),
                       "194fe98d",
                       (fun (s : string) _ (loc : Ploc.t) -> (s : 'e__3)))])),
           "194fe98d",
           (fun (lev : 'e__3 option) (i : string) (loc : Ploc.t) ->
              (let n = MLast.ExLid (loc, i) in
               {ap_loc = loc; ap_patt = None;
                ap_symb = ASnterm (loc, (i, n), lev)} :
               'psymbol)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop
                   (Grammar.s_token ("LIDENT", "")))
                (Grammar.s_token ("", "=")))
             (Grammar.s_nterm (symbol : 'symbol Grammar.Entry.e)),
           "194fe98d",
           (fun (s : 'symbol) _ (p : string) (loc : Ploc.t) ->
              ({ap_loc = loc; ap_patt = Some (MLast.PaLid (loc, p));
                ap_symb = s} :
               'psymbol)))]];
    Grammar.extension (sep_opt_sep : 'sep_opt_sep Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop
                   (Grammar.s_token ("UIDENT", "SEP")))
                (Grammar.s_nterm (symbol : 'symbol Grammar.Entry.e)))
             (Grammar.s_flag
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("UIDENT", "OPT_SEP")),
                       "194fe98d",
                       (fun (x : string) (loc : Ploc.t) -> (x : 'e__4)))])),
           "194fe98d",
           (fun (b : bool) (t : 'symbol) (sep : string) (loc : Ploc.t) ->
              (t, b : 'sep_opt_sep)))]];
    Grammar.extension (symbol : 'symbol Grammar.Entry.e) None
      [Some "top", Some Gramext.NonA,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop
                (Grammar.s_token ("UIDENT", "FLAG")))
             Grammar.s_self,
           "194fe98d",
           (fun (s : 'symbol) _ (loc : Ploc.t) ->
              (ASflag (loc, s) : 'symbol)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop
                (Grammar.s_token ("UIDENT", "OPT")))
             Grammar.s_self,
           "194fe98d",
           (fun (s : 'symbol) _ (loc : Ploc.t) ->
              (ASopt (loc, s) : 'symbol)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop
                   (Grammar.s_token ("UIDENT", "LIST1")))
                Grammar.s_self)
             (Grammar.s_opt
                (Grammar.s_nterm
                   (sep_opt_sep : 'sep_opt_sep Grammar.Entry.e))),
           "194fe98d",
           (fun (sep : 'sep_opt_sep option) (s : 'symbol) _ (loc : Ploc.t) ->
              (ASlist (loc, LML_1, s, sep) : 'symbol)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop
                   (Grammar.s_token ("UIDENT", "LIST0")))
                Grammar.s_self)
             (Grammar.s_opt
                (Grammar.s_nterm
                   (sep_opt_sep : 'sep_opt_sep Grammar.Entry.e))),
           "194fe98d",
           (fun (sep : 'sep_opt_sep option) (s : 'symbol) _ (loc : Ploc.t) ->
              (ASlist (loc, LML_0, s, sep) : 'symbol)))];
       Some "vala", None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop
                   (Grammar.s_token ("UIDENT", "V")))
                Grammar.s_next)
             (Grammar.s_list0 (Grammar.s_token ("STRING", ""))),
           "194fe98d",
           (fun (al : string list) (s : 'symbol) _ (loc : Ploc.t) ->
              (ASvala (loc, s, al) : 'symbol)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop
                   (Grammar.s_token ("UIDENT", "V")))
                (Grammar.s_token ("UIDENT", "")))
             (Grammar.s_list0 (Grammar.s_token ("STRING", ""))),
           "194fe98d",
           (fun (al : string list) (x : string) _ (loc : Ploc.t) ->
              (let s = AStok (loc, x, None) in ASvala (loc, s, al) :
               'symbol)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop
                   (Grammar.s_token ("UIDENT", "V")))
                (Grammar.s_token ("UIDENT", "NEXT")))
             (Grammar.s_list0 (Grammar.s_token ("STRING", ""))),
           "194fe98d",
           (fun (al : string list) _ _ (loc : Ploc.t) ->
              (let s = ASnext loc in ASvala (loc, s, al) : 'symbol)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop
                   (Grammar.s_token ("UIDENT", "V")))
                (Grammar.s_token ("UIDENT", "SELF")))
             (Grammar.s_list0 (Grammar.s_token ("STRING", ""))),
           "194fe98d",
           (fun (al : string list) _ _ (loc : Ploc.t) ->
              (let s = ASself loc in ASvala (loc, s, al) : 'symbol)))];
       Some "simple", None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "(")))
                Grammar.s_self)
             (Grammar.s_token ("", ")")),
           "194fe98d",
           (fun _ (s_t : 'symbol) _ (loc : Ploc.t) -> (s_t : 'symbol)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "/")),
           "194fe98d", (fun _ (loc : Ploc.t) -> (AScut loc : 'symbol)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop
                (Grammar.s_nterm (name : 'name Grammar.Entry.e)))
             (Grammar.s_opt
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("UIDENT", "LEVEL")))
                         (Grammar.s_token ("STRING", "")),
                       "194fe98d",
                       (fun (s : string) _ (loc : Ploc.t) -> (s : 'e__6)))])),
           "194fe98d",
           (fun (lev : 'e__6 option) (n : 'name) (loc : Ploc.t) ->
              (ASnterm (loc, n, lev) : 'symbol)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next Grammar.r_stop
                      (Grammar.s_token ("UIDENT", "")))
                   (Grammar.s_token ("", ".")))
                (Grammar.s_nterm (raw_qualid : 'raw_qualid Grammar.Entry.e)))
             (Grammar.s_opt
                (Grammar.s_rules
                   [Grammar.production
                      (Grammar.r_next
                         (Grammar.r_next Grammar.r_stop
                            (Grammar.s_token ("UIDENT", "LEVEL")))
                         (Grammar.s_token ("STRING", "")),
                       "194fe98d",
                       (fun (s : string) _ (loc : Ploc.t) -> (s : 'e__5)))])),
           "194fe98d",
           (fun (lev : 'e__5 option) (l, id : 'raw_qualid) _ (i : string)
                (loc : Ploc.t) ->
              (let l = i :: l in
               let qidname = longname_of_raw_qualid (l, id) in
               let v = expr_of_raw_qualid loc (l, id) in
               ASnterm (loc, (qidname, v), lev) :
               'symbol)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_nterm (string : 'string Grammar.Entry.e)),
           "194fe98d",
           (fun (e : 'string) (loc : Ploc.t) -> (ASkeyw (loc, e) : 'symbol)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop (Grammar.s_token ("UIDENT", "")))
             (Grammar.s_nterm (string : 'string Grammar.Entry.e)),
           "194fe98d",
           (fun (e : 'string) (x : string) (loc : Ploc.t) ->
              (AStok (loc, x, Some e) : 'symbol)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop (Grammar.s_token ("UIDENT", "")),
           "194fe98d",
           (fun (x : string) (loc : Ploc.t) ->
              (AStok (loc, x, None) : 'symbol)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "[")))
                (Grammar.s_list0sep
                   (Grammar.s_nterm (rule : 'rule Grammar.Entry.e))
                   (Grammar.s_token ("", "|")) false))
             (Grammar.s_token ("", "]")),
           "194fe98d",
           (fun _ (rl : 'rule list) _ (loc : Ploc.t) ->
              (ASrules (loc, {au_loc = loc; au_rules = rl}) : 'symbol)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop (Grammar.s_token ("UIDENT", "NEXT")),
           "194fe98d", (fun _ (loc : Ploc.t) -> (ASnext loc : 'symbol)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop (Grammar.s_token ("UIDENT", "SELF")),
           "194fe98d", (fun _ (loc : Ploc.t) -> (ASself loc : 'symbol)))]];
    Grammar.extension (pattern : 'pattern Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next
                   (Grammar.r_next
                      (Grammar.r_next Grammar.r_stop
                         (Grammar.s_token ("", "(")))
                      Grammar.s_self)
                   (Grammar.s_token ("", ",")))
                (Grammar.s_nterm
                   (patterns_comma : 'patterns_comma Grammar.Entry.e)))
             (Grammar.s_token ("", ")")),
           "194fe98d",
           (fun _ (pl : 'patterns_comma) _ (p : 'pattern) _ (loc : Ploc.t) ->
              (MLast.PaTup (loc, p :: pl) : 'pattern)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "(")))
                Grammar.s_self)
             (Grammar.s_token ("", ")")),
           "194fe98d",
           (fun _ (p : 'pattern) _ (loc : Ploc.t) -> (p : 'pattern)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "_")),
           "194fe98d",
           (fun _ (loc : Ploc.t) -> (MLast.PaAny loc : 'pattern)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop (Grammar.s_token ("LIDENT", "")),
           "194fe98d",
           (fun (i : string) (loc : Ploc.t) ->
              (MLast.PaLid (loc, i) : 'pattern)))]];
    Grammar.extension (patterns_comma : 'patterns_comma Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next (Grammar.r_next Grammar.r_stop Grammar.s_self)
                (Grammar.s_token ("", ",")))
             (Grammar.s_nterm (pattern : 'pattern Grammar.Entry.e)),
           "194fe98d",
           (fun (p : 'pattern) _ (pl : 'patterns_comma) (loc : Ploc.t) ->
              (pl @ [p] : 'patterns_comma)))];
       None, None,
       [Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_nterm (pattern : 'pattern Grammar.Entry.e)),
           "194fe98d",
           (fun (p : 'pattern) (loc : Ploc.t) -> ([p] : 'patterns_comma)))]];
    Grammar.extension (name : 'name Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_nterm (qualid : 'qualid Grammar.Entry.e)),
           "194fe98d", (fun (e : 'qualid) (loc : Ploc.t) -> (e : 'name)))]];
    Grammar.extension (qualid : 'qualid Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next Grammar.r_stop
             (Grammar.s_nterm (raw_qualid : 'raw_qualid Grammar.Entry.e)),
           "194fe98d",
           (fun (l, id : 'raw_qualid) (loc : Ploc.t) ->
              (let qidname = longname_of_raw_qualid (l, id) in
               let v = expr_of_raw_qualid loc (l, id) in qidname, v :
               'qualid)))]];
    Grammar.extension (raw_qualid : 'raw_qualid Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next Grammar.r_stop (Grammar.s_token ("LIDENT", "")),
           "194fe98d",
           (fun (id : string) (loc : Ploc.t) -> ([], id : 'raw_qualid)));
        Grammar.production
          (Grammar.r_next
             (Grammar.r_next Grammar.r_stop
                (Grammar.s_list1
                   (Grammar.s_rules
                      [Grammar.production
                         (Grammar.r_next
                            (Grammar.r_next Grammar.r_stop
                               (Grammar.s_token ("UIDENT", "")))
                            (Grammar.s_token ("", ".")),
                          "194fe98d",
                          (fun _ (i : string) (loc : Ploc.t) ->
                             (i : 'e__7)))])))
             (Grammar.s_token ("LIDENT", "")),
           "194fe98d",
           (fun (id : string) (l : 'e__7 list) (loc : Ploc.t) ->
              (l, id : 'raw_qualid)))]];
    Grammar.extension (string : 'string Grammar.Entry.e) None
      [None, None,
       [Grammar.production
          (Grammar.r_next
             (Grammar.r_next
                (Grammar.r_next Grammar.r_stop (Grammar.s_token ("", "$")))
                (Grammar.s_nterm (expr : 'expr Grammar.Entry.e)))
             (Grammar.s_token ("", "$")),
           "194fe98d",
           (fun _ (e : 'expr) _ (loc : Ploc.t) ->
              (ATexpr (loc, e) : 'string)));
        Grammar.production
          (Grammar.r_next Grammar.r_stop (Grammar.s_token ("STRING", "")),
           "194fe98d",
           (fun (s : string) (loc : Ploc.t) ->
              (ATstring (loc, s) : 'string)))]]]);;

Pcaml.add_option "-quotify" (Arg.Set quotify) "Generate code for quotations";;
Pcaml.add_option "-meta_action" (Arg.Set meta_action) "Undocumented";;
