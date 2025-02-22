(* camlp5r *)
(* q_ast_base.ml,v *)
(* Copyright (c) INRIA 2007-2017 *)

(* #load "pa_macro.cmo" *)
(* #load "pa_extend.cmo" *)
(* #load "q_MLast.cmo" *)

(* AST quotations that works by running the language parser (and its possible
   extensions) and meta-ifying the nodes. Works completely only in "strict"
   mode. In "transitional" mode, not all antiquotations are available. *)

let eval_anti entry loc typ str =
  let loc =
    let sh =
      if typ = "" then String.length "$"
      else String.length "$" + String.length typ + String.length ":"
    in
    let len = String.length str in Ploc.sub loc sh len
  in
  let r =
    try
      Ploc.call_with Plexer.force_antiquot_loc false
        (Grammar.Entry.parse entry) (Stream.of_string str)
    with Ploc.Exc (loc1, exc) ->
      let shift = Ploc.first_pos loc in
      let loc =
        Ploc.make_loc (Ploc.file_name loc)
          (Ploc.line_nb loc + Ploc.line_nb loc1 - 1)
          (if Ploc.line_nb loc1 = 1 then Ploc.bol_pos loc
           else shift + Ploc.bol_pos loc1)
          (shift + Ploc.first_pos loc1, shift + Ploc.last_pos loc1) ""
      in
      raise (Ploc.Exc (loc, exc))
  in
  loc, r
;;

let skip_to_next_colon s i =
  let rec loop j =
    if j = String.length s then i, 0
    else
      match s.[j] with
        ':' -> j, j - i - 1
      | 'a'..'z' | 'A'..'Z' | '0'..'9' | '!' | '_' -> loop (j + 1)
      | _ -> i, 0
  in
  loop (i + 1)
;;

let split_anti_loc s =
  try
    let i = String.index s ':' in
    let (j, len) = skip_to_next_colon s i in
    let locs = String.sub s 0 i in
    let kind = String.sub s (i + 1) len in
    let rest = String.sub s (j + 1) (String.length s - j - 1) in
    Some (locs, kind, rest)
  with Not_found | Failure _ -> None
;;

let replace_antiloc_kind ~newkind s =
  match split_anti_loc s with
    None -> s
  | Some (locs, _, rest) -> String.concat ":" [locs; newkind; rest]
;;

let get_anti_loc s =
  try
    let i = String.index s ':' in
    let (j, len) = skip_to_next_colon s i in
    let kind = String.sub s (i + 1) len in
    let loc =
      let k = String.index s ',' in
      let bp = int_of_string (String.sub s 0 k) in
      let ep = int_of_string (String.sub s (k + 1) (i - k - 1)) in
      Ploc.make_unlined (bp, ep)
    in
    Some (loc, kind, String.sub s (j + 1) (String.length s - j - 1))
  with Not_found | Failure _ -> None
;;

module type MetaSig =
  sig
    type t;;
    type prefix_t;;
    val loc_v : unit -> t;;
    val node : ?prefix:prefix_t -> string -> t list -> t;;
    val node_no_loc : ?prefix:prefix_t -> string -> t list -> t;;
    val list : ('a -> t) -> 'a list -> t;;
    val option : ('a -> t) -> 'a option -> t;;
    val vala : ('a -> t) -> 'a MLast.v -> t;;
    val char : char -> t;;
    val bool : bool -> t;;
    val int : int -> t;;
    val int32 : int32 -> t;;
    val int64 : int64 -> t;;
    val nativeint : nativeint -> t;;
    val float : float -> t;;
    val string : string -> t;;
    val tuple : t list -> t;;
    val record : (MLast.patt * t) list -> t;;
    val xtr_typed : string -> Ploc.t -> string -> t;;
    val xtr : Ploc.t -> string -> t;;
    val xtr_or_anti : Ploc.t -> (t -> t) -> string -> t;;
  end
;;

let anti_anti n = "_" ^ n;;
let is_anti_anti n = String.length n > 0 && n.[0] = '_';;

module E_MetaSig =
  struct
    type t = MLast.expr;;
    type prefix_t = MLast.longid;;
    let loc = Ploc.dummy;;
    let loc_v () = MLast.ExLid (loc, !(Ploc.name));;
    let node ?prefix con el =
      let prefix =
        match prefix with
          None -> MLast.LiUid (loc, "MLast")
        | Some p -> p
      in
      List.fold_left (fun e1 e2 -> MLast.ExApp (loc, e1, e2))
        (MLast.ExApp
           (loc, MLast.ExLong (loc, MLast.LiAcc (loc, prefix, con)),
            loc_v ()))
        el
    ;;
    let node_no_loc ?prefix con el =
      let prefix =
        match prefix with
          None -> MLast.LiUid (loc, "MLast")
        | Some p -> p
      in
      List.fold_left (fun e1 e2 -> MLast.ExApp (loc, e1, e2))
        (MLast.ExLong (loc, MLast.LiAcc (loc, prefix, con))) el
    ;;
    let list elem el =
      let rec loop el =
        match el with
          [] -> MLast.ExLong (loc, MLast.LiUid (loc, "[]"))
        | e :: el ->
            MLast.ExApp
              (loc,
               MLast.ExApp
                 (loc, MLast.ExLong (loc, MLast.LiUid (loc, "::")), elem e),
               loop el)
      in
      loop el
    ;;
    let option elem oe =
      match oe with
        None -> MLast.ExLong (loc, MLast.LiUid (loc, "None"))
      | Some e ->
          MLast.ExApp
            (loc, MLast.ExLong (loc, MLast.LiUid (loc, "Some")), elem e)
    ;;
    let vala elem e = elem e;;
    let char c = let c = Char.escaped c in MLast.ExChr (loc, c);;
    let bool b =
      if b then MLast.ExLong (loc, MLast.LiUid (loc, "True"))
      else MLast.ExLong (loc, MLast.LiUid (loc, "False"))
    ;;
    let int n =
      let loc = Ploc.dummy in MLast.ExInt (loc, string_of_int n, "")
    ;;
    let int32 n =
      let loc = Ploc.dummy in MLast.ExInt (loc, Int32.to_string n, "l")
    ;;
    let int64 n =
      let loc = Ploc.dummy in MLast.ExInt (loc, Int64.to_string n, "L")
    ;;
    let nativeint n =
      let loc = Ploc.dummy in MLast.ExInt (loc, Nativeint.to_string n, "n")
    ;;
    let float n =
      let loc = Ploc.dummy in MLast.ExFlo (loc, Float.to_string n)
    ;;
    let string s = MLast.ExStr (loc, (loc, s));;
    let tuple le = MLast.ExTup (loc, le);;
    let record lfe = MLast.ExRec (loc, lfe, None);;
    let xtr_typed wantty loc s =
      match get_anti_loc s with
        Some (_, typ, str) when typ = wantty ->
          let (loc, r) = eval_anti Pcaml.expr_eoi loc "" str in
          MLast.ExAnt (loc, r)
      | _ -> assert false
    ;;
    let xtr loc s =
      match get_anti_loc s with
        Some (_, typ, str) ->
          begin match typ with
            "" ->
              let (loc, r) = eval_anti Pcaml.expr_eoi loc "" str in
              MLast.ExAnt (loc, r)
          | _ -> assert false
          end
      | None -> assert false
    ;;
    let xtr_or_anti loc f s =
      match get_anti_loc s with
        Some (_, typ, str) ->
          begin match typ with
            "" | "exp" ->
              let (loc, r) = eval_anti Pcaml.expr_eoi loc typ str in
              MLast.ExAnt (loc, r)
          | "anti" ->
              let (loc, r) = eval_anti Pcaml.expr_eoi loc "anti" str in
              f (MLast.ExAnt (loc, r))
          | _ -> assert false
          end
      | None -> assert false
    ;;
  end
;;

module P_MetaSig =
  struct
    type t = MLast.patt;;
    type prefix_t = MLast.longid;;
    let loc = Ploc.dummy;;
    let loc_v () = MLast.PaAny loc;;
    let node ?prefix con pl =
      let prefix =
        match prefix with
          None -> MLast.LiUid (loc, "MLast")
        | Some p -> p
      in
      List.fold_left (fun p1 p2 -> MLast.PaApp (loc, p1, p2))
        (MLast.PaApp
           (loc, MLast.PaLong (loc, MLast.LiAcc (loc, prefix, con), []),
            MLast.PaAny loc))
        pl
    ;;
    let node_no_loc ?prefix con pl =
      let prefix =
        match prefix with
          None -> MLast.LiUid (loc, "MLast")
        | Some p -> p
      in
      List.fold_left (fun p1 p2 -> MLast.PaApp (loc, p1, p2))
        (MLast.PaLong (loc, MLast.LiAcc (loc, prefix, con), [])) pl
    ;;
    let list elem el =
      let rec loop el =
        match el with
          [] -> MLast.PaLong (loc, MLast.LiUid (loc, "[]"), [])
        | e :: el ->
            MLast.PaApp
              (loc,
               MLast.PaApp
                 (loc, MLast.PaLong (loc, MLast.LiUid (loc, "::"), []),
                  elem e),
               loop el)
      in
      loop el
    ;;
    let option elem oe =
      match oe with
        None -> MLast.PaLong (loc, MLast.LiUid (loc, "None"), [])
      | Some e ->
          MLast.PaApp
            (loc, MLast.PaLong (loc, MLast.LiUid (loc, "Some"), []), elem e)
    ;;
    let vala elem p = elem p;;
    let char c = let c = Char.escaped c in MLast.PaChr (loc, c);;
    let bool b =
      if b then MLast.PaLong (loc, MLast.LiUid (loc, "True"), [])
      else MLast.PaLong (loc, MLast.LiUid (loc, "False"), [])
    ;;
    let int n =
      let loc = Ploc.dummy in MLast.PaInt (loc, string_of_int n, "")
    ;;
    let int32 n =
      let loc = Ploc.dummy in MLast.PaInt (loc, Int32.to_string n, "l")
    ;;
    let int64 n =
      let loc = Ploc.dummy in MLast.PaInt (loc, Int64.to_string n, "L")
    ;;
    let nativeint n =
      let loc = Ploc.dummy in MLast.PaInt (loc, Nativeint.to_string n, "n")
    ;;
    let float n =
      let loc = Ploc.dummy in MLast.PaFlo (loc, Float.to_string n)
    ;;
    let string s = MLast.PaStr (loc, s);;
    let tuple lp = MLast.PaTup (loc, lp);;
    let record lfp = MLast.PaRec (loc, lfp);;
    let xtr_typed wantty loc s =
      match get_anti_loc s with
        Some (_, typ, str) when typ = wantty ->
          let (loc, r) = eval_anti Pcaml.patt_eoi loc "" str in
          MLast.PaAnt (loc, r)
      | _ -> assert false
    ;;
    let xtr loc s =
      match get_anti_loc s with
        Some (_, typ, str) ->
          begin match typ with
            "" ->
              let (loc, r) = eval_anti Pcaml.patt_eoi loc "" str in
              MLast.PaAnt (loc, r)
          | _ -> assert false
          end
      | None -> assert false
    ;;
    let xtr_or_anti loc f s =
      match get_anti_loc s with
        Some (_, typ, str) ->
          begin match typ with
            "" | "exp" ->
              let (loc, r) = eval_anti Pcaml.patt_eoi loc "exp" str in
              MLast.PaAnt (loc, r)
          | "anti" ->
              let (loc, r) = eval_anti Pcaml.patt_eoi loc "anti" str in
              f (MLast.PaAnt (loc, r))
          | _ -> assert false
          end
      | None -> assert false
    ;;
  end
;;

(* *)

let check_anti_loc s =
  try
    let i = String.index s ':' in
    let (j, len) = skip_to_next_colon s i in String.sub s (i + 1) len
  with Not_found | Failure _ -> raise Stream.Failure
;;

let lex = Grammar.glexer Pcaml.gram in
let tok_match = lex.Plexing.tok_match in
lex.Plexing.tok_match <-
  function
    "ANTIQUOT_LOC", p_prm ->
      if p_prm <> "" && (p_prm.[0] = '~' || p_prm.[0] = '?') then
        let p_prm0 = p_prm.[0] in
        if p_prm.[String.length p_prm - 1] = ':' then
          let p_prm = String.sub p_prm 1 (String.length p_prm - 2) in
          function
            "ANTIQUOT_LOC", prm ->
              if prm <> "" && prm.[0] = p_prm0 then
                if prm.[String.length prm - 1] = ':' then
                  let prm = String.sub prm 1 (String.length prm - 2) in
                  let kind = check_anti_loc prm in
                  if kind = p_prm || kind = anti_anti p_prm then prm
                  else raise Stream.Failure
                else raise Stream.Failure
              else raise Stream.Failure
          | _ -> raise Stream.Failure
        else
          let p_prm = String.sub p_prm 1 (String.length p_prm - 1) in
          function
            "ANTIQUOT_LOC", prm ->
              if prm <> "" && prm.[0] = p_prm0 then
                if prm.[String.length prm - 1] = ':' then raise Stream.Failure
                else
                  let prm = String.sub prm 1 (String.length prm - 1) in
                  let kind = check_anti_loc prm in
                  if kind = p_prm || kind = anti_anti p_prm then prm
                  else raise Stream.Failure
              else raise Stream.Failure
          | _ -> raise Stream.Failure
      else
        (function
           "ANTIQUOT_LOC", prm ->
             if prm <> "" && (prm.[0] = '~' || prm.[0] = '?') then
               raise Stream.Failure
             else
               let kind = check_anti_loc prm in
               if kind = p_prm then prm else raise Stream.Failure
         | _ -> raise Stream.Failure)
  | "V", p_prm ->
      (function
         "ANTIQUOT_LOC", prm ->
           let kind = check_anti_loc prm in
           if kind = p_prm || kind = anti_anti p_prm then prm
           else raise Stream.Failure
       | _ -> raise Stream.Failure)
  | "V CHAR", "" ->
      (function
         "ANTIQUOT_LOC", prm ->
           let kind = check_anti_loc prm in
           if kind = "chr" || kind = anti_anti "chr" then prm
           else raise Stream.Failure
       | _ -> raise Stream.Failure)
  | "V FLAG", "" ->
      (function
         "ANTIQUOT_LOC", prm ->
           let kind = check_anti_loc prm in
           if kind = "flag" || kind = anti_anti "flag" then prm
           else raise Stream.Failure
       | _ -> raise Stream.Failure)
  | "V FLOAT", "" ->
      (function
         "ANTIQUOT_LOC", prm ->
           let kind = check_anti_loc prm in
           if kind = "flo" || kind = anti_anti "flo" then prm
           else raise Stream.Failure
       | _ -> raise Stream.Failure)
  | "V INT", "" ->
      (function
         "ANTIQUOT_LOC", prm ->
           let kind = check_anti_loc prm in
           if kind = "int" || kind = anti_anti "int" then prm
           else raise Stream.Failure
       | _ -> raise Stream.Failure)
  | "V INT_l", "" ->
      (function
         "ANTIQUOT_LOC", prm ->
           let kind = check_anti_loc prm in
           if kind = "int32" || kind = anti_anti "int32" then prm
           else raise Stream.Failure
       | _ -> raise Stream.Failure)
  | "V INT_L", "" ->
      (function
         "ANTIQUOT_LOC", prm ->
           let kind = check_anti_loc prm in
           if kind = "int64" || kind = anti_anti "int64" then prm
           else raise Stream.Failure
       | _ -> raise Stream.Failure)
  | "V INT_n", "" ->
      (function
         "ANTIQUOT_LOC", prm ->
           let kind = check_anti_loc prm in
           if kind = "nativeint" || kind = anti_anti "nativeint" then prm
           else raise Stream.Failure
       | _ -> raise Stream.Failure)
  | "V LIDENT", "" ->
      (function
         "ANTIQUOT_LOC", prm ->
           if prm <> "" && (prm.[0] = '~' || prm.[0] = '?') then
             raise Stream.Failure
           else
             let kind = check_anti_loc prm in
             if kind = "lid" || kind = anti_anti "lid" then prm
             else raise Stream.Failure
       | _ -> raise Stream.Failure)
  | "V LIST", "" ->
      (function
         "ANTIQUOT_LOC", prm ->
           let kind = check_anti_loc prm in
           if kind = "list" || kind = anti_anti "list" then prm
           else raise Stream.Failure
       | _ -> raise Stream.Failure)
  | "V OPT", "" ->
      (function
         "ANTIQUOT_LOC", prm ->
           let kind = check_anti_loc prm in
           if kind = "opt" || kind = anti_anti "opt" then prm
           else raise Stream.Failure
       | _ -> raise Stream.Failure)
  | "V QUESTIONIDENT", "" ->
      (function
         "ANTIQUOT_LOC", prm ->
           if prm <> "" && prm.[0] = '?' then
             if prm.[String.length prm - 1] = ':' then raise Stream.Failure
             else
               let prm = String.sub prm 1 (String.length prm - 1) in
               let kind = check_anti_loc prm in
               if kind = "" || kind = anti_anti "" then prm
               else raise Stream.Failure
           else raise Stream.Failure
       | _ -> raise Stream.Failure)
  | "V QUESTIONIDENTCOLON", "" ->
      (function
         "ANTIQUOT_LOC", prm ->
           if prm <> "" && prm.[0] = '?' then
             if prm.[String.length prm - 1] = ':' then
               let prm = String.sub prm 1 (String.length prm - 2) in
               let kind = check_anti_loc prm in
               if kind = "" || kind = anti_anti "" then prm
               else raise Stream.Failure
             else raise Stream.Failure
           else raise Stream.Failure
       | _ -> raise Stream.Failure)
  | "V STRING", "" ->
      (function
         "ANTIQUOT_LOC", prm ->
           if prm <> "" && (prm.[0] = '~' || prm.[0] = '?') then
             raise Stream.Failure
           else
             let kind = check_anti_loc prm in
             if kind = "str" || kind = anti_anti "str" then prm
             else raise Stream.Failure
       | _ -> raise Stream.Failure)
  | "V TILDEIDENT", "" ->
      (function
         "ANTIQUOT_LOC", prm ->
           if prm <> "" && prm.[0] = '~' then
             if prm.[String.length prm - 1] = ':' then raise Stream.Failure
             else
               let prm = String.sub prm 1 (String.length prm - 1) in
               let kind = check_anti_loc prm in
               if kind = "" || kind = anti_anti "" then prm
               else raise Stream.Failure
           else raise Stream.Failure
       | _ -> raise Stream.Failure)
  | "V TILDEIDENTCOLON", "" ->
      (function
         "ANTIQUOT_LOC", prm ->
           if prm <> "" && prm.[0] = '~' then
             if prm.[String.length prm - 1] = ':' then
               let prm = String.sub prm 1 (String.length prm - 2) in
               let kind = check_anti_loc prm in
               if kind = "" || kind = anti_anti "" then prm
               else raise Stream.Failure
             else raise Stream.Failure
           else raise Stream.Failure
       | _ -> raise Stream.Failure)
  | "V UIDENT", "" ->
      (function
         "ANTIQUOT_LOC", prm ->
           if prm <> "" && (prm.[0] = '~' || prm.[0] = '?') then
             raise Stream.Failure
           else
             let kind = check_anti_loc prm in
             if kind = "uid" || kind = anti_anti "uid" then prm
             else raise Stream.Failure
       | _ -> raise Stream.Failure)
  | tok -> tok_match tok;;

(* reinit the entry functions to take the new tok_match into account *)
Grammar.iter_entry Grammar.reinit_entry_functions
  (Grammar.Entry.obj Pcaml.expr);;
