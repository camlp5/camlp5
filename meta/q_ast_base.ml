(* camlp5r *)
(* q_ast_base.ml,v *)
(* Copyright (c) INRIA 2007-2017 *)

#load "pa_macro.cmo";
#load "pa_extend.cmo";
#load "q_MLast.cmo";

(* AST quotations that works by running the language parser (and its possible
   extensions) and meta-ifying the nodes. Works completely only in "strict"
   mode. In "transitional" mode, not all antiquotations are available. *)

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
          Ploc.make_loc (Ploc.file_name loc)
            (Ploc.line_nb loc + Ploc.line_nb loc1 - 1)
            (if Ploc.line_nb loc1 = 1 then Ploc.bol_pos loc
             else shift + Ploc.bol_pos loc1)
            (shift + Ploc.first_pos loc1,
             shift + Ploc.last_pos loc1) ""
          in
          raise (Ploc.Exc loc exc) ]
  in
  (loc, r)
;

value skip_to_next_colon s i =
  loop (i + 1) where rec loop j =
    if j = String.length s then (i, 0)
    else
      match s.[j] with
      [ ':' -> (j, j - i - 1)
      | 'a'..'z' | 'A'..'Z' | '0'..'9' | '!' | '_' -> loop (j + 1)
      | _ -> (i, 0) ]
;

value split_anti_loc s =
  try
    let i = String.index s ':' in
    let (j, len) = skip_to_next_colon s i in
    let locs = String.sub s 0 i in
    let kind = String.sub s (i + 1) len in
    let rest = String.sub s (j+1) (String.length s - j - 1) in
    Some (locs, kind, rest)
  with 
  [ Not_found | Failure _ -> None ]
;

value replace_antiloc_kind ~{newkind} s =
  match split_anti_loc s with [
    None -> s
  | Some (locs, _, rest) -> String.concat ":" [locs; newkind; rest]
  ]
;

value get_anti_loc s =
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
  with
  [ Not_found | Failure _ -> None ]
;

module type MetaSig =
  sig
    type t = 'abstract;
    type prefix_t = 'abstract;
    value loc_v : unit -> t;
    value node : ?prefix:prefix_t -> string -> list t -> t;
    value node_no_loc : ?prefix:prefix_t -> string -> list t -> t;
    value list : ('a -> t) -> list 'a -> t;
    value option : ('a -> t) -> option 'a -> t;
    value vala : ('a -> t) -> MLast.v 'a -> t;
    value char : char -> t;
    value bool : bool -> t;
    value int : int -> t;
    value int32 : int32 -> t;
    value int64 : int64 -> t;
    value nativeint : nativeint -> t;
    value float : float -> t;
    value string : string -> t;
    value tuple : list t -> t;
    value record : list (MLast.patt * t) -> t;
    value xtr_typed : string -> Ploc.t -> string -> t;
    value xtr : Ploc.t -> string -> t;
    value xtr_or_anti : Ploc.t -> (t -> t) -> string -> t;
  end
;

value anti_anti n = "_" ^ n;
value is_anti_anti n = String.length n > 0 && n.[0] = '_';

module E_MetaSig = struct
  type t = MLast.expr;
  type prefix_t = MLast.longid;
  value loc = Ploc.dummy;
  value loc_v () = <:expr< $lid:Ploc.name.val$ >>;
  value node ?{prefix} con el =
    let prefix = match prefix with [ None -> <:longident< MLast >> | Some p -> p ] in
    List.fold_left (fun e1 e2 -> <:expr< $e1$ $e2$ >>)
      <:expr< $longid:prefix$ . $uid:con$ $loc_v ()$ >> el
  ;
  value node_no_loc ?{prefix} con el =
    let prefix = match prefix with [ None -> <:longident< MLast >> | Some p -> p ] in
    List.fold_left (fun e1 e2 -> <:expr< $e1$ $e2$ >>)
      <:expr< $longid:prefix$ . $uid:con$ >> el
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
              if is_anti_anti typ then <:expr< $anti:r$ >>
              else if not Pcaml.strict_mode.val then <:expr< $anti:r$ >>
              else <:expr< Ploc.VaVal $anti:r$ >>
          | None -> assert False ]
      | Ploc.VaVal v ->
          if not Pcaml.strict_mode.val then elem v
          else <:expr< Ploc.VaVal $elem v$ >> ]
    END
  ;
  value char c = let c = Char.escaped c in <:expr< $chr:c$ >>;
  value bool b = if b then <:expr< True >> else <:expr< False >>;
  value int n = let loc = Ploc.dummy in <:expr< $int:string_of_int n$ >> ;
  value int32 n = let loc = Ploc.dummy in <:expr< $int32:Int32.to_string n$ >> ;
  value int64 n = let loc = Ploc.dummy in <:expr< $int64:Int64.to_string n$ >> ;
  value nativeint n = let loc = Ploc.dummy in <:expr< $nativeint:Nativeint.to_string n$ >> ;
  value float n = let loc = Ploc.dummy in <:expr< $flo:Float.to_string n$ >> ;
  value string s = <:expr< $str:s$ >>;
  value tuple le = <:expr< ($list:le$) >>;
  value record lfe = <:expr< {$list:lfe$} >>;
  value xtr_typed wantty loc s =
    match get_anti_loc s with
    [ Some (_, typ, str) when typ = wantty ->
        let (loc, r) = eval_anti Pcaml.expr_eoi loc "" str in
        <:expr< $anti:r$ >>
    | _ -> assert False ]
  ;
  value xtr loc s =
    match get_anti_loc s with
    [ Some (_, typ, str) ->
        match typ with
        [ "" ->
            let (loc, r) = eval_anti Pcaml.expr_eoi loc "" str in
            <:expr< $anti:r$ >>
        | _ -> assert False ]
    | None -> assert False ]
  ;
  value xtr_or_anti loc f s =
    match get_anti_loc s with
    [ Some (_, typ, str) ->
        match typ with
        [ "" | "exp" ->
            let (loc, r) = eval_anti Pcaml.expr_eoi loc typ str in
            <:expr< $anti:r$ >>
        | "anti" ->
            let (loc, r) = eval_anti Pcaml.expr_eoi loc "anti" str in
            f <:expr< $anti:r$ >>
        | _ -> assert False ]
    | None -> assert False ]
  ;
end
;

module P_MetaSig = struct
  type t = MLast.patt;
  type prefix_t = MLast.longid;
  value loc = Ploc.dummy;
  value loc_v () = <:patt< _ >>;
  value node ?{prefix} con pl =
    let prefix = match prefix with [ None -> <:longident< MLast >> | Some p -> p ] in
    List.fold_left (fun p1 p2 -> <:patt< $p1$ $p2$ >>)
      <:patt< $longid:prefix$ . $uid:con$ _ >> pl
  ;
  value node_no_loc ?{prefix} con pl =
    let prefix = match prefix with [ None -> <:longident< MLast >> | Some p -> p ] in
    List.fold_left (fun p1 p2 -> <:patt< $p1$ $p2$ >>)
      <:patt< $longid:prefix$ . $uid:con$ >> pl
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
              if is_anti_anti typ then <:patt< $anti:r$ >>
              else if not Pcaml.strict_mode.val then <:patt< $anti:r$ >>
              else <:patt< Ploc.VaVal $anti:r$ >>
          | None -> assert False ]
      | Ploc.VaVal v ->
          if not Pcaml.strict_mode.val then elem v
          else <:patt< Ploc.VaVal $elem v$ >> ]
    END
  ;
  value char c = let c = Char.escaped c in <:patt< $chr:c$ >>;
  value bool b = if b then <:patt< True >> else <:patt< False >>;
  value int n = let loc = Ploc.dummy in <:patt< $int:string_of_int n$ >> ;
  value int32 n = let loc = Ploc.dummy in <:patt< $int32:Int32.to_string n$ >> ;
  value int64 n = let loc = Ploc.dummy in <:patt< $int64:Int64.to_string n$ >> ;
  value nativeint n = let loc = Ploc.dummy in <:patt< $nativeint:Nativeint.to_string n$ >> ;
  value float n = let loc = Ploc.dummy in <:patt< $flo:Float.to_string n$ >> ;
  value string s = <:patt< $str:s$ >>;
  value tuple lp = <:patt< ($list:lp$) >>;
  value record lfp = <:patt< {$list:lfp$} >>;
  value xtr_typed wantty loc s =
    match get_anti_loc s with
    [ Some (_, typ, str) when typ = wantty ->
        let (loc, r) = eval_anti Pcaml.patt_eoi loc "" str in
        <:patt< $anti:r$ >>
    | _ -> assert False ]
  ;
  value xtr loc s =
    match get_anti_loc s with
    [ Some (_, typ, str) ->
        match typ with
        [ "" ->
            let (loc, r) = eval_anti Pcaml.patt_eoi loc "" str in
            <:patt< $anti:r$ >>
        | _ -> assert False ]
    | None -> assert False ]
  ;
  value xtr_or_anti loc f s =
    match get_anti_loc s with
    [ Some (_, typ, str) ->
        match typ with
        [ "" | "exp" ->
            let (loc, r) = eval_anti Pcaml.patt_eoi loc "exp" str in
            <:patt< $anti:r$ >>
        | "anti" ->
            let (loc, r) = eval_anti Pcaml.patt_eoi loc "anti" str in
            f <:patt< $anti:r$ >>
        | _ -> assert False ]
    | None -> assert False ]
  ;
end
;

value check_anti_loc s =
  try
    let i = String.index s ':' in
    let (j, len) = skip_to_next_colon s i in
    String.sub s (i + 1) len
  with
  [ Not_found | Failure _ -> raise Stream.Failure ]
;

let lex = Grammar.glexer Pcaml.gram in
let tok_match = lex.Plexing.tok_match in
lex.Plexing.tok_match :=
  fun
  [("ANTIQUOT_LOC", p_prm) ->
      if p_prm <> "" && (p_prm.[0] = '~' || p_prm.[0] = '?') then
        let p_prm0 = p_prm.[0] in
        if p_prm.[String.length p_prm - 1] = ':' then
          let p_prm = String.sub p_prm 1 (String.length p_prm - 2) in
          fun
          [ ("ANTIQUOT_LOC", prm) ->
              if prm <> "" && prm.[0] = p_prm0 then
                if prm.[String.length prm - 1] = ':' then
                  let prm = String.sub prm 1 (String.length prm - 2) in
                  let kind = check_anti_loc prm in
                  if kind = p_prm || kind = anti_anti p_prm then prm
                  else raise Stream.Failure
                else raise Stream.Failure
              else raise Stream.Failure
          | _ -> raise Stream.Failure ]
        else
          let p_prm = String.sub p_prm 1 (String.length p_prm - 1) in
          fun
          [ ("ANTIQUOT_LOC", prm) ->
              if prm <> "" && prm.[0] = p_prm0 then
                if prm.[String.length prm - 1] = ':' then
                  raise Stream.Failure
                else
                  let prm = String.sub prm 1 (String.length prm - 1) in
                  let kind = check_anti_loc prm in
                  if kind = p_prm || kind = anti_anti p_prm then prm
                  else raise Stream.Failure
              else raise Stream.Failure
          | _ -> raise Stream.Failure ]
      else
        fun
        [ ("ANTIQUOT_LOC", prm) ->
            if prm <> "" && (prm.[0] = '~' || prm.[0] = '?') then
              raise Stream.Failure
            else
              let kind = check_anti_loc prm in
              if kind = p_prm then prm
              else raise Stream.Failure
        | _ -> raise Stream.Failure ]
  | ("V", p_prm) ->
      fun
      [ ("ANTIQUOT_LOC", prm) ->
          let kind = check_anti_loc prm in
          if kind = p_prm || kind = anti_anti p_prm then prm
          else raise Stream.Failure
      | _ -> raise Stream.Failure ]
  | ("V CHAR", "") ->
      fun
      [ ("ANTIQUOT_LOC", prm) ->
          let kind = check_anti_loc prm in
          if kind = "chr" || kind = anti_anti "chr" then prm
          else raise Stream.Failure
      | _ -> raise Stream.Failure ]
  | ("V FLAG", "") ->
      fun
      [ ("ANTIQUOT_LOC", prm) ->
          let kind = check_anti_loc prm in
          if kind = "flag" || kind = anti_anti "flag" then prm
          else raise Stream.Failure
      | _ -> raise Stream.Failure ]
  | ("V FLOAT", "") ->
      fun
      [ ("ANTIQUOT_LOC", prm) ->
          let kind = check_anti_loc prm in
          if kind = "flo" || kind = anti_anti "flo" then prm
          else raise Stream.Failure
      | _ -> raise Stream.Failure ]
  | ("V INT", "") ->
      fun
      [ ("ANTIQUOT_LOC", prm) ->
          let kind = check_anti_loc prm in
          if kind = "int" || kind = anti_anti "int" then prm
          else raise Stream.Failure
      | _ -> raise Stream.Failure ]
  | ("V INT_l", "") ->
      fun
      [ ("ANTIQUOT_LOC", prm) ->
          let kind = check_anti_loc prm in
          if kind = "int32" || kind = anti_anti "int32" then prm
          else raise Stream.Failure
      | _ -> raise Stream.Failure ]
  | ("V INT_L", "") ->
      fun
      [ ("ANTIQUOT_LOC", prm) ->
          let kind = check_anti_loc prm in
          if kind = "int64" || kind = anti_anti "int64" then prm
          else raise Stream.Failure
      | _ -> raise Stream.Failure ]
  | ("V INT_n", "") ->
      fun
      [ ("ANTIQUOT_LOC", prm) ->
          let kind = check_anti_loc prm in
          if kind = "nativeint" || kind = anti_anti "nativeint" then prm
          else raise Stream.Failure
      | _ -> raise Stream.Failure ]
  | ("V LIDENT", "") ->
      fun
      [ ("ANTIQUOT_LOC", prm) ->
          if prm <> "" && (prm.[0] = '~' || prm.[0] = '?') then
            raise Stream.Failure
          else
            let kind = check_anti_loc prm in
            if kind = "lid" || kind = anti_anti "lid" then prm
            else raise Stream.Failure
      | _ -> raise Stream.Failure ]
  | ("V LIST", "") ->
      fun
      [ ("ANTIQUOT_LOC", prm) ->
          let kind = check_anti_loc prm in
          if kind = "list" || kind = anti_anti "list" then prm
          else raise Stream.Failure
      | _ -> raise Stream.Failure ]
  | ("V OPT", "") ->
      fun
      [ ("ANTIQUOT_LOC", prm) ->
          let kind = check_anti_loc prm in
          if kind = "opt" || kind = anti_anti "opt" then prm
          else raise Stream.Failure
      | _ -> raise Stream.Failure ]
  | ("V QUESTIONIDENT", "") ->
      fun
      [ ("ANTIQUOT_LOC", prm) ->
          if prm <> "" && prm.[0] = '?' then
            if prm.[String.length prm - 1] = ':' then
              raise Stream.Failure
            else
              let prm = String.sub prm 1 (String.length prm - 1) in
              let kind = check_anti_loc prm in
              if kind = "" || kind = anti_anti "" then prm
              else raise Stream.Failure
          else raise Stream.Failure
      | _ -> raise Stream.Failure ]
  | ("V QUESTIONIDENTCOLON", "") ->
      fun
      [ ("ANTIQUOT_LOC", prm) ->
          if prm <> "" && prm.[0] = '?' then
            if prm.[String.length prm - 1] = ':' then
              let prm = String.sub prm 1 (String.length prm - 2) in
              let kind = check_anti_loc prm in
              if kind = "" || kind = anti_anti "" then prm
              else raise Stream.Failure
            else raise Stream.Failure
          else raise Stream.Failure
      | _ -> raise Stream.Failure ]
  | ("V STRING", "") ->
      fun
      [ ("ANTIQUOT_LOC", prm) ->
          if prm <> "" && (prm.[0] = '~' || prm.[0] = '?') then
            raise Stream.Failure
          else
            let kind = check_anti_loc prm in
            if kind = "str" || kind = anti_anti "str" then prm
            else raise Stream.Failure
      | _ -> raise Stream.Failure ]
  | ("V TILDEIDENT", "") ->
      fun
      [ ("ANTIQUOT_LOC", prm) ->
          if prm <> "" && prm.[0] = '~' then
            if prm.[String.length prm - 1] = ':' then raise Stream.Failure
            else
              let prm = String.sub prm 1 (String.length prm - 1) in
              let kind = check_anti_loc prm in
              if kind = "" || kind = anti_anti "" then prm
              else raise Stream.Failure
          else raise Stream.Failure
      | _ -> raise Stream.Failure ]
  | ("V TILDEIDENTCOLON", "") ->
      fun
      [ ("ANTIQUOT_LOC", prm) ->
          if prm <> "" && prm.[0] = '~' then
            if prm.[String.length prm - 1] = ':' then
              let prm = String.sub prm 1 (String.length prm - 2) in
              let kind = check_anti_loc prm in
              if kind = "" || kind = anti_anti "" then prm
              else raise Stream.Failure
            else raise Stream.Failure
          else raise Stream.Failure
      | _ -> raise Stream.Failure ]
  | ("V UIDENT", "") ->
      fun
      [ ("ANTIQUOT_LOC", prm) ->
          if prm <> "" && (prm.[0] = '~' || prm.[0] = '?') then
            raise Stream.Failure
          else
            let kind = check_anti_loc prm in
            if kind = "uid" || kind = anti_anti "uid" then prm
            else raise Stream.Failure
      | _ -> raise Stream.Failure ]
  | tok -> tok_match tok ]
;

(* reinit the entry functions to take the new tok_match into account *)
Grammar.iter_entry Grammar.reinit_entry_functions
  (Grammar.Entry.obj Pcaml.expr);
