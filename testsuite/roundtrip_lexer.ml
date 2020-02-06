(* camlp5r *)
(* roundtrip_lexer.ml,v *)

value stream_of_list =
  let rec srec = fun [
        [] -> [: :]
      | [ h::t ] -> [: `h ; srec t :]
      ]
  in srec
;

type d_op_t = [
    DOP_le |
    DOP_lt |
    DOP_eq |
    DOP_ne |
    DOP_gt |
    DOP_ge
  ]
;

type d_version_t = [ DVERSION of string ]
;

value ocaml_version = "OCAML_4_10_0" ;

value is_version s = Pcre.pmatch ~{pat="^OCAML_[0-9_]+(?:_[0-9a-zA-Z]+)$"} s ;

type dexpr = [
    DE_uident of Ploc.t and string
  | DE_version_op of Ploc.t and (Ploc.t * d_op_t) and (Ploc.t * d_version_t)
  | DE_parens of Ploc.t and dexpr and Ploc.t
  | DE_not of Ploc.t and dexpr
  | DE_and of dexpr and Ploc.t and dexpr
  | DE_or of dexpr and Ploc.t and dexpr
  ]
;

type base_token = (Ploc.t * (string * string)) ;

type ifdef_t = [
  DEF_ifdef of bool and (*IFDEF*) Ploc.t and dexpr and (*THEN*) Ploc.t and tokens and else_t and (*END*) Ploc.t
  ]
and else_t = [
  DEF_none
| DEF_else of (*ELSE*) Ploc.t and tokens
| DEF_elsifdef of bool and (*ELSIFDEF*) Ploc.t and dexpr and (*THEN*) Ploc.t and tokens and else_t
  ]
and tokens = list t
and t = [ L of ifdef_t | R of base_token ]
;

module PA = struct

value pa_d_op =
  parser
    [
      [: `(loc,("","<")) :] -> (loc,DOP_lt)
    | [: `(loc,("","<=")) :] -> (loc,DOP_le)
    | [: `(loc,("","=")) :] -> (loc,DOP_eq)
    | [: `(loc,("","<>")) :] -> (loc,DOP_ne)
    | [: `(loc,("",">")) :] -> (loc,DOP_gt)
    | [: `(loc,("",">=")) :] -> (loc,DOP_ge)
    ]
;

value pa_d_version =
  parser
    [
      [: `(loc,("UIDENT",vs)) when is_version vs  :] -> (loc, DVERSION vs)
    ]
;

value rec pa_dexpr0 =
  parser
    [
      [: `(loc1,("","(")) ; de = pa_dexpr2 ; `(loc2,("",")")) :] -> DE_parens loc1 de loc2
    | [: `(loc,("UIDENT","NOT")) ; de = pa_dexpr0 :] -> DE_not loc de
    | [: `(loc1,("UIDENT","OCAML_VERSION")) ; (loc2, op) = pa_d_op ; (loc3, vers) = pa_d_version :] ->
       DE_version_op loc1 (loc2, op) (loc3, vers)
    | [: `(loc,("UIDENT", id)) :] -> DE_uident loc id
    ]
and pa_dexpr1 = parser
    [
      [: lhs = pa_dexpr0 ; `(loc, ("UIDENT", "AND")) ; rhs = pa_dexpr1 :] -> DE_and lhs loc rhs
    | [: lhs = pa_dexpr0 :] -> lhs
    ]
and pa_dexpr2 = parser
    [
      [: lhs = pa_dexpr1 ; `(loc, ("UIDENT", "OR")) ; rhs = pa_dexpr2 :] -> DE_or lhs loc rhs
    | [: lhs = pa_dexpr1 :] -> lhs
    ]
 ;

value pa_dexpr = pa_dexpr2
;

value tokens_until termlist =
  let rec trec acc =
    parser
      [
        [: `((_, tok) as p) when not (List.mem tok termlist) ; strm :] ->
        trec [ p::acc ] strm
      | [: :] -> List.rev acc
      ]
  in
  trec []
;

value keywords = ["IFDEF"; "IFNDEF"; "ELSE"; "THEN" ; "END"; "ELSIFDEF"; "ELSIFNDEF"] ;

value rec pa_ifdef =
  parser
    [
      [: `(loc1,("UIDENT","IFDEF")) ; de = pa_dexpr ; `(loc2,("UIDENT","THEN")) ;
          l = pa_t_list ;
          e = pa_else ; `(loc3,("UIDENT","END")) :] ->
      DEF_ifdef True loc1 de loc2 l e loc3
    | [: `(loc1,("UIDENT","IFNDEF")) ; de = pa_dexpr ; `(loc2,("UIDENT","THEN")) ;
          l = pa_t_list ;
          e = pa_else ; `(loc3,("UIDENT","END")) :] ->
      DEF_ifdef False loc1 de loc2 l e loc3
    ]
and pa_else =
  parser
    [
      [: `(loc1,("UIDENT","ELSE")) ; l = pa_t_list :] ->
      DEF_else loc1 l
    | [: `(loc1,("UIDENT","ELSIFDEF")) ; de = pa_dexpr ; `(loc2,("UIDENT","THEN")) ;
          l = pa_t_list ;
          e = pa_else :] ->
      DEF_elsifdef True loc1 de loc2 l e
    | [: `(loc1,("UIDENT","ELSIFNDEF")) ; de = pa_dexpr ; `(loc2,("UIDENT","THEN")) ;
          l = pa_t_list ;
          e = pa_else :] ->
      DEF_elsifdef False loc1 de loc2 l e
    | [: :] ->
      DEF_none
    ]
and pa_t =
  parser
    [
      [: d = pa_ifdef :] -> L d
    | [: `((_,("UIDENT",t)) as p) when not(List.mem t keywords) ; strm :] -> R p
    | [: `((_,(ty,_)) as p) when (ty <> "UIDENT") ; strm :] -> R p
    ]
and pa_t_list strm =
  let rec parec acc =
    parser
      [
        [: e = pa_t ; strm :] -> parec [ e :: acc ] strm
      | [: :] -> List.rev acc
      ]
  in parec [] strm
;

end ;

module PP = struct

value pp_d_op (loc,d_op) =
  let s = match d_op with [
        DOP_le -> "<="
      | DOP_lt -> "<"
      | DOP_eq -> "="
      | DOP_ne -> "<>"
      | DOP_gt -> ">"
      | DOP_ge -> ">="
  ] in
  [: `(loc,("",s)) :]
;
value pp_d_version = fun [ (loc, (DVERSION s)) -> [: `(loc,("UIDENT",s)) :] ] ;

value rec pp_dexpr =
  fun [
      DE_uident loc id -> [: `(loc,("UIDENT", id)) :]
    | DE_version_op loc1 loc_op loc_vers ->
       [: `(loc1,("UIDENT","OCAML_VERSION")) ; pp_d_op loc_op ; pp_d_version loc_vers :]
    | DE_parens loc1 de loc2 -> [: `(loc1,("","(")) ; pp_dexpr de ; `(loc2,("",")")) :]
    | DE_not loc de -> [: `(loc,("UIDENT","NOT")) ; pp_dexpr de :]
    | DE_and de1 loc de2 -> [: pp_dexpr de1 ; `(loc,("UIDENT","AND")) ; pp_dexpr de2 :]
    | DE_or de1 loc de2 -> [: pp_dexpr de1 ; `(loc,("UIDENT","OR")) ; pp_dexpr de2 :]
    ]
;

value rec pp_def =
  fun [
      DEF_ifdef b loc1 de loc2 l e loc3 ->
      let starter = if b then "IFDEF" else "IFNDEF" in
      [: `(loc1,("UIDENT",starter)) ; pp_dexpr de ; `(loc2,("UIDENT","THEN")) ;
          pp_t_list l ;
          pp_else e ; `(loc3,("UIDENT","END")) :]
    ]
and pp_else =
  fun [
      DEF_none -> [: :]
    | DEF_else loc l -> [: `(loc,("UIDENT","ELSE")) ; pp_t_list l :]
    | DEF_elsifdef b loc1 de loc2 l e ->
      let starter = if b then "ELSIFDEF" else "ELSIFNDEF" in
       [: `(loc1,("UIDENT",starter)) ; pp_dexpr de ; `(loc2,("UIDENT","THEN")) ;
          pp_t_list l ;
          pp_else e :]
    ]
and pp_t_list =
  fun [
      [] -> [: :]
    | [(L def) :: tl] -> [: pp_def def ; pp_t_list tl :]
    | [(R tok) :: tl] -> [: `tok ; pp_t_list tl :]
    ]
;
end ;

module DorT = struct

value lift =
  let rec trec =
    parser
      [
        [: d = PA.pa_ifdef ; strm :] -> [: `L d ; trec strm :]
      | [: `t ; strm :] -> [: `R t ; trec strm :]
      | [: :] -> [: :]
      ]
  in trec
;

value unlift =
  let rec trec =
    parser
      [
        [: `R tok ; strm :] -> [: `tok ; trec strm :]
      | [: `L def ; strm :] -> [: PP.pp_def def ; trec strm :]
      | [: :] -> [: :]
      ]
  in
  trec
;

value eval_op op = fun [
 (DVERSION vers) ->
 match op with [
     DOP_le -> ocaml_version <= vers
   | DOP_lt -> ocaml_version < vers
   | DOP_eq  -> ocaml_version = vers
   | DOP_ne  -> ocaml_version <> vers
   | DOP_gt  -> ocaml_version > vers
   | DOP_ge -> ocaml_version >= vers
   ]
]
;

value eval_dexpr env =
  let rec evrec = 
    fun 
      [
        DE_uident _ id -> List.mem_assoc id env
      | DE_version_op _ (_, op) (_, vers) ->
         eval_op op vers
      | DE_parens _ de _ -> evrec de
      | DE_not _ de -> not (evrec de)
      | DE_and de1 _ de2 -> (evrec de1) && (evrec de2)
      | DE_or de1 _ de2 -> (evrec de1) || (evrec de2)
      ] in
  evrec
;

value rec eval_def env =
  fun [
      DEF_ifdef b _ de _ then_tokens elses _ ->
      if eval_dexpr env de then
        eval_t_list env then_tokens
      else match elses with [
        DEF_none -> [: :]
      | DEF_else _ else_tokens -> eval_t_list env else_tokens
      | DEF_elsifdef b _ de _ l elses ->
         eval_def env (DEF_ifdef b Ploc.dummy de Ploc.dummy l elses Ploc.dummy)
             ]
    ]

and eval_t env = fun [
  R tok -> [: `R tok :]
| L def -> eval_def env def
]

and eval_t_list env =
  let rec evrec = fun [
      [] -> [: :]
    | [h :: tl] -> [: eval_t env h ; evrec tl :]
  ]
  in
  evrec
;

value eval env =
  let rec evrec = parser
    [
      [: `h ; strm :] -> [: eval_t env h ; evrec strm :]
    | [: :] -> [: :]
    ]
  in evrec
;
end ;

value lex_stream1 is = do {
  Plexer.dollar_for_antiquotation.val := False ;
  let lexer = Plexer.gmake() in
  let (strm, locfun) = lexer.Plexing.tok_func is in
  let rec addloc i =
    parser
      [
        [: `(("EOI",_) as p) :] -> [: `(Ploc.dummy,p) :]
      | [: `p ; strm :] ->
        let loc = i |> locfun in
        [: `(loc,p) ; addloc (i+1) strm :]
      ] in
  addloc 0 strm
}
;

value pp_stream1 oc strm =
  let rec pp1 =
    parser
      [
        [: `(loc,("STRING",tok)) ; strm :] -> do {
          output_string oc (Ploc.comment loc) ;
          Printf.fprintf oc "\"%s\"" tok ;
          pp1 strm
        }
      | [: `(loc,(_,tok)) ; strm :] -> do {
          output_string oc (Ploc.comment loc) ;
          output_string oc tok ;
          pp1 strm
        }
      | [: :] -> ()
      ] in
  pp1 strm
;

value rec sep_last = fun [
    [] -> failwith "sep_last"
  | [ hd ] -> (hd,[])
  | [ hd::tl ] ->
      let (l,tl) = sep_last tl in (l,[ hd::tl ])
  ]
;

value invoked_with ?{flag} cmdna =
  let variant_names = [cmdna; cmdna^".byte"; cmdna^".native"; cmdna^".opt"] in

  let argv = Array.to_list Sys.argv in
  let path = Pcre.split ~{rex=(Pcre.regexp "/")} (List.hd argv) in
  let (fname, _) = sep_last path in

  List.exists ((=) fname) variant_names &&
  match flag with [
    None -> True
  | Some flag ->
    let flag' = "-"^flag in
    let flag'' = "--"^flag in
    List.exists ((=) flag') (List.tl argv) ||
      List.exists ((=) flag'') (List.tl argv) ]
;

value files = ref [] ;
value mode = ref "lexer-passturn" ;
value env = ref [("OCAML_VERSION", Some ocaml_version)] ;

value set_mode s = mode.val := s ;

value add_def s =
  if List.mem_assoc s env.val then
    failwith (Printf.sprintf "%s already defined" s)
  else
    env.val := [(s,None) :: env.val] ;

value un_def s =
  if not (List.mem_assoc s env.val) then
    failwith (Printf.sprintf "%s not defined" s)
  else
    env.val := List.remove_assoc s env.val ;

value roundtrip_lexer () = do {
    Arg.(parse [
             ("-mode",(Symbol ["lexer-passthru";"parse-pp";"ifdef-eval"] set_mode)," choose mode") ;
             ("-D", String add_def, " add def") ;
             ("-U", String un_def, " un def")
      ]
      (fun s -> files.val := [ s :: files.val ])
      "roundtrip_lexer: usage") ;
      let open_or opener ifminus = fun [
        "-" -> ifminus | f -> opener f
      ] in
      let (ic, oc) = match List.rev files.val with [
        [] -> (stdin, stdout)
      | [ifile] -> (open_or open_in stdin ifile,
                    stdout)
      | [ifile; ofile] -> (open_or open_in stdin ifile,
                           open_or open_out stdout ofile)
      | _ -> failwith "too many filenames provided"
      ] in
    let cs = Stream.of_channel ic in
    if mode.val = "lexer-passthru" then
      cs |> lex_stream1 |> pp_stream1 oc
    else if mode.val = "parse-pp" then
      cs |> lex_stream1 |> DorT.lift |> DorT.unlift |> pp_stream1 oc
    else if mode.val = "ifdef-eval" then
      cs |> lex_stream1 |> DorT.lift |> DorT.eval env.val |> DorT.unlift |> pp_stream1 oc
    else assert False
    ;
    output_string oc "\n" ;
    close_out oc ;
    close_in ic
  }
;

value _ =
if invoked_with "roundtrip_lexer" then
  roundtrip_lexer ()
else ()
;

(*
;;; Local Variables: ***
;;; mode:tuareg ***
;;; End: ***

*)
