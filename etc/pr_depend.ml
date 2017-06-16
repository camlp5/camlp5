(* camlp5r *)
(* pr_depend.ml,v *)
(* Copyright (c) INRIA 2007-2017 *)

#load "pa_macro.cmo";
#load "q_MLast.cmo";

open MLast;
open Versdep;

value not_impl name x = do {
  let desc =
    if Obj.is_block (Obj.repr x) then
      "tag = " ^ string_of_int (Obj.tag (Obj.repr x))
    else "int_val = " ^ string_of_int (Obj.magic x)
  in
  Printf.eprintf "pr_depend: not impl: %s; %s\n" name desc;
  flush stderr
};

module StrSet =
  Set.Make (struct type t = string; value compare = compare; end)
;

value fset = ref StrSet.empty;
value addmodule s = fset.val := StrSet.add s fset.val;

value list = List.iter;

value option f =
  fun
  [ Some x -> f x
  | None -> () ]
;

value vala f v = Pcaml.vala_mapa f (fun _ -> ()) v;

value longident =
  fun
  [ [s; _ :: _] -> addmodule s
  | _ -> () ]
;

value rec ctyp =
  fun
  [ TyAcc _ t _ -> ctyp_module t
  | TyAli _ t1 t2 -> do { ctyp t1; ctyp t2 }
  | TyApp _ t1 t2 -> do { ctyp t1; ctyp t2 }
  | TyAny _ -> ()
  | TyArr _ t1 t2 -> do { ctyp t1; ctyp t2 }
  | <:ctyp< # $list:li$ >> -> longident li
  | TyLab _ _ t -> ctyp t
  | TyLid _ _ -> ()
  | TyMan _ t1 _ t2 -> do { ctyp t1; ctyp t2 }
  | TyOlb _ _ t -> ctyp t
  | <:ctyp< ' $_$ >> -> ()
  | <:ctyp< { $list:ldl$ } >> -> list label_decl ldl
  | <:ctyp< [ $list:cdl$ ] >> -> list constr_decl cdl
  | <:ctyp< ( $list:tl$ ) >> -> list ctyp tl
  | <:ctyp< [ = $list:sbtll$ ] >> -> list variant sbtll
  | <:ctyp< [ > $list:sbtll$ ] >> -> list variant sbtll
  | <:ctyp< [ < $list:sbtll$ > $list:_$ ] >> -> list variant sbtll
  | x -> not_impl "ctyp" x ]
and constr_decl (_, _, tl, rto) = list ctyp (Pcaml.unvala tl)
and label_decl (_, _, _, t) = ctyp t
and variant =
  fun
  [ <:poly_variant< ` $_$ of $flag:_$ $list:tl$ >> -> list ctyp tl
  | <:poly_variant< $t$ >> -> ctyp t
  | IFDEF STRICT THEN
      _ -> failwith "Pr_depend.variant"
    END ]
and ctyp_module =
  fun
  [ <:ctyp< $t$.$_$ >> -> ctyp_module t
  | <:ctyp< $t1$ $t2$ >> -> do { ctyp t1; ctyp t2 }
  | <:ctyp< $uid:m$ >> -> addmodule m
  | x -> not_impl "ctyp_module" x ]
;

value rec patt =
  fun
  [ PaAcc _ p _ -> patt_module p
  | PaAli _ p1 p2 -> do { patt p1; patt p2 }
  | PaAny _ -> ()
  | PaApp _ p1 p2 -> do { patt p1; patt p2 }
  | <:patt< [| $list:pl$ |] >> -> list patt pl
  | PaChr _ _ -> ()
  | PaInt _ _ _ -> ()
  | PaFlo _ _ -> ()
  | <:patt< ~{$_$ $opt:po$} >> -> option patt po
  | <:patt< $lid:_$ >> -> ()
  | <:patt< ?{$_$ = $e$} >> -> expr e
  | <:patt< ?{$_$} >> -> ()
  | <:patt< $p1$ | $p2$ >> -> do { patt p1; patt p2 }
  | <:patt< {$list:lpl$} >> -> list label_patt lpl
  | <:patt< $p1$ .. $p2$ >> -> do { patt p1; patt p2 }
  | <:patt< $str:_$ >> -> ()
  | <:patt< ($list:pl$) >> -> list patt pl
  | <:patt< ($p$ : $t$) >> -> do { patt p; ctyp t }
  | <:patt< $uid:_$ >> -> ()
  | <:patt< (module $_$ : $mt$) >> -> module_type mt
  | PaVrn _ _ -> ()
  | x -> not_impl "patt" x ]
and patt_module =
  fun
  [ <:patt< $uid:m$ >> -> addmodule m
  | <:patt< $p$.$_$ >> -> patt_module p
  | x -> not_impl "patt_module" x ]
and label_patt (p1, p2) = do { patt p1; patt p2 }
and expr =
  fun
  [ <:expr< $lid:s$.$e2$ >> -> do { expr_module e2 }
  | <:expr< $e1$.$e2$ >> -> do { expr_module e1; expr e2 }
  | ExApp _ e1 e2 -> do { expr e1; expr e2 }
  | ExAre _ e1 e2 -> do { expr e1; expr e2 }
  | <:expr< [| $list:el$ |] >> -> list expr el
  | ExAsr _ e -> expr e
  | ExAss _ e1 e2 -> do { expr e1; expr e2 }
  | <:expr< $chr:_$ >> -> ()
  | ExCoe _ e t1 t2 -> do { expr e; option ctyp t1; ctyp t2 }
  | <:expr< for $lid:_$ = $e1$ $to:_$ $e2$ do { $list:el$ } >> -> do {
      expr e1;
      expr e2;
      list expr el
    }
  | <:expr< fun [ $list:pwel$ ] >> -> list match_case pwel
  | ExIfe _ e1 e2 e3 -> do { expr e1; expr e2; expr e3 }
  | ExInt _ _ _ -> ()
  | ExFlo _ _ -> ()
  | ExLab _ <:vala< lpeo >> ->
      list (fun (_, eo) -> option expr (Pcaml.unvala eo)) lpeo
  | ExLaz _ e -> expr e
  | <:expr< let $flag:_$ $list:pel$ in $e$ >> -> do {
      list let_binding pel;
      expr e
    }
  | ExLid _ _ -> ()
  | <:expr< let module $uid:_$ = $me$ in $e$ >> -> do {
      module_expr me;
      expr e
    }
  | <:expr< match $e$ with [ $list:pwel$ ] >> -> do {
      expr e;
      list match_case pwel
    }
  | <:expr< new $list:li$ >> -> longident li
  | ExOlb _ _ eo -> option expr (Pcaml.unvala eo)
  | <:expr< {$list:lel$} >> -> list label_expr lel
  | <:expr< {($w$) with $list:lel$} >> -> do {
      list label_expr lel;
      expr w
    }
  | <:expr< do { $list:el$ } >> -> list expr el
  | ExSnd _ e _ -> expr e
  | ExSte _ e1 e2 -> do { expr e1; expr e2 }
  | <:expr< $str:_$ >> -> ()
  | <:expr< try $e$ with [ $list:pwel$ ] >> -> do {
      expr e;
      list match_case pwel
    }
  | <:expr< ($list:el$) >> -> list expr el
  | <:expr< ($e$ : $t$) >> -> do { expr e; ctyp t }
  | <:expr< $uid:_$ >> -> ()
  | ExVrn _ _ -> ()
  | <:expr< while $e$ do { $list:el$ } >> -> do { expr e; list expr el }
  | x -> not_impl "expr" x ]
and expr_module =
  fun
  [ <:expr< $uid:m$ >> -> addmodule m
  | e -> expr e ]
and let_binding (p, e) = do { patt p; expr e }
and label_expr (p, e) = do { patt p; expr e }
and match_case (p, w, e) = do { patt p; vala (option expr) w; expr e }
and module_type =
  fun
  [ <:module_type< $uid:m$ . $_$ >> -> addmodule m
  | <:module_type< functor ($uid:_$ : $mt1$) -> $mt2$ >> -> do {
      module_type mt1;
      module_type mt2
    }
  | <:module_type< sig $list:sil$ end >> -> list sig_item sil
  | <:module_type< $uid:_$ >> -> ()
  | <:module_type< $mt$ with $list:wc$ >> -> do {
      module_type mt;
      list with_constr wc
    }
  | x -> not_impl "module_type" x ]
and with_constr =
  fun
  [ WcTyp _ _ _ _ t -> ctyp t
  | x -> not_impl "with_constr" x ]
and sig_item =
  fun
  [ <:sig_item< declare $list:sil$ end >> -> list sig_item sil
  | <:sig_item< exception $uid:_$ of $list:tl$ >> -> list ctyp tl
  | SgExt _ _ t _ -> ctyp t
  | <:sig_item< include $mt$ >> -> module_type mt
  | <:sig_item< module $flag:_$ $list:ntl$ >> ->
      list (fun (_, mt) -> module_type mt) ntl
  | SgMty _ _ mt -> module_type mt
  | <:sig_item< open $[s :: _]$ >> -> addmodule s
  | <:sig_item< type $list:tdl$ >> -> list type_decl tdl
  | SgVal _ _ t -> ctyp t
  | <:sig_item< # $_$ $_$ >> -> ()
  | x -> not_impl "sig_item" x ]
and module_expr =
  fun
  [ <:module_expr< $_$ . $uid:m$ >> -> addmodule m
  | <:module_expr< $me1$ $me2$ >> -> do { module_expr me1; module_expr me2 }
  | <:module_expr< functor ($uid:_$ : $mt$) -> $me$ >> -> do {
      module_type mt;
      module_expr me
    }
  | <:module_expr< struct $list:sil$ end >> -> list str_item sil
  | <:module_expr< ($me$ : $mt$) >> -> do { module_expr me; module_type mt }
  | <:module_expr< $uid:_$ >> -> ()
  | x -> not_impl "module_expr" x ]
and str_item =
  fun
  [ <:str_item< class $list:cil$ >> ->
      list (fun ci -> class_expr ci.ciExp) cil
  | <:str_item< declare $list:sil$ end >> -> list str_item sil
  | StDir _ _ _ -> ()
  | <:str_item< exception $uid:_$ of $list:tl$ = $list:_$ >> -> list ctyp tl
  | <:str_item< $exp:e$ >> -> expr e
  | <:str_item< external $lid:_$ : $t$ = $list:_$ >> -> ctyp t
  | <:str_item< include $me$ >> -> module_expr me
  | <:str_item< module $flag:_$ $list:nel$ >> ->
      list (fun (_, me) -> module_expr me) nel
  | <:str_item< module type $_$ = $mt$ >> -> module_type mt
  | <:str_item< open $[s :: _]$ >> -> addmodule s
  | <:str_item< type $list:tdl$ >> -> list type_decl tdl
  | <:str_item< value $flag:_$ $list:pel$ >> -> list let_binding pel
  | StUse _ _ _ -> ()
  | x -> not_impl "str_item" x ]
and type_decl td = ctyp td.MLast.tdDef
and class_expr =
  fun
  [ <:class_expr< $ce$ $e$ >> -> do { class_expr ce; expr e }
  | <:class_expr< [ $list:tl$ ] $list:li$ >> -> do {
      longident li;
      list ctyp tl
    }
  | <:class_expr< fun $p$ -> $ce$ >> -> do { patt p; class_expr ce }
  | <:class_expr< let $flag:_$ $list:pel$ in $ce$ >> -> do {
      list let_binding pel;
      class_expr ce
    }
  | <:class_expr< object $opt:po$ $list:csil$ end >> -> do {
      option patt po;
      list class_str_item csil
    }
  | x -> not_impl "class_expr" x ]
and class_str_item =
  fun
  [ CrInh _ ce _ -> class_expr ce
  | CrIni _ e -> expr e
  | <:class_str_item< method $priv:_$ $lid:_$ = $e$ >> -> expr e
  | <:class_str_item< method $priv:_$ $lid:_$ : $t$ = $e$ >> -> do {
      expr e;
      ctyp t
    }
  | CrVal _ _ _ _ e -> expr e
  | CrVir _ _ _ t -> ctyp t
  | x -> not_impl "class_str_item" x ]
;

(* Print dependencies *)

value load_path = ref [""];

value find_in_path path name =
  if not (Filename.is_implicit name) then
    if Sys.file_exists name then name else raise Not_found
  else
    let rec try_dir =
      fun
      [ [] -> raise Not_found
      | [dir :: rem] ->
          let fullname = Filename.concat dir name in
          if Sys.file_exists fullname then fullname else try_dir rem ]
    in
    try_dir path
;

value find_depend modname (byt_deps, opt_deps) =
  let name = string_uncapitalize modname in
  try
    let filename = find_in_path load_path.val (name ^ ".mli") in
    let basename = Filename.chop_suffix filename ".mli" in
    let byt_dep = basename ^ ".cmi" in
    let opt_dep =
      if Sys.file_exists (basename ^ ".ml") then basename ^ ".cmx"
      else basename ^ ".cmi"
    in
    ([byt_dep :: byt_deps], [opt_dep :: opt_deps])
  with
  [ Not_found ->
      try
        let filename = find_in_path load_path.val (name ^ ".ml") in
        let basename = Filename.chop_suffix filename ".ml" in
        ([basename ^ ".cmo" :: byt_deps], [basename ^ ".cmx" :: opt_deps])
      with
      [ Not_found -> (byt_deps, opt_deps) ] ]
;

value (depends_on, escaped_eol) =
  match Sys.os_type with
  [ "Unix" | "Win32" | "Cygwin" -> (": ", "\\\n    ")
  | "MacOS" -> ("\196 ", "\182\n    ")
  | _ -> assert False ]
;

value print_depend target_file deps =
  match deps with
  [ [] -> ()
  | _ -> do {
      print_string target_file;
      print_string depends_on;
      let rec print_items pos =
        fun
        [ [] -> print_string "\n"
        | [dep :: rem] ->
            if pos + String.length dep <= 77 then do {
              print_string dep;
              if rem <> [] then print_string " " else ();
              print_items (pos + String.length dep + 1) rem
            }
            else do {
              print_string escaped_eol;
              print_string dep;
              if rem <> [] then print_string " " else ();
              print_items (String.length dep + 5) rem
            } ]
      in
      print_items (String.length target_file + 2) deps
    } ]
;

(* Main *)

value file_name_of_ast =
  fun
  [ [(_, loc) :: _] -> Ploc.file_name loc
  | [] -> Plexing.input_file.val ]
;

value depend_sig (ast, eoi_loc) = do {
  fset.val := StrSet.empty;
  List.iter (fun (si, _) -> sig_item si) ast;
  let fname = file_name_of_ast ast in
  if Filename.check_suffix fname ".mli" then
    let basename = Filename.chop_suffix fname ".mli" in
    let (byt_deps, _) = StrSet.fold find_depend fset.val ([], []) in
    let byt_deps = list_sort compare byt_deps in
    print_depend (basename ^ ".cmi") byt_deps
  else ()
};

value depend_str (ast, eoi_loc) = do {
  fset.val := StrSet.empty;
  List.iter (fun (si, _) -> str_item si) ast;
  let fname = file_name_of_ast ast in
  let basename =
    if Filename.check_suffix fname ".ml" then
      Filename.chop_suffix fname ".ml"
    else
      try
        let len = String.rindex fname '.' in
        String.sub fname 0 len
      with
      [ Failure _ | Not_found -> fname ]
  in
  let init_deps =
    if Sys.file_exists (basename ^ ".mli") then
      let cmi_name = basename ^ ".cmi" in ([cmi_name], [cmi_name])
    else ([], [])
  in
  let (byt_deps, opt_deps) = StrSet.fold find_depend fset.val init_deps in
  let byt_deps = list_sort compare byt_deps in
  let opt_deps = list_sort compare opt_deps in
  print_depend (basename ^ ".cmo") byt_deps;
  print_depend (basename ^ ".cmx") opt_deps
};

Pcaml.print_interf.val := depend_sig;
Pcaml.print_implem.val := depend_str;

Pcaml.add_option "-I"
  (Arg.String (fun dir -> load_path.val := load_path.val @ [dir]))
  "<dir> Add <dir> to the list of include directories.";
