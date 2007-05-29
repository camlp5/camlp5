(* camlp4r q_MLast.cmo ./pa_extfun.cmo *)
(* $Id$ *)
(* Copyright (c) INRIA 2007 *)

open Sformat;

module Buff =
  struct
    value buff = ref (String.create 80);
    value store len x = do {
      if len >= String.length buff.val then
        buff.val := buff.val ^ String.create (String.length buff.val)
      else ();
      buff.val.[len] := x;
      succ len
    };
    value mstore len s =
      add_rec len 0 where rec add_rec len i =
        if i == String.length s then len
        else add_rec (store len s.[i]) (succ i)
    ;
    value get len = String.sub buff.val 0 len;
  end
;

value file = ref "";

value is_infix = do {
  let infixes = Hashtbl.create 73 in
  List.iter (fun s -> Hashtbl.add infixes s True)
    ["!="; "&&"; "*"; "**"; "*."; "+"; "+."; "-"; "-."; "/"; "/."; "<"; "<.";
     "<="; "<=."; "<>"; "<>."; "="; "=."; "=="; ">"; ">."; ">="; ">=."; "@";
     "^"; "asr"; "land"; "lor"; "lsl"; "lsr"; "lxor"; "mod"; "or"; "||";
     "~-"; "~-."];
  fun s -> try Hashtbl.find infixes s with [ Not_found -> False ]
};

(* temporary, just before all expr infixes are implemented *)
value is_not_yet_implemented_infix = do {
  let infixes = Hashtbl.create 73 in
  List.iter (fun s -> Hashtbl.add infixes s True)
    ["*"; "**"; "*."; "/"; "/."; "<."; "<=."; "<>."; "=."; ">."; ">=.";
     "asr"; "land"; "lor"; "lsl"; "lsr"; "lxor"; "mod"; "or"; "~-"; "~-."];
  fun s -> try Hashtbl.find infixes s with [ Not_found -> False ]
};

value is_keyword =
  let keywords = ["value"] in
  fun s -> List.mem s keywords
;

value has_special_chars s =
  if String.length s = 0 then False
  else
    match s.[0] with
    [ '0'..'9' | 'A'..'Z' | 'a'..'z' | '_' -> False
    | _ -> True ]
;

value rec is_irrefut_patt =
  fun
  [ <:patt< $lid:_$ >> -> True
  | <:patt< () >> -> True
  | <:patt< _ >> -> True
  | <:patt< ($x$ as $y$) >> -> is_irrefut_patt x && is_irrefut_patt y
  | <:patt< { $list:fpl$ } >> ->
      List.for_all (fun (_, p) -> is_irrefut_patt p) fpl
  | <:patt< ($p$ : $_$) >> -> is_irrefut_patt p
  | <:patt< ($list:pl$) >> -> List.for_all is_irrefut_patt pl
  | <:patt< ? $_$ >> -> True
  | <:patt< ? ($_$ = $_$) >> -> True
  | <:patt< ~ $_$ >> -> True
  | _ -> False ]
;

value not_impl name ind b x k =
  let desc =
    if Obj.tag (Obj.repr x) = Obj.tag (Obj.repr "") then
      sprintf "\"%s\"" (Obj.magic x)
    else if Obj.is_block (Obj.repr x) then
      "tag = " ^ string_of_int (Obj.tag (Obj.repr x))
    else "int_val = " ^ string_of_int (Obj.magic x)
  in
  sprintf "%s\"pr_r, not impl: %s; %s\"%s" b name (String.escaped desc) k
;

value tab ind = String.make ind ' ';

value var_escaped ind b v k =
  let x =
    if is_infix v || has_special_chars v then "\\" ^ v
    else if is_keyword v then v ^ "__"
    else v
  in
  sprintf "%s%s%s" b x k
;

value rec mod_ident ind b sl k =
  match sl with
  [ [] -> sprintf "%s%s" b k
  | [s] -> var_escaped ind b s k
  | [s :: sl] -> mod_ident ind (sprintf "%s%s." b s) sl k ]
;

(*
value option ind elem b z k =
  match z with
  [ Some z -> elem ind b z k
  | None -> sprintf "%s%s" b k ]
;
*)

(* horizontal list *)
value rec hlist elem ind b xl k =
  match xl with
  [ [] -> sprintf "%s%s" b k
  | [x] -> elem ind b x k
  | [x :: xl] -> sprintf "%s %s" (elem ind b x "") (hlist elem ind "" xl k) ]
;

(* horizontal list with different function from 2nd element on *)
value rec hlist2 elem elem2 ind b xl k =
  match xl with
  [ [] -> sprintf "%s%s" b k
  | [x] -> elem ind b x k
  | [x :: xl] ->
      sprintf "%s %s" (elem ind b x "") (hlist2 elem2 elem2 ind "" xl k) ]
;

(* horizontal list with different function for the last element *)
value rec hlistl elem eleml ind b xl k =
  match xl with
  [ [] -> sprintf "%s%s" b k
  | [x] -> eleml ind b x k
  | [x :: xl] ->
      sprintf "%s %s" (elem ind b x "") (hlistl elem eleml ind "" xl k) ]
;

(* vertical list *)
value rec vlist elem ind b xl k =
  match xl with
  [ [] -> sprintf "%s%s" b k
  | [x] -> elem ind b x k
  | [x :: xl] ->
      sprintf "%s\n%s" (elem ind b x "") (vlist elem ind (tab ind) xl k) ]
;

(* vertical list with different function from 2nd element on *)
value rec vlist2 elem elem2 ind b xl k =
  match xl with
  [ [] -> sprintf "%s%s" b k
  | [x] -> elem ind b x k
  | [x :: xl] ->
      sprintf "%s\n%s" (elem ind b x "")
        (vlist2 elem2 elem2 ind (tab ind) xl k) ]
;

(* vertical list with different function for the last element *)
value rec vlistl elem eleml ind b xl k =
  match xl with
  [ [] -> sprintf "%s%s" b k
  | [x] -> eleml ind b x k
  | [x :: xl] ->
      sprintf "%s\n%s" (elem ind b x "")
        (vlistl elem eleml ind (tab ind) xl k) ]
;

(* paragraph list with different function for the last element;
   the list elements are pairs where second elements are separators
   (the last separator is ignored) *)
value rec plistl elem eleml ind sh b xl k =
  match xl with
  [ [] -> assert False
  | [(x, _)] -> eleml ind b x k
  | [(x, sep) :: xl] ->
      let s =
        horiz_vertic (fun () -> Some (elem ind b x sep)) (fun () -> None)
      in
      match s with
      [ Some b ->
          loop b xl where rec loop b =
            fun
            [ [] -> assert False
            | [(x, _)] ->
                horiz_vertic (fun () -> eleml ind (sprintf "%s " b) x k)
                  (fun () ->
                     let s = eleml (ind + sh) (tab (ind + sh)) x k in
                     sprintf "%s\n%s" b s)
            | [(x, sep) :: xl] ->
                let s =
                  horiz_vertic
                    (fun () -> Some (elem ind (sprintf "%s " b) x sep))
                    (fun () -> None)
                in
                match s with
                [ Some b -> loop b xl
                | None ->
                    let s =
                      plistl elem eleml (ind + sh) 0 (tab (ind + sh))
                        [(x, sep) :: xl] k
                    in
                    sprintf "%s\n%s" b s ] ]
      | None ->
          let s1 = elem ind b x sep in
          let s2 = plistl elem eleml (ind + sh) 0 (tab (ind + sh)) xl k in
          sprintf "%s\n%s" s1 s2 ] ]
;

(* paragraph list *)
value plist elem ind sh b xl k = plistl elem elem ind sh b xl k;

value comma_after elem ind b x k = elem ind b x (sprintf ";%s" k);
value star_after elem ind b x k = elem ind b x (sprintf " *%s" k);
value op_after elem ind b (x, op) k = elem ind b x (sprintf "%s%s" op k);

value and_before elem ind b x k = elem ind (sprintf "%sand " b) x k;
value bar_before elem ind b x k = elem ind (sprintf "%s| " b) x k;

value operator ind left right sh b op x y k =
  let op = if op = "" then "" else " " ^ op in
  horiz_vertic
    (fun () ->
       sprintf "%s%s%s %s%s" b (left 0 "" x "") op (right 0 "" y "") k)
    (fun () ->
       let s1 = left ind b x op in
       let s2 = right (ind + 2) (tab (ind + 2)) y k in
       sprintf "%s\n%s" s1 s2)
;

value left_operator ind sh unfold next b x k =
  let xl =
    loop [] x "" where rec loop xl x op =
      match unfold x with
      [ Some (x1, op1, x2) -> loop [(x2, op) :: xl] x1 op1
      | None -> [(x, op) :: xl] ]
  in
  match xl with
  [ [(x, _)] -> next ind b x k
  | _ ->
      horiz_vertic (fun () -> hlist (op_after next) ind b xl k)
        (fun () -> plist next ind 2 b xl k) ]
;

value right_operator ind sh unfold next b x k =
  let xl =
    loop [] x where rec loop xl x =
      match unfold x with
      [ Some (x1, op, x2) -> loop [(x1, op) :: xl] x2
      | None -> List.rev [(x, "") :: xl] ]
  in
  match xl with
  [ [(x, _)] -> next ind b x k
  | _ ->
      horiz_vertic (fun () -> hlist (op_after next) ind b xl k)
        (fun () -> plist next ind 2 b xl k) ]
;

(*
 * Extensible printers
 *)

type printer_t 'a =
  { pr_fun : mutable string -> pr_fun 'a;
    pr_levels : mutable list (pr_level 'a) }
and pr_level 'a = { pr_label : string; pr_rules : mutable pr_rule 'a }
and pr_rule 'a =
  Extfun.t 'a (pr_fun 'a -> pr_fun 'a -> int -> string -> string -> string)
and pr_fun 'a = int -> string -> 'a -> string -> string;

(*
value rec find_pr_level lab =
  fun
  [ [] -> failwith ("level " ^ lab ^ " not found")
  | [lev :: levl] ->
      if lev.pr_label = lab then lev else find_pr_level lab levl ]
;
*)

value printer loc_of name = do {
  let pr_fun name pr lab =
    loop False pr.pr_levels where rec loop app =
      fun
      [ [] -> fun ind b z k ->
          failwith
            (Printf.sprintf "unable to print %s%s" name
               (if lab = "" then "" else " \"" ^ lab ^ "\""))
      | [lev :: levl] ->
          if app || lev.pr_label = lab then
            let next = loop True levl in
            curr where rec curr ind b z k =
              Extfun.apply lev.pr_rules z curr next ind b k
          else loop app levl ]
  in
  let pr = {pr_fun = fun []; pr_levels = []} in
  pr.pr_fun := pr_fun name pr;
  pr
};

value pr_expr = printer MLast.loc_of_expr "expr";
value pr_patt = printer MLast.loc_of_patt "patt";
value pr_ctyp = printer MLast.loc_of_ctyp "type";
value pr_str_item = printer MLast.loc_of_str_item "str_item";
value pr_sig_item = printer MLast.loc_of_sig_item "sig_item";
value pr_module_expr = printer MLast.loc_of_module_expr "module_expr";
value pr_module_type = printer MLast.loc_of_module_type "module_type";

value expr ind b z k = pr_expr.pr_fun "top" ind b z k;
value patt ind b z k = pr_patt.pr_fun "top" ind b z k;
value ctyp ind b z k = pr_ctyp.pr_fun "top" ind b z k;
value str_item ind b z k = pr_str_item.pr_fun "top" ind b z k;
value sig_item ind b z k = pr_sig_item.pr_fun "top" ind b z k;
value module_expr ind b z k = pr_module_expr.pr_fun "top" ind b z k;
value module_type ind b z k = pr_module_type.pr_fun "top" ind b z k;
(*
value expr_fun_args ge = Extfun.apply Pcaml.pr_expr_fun_args.val ge;

value patt_as ind b z k =
  match z with
  [ <:patt< ($x$ as $y$) >> -> patt ind b x (patt ind " as " y k)
  | z -> patt ind b z k ]
;

(* utilities specific to pr_r *)

Pcaml.pr_expr_fun_args.val :=
  extfun Extfun.empty with
  [ <:expr< fun $p$ -> $e$ >> as z ->
      if is_irrefut_patt p then
        let (pl, e) = expr_fun_args e in
        ([p :: pl], e)
      else ([], z)
  | z -> ([], z) ]
;
*)

value binding elem ind b (p, e) k =
  horiz_vertic
    (fun () -> sprintf "%s %s%s" (patt 0 b p " =") (elem 0 "" e "") k)
    (fun () ->
       sprintf "%s\n%s" (patt ind b p " =")
         (elem (ind + 2) (tab (ind + 2)) e k))
;

value match_assoc ind b (p, w, e) k =
  horiz_vertic
    (fun () ->
       sprintf "%s%s%s -> %s%s" b (patt 0 "" p "")
         (match w with
          [ Some e -> sprintf " when %s" (expr 0 "" e "")
          | None -> "" ])
         (expr 0 "" e "") k)
    (fun () ->
       let s1 =
         match w with
         [ Some e ->
             horiz_vertic
               (fun () -> 
                  sprintf "%s%s when %s ->" b (patt 0 "" p "")
                    (expr 0 "" e ""))
               (fun () ->
                  let s1 = patt (ind + 2) b p "" in
                  let s2 =
                    horiz_vertic
                      (fun () ->
                         sprintf "%swhen %s ->" (tab (ind + 2))
                           (expr 0 "" e ""))
                      (fun () ->
                         let s1 = sprintf "%swhen" (tab (ind + 2)) in
                         let s2 = expr (ind + 4) (tab (ind + 4)) e " ->" in
                         sprintf "%s\n%s" s1 s2)
                  in
                  sprintf "%s\n%s" s1 s2)
         | None -> patt (ind + 2) b p " ->" ]
       in
       let s2 = expr (ind + 4) (tab (ind + 4)) e k in
       sprintf "%s\n%s" s1 s2)
;

value match_assoc_list ind b pwel k =
  vlist2 match_assoc (bar_before match_assoc) ind (sprintf "%s[ " b) pwel
    (sprintf " ]%s" k)
;

value rec make_expr_list =
  fun
  [ <:expr< [$x$ :: $y$] >> ->
      let (xl, c) = make_expr_list y in
      ([x :: xl], c)
  | <:expr< [] >> -> ([], None)
  | x -> ([], Some x) ]
;

value rec make_patt_list =
  fun
  [ <:patt< [$x$ :: $y$] >> ->
      let (xl, c) = make_patt_list y in
      ([x :: xl], c)
  | <:patt< [] >> -> ([], None)
  | x -> ([], Some x) ]
;

(*
value x_list ind elem b (xl, c) k =
  let ini =
    match c with
    [ None -> ("", [])
    | Some x -> (" ::", [(x, "")]) ]
  in
  let (_, xl) =
    List.fold_right (fun x (sep, xl) -> (";", [(x, sep) :: xl])) xl ini
  in
  listws_hv (ind + 1) 0 elem (sprintf "%s[" b) xl (sprintf "]%s" k)
;

value rec type_params ind b l k =
  match l with
  [ [(s, vari) :: l] ->
      let b =
        match vari with
        [ (True, False) -> sprintf "%s+" b
        | (False, True) -> sprintf "%s-" b
        | _ -> b ]
      in
      sprintf " %s'%s%s%s" b s "" (type_params ind "" l k)
  | [] -> sprintf "%s%s" b k ]
;

value type_decl ind last b ((_, tn), tp, te, cl) k =
  let tn = var_escaped ind "" tn "" in
  if last then
    sprint_indent_unindent ind 2
      (fun ind -> sprintf "%s %s%s =" b tn (type_params ind "" tp ""))
      (fun ind b _ ->
         ctyp ind b te
           (sprintf "%s%s" (if cl = [] then "" else " \"constraint\"") ""))
      (fun ind b _ -> sprintf "%s%s" b k)
  else
    sprint_indent ind 2
      (fun ind _ -> sprintf "%s %s%s =" b tn (type_params ind "" tp ""))
      (fun ind b _ ->
         ctyp ind b te
           (sprintf "%s%s" (if cl = [] then "" else " \"constraint\"") k))
;

value rec type_decl_list ind b tdl k =
  match tdl with
  [ [] -> sprintf "%s%s" b k
  | [td] -> type_decl ind True b td k
  | [td :: tdl] ->
      let () = horiz_vertic (fun nofit -> nofit ()) (fun () -> ()) in
      let s1 = type_decl ind False b td "" in
      let s1 = sprintf "%s\n" s1 in
      sprintf "%s%s" s1
        (type_decl_list ind (sprintf "%sand" (tab ind)) tdl k) ]
;
*)

value type_var ind b (tv, (p, m)) k =
  sprintf "%s%s'%s%s" b (if p then "+" else if m then "-" else "") tv k
;

value type_decl ind b ((_, tn), tp, te, cl) k =
  horiz_vertic
    (fun () ->
       sprintf "%s%s%s = %s%s%s" b tn
         (if tp = [] then "" else sprintf " %s" (hlist type_var 0 "" tp ""))
         (ctyp 0 "" te "")
         (if cl = [] then "" else not_impl "type_decl cl" ind "" cl "") k)
    (fun () ->
       let s1 =
         horiz_vertic
           (fun () ->
              sprintf "%s%s%s =" b tn
                (if tp = [] then "" else
                 sprintf " %s" (hlist type_var 0 "" tp "")))
           (fun () -> not_impl "type_decl vertic 1" ind b tn k)
       in
       let s2 =
         if cl = [] then ctyp (ind + 2) (tab (ind + 2)) te k
        else
           horiz_vertic
             (fun () ->
                sprintf "%s%s%s%s" (tab (ind + 2)) (ctyp 0 "" te "")
                  (not_impl "type_decl cl 2" ind "" cl "") k)
             (fun () -> not_impl "type_decl vertic 2" ind "" tn k)
       in
       sprintf "%s\n%s" s1 s2)
;

value label_decl ind b (_, l, m, t) k =
  horiz_vertic
    (fun () ->
       sprintf "%s%s : %s%s%s" b l (if m then "mutable " else "")
         (ctyp 0 "" t "") k)
    (fun () ->
       let s1 = sprintf "%s%s :%s" b l (if m then "mutable " else "") in
       let s2 = ctyp (ind + 2) (tab (ind + 2)) t k in
       sprintf "%s\n%s" s1 s2)
;

value cons_decl ind b (_, c, tl) k =
  horiz_vertic
    (fun () ->
       let s1 = sprintf "%s%s" b c in
       let s2 =
         if tl = [] then ""
         else sprintf " of %s" (hlist2 ctyp (and_before ctyp) 0 "" tl "")
       in
       sprintf "%s%s%s" s1 s2 k)
    (fun () -> not_impl "cons_decl vertic" ind b c k)
;

(* definitions of printers by decreasing level *)

value ctyp_top =
  extfun Extfun.empty with
  [ <:ctyp< $x$ == $y$ >> ->
      fun curr next ind b k -> operator ind next next 2 b "==" x y k
  | z -> fun curr next ind b k -> next ind b z k ]
;

value ctyp_arrow =
  extfun Extfun.empty with
  [ <:ctyp< $_$ -> $_$ >> as z ->
      fun curr next ind b k ->
        let unfold =
          fun
          [ <:ctyp< $x$ -> $y$ >> -> Some (x, " ->", y)
          | _ -> None ]
        in
        right_operator ind 2 unfold next b z k
  | z -> fun curr next ind b k -> next ind b z k ]
;

value ctyp_apply =
  extfun Extfun.empty with
  [ <:ctyp< $_$ $_$ >> as z ->
      fun curr next ind b k ->
        let unfold =
          fun
          [ <:ctyp< $x$ $y$ >> -> Some (x, "", y)
          | _ -> None ]
        in
        left_operator ind 0 unfold next b z k
  | z -> fun curr next ind b k -> next ind b z k ]
;

value ctyp_dot =
  extfun Extfun.empty with
  [ <:ctyp< $x$ . $y$ >> ->
      fun curr next ind b k -> curr ind (curr ind b x ".") y k
  | z -> fun curr next ind b k -> next ind b z k ]
;

value ctyp_simple =
  extfun Extfun.empty with
  [
(*
    <:ctyp< ($x$ as $y$) >> ->
      fun curr next ind b k ->
        sprint_indent (ind + 1) 2
          (fun ind _ -> ctyp 0 (sprintf "%s(" b) x " as")
          (fun ind b _ -> ctyp ind b y (sprintf ")%s" k))
  |
*)
    <:ctyp< { $list:ltl$ } >> ->
      fun curr next ind b k ->
        horiz_vertic
          (fun () ->
             hlistl (comma_after label_decl) label_decl 0
               (sprintf "%s{ " b) ltl (sprintf " }%s" k))
          (fun () ->
             vlistl (comma_after label_decl) label_decl (ind + 2)
               (sprintf "%s{ " b) ltl (sprintf " }%s" k))
(*
  | <:ctyp< [= $list:rfl$ ] >> as t ->
      fun curr next ind b k ->
        let vdl =
          List.map
            (fun rf ->
               match rf with
               [ <:row_field< `$s$ of $opt:_$ $list:tl$ >> ->
                   (MLast.loc_of_ctyp t, s, tl)
               | <:row_field< $t$ >> -> (MLast.loc_of_ctyp t, "Foo", []) ])
            rfl
        in
        let loc = MLast.loc_of_ctyp t in
        curr ind b <:ctyp< [ $list:vdl$ ] >> k
*)
  | <:ctyp< [ $list:vdl$ ] >> ->
      fun curr next ind b k ->
        horiz_vertic
          (fun () ->
             hlist2 cons_decl (bar_before cons_decl) 0
               (sprintf "%s[ " b) vdl (sprintf " ]%s" k))
          (fun () ->
             vlist2 cons_decl (bar_before cons_decl) ind
               (sprintf "%s[ " b) vdl (sprintf " ]%s" k))
  | <:ctyp< ($list:tl$) >> ->
      fun curr next ind b k ->
        horiz_vertic
          (fun () ->
             sprintf "%s(%s)%s" b (hlistl (star_after ctyp) ctyp 0 "" tl "")
               k)
          (fun () ->
             let tl = List.map (fun t -> (t, " * ")) tl in
             plist ctyp ind 1 (sprintf "%s(" b) tl (sprintf ")%s" k))
  | <:ctyp< $lid:t$ >> ->
      fun curr next ind b k -> var_escaped ind b t k
  | <:ctyp< $uid:t$ >> ->
      fun curr next ind b k -> sprintf "%s%s%s" b t k
  | <:ctyp< ' $s$ >> ->
      fun curr next ind b k -> sprintf "%s'%s%s" b s k
  | <:ctyp< _ >> ->
      fun curr next ind b k -> sprintf "%s_%s" b k
(*
  | <:ctyp< ? $_$ : $t$ >> | <:ctyp< ~ $_$ : $t$ >> ->
      fun curr next ind b k -> pr_ctyp.pr_fun "apply" ind b t k
  | <:ctyp< < $list:_$ $opt:_$ > >> ->
      fun curr next ind b k ->
        failwith "cannot convert objects in syntax 's'"
*)
  | <:ctyp< $_$ $_$ >> | <:ctyp< $_$ -> $_$ >> as z ->
      fun curr next ind b k ->
        ctyp (ind + 1) (sprintf "%s(" b) z (sprintf ")%s" k)
  | z ->
      fun curr next ind b k -> not_impl "ctyp" ind b z k ]
;

value expr_top =
  extfun Extfun.empty with
  [ <:expr< if $e1$ then $e2$ else $e3$ >> ->
      fun curr next ind b k ->
        horiz_vertic
         (fun () ->
            sprintf "%sif %s then %s else %s%s" b (expr 0 "" e1 "")
              (expr 0 "" e2 "") (expr 0 "" e3 "") k)
         (fun () ->
            let s1 =
              horiz_vertic
                (fun () ->
                   sprintf "%sif %s then %s" b (expr 0 "" e1 "")
                     (expr 0 "" e2 ""))
                (fun () ->
                   let s1 =
                     horiz_vertic
                       (fun () -> sprintf "%sif %s then" b (expr 0 "" e1 ""))
                       (fun () ->
                          let s1 = expr (ind + 3) (sprintf "%sif " b) e1 "" in
                          let s2 = sprintf "%sthen" (tab ind) in
                          sprintf "%s\n%s" s1 s2)
                   in
                   let s2 = expr (ind + 2) (tab (ind + 2)) e2 "" in
                   sprintf "%s\n%s" s1 s2)
            in
            let s2 =
              horiz_vertic
                (fun () -> sprintf "%selse %s%s" (tab ind) (expr 0 "" e3 "") k)
                (fun () ->
                   let s = expr (ind + 2) (tab (ind + 2)) e3 k in
                   sprintf "%selse\n%s" (tab ind) s)
            in
            sprintf "%s\n%s" s1 s2)
  | <:expr< fun [ $list:pwel$ ] >> ->
      fun curr next ind b k ->
        match pwel with
        [ [(p1, None, e1)] when is_irrefut_patt p1 ->
            horiz_vertic
              (fun () ->
                 sprintf "%s %s" (patt ind (sprintf "%sfun " b) p1 " ->")
                   (expr 0 "" e1 k))
              (fun () ->
                 sprintf "%s\n%s" (patt ind (sprintf "%sfun " b) p1 " ->")
                   (expr (ind + 2) (tab (ind + 2)) e1 k))
        | [] -> sprintf "%sfun []%s" b k
        | pwel ->
            let s = match_assoc_list ind (tab ind) pwel k in
            sprintf "%sfun\n%s" b s ]
  | <:expr< try $e1$ with [ $list:pwel$ ] >> |
    <:expr< match $e1$ with [ $list:pwel$ ] >> as e ->
      fun curr next ind b k ->
        let op =
          match e with
          [ <:expr< try $_$ with [ $list:_$ ] >> -> "try"
          | _ -> "match" ]
        in
        horiz_vertic
          (fun () ->
             sprintf "%s%s %s with %s%s" b op (expr 0 "" e1 "")
               (match_assoc_list 0 "" pwel "") k)
          (fun () ->
             let s1 =
               horiz_vertic
                 (fun () -> sprintf "%s%s %s with" b op (expr ind "" e1 ""))
                 (fun () ->
                    let s = expr (ind + 2) (tab (ind + 2)) e1 "" in
                    sprintf "%s%s\n%s\n%swith" b op s (tab ind))
             in
             let s2 = match_assoc_list ind (tab ind) pwel k in
             sprintf "%s\n%s" s1 s2)
  | <:expr< let $opt:rf1$ $list:pel1$ in $e1$ >> ->
      fun curr next ind b k ->
        horiz_vertic
          (fun () ->
             let s1 =
               hlist2 (binding expr) (and_before (binding expr)) ind
                 (sprintf "%slet %s" b (if rf1 then "rec " else ""))
                 pel1 " in"
             in
             let s2 = expr 0 "" e1 k in
             sprintf "%s %s" s1 s2)
          (fun () ->
             let s1 =
               vlist2 (binding expr) (and_before (binding expr)) ind
                 (sprintf "%slet %s" b (if rf1 then "rec " else ""))
                 pel1 " in"
             in
             let s2 = expr ind (tab ind) e1 k in
             sprintf "%s\n%s" s1 s2)
(*
  | <:expr< while $e1$ do { $list:el$ } >> ->
      fun curr next ind b k ->
        sprint_indent_unindent ind 2
          (fun ind ->
             sprint_indent_unindent ind 2 (fun _ -> sprintf "%swhile" b)
               (fun ind b _ -> curr ind b e1 "")
               (fun ind b1 b2 -> sprintf "%s%sdo" b1 b2))
          (fun ind b nl ->
             if nl then
               let letexprl = let_and_seq_list_of_list [] el in
               let_in_and_sequence_combination ind b letexprl ";"
             else listws ind curr "" ";" False el ";")
          (fun ind b1 b2 -> sprintf "%s%sdone%s" b1 b2 k)
*)
  | <:expr< for $v$ = $e1$ $to:d$ $e2$ do { $list:el$ } >> ->
      fun curr next ind b k ->
        horiz_vertic
          (fun () ->
             sprintf "%sfor %s = %s %s %s do { %s }%s" b v
               (curr ind "" e1 "") (if d then "to" else "downto")
               (curr ind "" e2 "")
               (hlistl (comma_after expr) expr 0 "" el "") k)
          (fun () ->
             let s1 =
               horiz_vertic
                 (fun () ->
                    sprintf "%sfor %s = %s %s %s do {" b v
                      (curr ind "" e1 "") (if d then "to" else "downto")
                      (curr ind "" e2 ""))
                 (fun () -> not_impl "for vertic 1" ind b v "")
             in
             let s2 =
               vlistl (comma_after expr) expr (ind + 2) (tab (ind + 2)) el ""
             in
             let s3 = sprintf "%s}%s" (tab ind) k in
             sprintf "%s\n%s\n%s" s1 s2 s3)
  | z ->
      fun curr next ind b k -> next ind b z k ]
;

value expr_assign =
  extfun Extfun.empty with
  [ <:expr< $x$ := $y$ >> ->
      fun curr next ind b k -> operator ind next expr 2 b ":=" x y k
  | z -> fun curr next ind b k -> next ind b z k ]
;

value expr_or =
  extfun Extfun.empty with
  [ z ->
      fun curr next ind b k ->
        let unfold =
          fun
          [ <:expr< $lid:op$ $x$ $y$ >> ->
              if List.mem op ["||"] then Some (x, " " ^ op, y) else None
          | _ -> None ]
        in
        right_operator ind 0 unfold next b z k ]
;

value expr_and =
  extfun Extfun.empty with
  [ z ->
      fun curr next ind b k ->
        let unfold =
          fun
          [ <:expr< $lid:op$ $x$ $y$ >> ->
              if List.mem op ["&&"] then Some (x, " " ^ op, y) else None
          | _ -> None ]
        in
        right_operator ind 0 unfold next b z k ]
;

value expr_less =
  extfun Extfun.empty with
  [ <:expr< $lid:op$ $x$ $y$ >> as z ->
      fun curr next ind b k ->
        match op with
        [ "!=" | "<" | "<=" | "<>" | "=" | "==" | ">" | ">=" ->
            operator ind next next 0 b op x y k
        | _ -> next ind b z k ]
  | z -> fun curr next ind b k -> next ind b z k ]
;

value expr_concat =
  extfun Extfun.empty with
  [ z ->
      fun curr next ind b k ->
        let unfold =
          fun
          [ <:expr< $lid:op$ $x$ $y$ >> ->
              if List.mem op ["^"; "@"] then Some (x, " " ^ op, y) else None
          | _ -> None ]
        in
        right_operator ind 0 unfold next b z k ]
;

value expr_add =
  let ops = ["+"; "+."; "-"; "-."] in
  extfun Extfun.empty with
  [ z ->
      fun curr next ind b k ->
        let unfold =
          fun
          [ <:expr< $lid:op$ $x$ $y$ >> ->
              if List.mem op ops then Some (x, " " ^ op, y) else None
          | _ -> None ]
        in
        left_operator ind 0 unfold next b z k ]
;

(*
value expr_mul =
  let ops = ["*"; "*."; "/"; "/."; "land"; "lor"; "lxor"; "mod"] in
  extfun Extfun.empty with
  [ z ->
      fun curr next ind b k ->
        let unfold =
          fun
          [ <:expr< $lid:op$ $x$ $y$ >> ->
              if List.mem op ops then Some (x, " " ^ op, y) else None
          | _ -> None ]
        in
        left_operator ind 0 unfold next b z k ]
;

value expr_pow =
  extfun Extfun.empty with
  [ z ->
      fun curr next ind b k ->
        let unfold =
          fun
          [ <:expr< $lid:op$ $x$ $y$ >> ->
              if List.mem op ["**"; "lsl"] then Some (x, " " ^ op, y)
              else None
          | _ -> None ]
        in
        right_operator ind 0 unfold next b z k ]
;

value expr_unary_minus =
  extfun Extfun.empty with
  [ <:expr< ~- $x$ >> ->
      fun curr next ind b k -> curr ind (sprintf "%s- " b) x k
  | <:expr< ~-. $x$ >> ->
      fun curr next ind b k -> curr ind (sprintf "%s-. " b) x k
  | z ->
      fun curr next ind b k -> next ind b z k ]
;
*)

value expr_apply =
  extfun Extfun.empty with
  [ <:expr< assert $e$ >> ->
      fun curr next ind b k ->
        horiz_vertic (fun () -> sprintf "%sassert %s%s" b (next 0 "" e "") k)
          (fun () -> not_impl "assert vertical" ind b e k)
(*
  | <:expr< lazy $e$ >> ->
      fun curr next ind b k ->
        sprint_indent ind 2 (fun _ _ -> sprintf "%slazy" b)
          (fun ind b _ -> next ind b e k)
  | <:expr< $int:s$ >> as e ->
      fun curr next ind b k ->
        if String.length s > 0 && s.[0] = '-' then sprintf "%s%s%s" b s k
        else next ind b e k
*)
  | <:expr< $_$ $_$ >> as z ->
      fun curr next ind b k ->
        let inf =
          match z with
          [ <:expr< $lid:n$ $_$ $_$ >> -> is_infix n
          | <:expr< [$_$ :: $_$] >> -> True
          | _ -> False ]
        in
        if inf then next ind b z k
        else
          let unfold =
            fun
            [ <:expr< $x$ $y$ >> -> Some (x, "", y)
            | e -> None ]
          in
          left_operator ind 2 unfold next b z k
  | z ->
      fun curr next ind b k -> next ind b z k ]
;

value expr_dot =
  extfun Extfun.empty with
  [ <:expr< $x$ . $y$ >> ->
      fun curr next ind b k ->
        horiz_vertic (fun () -> curr 0 (curr 0 b x ".") y k)
          (fun () -> not_impl ". vertic" ind b x k)
  | <:expr< $x$ .( $y$ ) >> ->
      fun curr next ind b k ->
        expr ind (curr ind b x ".(") y (sprintf ")%s" k)
  | <:expr< $x$ .[ $y$ ] >> ->
      fun curr next ind b k ->
        expr ind (curr ind b x ".[") y (sprintf "]%s" k)
  | z ->
      fun curr next ind b k -> next ind b z k ]
;

value expr_simple =
  extfun Extfun.empty with
  [ <:expr< do { $list:el$ } >> ->
      fun curr next ind b k ->
        horiz_vertic
          (fun () ->
             sprintf "%sdo {%s%s%s}%s" b " "
               (hlistl (comma_after expr) expr 0 "" el "") " " k)
          (fun () ->
             sprintf "%sdo {%s%s%s}%s" b "\n"
               (vlistl (comma_after expr) expr (ind + 2) (tab (ind + 2)) el
                  "")
               ("\n" ^ tab ind) k)
  | <:expr< ($list:el$) >> ->
      fun curr next ind b k ->
        let el = List.map (fun e -> (e, ",")) el in
        plist expr ind 1 (sprintf "%s(" b) el (sprintf ")%s" k)
  | <:expr< {$list:lel$} >> ->
      fun curr next ind b k ->
        let lxl = List.map (fun lx -> (lx, ";")) lel in
        plist (binding expr) (ind + 1) 0 (sprintf "%s{" b) lxl
          (sprintf "}%s" k)
(*
  | <:expr< {($e$) with $list:lel$} >> ->
      fun curr next ind b k ->
        let b1 = expr ind "(" e ") with " in
        let lxl = List.map (fun lx -> (lx, ";")) lel in
        listws_hv (ind + 1) 0
          (fun ind b pe k -> binding ind False (b, "") pe ("", k))
          (sprintf "%s{%s" b b1) lxl (sprintf "}%s" k)
  | <:expr< [| $list:el$ |] >> ->
      fun curr next ind b k ->
        if el = [] then sprintf "%s[| |]%s" b k
        else
          let el = List.map (fun e -> (e, ";")) el in
          listws_hv (ind + 3) 0 expr (sprintf "%s[| " b) el
            (sprintf " |]%s" k)
*)
  | <:expr< [$_$ :: $_$] >> as z ->
      fun curr next ind b k ->
        let (xl, y) = make_expr_list z in
        let xl = List.map (fun x -> (x, ";")) xl in
        let expr2 ind b x k =
          match y with
          [ Some y ->
              horiz_vertic
                (fun () ->
                   sprintf "%s%s :: %s]%s" b (expr ind "" x "")
                     (expr ind "" y "") k)
                (fun () ->
                   let s1 = expr ind b x " ::" in
                   let s2 =
                     expr (ind + 2) (tab (ind + 2)) y (sprintf "]%s" k)
                   in
                   sprintf "%s\n%s" s1 s2)
          | None -> expr ind b x (sprintf "]%s" k) ]
        in
        plistl expr expr2 (ind + 1) 0 (sprintf "%s[" b) xl k
  | <:expr< ($e$ : $t$) >> ->
      fun curr next ind b k ->
        horiz_vertic
          (fun () ->
             sprintf "%s(%s : %s)%s" b (expr 0 "" e "") (ctyp 0 "" t "") k)
          (fun () ->
             let s1 = expr (ind + 1) (sprintf "%s(" b) e " :" in
             let s2 = ctyp (ind + 1) (tab (ind + 1)) t (sprintf ")%s" k) in
             sprintf "%s\n%s" s1 s2)
  | <:expr< $int:s$ >> | <:expr< $flo:s$ >> ->
      fun curr next ind b k ->
        if String.length s > 0 && s.[0] = '-' then sprintf "%s(%s)%s" b s k
        else sprintf "%s%s%s" b s k
(*
  | <:expr< $int32:s$ >> ->
      fun curr next ind b k ->
        let s = s ^ "l" in
        if String.length s > 0 && s.[0] = '-' then sprintf "%s(%s)%s" b s k
        else sprintf "%s%s%s" b s k
  | <:expr< $int64:s$ >> ->
      fun curr next ind b k ->
        let s = s ^ "L" in
        if String.length s > 0 && s.[0] = '-' then sprintf "%s(%s)%s" b s k
        else sprintf "%s%s%s" b s k
  | <:expr< $nativeint:s$ >> ->
      fun curr next ind b k ->
        let s = s ^ "n" in
        if String.length s > 0 && s.[0] = '-' then sprintf "%s(%s)%s" b s k
        else sprintf "%s%s%s" b s k
*)
  | <:expr< $lid:s$ >> ->
      fun curr next ind b k -> var_escaped ind b s k
  | <:expr< $uid:s$ >> | <:expr< `$uid:s$ >> ->
      fun curr next ind b k -> sprintf "%s%s%s" b s k
  | <:expr< $str:s$ >> ->
      fun curr next ind b k -> sprintf "%s\"%s\"%s" b s k
  | <:expr< $chr:s$ >> ->
      fun curr next ind b k -> sprintf "%s'%s'%s" b s k
(*
  | <:expr< ? $s$ >> ->
      fun curr next ind b k -> var_escaped ind b s k
  | <:expr< ~ $_$ : $z$ >> ->
      fun curr next ind b k -> curr ind b z k
  | <:expr< let $opt:_$ $list:_$ in $e$ >> as z
    when snd (let_and_seq_list e) ->
      fun curr next ind b k -> expr ind b z k
*)
  | <:expr< $_$ $_$ >> (* | <:expr< $_$ := $_$ >> *) |
    <:expr< fun [ $list:_$ ] >> | <:expr< if $_$ then $_$ else $_$ >> |
    <:expr< let $opt:_$ $list:_$ in $_$ >> |
    <:expr< match $_$ with [ $list:_$ ] >> |
    <:expr< try $_$ with [ $list:_$ ] >> as z ->
      fun curr next ind b k ->
        let (inf, n) =
          match z with
          [ <:expr< $lid:n$ $_$ $_$ >> -> (is_not_yet_implemented_infix n, n)
          | _ -> (False, "") ]
        in
        if inf then not_impl "op" ind b n k
        else expr (ind + 1) (sprintf "%s(" b) z (sprintf ")%s" k)
  | z ->
      fun curr next ind b k -> not_impl "expr" ind b z k ]
;

value patt_top =
  extfun Extfun.empty with
  [ <:patt< $_$ | $_$ >> as z ->
      fun curr next ind b k ->
        let unfold =
          fun
          [ <:patt< $x$ | $y$ >> -> Some (x, " |", y)
          | _ -> None ]
        in
        left_operator ind 0 unfold next b z k
  | z -> fun curr next ind b k -> next ind b z k ]
;

value patt_range =
  extfun Extfun.empty with
  [ <:patt< $x$ .. $y$ >> ->
      fun curr next ind b k ->
        sprintf "%s..%s" (next ind b x "") (next ind "" y k)
  | z -> fun curr next ind b k -> next ind b z k ]
;

value patt_apply =
  extfun Extfun.empty with
  [ <:patt< $_$ $_$ >> as z ->
      fun curr next ind b k ->
        let unfold =
          fun
          [ <:patt< [ $_$ :: $_$ ] >> -> None
          | <:patt< $x$ $y$ >> -> Some (x, "", y)
          | p -> None ]
        in
        left_operator ind 2 unfold next b z k
  | z -> fun curr next ind b k -> next ind b z k ]
;

value patt_dot =
  extfun Extfun.empty with
  [ <:patt< $x$ . $y$ >> ->
      fun curr next ind b k -> curr ind (curr ind b x ".") y k
  | z -> fun curr next ind b k -> next ind b z k ]
;

value patt_simple =
  extfun Extfun.empty with
  [ <:patt< ($x$ as $y$) >> ->
      fun curr next ind b k ->
        horiz_vertic
          (fun () ->
             sprintf "%s(%s as %s)%s" b (patt 0 "" x "") (patt 0 "" y "") k)
          (fun () ->
             let s1 = patt (ind + 1) (sprintf "%s(" b) x "" in
             let s2 =
               patt (ind + 1) (sprintf "%sas " (tab (ind + 1))) y
                 (sprintf ")%s" k)
             in
             sprintf "%s\n%s" s1 s2)
  | <:patt< ($list:pl$) >> ->
      fun curr next ind b k ->
        let pl = List.map (fun p -> (p, ",")) pl in
        plist patt ind 1 (sprintf "%s(" b) pl (sprintf ")%s" k)
  | <:patt< {$list:lpl$} >> ->
      fun curr next ind b k ->
        let lxl = List.map (fun lx -> (lx, ";")) lpl in
        plist (binding patt) (ind + 1) 0 (sprintf "%s{" b) lxl
          (sprintf "}%s" k)
  | <:patt< [$_$ :: $_$] >> as z ->
      fun curr next ind b k ->
        let (xl, y) = make_patt_list z in
        let xl = List.map (fun x -> (x, ";")) xl in
        let patt2 ind b x k =
          match y with
          [ Some y ->
              horiz_vertic
                (fun () ->
                   sprintf "%s%s :: %s]%s" b (patt ind "" x "")
                     (patt ind "" y "") k)
                (fun () ->
                   let s1 = patt ind b x " ::" in
                   let s2 =
                     patt (ind + 2) (tab (ind + 2)) y (sprintf "]%s" k)
                   in
                   sprintf "%s\n%s" s1 s2)
          | None -> patt ind b x (sprintf "]%s" k) ]
        in
        plistl patt patt2 (ind + 1) 0 (sprintf "%s[" b) xl k
  | <:patt< ($p$ : $t$) >> ->
      fun curr next ind b k ->
        horiz_vertic
          (fun () ->
             sprintf "%s(%s : %s)%s" b (patt 0 "" p "") (ctyp 0 "" t "") k)
          (fun () ->
             let s1 = patt ind (sprintf "%s(" b) p " :" in
             let s2 = ctyp (ind + 1) (tab (ind + 1)) t (sprintf ")%s" k) in
             sprintf "%s\n%s" s1 s2)
  | <:patt< $int:s$ >> ->
      fun curr next ind b k -> sprintf "%s%s%s" b s k
  | <:patt< $lid:s$ >> | <:patt< ~ $s$ >> ->
      fun curr next ind b k -> var_escaped ind b s k
  | <:patt< $uid:s$ >> | <:patt< `$uid:s$ >> ->
      fun curr next ind b k -> sprintf "%s%s%s" b s k
  | <:patt< $chr:s$ >> ->
      fun curr next ind b k -> sprintf "%s'%s'%s" b s k
  | <:patt< $str:s$ >> ->
      fun curr next ind b k -> sprintf "%s\"%s\"%s" b s k
  | <:patt< _ >> ->
      fun curr next ind b k -> sprintf "%s_%s" b k
(*
  | <:patt< ? $s$ >> | <:patt< ? ($lid:s$ = $_$) >> ->
      fun curr next ind b k -> var_escaped ind b s k
*)
  | <:patt< $_$ $_$ >> | <:patt< $_$ | $_$ >> | <:patt< $_$ .. $_$ >>
    as z ->
      fun curr next ind b k ->
        patt (ind + 1) (sprintf "%s(" b) z (sprintf ")%s" k)
  | z ->
      fun curr next ind b k -> not_impl "patt" ind b z k ]
;

value string ind b s k = sprintf "%s\"%s\"%s" b s k;

value external_decl ind b (n, t, sl) k =
  horiz_vertic
    (fun () ->
       sprintf "%sexternal %s : %s = %s%s" b n (ctyp 0 "" t "")
         (hlist string 0 "" sl "") k)
    (fun () -> not_impl "external_decl vertic" ind b n k)
;

value exception_decl ind b (e, tl, id) k =
  horiz_vertic
    (fun () ->
       sprintf "%sexception %s%s%s%s" b e
         (if tl = [] then ""
          else
            sprintf " of %s" (hlist2 ctyp (and_before ctyp) 0 "" tl ""))
         (if id = [] then ""
          else sprintf " = %s" (mod_ident 0 "" id ""))
         k)
    (fun () -> not_impl "exception vertic" ind b e k)
;

value str_item_top =
  extfun Extfun.empty with
  [ <:str_item< # $s$ $e$ >> ->
      fun curr next ind b k -> expr ind (sprintf "%s#%s " b s) e k
  | <:str_item< declare $list:sil$ end >> ->
      fun curr next ind b k ->
        horiz_vertic
          (fun () ->
             if sil = [] then sprintf "%sdeclare end%s" b k
             else not_impl "declare horiz" ind b sil k)
          (fun () -> not_impl "declare vertic" ind b sil k)
  | <:str_item< exception $e$ of $list:tl$ = $id$ >> ->
      fun curr next ind b k -> exception_decl ind b (e, tl, id) k
  | <:str_item< external $n$ : $t$ = $list:sl$ >> ->
      fun curr next ind b k -> external_decl ind b (n, t, sl) k
  | <:str_item< module $m$ = $me$ >> ->
      fun curr next ind b k ->
        horiz_vertic
          (fun () ->
             sprintf "%smodule %s = %s%s" b m (module_expr 0 "" me "") k)
          (fun () ->
             sprintf "%smodule %s =\n%s\n%s" b m
               (module_expr (ind + 2) (tab (ind + 2)) me "") (tab ind ^ k))
  | <:str_item< module type $m$ = $mt$ >> ->
      fun curr next ind b k ->
        horiz_vertic
          (fun () ->
             sprintf "%smodule type %s = %s%s" b m (module_type 0 "" mt "") k)
          (fun () ->
             sprintf "%smodule type %s =\n%s\n%s" b m
               (module_type (ind + 2) (tab (ind + 2)) mt "") (tab ind ^ k))
  | <:str_item< open $i$ >> ->
      fun curr next ind b k -> mod_ident ind (sprintf "%sopen " b) i k
  | <:str_item< type $list:tdl$ >> ->
      fun curr next ind b k ->
        vlist2 type_decl (and_before type_decl) ind (sprintf "%stype " b) tdl
          k
  | <:str_item< value $opt:rf$ $list:pel$ >> ->
      fun curr next ind b k ->
        horiz_vertic
          (fun () ->
             let s =
               hlist2 (binding expr) (and_before (binding expr)) ind
                 (sprintf "%svalue %s" b (if rf then "rec " else "")) pel ""
             in
             sprintf "%s%s" s k)
          (fun () ->
             let s =
               vlist2 (binding expr) (and_before (binding expr)) ind
                 (sprintf "%svalue %s" b (if rf then "rec " else "")) pel ""
             in
             sprintf "%s\n%s%s" s (tab ind) k)
  | <:str_item< $exp:e$ >> ->
      fun curr next ind b k -> expr ind b e k
(*
  | MLast.StUse _ _ _ ->
      fun curr next ind b k ->
        (* extra ast generated by camlp4 *)
        ""
*)
  | z ->
      fun curr next ind b k -> not_impl "str_item" ind b z k ]
;

value sig_item_top =
  extfun Extfun.empty with
  [
(*
    <:sig_item< exception $e$ of $list:tl$ >> ->
      fun curr next ind b k -> exception_item ind b e tl [] k
  |
*)
    <:sig_item< external $n$ : $t$ = $list:sl$ >> ->
      fun curr next ind b k -> external_decl ind b (n, t, sl) k
  | <:sig_item< module $m$ : $mt$ >> ->
      fun curr next ind b k ->
        horiz_vertic
          (fun () ->
             sprintf "%smodule %s : %s%s" b m (module_type 0 "" mt "") k)
          (fun () ->
             sprintf "%smodule %s :\n%s\n%s" b m
               (module_type (ind + 2) (tab (ind + 2)) mt "") (tab ind ^ k))
(*
  | <:sig_item< module type $m$ = $mt$ >> ->
      fun curr next ind b k ->
        sprint_indent_unindent ind 2
          (fun ind -> sprintf "%smodule type %s =" b m)
          (fun ind b _ -> module_type ind b mt "")
          (fun ind b _ -> sprintf "%s%s" b k)
  | <:sig_item< open $i$ >> ->
      fun curr next ind b k -> mod_ident ind (sprintf "%sopen " b) i k
*)
  | <:sig_item< type $list:tdl$ >> ->
      fun curr next ind b k ->
        vlist2 type_decl (and_before type_decl) ind (sprintf "%stype " b) tdl
          k
  | <:sig_item< value $s$ : $t$ >> ->
      fun curr next ind b k ->
        horiz_vertic
          (fun () ->
             sprintf "%svalue %s : %s%s" b (var_escaped 0 "" s "")
               (ctyp 0 "" t "") k)
          (fun () ->
             let s1 = sprintf "%svalue %s :" b (var_escaped 0 "" s "") in
             let s2 = ctyp (ind + 2) (tab (ind + 2)) t k in
             sprintf "%s\n%s" s1 s2)
  | z ->
      fun curr next ind b k -> not_impl "sig_item" ind b z k ]
;

value module_expr_top =
  extfun Extfun.empty with
  [ <:module_expr< functor ($s$ : $mt$) -> $me$ >> ->
      fun curr next ind b k ->
        horiz_vertic
          (fun () ->
             sprintf "%sfunctor (%s: %s) -> %s%s" b s (module_type 0 "" mt "")
               (module_expr 0 "" me "") k)
          (fun () ->
             let s1 =
               horiz_vertic
                 (fun () ->
                    sprintf "%sfunctor (%s: %s) ->" b s
                      (module_type 0 "" mt ""))
                 (fun () -> not_impl "functor vertic" ind b 0 "")
             in
             let s2 = module_expr (ind + 2) (tab (ind + 2)) me k in
             sprintf "%s\n%s" s1 s2)
  | <:module_expr< struct $list:sil$ end >> ->
      fun curr next ind b k ->
        horiz_vertic
          (fun () ->
             sprintf "%sstruct%s%s%send%s" b " "
               (hlist (comma_after str_item) 0 "" sil "")
               " " k)
          (fun () ->
             sprintf "%sstruct%s%s%send%s" b "\n"
               (vlist (comma_after str_item) (ind + 2) (tab (ind + 2)) sil "")
               ("\n" ^ tab ind) k)
  | z ->
      fun curr next ind b k -> next ind b z k ]
;

value module_expr_apply =
  extfun Extfun.empty with
  [ <:module_expr< $x$ $y$ >> as z ->
      fun curr next ind b k ->
        let unfold =
          fun
          [ <:module_expr< $x$ $y$ >> -> Some (x, "", y)
          | e -> None ]
        in
        left_operator ind 2 unfold next b z k
  | z ->
      fun curr next ind b k -> next ind b z k ]
;

value module_expr_dot =
  extfun Extfun.empty with
  [ <:module_expr< $x$ . $y$ >> ->
      fun curr next ind b k -> curr ind (curr ind b x ".") y k
  | z -> fun curr next ind b k -> next ind b z k ]
;

value module_expr_simple =
  extfun Extfun.empty with
  [ <:module_expr< $uid:s$ >> ->
      fun curr next ind b k -> sprintf "%s%s%s" b s k
  | <:module_expr< ($me$ : $mt$) >> ->
      fun curr next ind b k ->
        horiz_vertic
          (fun () ->
             sprintf "%s(%s : %s)%s" b (module_expr 0 "" me "")
               (module_type 0 "" mt "") k)
          (fun () ->
             let s1 = module_expr (ind + 1) (sprintf "%s(" b) me " :" in
             let s2 =
               module_type (ind + 1) (tab (ind + 1)) mt (sprintf ")%s" k)
             in
             sprintf "%s\n%s" s1 s2)
  | <:module_expr< struct $list:_$ end >> as z ->
      fun curr next ind b k ->
        module_expr (ind + 1) (sprintf "%s(" b) z (sprintf ")%s" k)
  | z ->
      fun curr next ind b k -> not_impl "module_expr" ind b z k ]
;

(*
value with_constraint ind b wc k =
  match wc with
  [ <:with_constr< type $sl$ $list:tpl$ = $t$ >> ->
      let b =
        let k = type_params ind "" tpl " = " in
        mod_ident ind (sprintf "%swith type " b) sl k
      in
      ctyp ind b t k
  | <:with_constr< module $sl$ = $me$ >> ->
      module_expr ind (mod_ident ind (sprintf "%swith module " b) sl " = ")
        me k ]
;
*)

value module_type_top =
  extfun Extfun.empty with
  [
(*
    <:module_type< functor ($s$ : $mt1$) -> $mt2$ >> ->
      fun curr next ind b k ->
        sprint_indent (ind + 2) 0
          (fun ind _ ->
             module_type ind (sprintf "%sfunctor (%s : " b s) mt1 ") ->")
          (fun ind b _ -> module_type ind b mt2 k)
  |
*)
    <:module_type< sig $list:sil$ end >> ->
      fun curr next ind b k ->
        horiz_vertic
          (fun () ->
             sprintf "%ssig%s%s%send%s" b " "
               (hlist (comma_after sig_item) 0 "" sil "")
               " " k)
          (fun () ->
             sprintf "%ssig%s%s%send%s" b "\n"
               (vlist (comma_after sig_item) (ind + 2) (tab (ind + 2)) sil "")
               ("\n" ^ tab ind) k)
(*
  | <:module_type< $mt$ with $list:wcl$ >> ->
      fun curr next ind b k ->
        sprint_indent ind 2 (fun ind _ -> module_type ind b mt "")
          (fun ind b nl -> listws ind with_constraint b b nl wcl k)
*)
  | z ->
      fun curr next ind b k -> next ind b z k ]
;

(*
value module_type_dot =
  extfun Extfun.empty with
  [ <:module_type< $x$ . $y$ >> ->
      fun curr next ind b k -> curr ind (curr ind b x ".") y k
  | z -> fun curr next ind b k -> next ind b z k ]
;
*)

value module_type_simple =
  extfun Extfun.empty with
  [ <:module_type< $uid:s$ >> ->
      fun curr next ind b k -> sprintf "%s%s%s" b s k
  | z -> fun curr next ind b k -> not_impl "module_type" ind b z k ]
;

(* initialization or re-initialization of predefined printers *)

pr_expr.pr_levels :=
  [{pr_label = "top"; pr_rules = expr_top};
   {pr_label = "ass"; pr_rules = expr_assign};
   {pr_label = "bar"; pr_rules = expr_or};
   {pr_label = "amp"; pr_rules = expr_and};
   {pr_label = "less"; pr_rules = expr_less};
   {pr_label = "concat"; pr_rules = expr_concat};
   {pr_label = "add"; pr_rules = expr_add};
(*
   {pr_label = "mul"; pr_rules = expr_mul};
   {pr_label = "pow"; pr_rules = expr_pow};
   {pr_label = "unary"; pr_rules = expr_unary_minus};
*)
   {pr_label = "apply"; pr_rules = expr_apply};
   {pr_label = "dot"; pr_rules = expr_dot};
   {pr_label = "simple"; pr_rules = expr_simple}]
;

pr_patt.pr_levels :=
  [{pr_label = "top"; pr_rules = patt_top};
   {pr_label = "range"; pr_rules = patt_range};
   {pr_label = "apply"; pr_rules = patt_apply};
   {pr_label = "dot"; pr_rules = patt_dot};
   {pr_label = "simple"; pr_rules = patt_simple}]
;

pr_ctyp.pr_levels :=
  [{pr_label = "top"; pr_rules = ctyp_top};
   {pr_label = "arrow"; pr_rules = ctyp_arrow};
   {pr_label = "apply"; pr_rules = ctyp_apply};
   {pr_label = "dot"; pr_rules = ctyp_dot};
   {pr_label = "simple"; pr_rules = ctyp_simple}]
;

pr_str_item.pr_levels := [{pr_label = "top"; pr_rules = str_item_top}];
pr_sig_item.pr_levels := [{pr_label = "top"; pr_rules = sig_item_top}];

pr_module_expr.pr_levels :=
  [{pr_label = "top"; pr_rules = module_expr_top};
   {pr_label = "apply"; pr_rules = module_expr_apply};
   {pr_label = "dot"; pr_rules = module_expr_dot};
   {pr_label = "simple"; pr_rules = module_expr_simple}]
;

pr_module_type.pr_levels :=
  [{pr_label = "top"; pr_rules = module_type_top};
(*
   {pr_label = "dot"; pr_rules = module_type_dot};
*)
   {pr_label = "simple"; pr_rules = module_type_simple}]
;

(* main part *)

value sep = ref None;

value output_string_eval oc s =
  loop 0 where rec loop i =
    if i == String.length s then ()
    else if i == String.length s - 1 then output_char oc s.[i]
    else
      match (s.[i], s.[i + 1]) with
      [ ('\\', 'n') -> do { output_char oc '\n'; loop (i + 2) }
      | (c, _) -> do { output_char oc c; loop (i + 1) } ]
;

value input_source src bp len =
  let len = min (max 0 len) (String.length src) in
  String.sub src bp len
;

value copy_source src oc first bp ep =
  match sep.val with
  [ Some str ->
      if first then ()
      else if ep == String.length src then output_string oc "\n"
      else output_string_eval oc str
  | None ->
      let s = input_source src bp (ep - bp) in
      let s =
        if first then s
        else
          (* generally, what is before the first newline belongs to the
             previous phrase and should have been treated (included, perhaps)
             previously *)
          try
            let i = String.index s '\n' in
            String.sub s i (String.length s - i)
          with
          [ Not_found -> s ]
      in
      output_string oc s ]
;

value copy_to_end src oc first bp =
  let ilen = String.length src in
  if bp < ilen then copy_source src oc first bp ilen
  else output_string oc "\n"
;

value apply_printer f ast = do {
  if Pcaml.input_file.val = "-" then sep.val := Some "\n"
  else do {
    let ic = open_in_bin Pcaml.input_file.val in
    let src =
      loop 0 where rec loop len =
        match try Some (input_char ic) with [ End_of_file -> None ] with
        [ Some c -> loop (Buff.store len c)
        | None -> Buff.get len ]
    in
    file.val := src;
    close_in ic
  };
  let oc = stdout in
  let (first, last_pos) =
    List.fold_left
      (fun (first, last_pos) (si, loc) -> do {
         let bp = Stdpp.first_pos loc in
         let ep = Stdpp.last_pos loc in
         copy_source file.val oc first last_pos bp;
         flush oc;
         output_string oc (f 0 "" si ";");
         (False, ep)
       })
      (True, 0) ast
  in
  copy_to_end file.val oc first last_pos;
  flush oc
};

Pcaml.print_interf.val := apply_printer sig_item;
Pcaml.print_implem.val := apply_printer str_item;

Pcaml.add_option "-l" (Arg.Int (fun x -> Sformat.line_length.val := x))
  "<length> Maximum line length for pretty printing.";

Pcaml.add_option "-sep" (Arg.String (fun x -> sep.val := Some x))
  "<string> Use this string between phrases instead of reading source.";
