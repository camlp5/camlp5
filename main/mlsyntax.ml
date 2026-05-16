(* camlp5r *)
(* mlsyntax.ml *)
(* Copyright (c) INRIA 2007-2017 *)

value symbolchar_or f st ?{lim} s =
  let list =
    ['!'; '$'; '%'; '&'; '*'; '+'; '-'; '.'; '/'; ':'; '<'; '='; '>'; '?';
     '@'; '^'; '|'; '~']
  in
  let lim = match lim with [ None -> String.length s | Some j -> j ] in
  loop st where rec loop i =
    if i == lim then True
    else if List.mem s.[i] list || f s.[i] then loop (i + 1)
    else False
;

value symbolchar = symbolchar_or (fun x -> False) ;

value dotsymbolchar st ?{lim} s = 
  let list = [ '!'; '$'; '%'; '&'; '*'; '+'; '-'; '/'; ':'; '='; '>'; '?';
               '@'; '^'; '|' ]
  in
  let lim = match lim with [ None -> String.length s | Some j -> j ] in
  loop st where rec loop i =
    if i == lim then True
    else if List.mem s.[i] list then loop (i + 1)
    else False
;

value kwdopchar =
  let list = [ '$'; '&'; '*'; '+'; '-'; '/'; '<'; '='; '>';
               '@'; '^'; '|' ]
  in
  fun s i -> 
    if i == String.length s then True
    else List.mem s.[i] list
;

module Original = struct
  
value is_prefixop =
  let list = ['!'; '?'; '~'] in
  let excl = ["!="; "??"; "?!"] in
  fun x ->
    not (List.mem x excl) && String.length x >= 2 &&
    List.mem x.[0] list && symbolchar_or (fun x -> '#' = x)  1 x
;

value is_infixop0_0 =
  let list = ['|'] in
  let excl = ["||"] in
  fun x ->
    not (List.mem x excl) && String.length x >= 2 &&
    List.mem x.[0] list && symbolchar 1 x
;

value is_infixop0_1 =
  let list = ['&'] in
  let excl = ["&&"] in
  fun x ->
    not (List.mem x excl) && String.length x >= 2 &&
    List.mem x.[0] list && symbolchar 1 x
;

value is_infixop0_2 =
  let list = ['='; '<'; '>'; '$'] in
  let excl = ["<-"] in
  fun x ->
    not (List.mem x excl) && (x = "$" || String.length x >= 2) &&
    List.mem x.[0] list && symbolchar 1 x
;

value is_infixop0 s =
   is_infixop0_0 s
|| is_infixop0_1 s
|| is_infixop0_2 s
;

value is_infixop1 =
  let list = ['@'; '^'] in
  fun x ->
    String.length x >= 2 && List.mem x.[0] list &&
    symbolchar 1 x
;

value is_infixop2 =
  let list = ['+'; '-'] in
  fun x ->
    x <> "->" && String.length x >= 2 && List.mem x.[0] list &&
    symbolchar 1 x
;

value is_infixop3 =
  let list = ['*'; '/'; '%'] in
  let excl = ["**"] in
  fun x ->
    not (List.mem x excl) && String.length x >= 2 && List.mem x.[0] list &&
    symbolchar 1 x
;

value is_infixop4 x =
  String.length x >= 3 && x.[0] == '*' && x.[1] == '*' &&
  symbolchar 2 x
;

value is_hashop =
  let list = ['#'] in
  let excl = ["#"] in
  fun x ->
    not (List.mem x excl) && String.length x >= 2 &&
    List.mem x.[0] list && symbolchar_or (fun x -> '#' = x)  1 x
;

value is_operator0 = do {
  let ht = Hashtbl.create 73 in
  let ct = Hashtbl.create 73 in
  List.iter (fun x -> Hashtbl.add ht x True)
    ["asr"; "land"; "lor"; "lsl"; "lsr"; "lxor"; "mod"; "or"];
  List.iter (fun x -> Hashtbl.add ct x True)
    ['!'; '&'; '*'; '+'; '-'; '/'; ':'; '<'; '='; '>'; '@'; '^'; '|'; '~';
     '?'; '%'; '.'; '$'];
  fun x ->
    try Hashtbl.find ht x with
    [ Not_found -> try Hashtbl.find ct x.[0] with _ -> False ]
};

value is_andop s =
  String.length s > 3 &&
  String.sub s 0 3 = "and" &&
  kwdopchar s 3 &&
  dotsymbolchar 4 s
;

value is_letop s =
  String.length s > 3 &&
  String.sub s 0 3 = "let" &&
  kwdopchar s 3 &&
  dotsymbolchar 4 s
;

value is_operator s =
  is_operator0 s || is_hashop s
;

value is_infix_operator op =
  is_operator op && (match op.[0] with [ '!'| '?'| '~' -> False | _ -> True ])
;

value is_dotop s =
  String.length s >= 2 &&
  String.get s 0 = '.' &&
  dotsymbolchar 1 ~{lim=2} s &&
  symbolchar 2 s
;

value is_special_op s = is_operator s || is_letop s || is_andop s || is_dotop s ;

end ;

module Revised = struct
include Original ;

value is_infixop0_2 =
  let list = ['='; '<'; '>'; '$'] in
  let excl = ["<-"] in
  fun x ->
    not (List.mem x excl) && String.length x >= 2 &&
    List.mem x.[0] list && symbolchar 1 x
;

value is_infixop0 s =
   is_infixop0_0 s
|| is_infixop0_1 s
|| is_infixop0_2 s
;

value is_operator0 s = s <> "$" && is_operator s ;

value is_operator s =
  is_operator0 s || is_hashop s
;

value is_infix_operator op =
  is_operator op && (match op.[0] with [ '!'| '?'| '~' -> False | _ -> True ])
;

value is_dotop s =
  String.length s >= 2 &&
  String.get s 0 = '.' &&
  dotsymbolchar 1 ~{lim=2} s &&
  symbolchar 2 s
;

value is_special_op s = is_operator s || is_letop s || is_andop s || is_dotop s ;

end ;

module type PRINTERS = sig
value pr_attribute_body : Eprinter.t MLast.attribute_body;
value pr_expr : Eprinter.t MLast.expr;
value pr_patt : Eprinter.t MLast.patt;
value pr_ctyp : Eprinter.t MLast.ctyp;
value pr_str_item : Eprinter.t MLast.str_item;
value pr_sig_item : Eprinter.t MLast.sig_item;
value pr_longident : Eprinter.t MLast.longid;
value pr_module_expr : Eprinter.t MLast.module_expr;
value pr_module_type : Eprinter.t MLast.module_type;
value pr_class_sig_item : Eprinter.t MLast.class_sig_item;
value pr_class_str_item : Eprinter.t MLast.class_str_item;
value pr_class_type : Eprinter.t MLast.class_type;
value pr_class_expr : Eprinter.t MLast.class_expr;
   (** Some printers, set by [pr_dump.cmo], [pr_o.cmo] and [pr_r.cmo]. *)

value pr_expr_fun_args :
  ref (Extfun.t MLast.expr (list MLast.patt * MLast.expr));
end ;

module type PRINTBASESIG = sig
module Printers : PRINTERS ;
value options : ref (list (string * Arg.spec * string)) ;
value add_option : string -> Arg.spec -> string -> unit ;
value get_options : unit -> list (string * Arg.spec * string) ;
end
;


module PrintBase() : PRINTBASESIG = struct
module Printers = struct
value show_expr e = Format.asprintf "%a" Pp_debug.Pp_MLast.pp_expr e ;
value pr_attribute_body = Eprinter.make "pr_attribute_body";
value pr_expr = Eprinter.make ~{fail=show_expr} "expr";
value pr_patt = Eprinter.make "patt";
value pr_ctyp = Eprinter.make "type";
value pr_str_item = Eprinter.make "str_item";
value pr_sig_item = Eprinter.make "sig_item";
value pr_longident = Eprinter.make "longident";
value pr_module_expr = Eprinter.make "module_expr";
value pr_module_type = Eprinter.make "module_type";
value pr_class_sig_item = Eprinter.make "class_sig_item";
value pr_class_str_item = Eprinter.make "class_str_item";
value pr_class_expr = Eprinter.make "class_expr";
value pr_class_type = Eprinter.make "class_type";
value pr_expr_fun_args = ref Extfun.empty;
end ;
value options = ref [] ;
value add_option k v doc = options.val := [(k,v,doc) :: options.val] ;
value get_options () =
  let l = options.val in
  do {
    options.val := []
  ; l
  }
;
end
;

module type PARSERS = sig

type status = option Ploc.t;

value gram : Grammar.g;
   (** Grammar variable of the OCaml language *)

value attribute_body : Grammar.Entry.e MLast.attribute_body;
value interf : Grammar.Entry.e (list (MLast.sig_item * MLast.loc) * status);
value implem : Grammar.Entry.e (list (MLast.str_item * MLast.loc) * status);
value top_phrase : Grammar.Entry.e (option MLast.str_item);
value use_file : Grammar.Entry.e (list MLast.str_item * bool);
value functor_parameter : Grammar.Entry.e MLast.functor_parameter;
value module_type : Grammar.Entry.e MLast.module_type;
value longident : Grammar.Entry.e MLast.longid;
value longident_lident : Grammar.Entry.e MLast.longid_lident;
value extended_longident : Grammar.Entry.e MLast.longid;
value module_expr : Grammar.Entry.e MLast.module_expr;
value signature : Grammar.Entry.e (MLast.v (list MLast.sig_item));
value structure : Grammar.Entry.e (MLast.v (list MLast.str_item));
value sig_item : Grammar.Entry.e MLast.sig_item;
value str_item : Grammar.Entry.e MLast.str_item;
value expr : Grammar.Entry.e MLast.expr;
value patt : Grammar.Entry.e MLast.patt;
value ipatt : Grammar.Entry.e MLast.patt;
value ctyp : Grammar.Entry.e MLast.ctyp;
value let_binding : Grammar.Entry.e (MLast.patt * MLast.expr * MLast.attributes);
value type_decl : Grammar.Entry.e MLast.type_decl;
value type_extension : Grammar.Entry.e MLast.type_extension;
value extension_constructor : Grammar.Entry.e MLast.extension_constructor;
value match_case :
  Grammar.Entry.e (MLast.patt * MLast.v (option MLast.expr) * MLast.expr);
value constructor_declaration : Grammar.Entry.e MLast.generic_constructor;
value label_declaration :
  Grammar.Entry.e (MLast.loc * string * bool * MLast.ctyp * MLast.attributes);
value with_constr : Grammar.Entry.e MLast.with_constr;
value poly_variant : Grammar.Entry.e MLast.poly_variant;
value class_sig_item : Grammar.Entry.e MLast.class_sig_item;
value class_str_item : Grammar.Entry.e MLast.class_str_item;
value class_expr : Grammar.Entry.e MLast.class_expr;
value class_expr_simple : Grammar.Entry.e MLast.class_expr;
value class_type : Grammar.Entry.e MLast.class_type;
value alg_attribute : Grammar.Entry.e MLast.attribute;
value alg_attributes : Grammar.Entry.e MLast.attributes;
value ext_attributes : Grammar.Entry.e (option (Ploc.t * string) * MLast.attributes_no_anti);
   (** Some entries of the language, set by [pa_o.cmo] and [pa_r.cmo]. *)

open Exparser_types ;

value stream_expr : Grammar.Entry.e (MLast.loc * list sexp_comp);
value stream_parser : Grammar.Entry.e (MLast.loc * spat_parser_ast) ;
value stream_match : Grammar.Entry.e (MLast.loc * MLast.expr * spat_parser_ast) ;
end ;

module type PARSEBASESIG = sig
module Parsers : PARSERS ;
end
;


module ParseBase() : PARSEBASESIG = struct
module Parsers = struct

value gram =
  Grammar.gcreate
    {Plexing.tok_func _ = failwith "no loaded parsing module";
     Plexing.tok_using _ = (); Plexing.tok_removing _ = ();
     Plexing.tok_match = fun []; Plexing.tok_text _ = "";
     Plexing.tok_comm = None; Plexing.kwds = Hashtbl.create 23 }
;

(*
Camlp5 can be parsed with limited or full backtracking:
Grammar.set_algorithm gram Grammar.Functional;
Grammar.set_algorithm gram Grammar.Backtracking;
or without any change in the code, by setting the environment
variable CAMLP5PARAM to f or b.
*)

type status = option Ploc.t;

value attribute_body = Grammar.Entry.create gram "attribute_body";
value interf = Grammar.Entry.create gram "interf";
value implem = Grammar.Entry.create gram "implem";
value top_phrase = Grammar.Entry.create gram "top_phrase";
value use_file = Grammar.Entry.create gram "use_file";
value signature = Grammar.Entry.create gram "signature";
value structure = Grammar.Entry.create gram "structure";
value sig_item = Grammar.Entry.create gram "sig_item";
value str_item = Grammar.Entry.create gram "str_item";
value functor_parameter = Grammar.Entry.create gram "functor_parameter";
value module_type = Grammar.Entry.create gram "module_type";
value longident = Grammar.Entry.create gram "longident";
value longident_lident = Grammar.Entry.create gram "longident_lident";
value extended_longident = Grammar.Entry.create gram "extended_longident";
value module_expr = Grammar.Entry.create gram "module_expr";
value expr = Grammar.Entry.create gram "expr";
value patt = Grammar.Entry.create gram "patt";
value ipatt = Grammar.Entry.create gram "ipatt";
value ctyp = Grammar.Entry.create gram "ctyp";
value let_binding = Grammar.Entry.create gram "let_binding";
value type_decl = Grammar.Entry.create gram "type_declaration";
value type_extension = Grammar.Entry.create gram "type_extension";
value extension_constructor = Grammar.Entry.create gram "extension_constructor";
value match_case = Grammar.Entry.create gram "match_case";
value constructor_declaration =
  Grammar.Entry.create gram "constructor_declaration";
value label_declaration =
  Grammar.Entry.create gram "label_declaration";
value with_constr = Grammar.Entry.create gram "with_constr";
value poly_variant = Grammar.Entry.create gram "poly_variant";

value class_sig_item = Grammar.Entry.create gram "class_sig_item";
value class_str_item = Grammar.Entry.create gram "class_str_item";
value class_type = Grammar.Entry.create gram "class_type";
value class_expr = Grammar.Entry.create gram "class_expr";
value class_expr_simple = Grammar.Entry.create gram "class_expr_simple";

value alg_attribute = Grammar.Entry.create gram "alg_attribute";
value alg_attributes = Grammar.Entry.create gram "alg_attributes";
value ext_attributes = Grammar.Entry.create gram "ext_attributes";

value stream_expr = Grammar.Entry.create gram "stream_expr";
value stream_parser = Grammar.Entry.create gram "stream_parser";
value stream_match = Grammar.Entry.create gram "stream_match";
end ;
end
;
