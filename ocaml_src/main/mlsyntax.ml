(* camlp5r *)
(* mlsyntax.ml *)
(* Copyright (c) INRIA 2007-2017 *)

let symbolchar_or f st ?lim s =
  let list =
    ['!'; '$'; '%'; '&'; '*'; '+'; '-'; '.'; '/'; ':'; '<'; '='; '>'; '?';
     '@'; '^'; '|'; '~']
  in
  let lim =
    match lim with
      None -> String.length s
    | Some j -> j
  in
  let rec loop i =
    if i == lim then true
    else if List.mem s.[i] list || f s.[i] then loop (i + 1)
    else false
  in
  loop st
;;

let symbolchar = symbolchar_or (fun x -> false);;

let dotsymbolchar st ?lim s =
  let list =
    ['!'; '$'; '%'; '&'; '*'; '+'; '-'; '/'; ':'; '='; '>'; '?'; '@'; '^';
     '|']
  in
  let lim =
    match lim with
      None -> String.length s
    | Some j -> j
  in
  let rec loop i =
    if i == lim then true
    else if List.mem s.[i] list then loop (i + 1)
    else false
  in
  loop st
;;

let kwdopchar =
  let list = ['$'; '&'; '*'; '+'; '-'; '/'; '<'; '='; '>'; '@'; '^'; '|'] in
  fun s i -> if i == String.length s then true else List.mem s.[i] list
;;

module Original =
  struct
    let is_prefixop =
      let list = ['!'; '?'; '~'] in
      let excl = ["!="; "??"; "?!"] in
      fun x ->
        not (List.mem x excl) && String.length x >= 2 &&
        List.mem x.[0] list && symbolchar_or (fun x -> '#' = x) 1 x
    ;;
    let is_infixop0_0 =
      let list = ['|'] in
      let excl = ["||"] in
      fun x ->
        not (List.mem x excl) && String.length x >= 2 &&
        List.mem x.[0] list && symbolchar 1 x
    ;;
    let is_infixop0_1 =
      let list = ['&'] in
      let excl = ["&&"] in
      fun x ->
        not (List.mem x excl) && String.length x >= 2 &&
        List.mem x.[0] list && symbolchar 1 x
    ;;
    let is_infixop0_2 =
      let list = ['='; '<'; '>'; '$'] in
      let excl = ["<-"] in
      fun x ->
        not (List.mem x excl) && (x = "$" || String.length x >= 2) &&
        List.mem x.[0] list && symbolchar 1 x
    ;;
    let is_infixop0 s =
      is_infixop0_0 s || is_infixop0_1 s || is_infixop0_2 s
    ;;
    let is_infixop1 =
      let list = ['@'; '^'] in
      fun x -> String.length x >= 2 && List.mem x.[0] list && symbolchar 1 x
    ;;
    let is_infixop2 =
      let list = ['+'; '-'] in
      fun x ->
        x <> "->" && String.length x >= 2 && List.mem x.[0] list &&
        symbolchar 1 x
    ;;
    let is_infixop3 =
      let list = ['*'; '/'; '%'] in
      let excl = ["**"] in
      fun x ->
        not (List.mem x excl) && String.length x >= 2 &&
        List.mem x.[0] list && symbolchar 1 x
    ;;
    let is_infixop4 x =
      String.length x >= 3 && x.[0] == '*' && x.[1] == '*' && symbolchar 2 x
    ;;
    let is_hashop =
      let list = ['#'] in
      let excl = ["#"] in
      fun x ->
        not (List.mem x excl) && String.length x >= 2 &&
        List.mem x.[0] list && symbolchar_or (fun x -> '#' = x) 1 x
    ;;
    let is_operator0 =
      let ht = Hashtbl.create 73 in
      let ct = Hashtbl.create 73 in
      List.iter (fun x -> Hashtbl.add ht x true)
        ["asr"; "land"; "lor"; "lsl"; "lsr"; "lxor"; "mod"; "or"];
      List.iter (fun x -> Hashtbl.add ct x true)
        ['!'; '&'; '*'; '+'; '-'; '/'; ':'; '<'; '='; '>'; '@'; '^'; '|'; '~';
         '?'; '%'; '.'; '$'];
      fun x ->
        try Hashtbl.find ht x with
          Not_found -> try Hashtbl.find ct x.[0] with _ -> false
    ;;
    let is_andop s =
      String.length s > 3 && String.sub s 0 3 = "and" && kwdopchar s 3 &&
      dotsymbolchar 4 s
    ;;
    let is_letop s =
      String.length s > 3 && String.sub s 0 3 = "let" && kwdopchar s 3 &&
      dotsymbolchar 4 s
    ;;
    let is_operator s = is_operator0 s || is_hashop s;;
    let is_infix_operator op =
      is_operator op &&
      (match op.[0] with
         '!' | '?' | '~' -> false
       | _ -> true)
    ;;
    let is_dotop s =
      String.length s >= 2 && String.get s 0 = '.' &&
      dotsymbolchar 1 ~lim:2 s && symbolchar 2 s
    ;;
    let is_special_op s =
      is_operator s || is_letop s || is_andop s || is_dotop s
    ;;
  end
;;

module Revised =
  struct
    include Original;;
    let start_with s s_ini =
      let len = String.length s_ini in
      String.length s >= len && String.sub s 0 len = s_ini
    ;;
    let greek_tab =
      ["α"; "β"; "γ"; "δ"; "ε"; "ζ"; "η"; "θ"; "ι"; "κ"; "λ"; "μ"; "ν"; "ξ";
       "ο"; "π"; "ρ"; "σ"; "τ"; "υ"; "φ"; "χ"; "ψ"; "ω"]
    ;;
    let index_tab = [""; "₁"; "₂"; "₃"; "₄"; "₅"; "₆"; "₇"; "₈"; "₉"];;
    let greek_ascii_equiv s =
      let rec loop i =
        function
          g :: gl ->
            if start_with s g then
              let c1 = Char.chr (Char.code 'a' + i) in
              let glen = String.length g in
              let rest = String.sub s glen (String.length s - glen) in
              let rec loop i =
                function
                  k :: kl ->
                    if rest = k then
                      let s2 = if i = 0 then "" else string_of_int i in
                      String.make 1 c1 ^ s2
                    else loop (i + 1) kl
                | [] -> String.make 1 c1 ^ rest
              in
              loop 0 index_tab
            else loop (i + 1) gl
        | [] -> s
      in
      loop 0 greek_tab
    ;;
    let is_infixop0_2 =
      let list = ['='; '<'; '>'; '$'] in
      let excl = ["<-"] in
      fun x ->
        not (List.mem x excl) && String.length x >= 2 &&
        List.mem x.[0] list && symbolchar 1 x
    ;;
    let is_infixop0 s =
      is_infixop0_0 s || is_infixop0_1 s || is_infixop0_2 s
    ;;
    let is_operator0 s = s <> "$" && is_operator s;;
    let is_operator s = is_operator0 s || is_hashop s;;
    let is_infix_operator op =
      is_operator op &&
      (match op.[0] with
         '!' | '?' | '~' -> false
       | _ -> true)
    ;;
    let is_dotop s =
      String.length s >= 2 && String.get s 0 = '.' &&
      dotsymbolchar 1 ~lim:2 s && symbolchar 2 s
    ;;
    let is_special_op s =
      is_operator s || is_letop s || is_andop s || is_dotop s
    ;;
  end
;;

module type PRINTERS =
  sig
    val pr_attribute_body : MLast.attribute_body Eprinter.t;;
    val pr_expr : MLast.expr Eprinter.t;;
    val pr_patt : MLast.patt Eprinter.t;;
    val pr_ctyp : MLast.ctyp Eprinter.t;;
    val pr_str_item : MLast.str_item Eprinter.t;;
    val pr_sig_item : MLast.sig_item Eprinter.t;;
    val pr_longident : MLast.longid Eprinter.t;;
    val pr_module_expr : MLast.module_expr Eprinter.t;;
    val pr_module_type : MLast.module_type Eprinter.t;;
    val pr_class_sig_item : MLast.class_sig_item Eprinter.t;;
    val pr_class_str_item : MLast.class_str_item Eprinter.t;;
    val pr_class_type : MLast.class_type Eprinter.t;;
    val pr_class_expr : MLast.class_expr Eprinter.t;;
    val pr_expr_fun_args :
      (MLast.expr, MLast.patt list * MLast.expr) Extfun.t ref;;
  end
;;

module type PRINTBASESIG =
  sig
    module Printers : PRINTERS;;
    val options : (string * Arg.spec * string) list ref;;
    val add_option : string -> Arg.spec -> string -> unit;;
    val get_options : unit -> (string * Arg.spec * string) list;;
  end
;;


module PrintBase () : PRINTBASESIG =
  struct
    module Printers =
      struct
        let show_expr e = Format.asprintf "%a" Pp_debug.Pp_MLast.pp_expr e;;
        let pr_attribute_body = Eprinter.make "pr_attribute_body";;
        let pr_expr = Eprinter.make ~fail:show_expr "expr";;
        let pr_patt = Eprinter.make "patt";;
        let pr_ctyp = Eprinter.make "type";;
        let pr_str_item = Eprinter.make "str_item";;
        let pr_sig_item = Eprinter.make "sig_item";;
        let pr_longident = Eprinter.make "longident";;
        let pr_module_expr = Eprinter.make "module_expr";;
        let pr_module_type = Eprinter.make "module_type";;
        let pr_class_sig_item = Eprinter.make "class_sig_item";;
        let pr_class_str_item = Eprinter.make "class_str_item";;
        let pr_class_expr = Eprinter.make "class_expr";;
        let pr_class_type = Eprinter.make "class_type";;
        let pr_expr_fun_args = ref Extfun.empty;;
      end
    ;;
    let options = ref [];;
    let add_option k v doc = options := (k, v, doc) :: !options;;
    let get_options () = let l = !options in options := []; l;;
  end
;;

type status = Ploc.t option;;

module type PARSERS =
  sig
    val gram : Grammar.g;;
    val attribute_body : MLast.attribute_body Grammar.Entry.e;;
    val interf :
      ((MLast.sig_item * MLast.loc) list * status) Grammar.Entry.e;;
    val implem :
      ((MLast.str_item * MLast.loc) list * status) Grammar.Entry.e;;
    val top_phrase : MLast.str_item option Grammar.Entry.e;;
    val use_file : (MLast.str_item list * bool) Grammar.Entry.e;;
    val functor_parameter : MLast.functor_parameter Grammar.Entry.e;;
    val module_type : MLast.module_type Grammar.Entry.e;;
    val longident : MLast.longid Grammar.Entry.e;;
    val longident_lident : MLast.longid_lident Grammar.Entry.e;;
    val extended_longident : MLast.longid Grammar.Entry.e;;
    val module_expr : MLast.module_expr Grammar.Entry.e;;
    val signature : MLast.sig_item list MLast.v Grammar.Entry.e;;
    val structure : MLast.str_item list MLast.v Grammar.Entry.e;;
    val sig_item : MLast.sig_item Grammar.Entry.e;;
    val str_item : MLast.str_item Grammar.Entry.e;;
    val expr : MLast.expr Grammar.Entry.e;;
    val patt : MLast.patt Grammar.Entry.e;;
    val ipatt : MLast.patt Grammar.Entry.e;;
    val ctyp : MLast.ctyp Grammar.Entry.e;;
    val let_binding :
      (MLast.patt * MLast.expr * MLast.attributes) Grammar.Entry.e;;
    val type_decl : MLast.type_decl Grammar.Entry.e;;
    val type_extension : MLast.type_extension Grammar.Entry.e;;
    val extension_constructor : MLast.extension_constructor Grammar.Entry.e;;
    val match_case :
      (MLast.patt * MLast.expr option MLast.v * MLast.expr) Grammar.Entry.e;;
    val constructor_declaration : MLast.generic_constructor Grammar.Entry.e;;
    val label_declaration :
      (MLast.loc * string * bool * MLast.ctyp * MLast.attributes)
        Grammar.Entry.e;;
    val with_constr : MLast.with_constr Grammar.Entry.e;;
    val poly_variant : MLast.poly_variant Grammar.Entry.e;;
    val class_sig_item : MLast.class_sig_item Grammar.Entry.e;;
    val class_str_item : MLast.class_str_item Grammar.Entry.e;;
    val class_expr : MLast.class_expr Grammar.Entry.e;;
    val class_expr_simple : MLast.class_expr Grammar.Entry.e;;
    val class_type : MLast.class_type Grammar.Entry.e;;
    val alg_attribute : MLast.attribute Grammar.Entry.e;;
    val alg_attributes : MLast.attributes Grammar.Entry.e;;
    val ext_attributes :
      ((Ploc.t * string) option * MLast.attributes_no_anti) Grammar.Entry.e;;
    open Exparser_types;;
    val stream_expr : (MLast.loc * sexp_comp list) Grammar.Entry.e;;
    val stream_parser : (MLast.loc * spat_parser_ast) Grammar.Entry.e;;
    val stream_match :
      (MLast.loc * MLast.expr * spat_parser_ast) Grammar.Entry.e;;
  end
;;

type directive_fun = MLast.expr option -> unit;;

module type PARSEBASESIG =
  sig
    module Lexer : Plexer.LEXER;;
    module Parsers : PARSERS;;
    val input_file : string ref;;
    val options : (string * Arg.spec * string) list ref;;
    val add_option : string -> Arg.spec -> string -> unit;;
    val get_options : unit -> (string * Arg.spec * string) list;;
    val directives : (string * directive_fun) list ref;;
    val add_directive : string -> directive_fun -> unit;;
    val get_directives : unit -> (string * directive_fun) list;;
  end
;;


module ParseBase (Lexer : Plexer.LEXER) : PARSEBASESIG =
  struct
    module Lexer = Lexer;;
    module Parsers =
      struct
        let gram =
          Grammar.gcreate
            {Plexing.tok_func =
              (fun _ -> failwith "no loaded parsing module");
             Plexing.tok_using = (fun _ -> ());
             Plexing.tok_removing = (fun _ -> ());
             Plexing.tok_match =
               (fun _ -> raise (Match_failure ("mlsyntax.ml", 375, 25)));
             Plexing.tok_text = (fun _ -> ""); Plexing.tok_comm = None;
             Plexing.kwds = Hashtbl.create 23}
        ;;
        type status = Ploc.t option;;
        let attribute_body = Grammar.Entry.create gram "attribute_body";;
        let interf = Grammar.Entry.create gram "interf";;
        let implem = Grammar.Entry.create gram "implem";;
        let top_phrase = Grammar.Entry.create gram "top_phrase";;
        let use_file = Grammar.Entry.create gram "use_file";;
        let signature = Grammar.Entry.create gram "signature";;
        let structure = Grammar.Entry.create gram "structure";;
        let sig_item = Grammar.Entry.create gram "sig_item";;
        let str_item = Grammar.Entry.create gram "str_item";;
        let functor_parameter =
          Grammar.Entry.create gram "functor_parameter"
        ;;
        let module_type = Grammar.Entry.create gram "module_type";;
        let longident = Grammar.Entry.create gram "longident";;
        let longident_lident = Grammar.Entry.create gram "longident_lident";;
        let extended_longident =
          Grammar.Entry.create gram "extended_longident"
        ;;
        let module_expr = Grammar.Entry.create gram "module_expr";;
        let expr = Grammar.Entry.create gram "expr";;
        let patt = Grammar.Entry.create gram "patt";;
        let ipatt = Grammar.Entry.create gram "ipatt";;
        let ctyp = Grammar.Entry.create gram "ctyp";;
        let let_binding = Grammar.Entry.create gram "let_binding";;
        let type_decl = Grammar.Entry.create gram "type_declaration";;
        let type_extension = Grammar.Entry.create gram "type_extension";;
        let extension_constructor =
          Grammar.Entry.create gram "extension_constructor"
        ;;
        let match_case = Grammar.Entry.create gram "match_case";;
        let constructor_declaration =
          Grammar.Entry.create gram "constructor_declaration"
        ;;
        let label_declaration =
          Grammar.Entry.create gram "label_declaration"
        ;;
        let with_constr = Grammar.Entry.create gram "with_constr";;
        let poly_variant = Grammar.Entry.create gram "poly_variant";;
        let class_sig_item = Grammar.Entry.create gram "class_sig_item";;
        let class_str_item = Grammar.Entry.create gram "class_str_item";;
        let class_type = Grammar.Entry.create gram "class_type";;
        let class_expr = Grammar.Entry.create gram "class_expr";;
        let class_expr_simple =
          Grammar.Entry.create gram "class_expr_simple"
        ;;
        let alg_attribute = Grammar.Entry.create gram "alg_attribute";;
        let alg_attributes = Grammar.Entry.create gram "alg_attributes";;
        let ext_attributes = Grammar.Entry.create gram "ext_attributes";;
        let stream_expr = Grammar.Entry.create gram "stream_expr";;
        let stream_parser = Grammar.Entry.create gram "stream_parser";;
        let stream_match = Grammar.Entry.create gram "stream_match";;
      end
    ;;
    let input_file = Plexing.input_file;;
    let options = ref [];;
    let add_option k v doc = options := (k, v, doc) :: !options;;
    let get_options () = let l = !options in options := []; l;;
    let directives = ref ([] : (string * directive_fun) list);;
    let add_directive k v = directives := (k, v) :: !directives;;
    let get_directives () = let l = !directives in directives := []; l;;
  end
;;
