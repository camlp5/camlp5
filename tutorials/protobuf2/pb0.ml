(* camlp5r *)
(* pb0.ml,v *)

value input_file = ref "" ;
value nonws_re = Pcre.regexp "\\S" ;
value has_nonws s = Pcre.pmatch ~{rex=nonws_re} s;


type choice 'a 'b =
  [ Left of 'a
  | Right of 'b ]
;

type version_t = [ PROTO2 | PROTO3 ] ;
type visibility_t = [ WEAK | PUBLIC ] ;
type fullident_t = list string ;
type option_name_t = ((choice string fullident_t) * option string) ;

type signed 'a = { neg : bool ; it : 'a } ; 
value mksigned bopt v =
  let b = match bopt with [ None -> False | Some b -> b ] in
  { neg = b ; it = v } ;

type constant_t = [
  ConFULLID of Ploc.t and fullident_t
| ConINT of Ploc.t and signed string
| ConFLOAT of Ploc.t and signed string
| ConSTRING of Ploc.t and string
| ConBOOL of Ploc.t and bool
]
;

type label_t = [ REQUIRED | OPTIONAL | REPEATED ] ;
type type_name_t = { root : bool ; fid : fullident_t } ;
type type_t = [ DOUBLE | FLOAT | INT32 | INT64 | UINT32 | UINT64
      | SINT32 | SINT64 | FIXED32 | FIXED64 | SFIXED32 | SFIXED64
      | BOOL | STRING | BYTES | NAMED of type_name_t ] ;
type message_field_t = { mf_label : label_t ; mf_typ : type_t ; mf_name : string ; mf_num : int ; mf_options : list (option_name_t * constant_t) } ;

type int_or_max = [ MAX | NUM of int ] ;
type range_t = (int * option int_or_max) ;

type group_t = { group_label : label_t ; group_name : string ; group_num : int ; group_body : list message_member_t }
and message_member_t = [
  MM_EMPTY of Ploc.t
| MM_OPTION of Ploc.t and (option_name_t * constant_t)
| MM_FIELD of Ploc.t and message_field_t
| MM_GROUP of Ploc.t and group_t
| MM_ONEOF of Ploc.t and string and list oneof_member_t
| MM_MAP of Ploc.t and type_t and type_t and string and int and list (option_name_t * constant_t)
| MM_EXTENSIONS of Ploc.t and list range_t
| MM_RESERVED of Ploc.t and choice (list range_t) (list string)
| MM_MESSAGE of Ploc.t and string and list message_member_t
| MM_ENUM of Ploc.t and string and list enum_member_t
]
and oneof_field_t = { of_type : type_t ; of_name : string ; of_num : int ; of_options : list (option_name_t * constant_t) }
and oneof_member_t = [
  OM_FIELD of Ploc.t and oneof_field_t
| OM_OPTION of Ploc.t and (option_name_t * constant_t)
| OM_EMPTY of Ploc.t
]

and enum_member_t = [
  EM_EMPTY of Ploc.t
| EM_OPTION of Ploc.t and (option_name_t * constant_t)
| EM_FIELD of Ploc.t and string and int and list (option_name_t * constant_t)
]
;

type stmt = [
  EMPTY of Ploc.t
| SYNTAX of Ploc.t and version_t
| IMPORT of Ploc.t and option visibility_t and string
| PACKAGE of Ploc.t and fullident_t
| OPTION of Ploc.t and (option_name_t * constant_t)
| MESSAGE of Ploc.t and string and list message_member_t
| ENUM of Ploc.t and string and list enum_member_t
]
;

value loc_of_member = fun [
  MM_EMPTY loc -> loc
| MM_OPTION loc _ -> loc
| MM_FIELD loc _ -> loc
| MM_GROUP loc _ -> loc
| MM_ONEOF loc _ _ -> loc
| MM_MAP loc _ _ _ _ _ -> loc
| MM_EXTENSIONS loc _ -> loc
| MM_RESERVED loc _ -> loc
| MM_MESSAGE loc _ _ -> loc
| MM_ENUM loc _ _ -> loc
]
;

value loc_of_oneof_member = fun [
  OM_FIELD loc _ -> loc
| OM_OPTION loc _ -> loc
| OM_EMPTY loc -> loc
]
;

value loc_of_enum_member = fun [
  EM_EMPTY loc -> loc
| EM_OPTION loc _ -> loc
| EM_FIELD loc _ _ _ -> loc
]
;

value loc_of_stmt = fun [
  EMPTY loc -> loc
| SYNTAX loc _ -> loc
| IMPORT loc _ _ -> loc
| PACKAGE loc _ -> loc
| OPTION loc _ -> loc
| MESSAGE loc _ _ -> loc
| ENUM loc _ _ -> loc
]
;

value g = Grammar.gcreate (Clexer.gmake ());
value member = Grammar.Entry.create g "member";
value stmt = Grammar.Entry.create g "statement";
value stmts = Grammar.Entry.create g "statements";
value stmts_eoi = Grammar.Entry.create g "statements_eoi";

value loc_strip_comment loc = Ploc.with_comment loc "" ;

EXTEND
  GLOBAL: member stmt stmts stmts_eoi ;
  label : [ [ "required" -> REQUIRED | "optional" -> OPTIONAL | "repeated" -> REPEATED | -> REQUIRED ] ] ;
  option_binding : [ [ n = option_name ; "=" ; c = constant -> (n,c) ] ] ;
  options : [ [ "[" ; l = LIST1 option_binding SEP "," ; "]" -> l | -> [] ] ] ;
  keytyp :
    [ [ "double" ->  DOUBLE
      | "float" ->  FLOAT
      | "int32"  ->  INT32
      | "int64"  ->  INT64
      | "uint32"  ->  UINT32
      | "uint64" ->  UINT64
      | "sint32"  ->  SINT32
      | "sint64"  ->  SINT64
      | "fixed32"  ->  FIXED32
      | "fixed64"  ->  FIXED64
      | "sfixed32" ->  SFIXED32
      | "sfixed64" ->  SFIXED64
      | "bool"  ->  BOOL
      | "string"  ->  STRING
    ] ] ;
  typ :
    [ [ t = keytyp -> t
      | "bytes"  ->  BYTES
      | root = [ "." -> True | -> False ] ; fid = fullident -> NAMED { root = root ; fid = fid }
    ] ] ;
  oneof_member:
  [ [ ";" -> OM_EMPTY loc
    | "option" ; b = option_binding ; ";" -> OM_OPTION loc b
    | ty = typ ; n = ident ; "=" ; num = int ; opts = options ; ";" ->
      OM_FIELD loc {of_type = ty ; of_name = n ; of_num = num ; of_options = opts }
  ] ] ;
  enum_member:
  [ [ ";" -> EM_EMPTY loc
    | "option" ; b = option_binding ; ";" -> EM_OPTION loc b
    | n = ident ; "=" ; num = signed_int ; opts = options ; ";" ->
      EM_FIELD loc n num opts
  ] ] ;
  member:
  [ [ ";" -> MM_EMPTY loc
    | "option" ; (n,c) = option_binding ; ";" ->
      MM_OPTION loc (n, c)
    | l = label ; t = typ ; n = ident ; "=" ; num = int ; opts = options ; ";" ->
      MM_FIELD loc { mf_label=l; mf_typ=t; mf_name=n; mf_num=num; mf_options = opts }
    | l = label ; "group" ; gn = UIDENT ; "=" ; num = int ;  "{" ; body = LIST0 member ; "}" ->
      MM_GROUP loc { group_label=l; group_name = gn ; group_num = num ; group_body = body }
    | "oneof" ; n = ident ; "{" ; l = LIST1 oneof_member ; "}" ->
      MM_ONEOF loc n l
    | "map" ; "<" ; keyty = keytyp ; "," ; valty = typ ; ">" ; n = ident ; "=" ; num = int ; opts = options ; ";" ->
      MM_MAP loc keyty valty n num opts
    | "extensions" ; l = LIST1 range SEP "," ; ";" ->
      MM_EXTENSIONS loc l
    | "reserved" ; l = LIST1 range SEP "," ; ";" -> MM_RESERVED loc (Left l)
    | "reserved" ; l = LIST1 ident SEP "," ; ";" -> MM_RESERVED loc (Right l)
    | "message" ; n = ident ; "{" ; l = LIST0 member ; "}" ->
      MM_MESSAGE loc n l
    | "enum" ; n = ident ; "{" ; l = LIST1 enum_member ; "}" ->
      MM_ENUM loc n l
  ] ] ;
  range :
  [ [ n = int -> (n, None)
    | n = int ; "to" ; m = int -> (n, Some (NUM m))
    | n = int ; "to" ; "max" -> (n, Some MAX)
  ] ] ;
  stmt:
    [ [ ";" -> EMPTY loc
      | "syntax" ; "=" ; s = STRING ; ";" ->
        match s with [
          "proto2" -> SYNTAX loc PROTO2
        | "proto3" -> SYNTAX loc PROTO3
        | _ -> Ploc.raise loc (Failure {foo|syntax must be either \"proto2\" or \"proto3\"|foo})
        ]
      | "import"; v = OPT [ "weak" -> WEAK | "public" -> PUBLIC ] ; s = STRING ; ";" ->
        IMPORT loc v s
      | "package"; fid = fullident ; ";" ->
        PACKAGE loc fid
      | "option" ; (n,c) = option_binding ; ";" ->
        OPTION loc (n, c)
      | "message" ; n = ident ; "{" ; l = LIST0 member ; "}" ->
        MESSAGE loc n l
      | "enum" ; n = ident ; "{" ; l = LIST1 enum_member ; "}" ->
        ENUM loc n l
      ]
    ]
  ;
  stmts : [ [ l = LIST1 stmt -> l ] ] ;
  stmts_eoi : [ [ l = stmts ; EOI -> l ] ] ;
  option_name: [ [
    fst = [ id = ident -> Left id | fid = [ "(" ; fid = fullident ; ")" -> fid ] -> Right fid ] ;
    snd = OPT [ "." ; id = ident -> id ] -> (fst, snd)
  ] ];
  constant : [ [
    s = OPT [ "-" -> True | "+" -> False ] ; i = INT -> ConINT loc (mksigned s i)
  | s = OPT [ "-" -> True | "+" -> False ] ; f = FLOAT -> ConFLOAT loc (mksigned s f)
  | s = STRING -> ConSTRING loc s
  | s = "true" -> ConBOOL loc True
  | s = "false" -> ConBOOL loc False
  | fid = fullident -> ConFULLID loc fid
  ] ] ;
  fullident : [ [ fid = LIST1 ident SEP "." -> fid ] ] ;
  ident: [ [ id = LIDENT -> id | id = UIDENT -> id ] ] ;
  int : [ [ n = INT -> int_of_string n ] ] ;
  signed_int : [ [ "-" ; n = INT -> -(int_of_string n) | n = INT -> int_of_string n ] ] ;
END;

value parse_member = Grammar.Entry.parse member ;
value parse_stmt = Grammar.Entry.parse stmt ;
value parse_stmts = Grammar.Entry.parse stmts ;
value parse_stmts_eoi = Grammar.Entry.parse stmts_eoi ;

value pr_member = Eprinter.make "member";
value pr_oneof_member = Eprinter.make "oneof_member";
value pr_enum_member = Eprinter.make "enum_member";
value pr_stmt = Eprinter.make "stmt";
value pr_stmts = Eprinter.make "stmts";

Eprinter.clear pr_member;
Eprinter.clear pr_oneof_member;
Eprinter.clear pr_enum_member;
Eprinter.clear pr_stmt;
Eprinter.clear pr_stmts;

value print_member = Eprinter.apply pr_member;
value print_commented_member pc member =
  let loc = loc_of_member member in
  let comment = Ploc.comment loc in
  let comment = if has_nonws comment then comment else "" in
  let pp = (fun () -> pprintf pc "%s%p" comment print_member member) in
    Pretty.horiz_vertic pp pp
;

value print_oneof_member = Eprinter.apply pr_oneof_member;
value print_commented_oneof_member pc member =
  let loc = loc_of_oneof_member member in
  let comment = Ploc.comment loc in
  let comment = if has_nonws comment then comment else "" in
  let pp = (fun () -> pprintf pc "%s%p" comment print_oneof_member member) in
    Pretty.horiz_vertic pp pp
;

value print_enum_member = Eprinter.apply pr_enum_member;
value print_commented_enum_member pc member =
  let loc = loc_of_enum_member member in
  let comment = Ploc.comment loc in
  let comment = if has_nonws comment then comment else "" in
  let pp = (fun () -> pprintf pc "%s%p" comment print_enum_member member) in
    Pretty.horiz_vertic pp pp
;

value print_stmt = Eprinter.apply pr_stmt;
value print_commented_stmt pc stmt =
  let loc = loc_of_stmt stmt in
  let comment = Ploc.comment loc in
  let comment = if has_nonws comment then comment else "" in
  let pp = (fun () -> pprintf pc "%s%p" comment print_stmt stmt) in
    Pretty.horiz_vertic pp pp
;

value print_stmts = Eprinter.apply pr_stmts;

value plist ?{sep=""} f sh pc l =
  let l = List.map (fun s -> (s, sep)) l in
  pprintf pc "%p" (Prtools.plist f sh) l
;

value fullident pc fid = pprintf pc "%s" (String.concat "." fid) ;
value option_name pc (lhs, rhs) =
  let pp_lhs pc = fun [
    Left id -> pprintf pc "%s" id
  | Right fid -> pprintf pc "(%p)" fullident fid
  ] in
  let pp_rhs pc = fun [
    None -> pprintf pc ""
  | Some id -> pprintf pc ".%s" id
  ] in
  pprintf pc "%p%p" pp_lhs lhs pp_rhs rhs
;

value constant pc = fun [
  ConFULLID _ fid -> fullident pc fid
| ConINT _ {neg=True; it=n} -> pprintf pc "-%s" n
| ConINT _ {neg=False; it=n} -> pprintf pc "%s" n
| ConFLOAT _ {neg=True; it=n} -> pprintf pc "-%s" n
| ConFLOAT _ {neg=False; it=n} -> pprintf pc "%s" n
| ConSTRING _ s -> pprintf pc "\"%s\"" s
| ConBOOL _ True -> pprintf pc "true"
| ConBOOL _ False -> pprintf pc "false"
]
;

value typ pc = fun [
  DOUBLE -> pprintf pc "double"
| FLOAT -> pprintf pc "float"
| INT32  -> pprintf pc "int32"
| INT64  -> pprintf pc "int64"
| UINT32  -> pprintf pc "uint32"
| UINT64 -> pprintf pc "uint64"
| SINT32  -> pprintf pc "sint32"
| SINT64  -> pprintf pc "sint64"
| FIXED32  -> pprintf pc "fixed32"
| FIXED64  -> pprintf pc "fixed64"
| SFIXED32 -> pprintf pc "sfixed32"
| SFIXED64 -> pprintf pc "sfixed64"
| BOOL  -> pprintf pc "bool"
| STRING  -> pprintf pc "string"
| BYTES  -> pprintf pc "bytes"
| NAMED n -> pprintf pc "%s%p" (if n.root then "." else "") fullident n.fid ]
;

value option_binding pc (n,c) =
  pprintf pc "%p = %p" option_name n constant c ;

value options pc l =
  if l = [] then pprintf pc ""
  else pprintf pc "[%p]" (plist ~{sep=","} option_binding 2) l
;

value pp_range pc = fun [
  (n, None) -> pprintf pc "%d" n
| (n, Some (NUM m)) -> pprintf pc "%d to %d" n m
| (n, Some MAX) -> pprintf pc "%d to max" n
]
;
value pp_ident pc id = pprintf pc "%s" id ;

EXTEND_PRINTER
  pr_oneof_member:
    [ [ OM_EMPTY _ -> pprintf pc ";"
      | OM_OPTION _ (n, c) -> pprintf pc "option %p;" option_binding (n,c)
      | OM_FIELD _ f -> pprintf pc "%p %s = %d %p;"
          typ f.of_type f.of_name f.of_num options f.of_options
    ] ] ;
  pr_enum_member:
    [ [ EM_EMPTY _ -> pprintf pc ";"
      | EM_OPTION _ (n, c) -> pprintf pc "option %p;" option_binding (n,c)
      | EM_FIELD _ n num opts -> pprintf pc "%s = %d %p;"
          n num options opts
    ] ] ;
  pr_member:
    [ [ MM_EMPTY _ -> pprintf pc ";"
      | MM_OPTION _ (n, c) -> pprintf pc "option %p;" option_binding (n,c)
      | MM_FIELD _ f ->
        pprintf pc "%s %p %s = %d%p;"
          (match f.mf_label with [ REQUIRED -> "required" | OPTIONAL -> "optional" | REPEATED -> "repeated"])
          typ f.mf_typ
          f.mf_name f.mf_num
          options f.mf_options
      | MM_GROUP _ g ->
        pprintf pc "%s %s = %d @[<2>{\n%p\n}@]"
          (match g.group_label with [ REQUIRED -> "required" | OPTIONAL -> "optional" | REPEATED -> "repeated"])
          g.group_name g.group_num
          (plist ~{sep="\n"} print_commented_member 2) g.group_body
      | MM_ONEOF _ n l ->
        pprintf pc "oneof %s @[<2>{@ %p@ }@]" n (plist print_commented_oneof_member 2) l
      | MM_MAP _ keyty valty n num opts ->
        pprintf pc "map<%p,%p>%s = %d%p;" typ keyty typ valty n num options opts
      | MM_EXTENSIONS _ l ->
         pprintf pc "extensions %p;" (plist ~{sep=","} pp_range 2) l
      | MM_RESERVED _ (Left l) -> pprintf pc "reserved %p;" (plist ~{sep=","} pp_range 2) l
      | MM_RESERVED _ (Right l) -> pprintf pc "reserved %p;" (plist ~{sep=","} pp_ident 2) l
      | MM_MESSAGE _ n l -> pprintf pc "message %s @[<2>{\n%p\n}@]"
          n (plist ~{sep="\n"} print_commented_member 2) l
      | MM_ENUM _ n l -> pprintf pc "enum %s @[<2>{@ %p@ }@]"
          n (plist print_commented_enum_member 2) l
    ] ] ;
  pr_stmt:
    [ [ EMPTY _ -> pprintf pc ";"
      | SYNTAX _ PROTO2 -> pprintf pc "syntax = \"proto2\";"
      | SYNTAX _ PROTO3 -> pprintf pc "syntax = \"proto3\";"
      | IMPORT _ v s -> pprintf pc "import%s\"%s\";"
          (match v with [ Some WEAK -> " weak " | Some PUBLIC -> " public " | _ -> " " ]) s
      | PACKAGE _ fid -> pprintf pc "package %p;" fullident fid
      | OPTION _ (n, c) -> pprintf pc "option %p;" option_binding (n,c)
      | MESSAGE _ n l -> pprintf pc "message %s @[<2>{\n%p\n}@]"
          n (plist ~{sep="\n"} print_commented_member 2) l
      | ENUM _ n l -> pprintf pc "enum %s @[<2>{@ %p@ }@]"
          n (plist print_commented_enum_member 2) l
      ]
    ]
  ;
  pr_stmts:
    [ [ l -> pprintf pc "%p" (plist print_commented_stmt 0) l ]
    ]
  ;
END;

open Printf;

(* Pretty.line_length.val := 10 ; *)

if not Sys.interactive.val then
try
    let l = parse_stmts_eoi (Stream.of_channel stdin) in do {
      printf "%s" (pprintf Pprintf.empty_pc "%p" print_stmts l)
    }
with [ Ploc.Exc loc exc ->
    Fmt.(pf stderr "%s%a@.%!" (Ploc.string_of_location loc) exn exc)
  | exc -> Fmt.(pf stderr "%a@.%!" exn exc)
]
else ()
;
