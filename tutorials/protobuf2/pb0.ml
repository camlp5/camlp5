(*
#load "pa_extend.cmo";
#load "pa_lexer.cmo";
#load "pa_extprint.cmo";
#load "pa_pprintf.cmo";
*)

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

type stmt = [
  EMPTY of Ploc.t
| SYNTAX of Ploc.t and version_t
| IMPORT of Ploc.t and option visibility_t and string
| PACKAGE of Ploc.t and fullident_t
| OPTION of Ploc.t and option_name_t and constant_t
]
;

value loc_of_stmt = fun [
  EMPTY loc -> loc
| SYNTAX loc _ -> loc
| IMPORT loc _ _ -> loc
| PACKAGE loc _ -> loc
| OPTION loc _ _ -> loc
]
;

value g = Grammar.gcreate (Clexer.gmake ());
value stmt = Grammar.Entry.create g "statement";
value stmts = Grammar.Entry.create g "statements";
value stmts_eoi = Grammar.Entry.create g "statements_eoi";

value loc_strip_comment loc = Ploc.with_comment loc "" ;

EXTEND
  GLOBAL: stmt stmts stmts_eoi ;
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
      | "option" ; n = option_name ; "=" ; c = constant ; ";" ->
        OPTION loc n c
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
END;

value parse_stmt = Grammar.Entry.parse stmt ;
value parse_stmts = Grammar.Entry.parse stmts ;
value parse_stmts_eoi = Grammar.Entry.parse stmts_eoi ;

value pr_stmt = Eprinter.make "stmt";
value pr_stmts = Eprinter.make "stmts";

Eprinter.clear pr_stmt;
Eprinter.clear pr_stmts;

value print_stmt = Eprinter.apply pr_stmt;
value print_commented_stmt pc stmt =
  let loc = loc_of_stmt stmt in
  let comment = Ploc.comment loc in
  let comment = if has_nonws comment then comment else "" in
  let pp = (fun () -> pprintf pc "%s%p" comment print_stmt stmt) in
    Pretty.horiz_vertic pp pp
;

value print_stmts = Eprinter.apply pr_stmts;

value plist f sh pc l =
  let l = List.map (fun s -> (s, "")) l in
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

EXTEND_PRINTER
  pr_stmt:
    [ [ EMPTY _ -> pprintf pc ";"
      | SYNTAX _ PROTO2 -> pprintf pc "syntax = \"proto2\";"
      | SYNTAX _ PROTO3 -> pprintf pc "syntax = \"proto3\";"
      | IMPORT _ v s -> pprintf pc "import%s\"%s\";"
          (match v with [ Some WEAK -> " weak " | Some PUBLIC -> " public " | _ -> " " ]) s
      | PACKAGE _ fid -> pprintf pc "package %p;" fullident fid
      | OPTION _ n c -> pprintf pc "option %p = %p;" option_name n constant c

      ]
    ]
  ;
  pr_stmts:
    [ [ l -> pprintf pc "%p" (plist print_commented_stmt 0) l ]
    ]
  ;
END;

open Printf;

Pretty.line_length.val := 10 ;

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
