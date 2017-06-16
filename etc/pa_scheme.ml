; camlp5 ./pa_schemer.cmo pa_extend.cmo q_MLast.cmo pr_dump.cmo
; pa_scheme.ml,v
; Copyright (c) INRIA 2007-2017

(open Pcaml)
(open Exparser)
(open Versdep)

(type (choice 'a 'b)
 (sum
  (Left 'a)
  (Right 'b)))

; Buffer

(module Buff
 (struct
  (define buff (ref (string_create 80)))
  (define (store len x)
   (begin
    (if (>= len (string_length buff.val))
     (:= buff.val
        (string_cat buff.val (string_create (string_length buff.val)))))
    (string_set buff.val len x)
    (succ len)))
  (define (mstore len s)
   (letrec
    (((add_rec len i)
      (if (== i (String.length s)) len (add_rec (store len s.[i]) (succ i)))))
    (add_rec len 0)))
  (define (get len) (bytes_to_string (string_sub buff.val 0 len)))))

(define (rename_id s)
 (if (&& (> (String.length s) 0) (= s.[(- (String.length s) 1)] '#'))
  (String.sub s 0 (- (String.length s) 1))
  (Pcaml.rename_id.val s)))

; Lexer

(definerec (skip_to_eol len)
 (parser
  (((` (as (or '\n' '\r') c))) (Buff.store len c))
  (((` c) (a (skip_to_eol (Buff.store len c))) !) a)))

(define no_ident ['(' ')' '[' ']' '{' '}' ' ' '\t' '\n' '\r' ';' '.'])

(definerec (ident len)
 (parser
  (((` x (not (List.mem x no_ident))) (a (ident (Buff.store len x))) !) a)
  (() len)))

(define (identifier kwt s)
 (let
  ((con
    (try (begin (: (Hashtbl.find kwt s) unit) "")
     (Not_found (match s.[0] ((range 'A' 'Z') "UIDENT") (_ "LIDENT"))))))
  (values con s)))

(definerec (string len)
 (parser
  (((` '"')) (Buff.get len))
  (((` '\\') (` c) (a (string (Buff.store (Buff.store len '\\') c))) !) a)
  (((` x) (a (string (Buff.store len x))) !) a)))

(definerec (end_exponent_part_under len)
 (parser
  (((` (as (range '0' '9') c))
    (a (end_exponent_part_under (Buff.store len c))) !)
   a)
  (() (values "FLOAT" (Buff.get len)))))

(define (end_exponent_part len)
 (parser
  (((` (as (range '0' '9') c))
    (a (end_exponent_part_under (Buff.store len c))) !)
   a)
  (() (raise (Stream.Error "ill-formed floating-point constant")))))

(define (exponent_part len)
 (parser
  (((` (as (or '+' '-') c)) (a (end_exponent_part (Buff.store len c))) !) a)
  (((a (end_exponent_part len))) a)))

(definerec (decimal_part len)
 (parser
  (((` (as (range '0' '9') c)) (a (decimal_part (Buff.store len c))) !) a)
  (((` (or 'e' 'E')) (a (exponent_part (Buff.store len 'E'))) !) a)
  (() (values "FLOAT" (Buff.get len)))))

(definerec (number len)
 (parser
  (((` (as (range '0' '9') c)) (a (number (Buff.store len c))) !) a)
  (((` '.') (a (decimal_part (Buff.store len '.'))) !) a)
  (((` (or 'e' 'E')) (a (exponent_part (Buff.store len 'E'))) !) a)
  (((` 'l')) (values "INT_l" (Buff.get len)))
  (((` 'L')) (values "INT_L" (Buff.get len)))
  (((` 'n')) (values "INT_n" (Buff.get len)))
  (() (values "INT" (Buff.get len)))))

(define binary (parser (((` (as (range '0' '1') c))) c)))

(define octal (parser (((` (as (range '0' '7') c))) c)))

(define hexa
 (parser
  (((` (as (or (range '0' '9') (range 'a' 'f') (range 'A' 'F')) c))) c)))

(definerec (digits_under kind len)
 (parser
  (((d kind) (a (digits_under kind (Buff.store len d))) !) a)
  (((` '_') (a (digits_under kind (Buff.store len '_'))) !) a)
  (((` 'l')) (values "INT_l" (Buff.get len)))
  (((` 'L')) (values "INT_L" (Buff.get len)))
  (((` 'n')) (values "INT_n" (Buff.get len)))
  (() (values "INT" (Buff.get len)))))

(define (digits kind bp len)
 (parser
  (((d kind) (a (digits_under kind (Buff.store len d)))) a)
  (() ep
   (Ploc.raise (Ploc.make_unlined (values bp ep))
    (Failure "ill-formed integer constant")))))

(define (base_number kwt bp len)
 (parser
  (((` (or 'b' 'B')) (a (digits binary bp (Buff.store len 'b'))) !) a)
  (((` (or 'o' 'O')) (a (digits octal bp (Buff.store len 'o'))) !) a)
  (((` (or 'x' 'X')) (a (digits hexa bp (Buff.store len 'x'))) !) a)
  (((len (ident (Buff.store 0 '#')))) (identifier kwt (Buff.get len)))))

(definerec (operator len)
 (parser
  (((` '.')) (Buff.store len '.'))
  (() len)))

(define (char_or_quote_id x)
 (parser
  (((` ''')) (values "CHAR" (String.make 1 x)))
  ((s) ep
   (if (List.mem x no_ident)
    (Ploc.raise (Ploc.make_unlined (values (- ep 2) (- ep 1)))
     (Stream.Error "bad quote"))
    (let*
     ((len (Buff.store (Buff.store 0 ''') x)) (s (Buff.get (ident len s))))
     (values "LIDENT" s))))))

(definerec (char len)
 (parser
  (((` ''')) len)
  (((` x) (a (char (Buff.store len x))) !) a)))

(define quote
 (parser
  (((` '\\') (` c) (len (char (Buff.store (Buff.store 0 '\\') c))))
   (values "CHAR" (Buff.get len)))
  (((` x) (a (char_or_quote_id x)) !) a)))

(definerec (antiquot_rest bp len)
 (parser
  (((` '$')) len)
  (((` x) (a (antiquot_rest bp (Buff.store len x)))) a)
  (() ep
   (Ploc.raise (Ploc.make_unlined (values bp ep))
    (Failure "antiquotation not terminated")))))

(define (antiloc d1 d2 s) (Printf.sprintf "%d,%d:%s" d1 d2 s))

(definerec (antiquot_loc bp len)
 (parser
  (((` '$')) ep (antiloc bp ep (^ ":" (Buff.get len))))
  (((` (as (or (range 'a' 'z') (range 'A' 'Z') (range '0' '9') '_') c))
    (a (antiquot_loc bp (Buff.store len c))))
   a)
  (((` ':') (len (antiquot_rest bp (Buff.store len ':')))) ep
   (antiloc bp ep (Buff.get len)))
  (((` c) (len (antiquot_rest bp (Buff.store len c)))) ep
   (antiloc bp ep (^ ":" (Buff.get len))))
  (() ep
   (Ploc.raise (Ploc.make_unlined (values bp ep))
    (Failure "antiquotation not terminated")))))

(definerec*
 ((next_token_after_spaces kwt)
  (parser bp
   (((` '(')) (values (values "" "(") (values bp (+ bp 1))))
   (((` ')')) (values (values "" ")") (values bp (+ bp 1))))
   (((` '[')) (values (values "" "[") (values bp (+ bp 1))))
   (((` ']')) (values (values "" "]") (values bp (+ bp 1))))
   (((` '{')) (values (values "" "{") (values bp (+ bp 1))))
   (((` '}')) (values (values "" "}") (values bp (+ bp 1))))
   (((` '.')) (values (values "DOT" "") (values bp (+ bp 1))))
   (((` '"') (s (string 0))) ep (values (values "STRING" s) (values bp ep)))
   (((` ''') (tok quote)) ep (values tok (values bp ep)))
   (((` '<') (tok (less kwt))) ep (values tok (values bp ep)))
   (((` '-') (tok (minus bp kwt))) ep (values tok (values bp ep)))
   (((` '#') (tok (sharp bp kwt))) ep (values tok (values bp ep)))
   (((` (as (range '0' '9') c)) (tok (number (Buff.store 0 c)))) ep
    (values tok (values bp ep)))
   (((` (as (or '+' '*' '/' '~') c)) (len (ident (Buff.store 0 c)))
     (len (operator len))) ep
    (values (identifier kwt (Buff.get len)) (values bp ep)))
   (((` '$') (tok (dollar bp kwt))) ep (values tok (values bp ep)))
   (((` c) (len (ident (Buff.store 0 c)))) ep
    (values (identifier kwt (Buff.get len)) (values bp ep)))
   (() (values (values "EOI" "") (values bp (+ bp 1))))))
 ((dollar bp kwt strm)
  (if Plexer.force_antiquot_loc.val
   (values "ANTIQUOT_LOC" (antiquot_loc bp 0 strm))
   (match_with_parser strm
    (((len (ident (Buff.store 0 '$')))) (identifier kwt (Buff.get len))))))
 ((sharp bp kwt)
  (parser
   (((` '(')) (values "" "#("))
   (((a (base_number kwt bp (Buff.store 0 '0')))) a)))
 ((minus bp kwt)
  (parser
   (((` '.')) (identifier kwt "-."))
   (((` (as (range '0' '9') c))
     (a (number (Buff.store (Buff.store 0 '-') c))))
    a)
   (((` '#') (a (base_number kwt bp (Buff.mstore 0 "-0")))) a)
   (((len (ident (Buff.store 0 '-')))) (identifier kwt (Buff.get len)))))
 ((less kwt)
  (parser
   (((` ':') (lab (label 0)) (` '<') ? "'<' expected" (q (quotation 0)))
    (values "QUOT" (^ lab (^ ":" q))))
   (((len (ident (Buff.store 0 '<')))) (identifier kwt (Buff.get len)))))
 ((label len)
  (parser
   (((` (as (or (range 'a' 'z') (range 'A' 'Z') '_') c))
     (a (label (Buff.store len c))) !)
    a)
   (() (Buff.get len))))
 ((quotation len)
  (parser
   (((` '>') (a (quotation_greater len)) !) a)
   (((` x) (a (quotation (Buff.store len x))) !) a)
   (() (failwith "quotation not terminated"))))
 ((quotation_greater len)
  (parser
   (((` '>')) (Buff.get len))
   (((a (quotation (Buff.store len '>')))) a))))

(define (get_buff len _) (Buff.get len))

(definerec*
 ((lexer len kwt)
  (parser bp
   (((` (as (or '\t' '\r') c)) (a (lexer (Buff.store len c) kwt)) !) a)
   (((` ' ') (a (after_space (Buff.store len ' ') kwt)) !) a)
   (((` ';') (len (skip_to_eol (Buff.store len ';'))) (a (lexer len kwt)) !)
    a)
   (((` '\n') s)
    (let ((len (Buff.store len '\n')))
     (if Sys.interactive.val
      (values (Buff.get len) (values (values "NL" "") (values bp (+ bp 1))))
      (lexer len kwt s))))
   (((comm (get_buff len)) (a (next_token_after_spaces kwt)))
    (values comm a))))
 ((after_space len kwt)
  (parser
   (((` '.')) ep
    (values (Buff.get len)
     (values (values "SPACEDOT" "") (values (- ep 1) ep))))
   (((a (lexer len kwt))) a))))

(define (lexer_using kwt (values con prm))
 (match con
  ((or "CHAR" "DOT" "EOI" "INT" "INT_l" "INT_L" "INT_n" "FLOAT" "LIDENT" "NL"
    "QUOT" "SPACEDOT" "STRING" "UIDENT")
   ())
  ((or "ANTIQUOT" "ANTIQUOT_LOC") ())
  ("" (try (Hashtbl.find kwt prm) (Not_found (Hashtbl.add kwt prm ()))))
  (_
   (raise
    (Plexing.Error
     (^ "the constructor \"" (^ con "\" is not recognized by Plexer")))))))

(define (lexer_text (values con prm))
 (if (= con "")
  (^ "'" (^ prm "'"))
  (if (= prm "") con (^ con (^ " \"" (^ prm "\""))))))

(define (lexer_gmake ())
 (let
  ((kwt (Hashtbl.create 89))
   ((lexer2 kwt (values s _ _))
    (let (((values comm (values t loc)) (lexer 0 kwt s)))
     (values t (Ploc.make_loc Plexing.input_file.val 1 0 loc comm)))))
  {(Plexing.tok_func (Plexing.lexer_func_of_parser (lexer2 kwt)))
   (Plexing.tok_using (lexer_using kwt)) (Plexing.tok_removing (lambda))
   (Plexing.tok_match Plexing.default_match) (Plexing.tok_text lexer_text)
   (Plexing.tok_comm None)}))

; Building AST

(type sexpr
 (sum
  (Sacc MLast.loc sexpr sexpr)
  (Santi MLast.loc string string)
  (Sarr MLast.loc (MLast.v (list sexpr)))
  (Schar MLast.loc (MLast.v string))
  (Sexpr MLast.loc (list sexpr))
  (Sint MLast.loc (MLast.v string))
  (Sint_l MLast.loc (MLast.v string))
  (Sint_L MLast.loc (MLast.v string))
  (Sint_n MLast.loc (MLast.v string))
  (Sfloat MLast.loc (MLast.v string))
  (Slid MLast.loc string)
  (Slidv MLast.loc (MLast.v string))
  (Slist MLast.loc (list sexpr))
  (Squot MLast.loc string string)
  (Srec MLast.loc (list sexpr))
  (Sstring MLast.loc (MLast.v string))
  (Suid MLast.loc string)
  (Suidv MLast.loc (MLast.v string))))

(define loc_of_sexpr
 (lambda_match
  ((or (Sacc loc _ _) (Santi loc _ _) (Sarr loc _) (Schar loc _) (Sexpr loc _)
    (Sint loc _) (Sint_l loc _) (Sint_L loc _) (Sint_n loc _) (Sfloat loc _)
    (Slid loc _) (Slidv loc _) (Slist loc _) (Squot loc _ _) (Srec loc _)
    (Sstring loc _) (Suid loc _) (Suidv loc _))
   loc)))
(define (error_loc loc err)
 (Ploc.raise loc (Stream.Error (^ err " expected"))))
(define (error se err) (error_loc (loc_of_sexpr se) err))
(:= Pcaml.sync.val (lambda _ ()))

(define strm_n "strm__")
(define (peek_fun loc) <:expr< Stream.peek >>)
(define (junk_fun loc) <:expr< Stream.junk >>)

(define assoc_left_parsed_op_list ["+" "*" "+." "*." "land" "lor" "lxor"])
(define assoc_right_parsed_op_list ["and" "or" "^" "@"])
(define and_by_couple_op_list ["=" "<>" "<" ">" "<=" ">=" "==" "!="])

(define (op_apply loc e1 e2)
 (lambda_match
  ("and" <:expr< $e1$ && $e2$ >>)
  ("or" <:expr< $e1$ || $e2$ >>)
  (x <:expr< $lid:x$ $e1$ $e2$ >>)))

(define string_se
 (lambda_match
  ((Sstring loc <:vala< s >>) s)
  (se (error se "string"))))

(definerec longident_se
 (lambda_match
  ((Sacc _ se1 se2) (@ (longident_se se1) (longident_se se2)))
  ((Suid _ s) [(rename_id s)])
  ((Slid _ s) [(rename_id s)])
  (se (error se "longident"))))

(define (lident_expr loc s)
 (if (&& (> (String.length s) 1) (= s.[0] '`'))
  (let ((s (String.sub s 1 (- (String.length s) 1)))) <:expr< ` $s$ >>)
  <:expr< $lid:(rename_id s)$ >>))

(definerec (anti_list_map f)
 (lambda_match
  ([(Santi _ (or "list" "_list") s)] <:vala< $s$ >>)
  (sel <:vala< (List.map f sel) >>)))

(define anti_longident_se
 (lambda_match
  ((Santi _ (or "list" "_list" "" "_") s) <:vala< $s$ >>)
  (se <:vala< (longident_se se) >>)))

(define anti_lid
 (lambda_match
  ((Slid _ s) (let ((s (rename_id s))) (Some <:vala< s >>)))
  ((Slidv _ s) (Some s))
  ((Santi _ (or "" "_") s) (Some <:vala< $s$ >>))
  (_ None)))

(define anti_lid_or_error
 (lambda_match
  ((Slid _ s) (let ((s (rename_id s))) <:vala< s >>))
  ((Slidv _ s) s)
  ((Santi _ (or "" "_") s) <:vala< $s$ >>)
  (se (error se "lowercase identifier"))))

(define anti_uid_or_error
 (lambda_match
  ((Suid _ s) (let ((s (rename_id s))) <:vala< s >>))
  ((Suidv _ s) s)
  ((Santi _ (or "" "_") s) <:vala< $s$ >>)
  (se (error se "uppercase identifier"))))

(definerec*
 (module_expr_se
  (lambda_match
   ((Sexpr loc [(Slid _ "functor") se1 se2 se3])
    (let*
     ((s (anti_uid_or_error se1))
      (mt (module_type_se se2))
      (me (module_expr_se se3)))
     <:module_expr< functor ($_uid:s$ : $mt$) -> $me$ >>))
   ((Sexpr loc [(Slid _ "struct") . sl])
    (let ((mel (anti_list_map str_item_se sl)))
     <:module_expr< struct $_list:mel$ end >>))
   ((Sexpr loc [se1 se2])
    (let* ((me1 (module_expr_se se1)) (me2 (module_expr_se se2)))
     <:module_expr< $me1$ $me2$ >>))
   ((Sexpr loc [(Slid _ ":") se1 se2])
    (let* ((me (module_expr_se se1)) (mt (module_type_se se2)))
     <:module_expr< ($me$ : $mt$) >>))
   ((Sacc loc se1 se2)
    (let* ((me1 (module_expr_se se1)) (me2 (module_expr_se se2)))
     <:module_expr< $me1$ . $me2$ >>))
   ((Suid loc s) <:module_expr< $uid:(rename_id s)$ >>)
   ((Suidv loc s) <:module_expr< $_uid:s$ >>)
   ((Santi loc "" s) <:module_expr< $xtr:s$ >>)
   (se (error se "module expr"))))
 (module_type_se
  (lambda_match
   ((Sexpr loc [(Slid _ "functor") se1 se2 se3])
    (let*
     ((s (anti_uid_or_error se1))
      (mt1 (module_type_se se2))
      (mt2 (module_type_se se3)))
     <:module_type< functor ($_uid:s$ : $mt1$) -> $mt2$ >>))
   ((Sexpr loc [(Slid _ "sig") . sel])
    (let ((sil (anti_list_map sig_item_se sel)))
     <:module_type< sig $_list:sil$ end >>))
   ((Sexpr loc [(Slid _ "with") se . sel])
    (let* ((mt (module_type_se se)) (wcl (anti_list_map with_constr_se sel)))
     <:module_type< $mt$ with $_list:wcl$ >>))
   ((Sexpr loc [se1 se2])
    (let* ((mt1 (module_type_se se1)) (mt2 (module_type_se se2)))
     <:module_type< $mt1$ $mt2$ >>))
   ((Sacc loc se1 se2)
    (let* ((mt1 (module_type_se se1)) (mt2 (module_type_se se2)))
     <:module_type< $mt1$ . $mt2$ >>))
   ((Slid loc s) <:module_type< $lid:(rename_id s)$ >>)
   ((Slidv loc s) <:module_type< $_lid:s$ >>)
   ((Suid loc s) <:module_type< $uid:(rename_id s)$ >>)
   ((Suidv loc s) <:module_type< $_uid:s$ >>)
   ((Santi loc "" s) <:module_type< $xtr:s$ >>)
   (se (error se "module type"))))
 (with_constr_se
  (lambda_match
   ((Sexpr loc [(Slid _ (as (or "type" "typeprivate") pf)) se1 se2])
    (let*
     (((values tn tp)
       (match se1
        ((Santi _ (or "list" "_list") s)
         (values <:vala< $s$ >> <:vala< [] >>))
        ((Sexpr _ [se . sel])
         (let*
          ((tn (anti_longident_se se)) (tp (anti_list_map type_param_se sel)))
          (values tn tp)))
        (se (values <:vala< (longident_se se) >> <:vala< [] >>))))
      (pf (= pf "typeprivate"))
      (te (ctyp_se se2)))
     <:with_constr< type $_:tn$ $_list:tp$ = $flag:pf$ $te$ >>))
   (se (error se "with constr"))))
 (sig_item_se
  (lambda_match
   ((Sexpr loc [(Slid _ "class") se1 se2])
    (let*
     (((values n tvl)
       (match se1
        ((Slid _ n) (values n []))
        ((Sexpr _ [(Slid _ n) . sel]) (values n (List.map type_param_se sel)))
        (se (error se "class name"))))
      (cd
       {(MLast.ciLoc loc) (MLast.ciVir <:vala< False >>)
        (MLast.ciPrm (values loc <:vala< tvl >>)) (MLast.ciNam <:vala< n >>)
        (MLast.ciExp (class_type_se se2))}))
     <:sig_item< class $list:[cd]$ >>))
   ((Sexpr loc [(Slid _ "exception") se . sel])
    (let* ((c (anti_uid_or_error se)) (tl (anti_list_map ctyp_se sel)))
     <:sig_item< exception $_:c$ of $_list:tl$ >>))
   ((Sexpr loc [(Slid _ "external") se1 se2 . sel])
    (let*
     ((i (anti_lid_or_error se1))
      (t (ctyp_se se2))
      (pd (anti_list_map string_se sel)))
     <:sig_item< external $_lid:i$ : $t$ = $_list:pd$ >>))
   ((Sexpr loc [(Slid _ "include") se])
    (let ((mt (module_type_se se))) <:sig_item< include $mt$ >>))
   ((Sexpr loc [(Slid _ "module") se1 se2])
    (let* ((s (anti_uid_or_error se1)) (mb (module_type_se se2)))
     <:sig_item< module $_uid:s$ : $mb$ >>))
   ((Sexpr loc [(Slid _ (as (or "module*" "modulerec*") rf)) . sel])
    (let ((rf (= rf "modulerec*")) (lmb (anti_list_map sig_module_se sel)))
     <:sig_item< module $flag:rf$ $_list:lmb$ >>))
   ((Sexpr loc [(Slid _ "moduletype") se1 se2])
    (let* ((s (anti_uid_or_error se1)) (mt (module_type_se se2)))
     <:sig_item< module type $_:s$ = $mt$ >>))
   ((Sexpr loc [(Slid _ "open") se])
    (let ((s (anti_longident_se se))) <:sig_item< open $_:s$ >>))
   ((Sexpr loc [(Slid _ "type") . sel])
    (let ((tdl (type_declaration_list_se sel)))
     <:sig_item< type $list:tdl$ >>))
   ((Sexpr loc [(Slid _ "type*") . sel])
    (let ((tdl (anti_list_map type_declaration_se sel)))
     <:sig_item< type $_list:tdl$ >>))
   ((Sexpr loc [(Slid _ "value") se1 se2])
    (let* ((s (anti_lid_or_error se1)) (t (ctyp_se se2)))
     <:sig_item< value $_lid:s$ : $t$ >>))
   ((Sexpr loc [(Slid _ "#") se1])
    (let ((s (anti_lid_or_error se1))) <:sig_item< # $_lid:s$ >>))
   ((Sexpr loc [(Slid _ "#") se1 se2])
    (let ((s (anti_lid_or_error se1)) (e (expr_se se2)))
     <:sig_item< # $_lid:s$ $e$ >>))
   (se (error se "sig item"))))
 ((str_item_se se)
  (match se
   ((Sexpr loc [(Slid _ "class") (Slid _ s) se])
    (let ((ce (class_expr_se se))) <:str_item< class $s$ = $ce$ >>))
   ((Sexpr loc [(Slid _ "class") (Sexpr _ [(Slid _ s) . sel]) se])
    (let ((tpl (List.map type_param_se sel)) (ce (class_expr_se se)))
     <:str_item< class $s$ [ $list:tpl$ ] = $ce$ >>))
   ((Sexpr loc [(Slid _ (as (or "define" "definerec") r)) se . sel])
    (let*
     ((r (= r "definerec"))
      ((values p e) (fun_binding_se se (begin_se loc sel))))
     <:str_item< value $flag:r$ $p$ = $e$ >>))
   ((Sexpr loc [(Slid _ (as (or "define*" "definerec*") rf)) . sel])
    (let* ((rf (= rf "definerec*")) (lbs (anti_list_map let_binding_se sel)))
     <:str_item< value $flag:rf$ $_list:lbs$ >>))
   ((Sexpr loc [(Slid _ "exception") se . sel])
    (let* ((c (anti_uid_or_error se)) (tl (anti_list_map ctyp_se sel)))
     <:str_item< exception $_:c$ of $_list:tl$ >>))
   ((Sexpr loc [(Slid _ "exceptionrebind") se1 se2])
    (let* ((c (anti_uid_or_error se1)) (id (anti_longident_se se2)))
     <:str_item< exception $_uid:c$ = $_:id$ >>))
   ((Sexpr loc [(Slid _ "external") se1 se2 . sel])
    (let*
     ((i (anti_lid_or_error se1))
      (t (ctyp_se se2))
      (pd (anti_list_map string_se sel)))
     <:str_item< external $_lid:i$ : $t$ = $_list:pd$ >>))
   ((Sexpr loc [(Slid _ "include") se])
    (let ((me (module_expr_se se))) <:str_item< include $me$ >>))
   ((Sexpr loc [(Slid _ "module") se1 se2])
    (let (((values i mb) (str_module_se (Sexpr loc [se1 se2]))))
     <:str_item< module $_uid:i$ = $mb$ >>))
   ((Sexpr loc [(Slid _ (as (or "module*" "modulerec*") rf)) . sel])
    (let* ((rf (= rf "modulerec*")) (lmb (anti_list_map str_module_se sel)))
     <:str_item< module $flag:rf$ $_list:lmb$ >>))
   ((Sexpr loc [(Slid _ "moduletype") se1 se2])
    (let* ((s (anti_uid_or_error se1)) (mt (module_type_se se2)))
     <:str_item< module type $_:s$ = $mt$ >>))
   ((Sexpr loc [(Slid _ "open") se])
    (let ((s (anti_longident_se se))) <:str_item< open $_:s$ >>))
   ((Sexpr loc [(Slid _ "type") . sel])
    (let ((tdl (type_declaration_list_se sel)))
     <:str_item< type $list:tdl$ >>))
   ((Sexpr loc [(Slid _ "type*") . sel])
    (let ((tdl (anti_list_map type_declaration_se sel)))
     <:str_item< type $_list:tdl$ >>))
   ((Sexpr loc [(Slid _ "#") se1])
    (match (anti_lid se1)
     ((Some s) <:str_item< # $_lid:s$ >>)
     (None
      (let* ((loc (loc_of_sexpr se)) (e (expr_se se)))
       <:str_item< $exp:e$ >>))))
   ((Sexpr loc [(Slid _ "#") se1 se2])
    (match (anti_lid se1)
     ((Some s) (let ((e (expr_se se2))) <:str_item< # $_lid:s$ $e$ >>))
     (None
      (let* ((loc (loc_of_sexpr se)) (e (expr_se se)))
       <:str_item< $exp:e$ >>))))
   (_
    (let* ((loc (loc_of_sexpr se)) (e (expr_se se)))
     <:str_item< $exp:e$ >>))))
 (str_module_se
  (lambda_match
   ((Sexpr loc [se1 se2])
    (values (anti_uid_or_error se1) (module_expr_se se2)))
   (se (error se "module binding"))))
 (sig_module_se
  (lambda_match
   ((Sexpr loc [se1 se2])
    (values (anti_uid_or_error se1) (module_type_se se2)))
   (se (error se "module binding"))))
 (expr_se
  (lambda_match
   ((Sacc loc se1 se2)
    (let ((e1 (expr_se se1)))
     (match se2
      ((Slist loc [se2]) (let ((e2 (expr_se se2))) <:expr< $e1$ .[ $e2$ ] >>))
      ((Sexpr loc [se2]) (let ((e2 (expr_se se2))) <:expr< $e1$ .( $e2$ ) >>))
      (_ (let ((e2 (expr_se se2))) <:expr< $e1$ . $e2$ >>)))))
   ((Slid loc s) (lident_expr loc s))
   ((Slidv loc s) <:expr< $_lid:s$ >>)
   ((Suid loc s) <:expr< $uid:(rename_id s)$ >>)
   ((Suidv loc s) <:expr< $_uid:s$ >>)
   ((Sint loc s) <:expr< $_int:s$ >>)
   ((Sint_l loc s) <:expr< $_int32:s$ >>)
   ((Sint_L loc s) <:expr< $_int64:s$ >>)
   ((Sint_n loc s) <:expr< $_nativeint:s$ >>)
   ((Sfloat loc s) <:expr< $_flo:s$ >>)
   ((Schar loc s) <:expr< $_chr:s$ >>)
   ((Sstring loc s) <:expr< $_str:s$ >>)
   ((Sexpr loc [(Slid _ "~") se])
    (let ((s (anti_lid_or_error se))) <:expr< ~{$_:s$} >>))
   ((Sexpr loc [(Slid _ "~") se1 se2])
    (let* ((s (anti_lid_or_error se1)) (e (expr_se se2)))
     <:expr< ~{$_:s$ = $e$} >>))
   ((Sexpr loc [(Slid _ "?") se1 se2])
    (let* ((s (anti_lid_or_error se1)) (e (expr_se se2)))
     <:expr< ?{$_:s$ = $e$} >>))
   ((Sexpr loc [(Slid _ "?") se])
    (let ((s (anti_lid_or_error se))) <:expr< ?{$_:s$} >>))
   ((Sexpr loc []) <:expr< () >>)
   ((when (Sexpr loc [(Slid _ s) e1 . (as [_ . _] sel)])
     (List.mem s assoc_left_parsed_op_list))
    (letrec
     (((loop e1)
       (lambda_match
        ([] e1)
        ([e2 . el] (loop (op_apply loc e1 e2 s) el)))))
     (loop (expr_se e1) (List.map expr_se sel))))
   ((when (Sexpr loc [(Slid _ s) . (as [_ _ . _] sel)])
     (List.mem s assoc_right_parsed_op_list))
    (letrec
     ((loop
       (lambda_match
        ([] (assert False))
        ([e1] e1)
        ([e1 . el] (let ((e2 (loop el))) (op_apply loc e1 e2 s))))))
     (loop (List.map expr_se sel))))
   ((when (Sexpr loc [(Slid _ s) . (as [_ _ . _] sel)])
     (List.mem s and_by_couple_op_list))
    (letrec
     ((loop
       (lambda_match
        ((or [] [_]) (assert False))
        ([e1 e2] <:expr< $lid:s$ $e1$ $e2$ >>)
        ([e1 . (as [e2 _ . _] el)]
         (let* ((a1 (op_apply loc e1 e2 s)) (a2 (loop el)))
          <:expr< $a1$ && $a2$ >>)))))
     (loop (List.map expr_se sel))))
   ((Sexpr loc [(Slid _ "-") se]) (let ((e (expr_se se))) <:expr< - $e$ >>))
   ((Sexpr loc [(Slid _ "-.") se]) (let ((e (expr_se se))) <:expr< -. $e$ >>))
   ((Sexpr loc [(Slid _ "if") se se1])
    (let* ((e (expr_se se)) (e1 (expr_se se1)))
     <:expr< if $e$ then $e1$ else () >>))
   ((Sexpr loc [(Slid _ "if") se se1 se2])
    (let* ((e (expr_se se)) (e1 (expr_se se1)) (e2 (expr_se se2)))
     <:expr< if $e$ then $e1$ else $e2$ >>))
   ((Sexpr loc [(Slid _ "cond") . sel])
    (letrec
     ((loop
       (lambda_match
        ([(Sexpr loc [(Slid _ "else") . sel])] (begin_se loc sel))
        ([(Sexpr loc [se1 . sel1]) . sel]
         (let* ((e1 (expr_se se1)) (e2 (begin_se loc sel1)) (e3 (loop sel)))
          <:expr< if $e1$ then $e2$ else $e3$ >>))
        ([] <:expr< () >>)
        ([se . _] (error se "cond clause")))))
     (loop sel)))
   ((Sexpr loc [(Slid _ "while") se . sel])
    (let* ((e (expr_se se)) (el (anti_list_map expr_se sel)))
     <:expr< while $e$ do { $_list:el$ } >>))
   ((Sexpr loc [(Slid _ (as (or "for" "fordown") d)) sei se1 se2 . sel])
    (let*
     ((i (anti_lid_or_error sei))
      (e1 (expr_se se1))
      (e2 (expr_se se2))
      (dir (= d "for"))
      (el (anti_list_map expr_se sel)))
     <:expr< for $_lid:i$ = $e1$ $to:dir$ $e2$ do { $_list:el$ } >>))
   ((Sexpr loc [(Slid loc1 "lambda")]) <:expr< fun [] >>)
   ((Sexpr loc [(Slid loc1 "lambda") sep . sel])
    (let ((e (begin_se loc1 sel)))
     (match (ipatt_opt_se sep)
      ((Left p) <:expr< fun $p$ -> $e$ >>)
      ((Right (values se sel))
       (List.fold_right
        (lambda (se e) (let ((p (ipatt_se se))) <:expr< fun $p$ -> $e$ >>))
        [se . sel] e)))))
   ((Sexpr loc [(Slid _ "lambda_match") . sel])
    (let
     ((pel
       (match sel
        ([(Sexpr _ [(Santi loc (or "list" "_list") s)])] <:vala< $s$ >>)
        (_ <:vala< (List.map (match_case loc) sel) >>))))
     <:expr< fun [ $_list:pel$ ] >>))
   ((Sexpr loc [(Slid _ (as (or "let" "letrec") r)) . sel])
    (match sel
     ([(Sexpr _ sel1) . sel2]
      (let*
       ((r (= r "letrec"))
        (lbs (anti_list_map let_binding_se sel1))
        (e (begin_se loc sel2)))
       <:expr< let $flag:r$ $_list:lbs$ in $e$ >>))
     ([(Slid _ n) (Sexpr _ sl) . sel]
      (let*
       ((n (rename_id n))
        ((values pl el)
         (List.fold_right
          (lambda (se (values pl el))
           (match se
            ((Sexpr _ [se1 se2])
             (values [(patt_se se1) . pl] [(expr_se se2) . el]))
            (se (error se "named let"))))
          sl (values [] [])))
        (e1
         (List.fold_right (lambda (p e) <:expr< fun $p$ -> $e$ >>) pl
          (begin_se loc sel)))
        (e2
         (List.fold_left (lambda (e1 e2) <:expr< $e1$ $e2$ >>)
          <:expr< $lid:n$ >> el)))
       <:expr< let rec $lid:n$ = $e1$ in $e2$ >>))
     ([se . _] (error se "let_binding"))
     (_ (error_loc loc "let_binding"))))
   ((Sexpr loc [(Slid _ "let*") . sel])
    (match sel
     ([(Sexpr _ sel1) . sel2]
      (List.fold_right
       (lambda (se ek)
        (let (((values p e) (let_binding_se se)))
         <:expr< let $p$ = $e$ in $ek$ >>))
       sel1 (begin_se loc sel2)))
     ([se . _] (error se "let_binding"))
     (_ (error_loc loc "let_binding"))))
   ((Sexpr loc [(Slid _ "letmodule") se1 se2 se3])
    (let*
     ((s (anti_uid_or_error se1)) (me (module_expr_se se2)) (e (expr_se se3)))
     <:expr< let module $_:s$ = $me$ in $e$ >>))
   ((Sexpr loc [(Slid _ "match") se . sel])
    (let*
     ((e (expr_se se))
      (pel
       (match sel
        ([(Sexpr _ [(Santi _ (or "list" "_list") s)])] <:vala< $s$ >>)
        (_ <:vala< (List.map (match_case loc) sel) >>))))
     <:expr< match $e$ with [ $_list:pel$ ] >>))
   ((Sexpr loc [(Slid _ "parser") . sel])
    (let*
     (((values po sel)
       (match sel
        ([(as (Slid _ _) se) . sel] (values (Some (patt_se se)) sel))
        (sel (values None sel))))
      (pcl (List.map parser_case_se sel)))
     (Exparser.cparser loc po pcl)))
   ((Sexpr loc [(Slid _ "match_with_parser") se . sel])
    (let*
     ((e (expr_se se))
      ((values po sel)
       (match sel
        ([(as (Slid _ _) se) . sel] (values (Some (patt_se se)) sel))
        (sel (values None sel))))
      (pcl (List.map parser_case_se sel)))
     (Exparser.cparser_match loc e po pcl)))
   ((Sexpr loc [(Slid _ "try") se . sel])
    (let*
     ((e (expr_se se))
      (pel
       (match sel
        ([(Sexpr _ [(Santi _ (or "list" "_list") s)])] <:vala< $s$ >>)
        (_ <:vala< (List.map (match_case loc) sel) >>))))
     <:expr< try $e$ with [ $_list:pel$ ] >>))
   ((Sexpr loc [(Slid _ "begin") . sel])
    (let ((el (anti_list_map expr_se sel))) <:expr< do { $_list:el$ } >>))
   ((Sexpr loc [(Slid _ ":=") se1 se2])
    (let* ((e1 (expr_se se1)) (e2 (expr_se se2))) <:expr< $e1$ := $e2$ >>))
   ((Sarr loc sel)
    (let ((el (Pcaml.vala_map (List.map expr_se) sel)))
     <:expr< [| $_list:el$ |] >>))
   ((Sexpr loc [(Slid _ "values") . sel])
    (let ((el (anti_list_map expr_se sel))) <:expr< ($_list:el$) >>))
   ((Srec loc [(Slid _ "with") se . sel])
    (let ((e (expr_se se)) (lel (anti_list_map (label_expr_se loc) sel)))
     <:expr< { ($e$) with $_list:lel$ } >>))
   ((Srec loc sel)
    (let ((lel (anti_list_map (label_expr_se loc) sel)))
     <:expr< { $_list:lel$ } >>))
   ((Sexpr loc [(Slid _ ":") se1 se2])
    (let* ((e (expr_se se1)) (t (ctyp_se se2))) <:expr< ($e$ : $t$) >>))
   ((Sexpr loc [se]) (let ((e (expr_se se))) <:expr< $e$ () >>))
   ((Sexpr loc [(Slid _ "assert") se])
    (let ((e (expr_se se))) <:expr< assert $e$ >>))
   ((Sexpr loc [(Slid _ "lazy") se])
    (let ((e (expr_se se))) <:expr< lazy $e$ >>))
   ((Sexpr loc [(Slid _ "new") se])
    (let ((sl (anti_longident_se se))) <:expr< new $_list:sl$ >>))
   ((Sexpr loc [(Slid _ "`") (Suid _ s)]) <:expr< ` $s$ >>)
   ((Sexpr loc [(Slid _ "send") se (Slid _ s)])
    (let ((e (expr_se se))) <:expr< $e$ # $s$ >>))
   ((Sexpr loc [se . sel])
    (List.fold_left
     (lambda (e se) (let ((e1 (expr_se se))) <:expr< $e$ $e1$ >>))
     (expr_se se) sel))
   ((Slist loc sel)
    (letrec
     ((loop
       (lambda_match
        ([] <:expr< [] >>)
        ([se1 (Slid _ ".") se2]
         (let* ((e (expr_se se1)) (el (expr_se se2)))
          <:expr< [$e$ :: $el$] >>))
        ([se . sel]
         (let* ((e (expr_se se)) (el (loop sel)))
          <:expr< [$e$ :: $el$] >>)))))
     (loop sel)))
   ((Squot loc typ txt) (Pcaml.handle_expr_quotation loc (values typ txt)))
   ((Santi loc "" s) <:expr< $xtr:s$ >>)
   ((Santi loc _ s) (error_loc loc "expr"))))
 ((begin_se loc)
  (lambda_match
   ([] <:expr< () >>)
   ([se] (expr_se se))
   (sel
    (let*
     ((el (List.map expr_se sel))
      (loc (Ploc.encl (loc_of_sexpr (List.hd sel)) loc)))
     <:expr< do { $list:el$ } >>))))
 (let_binding_se
  (lambda_match
   ((Sexpr loc [se . sel])
    (let ((e (begin_se loc sel)))
     (match (ipatt_opt_se se)
      ((Left p) (values p e))
      ((Right _) (fun_binding_se se e)))))
   (se (error se "let_binding"))))
 ((fun_binding_se se e)
  (match se
   ((Sexpr _ [(Slid _ "values") . _]) (values (ipatt_se se) e))
   ((Sexpr _ [(Slid _ ":") _ _]) (values (ipatt_se se) e))
   ((Sexpr _ [se1 . sel])
    (match (ipatt_opt_se se1)
     ((Left p)
      (let
       ((e
         (List.fold_right
          (lambda (se e)
           (let*
            ((loc (Ploc.encl (loc_of_sexpr se) (MLast.loc_of_expr e)))
             (p (ipatt_se se)))
            <:expr< fun $p$ -> $e$ >>))
          sel e)))
       (values p e)))
     ((Right _) (values (ipatt_se se) e))))
   (_ (values (ipatt_se se) e))))
 ((match_case loc)
  (lambda_match
   ((Sexpr loc [(Sexpr _ [(Slid _ "when") se sew]) . sel])
    (values (patt_se se) <:vala< (Some (expr_se sew)) >> (begin_se loc sel)))
   ((Sexpr loc [se . sel])
    (values (patt_se se) <:vala< None >> (begin_se loc sel)))
   (se (error se "match_case"))))
 ((label_expr_se loc)
  (lambda_match
   ((Sexpr _ [se1 se2]) (values (patt_se se1) (expr_se se2)))
   (se (error se "label_expr"))))
 ((label_patt_se loc)
  (lambda_match
   ((Sexpr _ [se1 se2]) (values (patt_se se1) (patt_se se2)))
   (se (error se "label_patt"))))
 ((label_ipatt_se loc)
  (lambda_match
   ((Sexpr _ [se1 se2]) (values (ipatt_se se1) (ipatt_se se2)))
   (se (error se "label_ipatt"))))
 (parser_case_se
  (lambda_match
   ((Sexpr _ [(Sexpr _ sel) se1 se2])
    (let*
     ((sp (stream_patt_se sel)) (po (Some (ipatt_se se1))) (e (expr_se se2)))
     (values sp po e)))
   ((Sexpr _ [(Sexpr _ sel) se])
    (let* ((sp (stream_patt_se sel)) (e (expr_se se))) (values sp None e)))
   (se (error se "parser_case"))))
 (stream_patt_se
  (lambda_match
   ([se . sel]
    (let* ((spc (stream_patt_comp_se se)) (sp (stream_patt_kont_se sel)))
     [(values spc SpoNoth) . sp]))
   ([] [])))
 (stream_patt_kont_se
  (lambda_match
   ([se (Slid _ "!") . sel]
    (let* ((spc (stream_patt_comp_se se)) (sp (stream_patt_kont_se sel)))
     [(values spc SpoBang) . sp]))
   ([se1 (Slid _ "?") se2 . sel]
    (let*
     ((spc (stream_patt_comp_se se1))
      (e (expr_se se2))
      (sp (stream_patt_kont_se sel)))
     [(values spc (SpoQues e)) . sp]))
   ([se . sel]
    (let* ((spc (stream_patt_comp_se se)) (sp (stream_patt_kont_se sel)))
     [(values spc SpoNoth) . sp]))
   ([] [])))
 (stream_patt_comp_se
  (lambda_match
   ((Sexpr loc [(Slid _ "`") se]) (SpTrm loc (patt_se se) <:vala< None >>))
   ((Sexpr loc [(Slid _ "`") se1 se2])
    (let ((e (expr_se se2))) (SpTrm loc (patt_se se1) <:vala< (Some e) >>)))
   ((Sexpr loc [(Slid _ "let") se1 se2])
    (SpLet loc (ipatt_se se1) (expr_se se2)))
   ((Sexpr loc [se1 se2]) (SpNtr loc (patt_se se1) (expr_se se2)))
   (se (SpStr (loc_of_sexpr se) (patt_se se)))))
 (patt_se
  (lambda_match
   ((Sacc loc se1 se2)
    (let* ((p1 (patt_se se1)) (p2 (patt_se se2))) <:patt< $p1$ . $p2$ >>))
   ((Slid loc "_") <:patt< _ >>)
   ((Slid loc s) <:patt< $lid:(rename_id s)$ >>)
   ((Slidv loc s) <:patt< $_lid:s$ >>)
   ((Suid loc s) <:patt< $uid:(rename_id s)$ >>)
   ((Suidv loc s) <:patt< $_uid:s$ >>)
   ((Sint loc s) <:patt< $_int:s$ >>)
   ((Sint_l loc s) <:patt< $_int32:s$ >>)
   ((Sint_L loc s) <:patt< $_int64:s$ >>)
   ((Sint_n loc s) <:patt< $_nativeint:s$ >>)
   ((Sfloat loc s) <:patt< $_flo:s$ >>)
   ((Schar loc s) <:patt< $_chr:s$ >>)
   ((Sstring loc s) <:patt< $_str:s$ >>)
   ((Sexpr loc [(Slid _ "~") se])
    (let ((s (anti_lid_or_error se))) <:patt< ~{$_:s$} >>))
   ((Sexpr loc [(Slid _ "~") se1 se2])
    (let ((s (anti_lid_or_error se1)) (p (patt_se se2)))
     <:patt< ~{$_:s$ = $p$} >>))
   ((Sexpr loc [(Slid _ "?") se])
    (match se
     ((Sexpr _ [se1 se2])
      (let ((s (anti_lid_or_error se1)) (e (expr_se se2)))
       <:patt< ?{$_:s$ = $e$} >>))
     (se (let ((s (anti_lid_or_error se))) <:patt< ?{$_:s$} >>))))
   ((Sexpr loc [(Slid _ "?") se1 se2])
    (let ((e (expr_se se2)))
     (match se1
      ((Sexpr _ [se1 se2])
       (let ((s (anti_lid_or_error se1)) (p (patt_se se2)))
        <:patt< ?{$_:s$ = ?{$p$ = $e$}} >>))
      (se (let ((s (anti_lid_or_error se))) <:patt< ?{$_:s$ = $e$} >>)))))
   ((Srec loc sel)
    (let ((lpl (anti_list_map (label_patt_se loc) sel)))
     <:patt< { $_list:lpl$ } >>))
   ((Sexpr loc [(Slid _ ":") se1 se2])
    (let* ((p (patt_se se1)) (t (ctyp_se se2))) <:patt< ($p$ : $t$) >>))
   ((Sexpr loc [(Slid _ "or") se . sel])
    (List.fold_left
     (lambda (p se) (let ((p1 (patt_se se))) <:patt< $p$ | $p1$ >>))
     (patt_se se) sel))
   ((Sexpr loc [(Slid _ "range") se1 se2])
    (let* ((p1 (patt_se se1)) (p2 (patt_se se2))) <:patt< $p1$ .. $p2$ >>))
   ((Sarr loc sel)
    (let ((pl (Pcaml.vala_map (List.map patt_se) sel)))
     <:patt< [| $_list:pl$ |] >>))
   ((Sexpr loc [(Slid _ "values") . sel])
    (let ((pl (anti_list_map patt_se sel))) <:patt< ($_list:pl$) >>))
   ((Sexpr loc [(Slid _ "as") se1 se2])
    (let* ((p1 (patt_se se1)) (p2 (patt_se se2))) <:patt< ($p1$ as $p2$) >>))
   ((Sexpr loc [(Slid _ "`") (Suid _ s)]) <:patt< ` $s$ >>)
   ((Sexpr loc [se . sel])
    (List.fold_left
     (lambda (p se) (let ((p1 (patt_se se))) <:patt< $p$ $p1$ >>))
     (patt_se se) sel))
   ((Sexpr loc []) <:patt< () >>)
   ((Slist loc sel)
    (letrec
     ((loop
       (lambda_match
        ([] <:patt< [] >>)
        ([se1 (Slid _ ".") se2]
         (let* ((p (patt_se se1)) (pl (patt_se se2)))
          <:patt< [$p$ :: $pl$] >>))
        ([se . sel]
         (let* ((p (patt_se se)) (pl (loop sel)))
          <:patt< [$p$ :: $pl$] >>)))))
     (loop sel)))
   ((Squot loc typ txt) (Pcaml.handle_patt_quotation loc (values typ txt)))
   ((Santi loc "" s) <:patt< $xtr:s$ >>)
   ((Santi loc _ s) (error_loc loc "patt"))))
 ((ipatt_se se)
  (match (ipatt_opt_se se) ((Left p) p) ((Right _) (patt_se se))))
 (ipatt_opt_se
  (lambda_match
   ((Slid loc "_") (Left <:patt< _ >>))
   ((Slid loc s) (Left <:patt< $lid:(rename_id s)$ >>))
   ((Sexpr loc [(Slid _ "~") (Slid _ s)]) (Left <:patt< ~{$lid:s$} >>))
   ((Sexpr loc [(Slid _ "~") (Slid _ s) se])
    (let ((p (patt_se se))) (Left <:patt< ~{$lid:s$ = $p$} >>)))
   ((Sexpr loc [(Slid _ "?") se])
    (match se
     ((Sexpr _ [se1 (Slid _ p)])
      (let ((s (anti_lid_or_error se1)))
       (Left <:patt< ?{$_:s$ = $lid:p$} >>)))
     (se (let ((s (anti_lid_or_error se))) (Left <:patt< ?{$_:s$} >>)))))
   ((Sexpr loc [(Slid _ "?") se1 se2])
    (let ((e (expr_se se2)))
     (match se1
      ((Sexpr _ [se1 (Slid _ p)])
       (let ((s (anti_lid_or_error se1)))
        (Left <:patt< ?{$_:s$ = ?{$lid:p$ = $e$}} >>)))
      (se
       (let ((s (anti_lid_or_error se)))
        (Left <:patt< ?{$_:s$ = $e$} >>))))))
   ((Sexpr loc [(Slid _ ":") se1 se2])
    (let* ((p (ipatt_se se1)) (t (ctyp_se se2)))
     (Left <:patt< ($p$ : $t$) >>)))
   ((Sexpr loc [(Slid _ "as") se1 se2])
    (let* ((p1 (ipatt_se se1)) (p2 (ipatt_se se2)))
     (Left <:patt< ($p1$ as $p2$) >>)))
   ((Sexpr loc [(Slid _ "values") . sel])
    (let ((pl (List.map ipatt_se sel))) (Left <:patt< ( $list:pl$ ) >>)))
   ((Srec loc sel)
    (let ((lpl (List.map (label_ipatt_se loc) sel)))
     (Left <:patt< { $list:lpl$ } >>)))
   ((Sexpr loc []) (Left <:patt< () >>))
   ((Sexpr loc [se . sel]) (Right (values se sel)))
   (se (error se "ipatt"))))
 (type_declaration_se
  (lambda_match
   ((Sexpr loc [se1 se2])
    (let*
     (((values n1 loc1 tpl)
       (match se1
        ((Sexpr _ [(Slid loc n) . sel])
         (values (rename_id n) loc (List.map type_param_se sel)))
        ((Slid loc n) (values (rename_id n) loc []))
        (se (error se "type declaration"))))
      (n (values loc1 <:vala< n1 >>)))
     {(MLast.tdNam <:vala< n >>) (MLast.tdPrm <:vala< tpl >>)
      (MLast.tdPrv <:vala< False >>) (MLast.tdDef (ctyp_se se2))
      (MLast.tdCon <:vala< [] >>)}))
   (se (error se "type_decl"))))
 (type_declaration_list_se
  (lambda_match
   ([se1 se2 . sel]
    (let*
     (((values n1 loc1 tpl)
       (match se1
        ((Sexpr _ [(Slid loc n) . sel])
         (values (rename_id n) loc (List.map type_param_se sel)))
        ((Slid loc n) (values (rename_id n) loc []))
        (se (error se "type declaration"))))
      (n (values loc1 <:vala< n1 >>))
      (td
       {(MLast.tdNam <:vala< n >>) (MLast.tdPrm <:vala< tpl >>)
        (MLast.tdPrv <:vala< False >>) (MLast.tdDef (ctyp_se se2))
        (MLast.tdCon <:vala< [] >>)}))
     [td . (type_declaration_list_se sel)]))
   ([] [])
   ([se . _] (error se "type_decl"))))
 ((type_param_se se)
  (match se
   ((when (Slid _ s) (&& (>= (String.length s) 2) (= s.[0] ''')))
    (let ((s (String.sub s 1 (- (String.length s) 1))))
     (values <:vala< (Some s) >> None)))
   ((when (Slid _ s) (&& (>= (String.length s) 3) (= s.[1] ''')))
    (let
     ((vara
       (if (= s.[0] '+') (Some True)
        (if (= s.[0] '-') (Some False) (error se "type_param"))))
      (s (String.sub s 2 (- (String.length s) 2))))
     (values <:vala< (Some s) >> vara)))
   (se (error se "type_param"))))
 (ctyp_se
  (lambda_match
   ((Sexpr loc [(Slid _ "sum") . sel])
    (let ((cdl (anti_list_map constructor_declaration_se sel)))
     <:ctyp< [ $_list:cdl$ ] >>))
   ((Sexpr loc [(Slid _ "variants") . sel])
    (let ((cdl (anti_list_map variant_declaration_se sel)))
     <:ctyp< [ = $_list:cdl$ ] >>))
   ((Sexpr loc [(Slid _ "variantsless") . sel])
    (let ((cdl (anti_list_map variant_declaration_se sel)))
     <:ctyp< [ < $_list:cdl$ ] >>))
   ((Sexpr loc [(Slid _ "variantsgreater") . sel])
    (let ((cdl (anti_list_map variant_declaration_se sel)))
     <:ctyp< [ > $_list:cdl$ ] >>))
   ((Srec loc sel)
    (let ((ldl (anti_list_map label_declaration_se sel)))
     <:ctyp< { $_list:ldl$ } >>))
   ((Sexpr loc [(Slid _ "->") . (as [_ _ . _] sel)])
    (letrec
     ((loop
       (lambda_match
        ([] (assert False))
        ([se] (ctyp_se se))
        ([se . sel]
         (let*
          ((t1 (ctyp_se se))
           (loc (Ploc.encl (loc_of_sexpr se) loc))
           (t2 (loop sel)))
          <:ctyp< $t1$ -> $t2$ >>)))))
     (loop sel)))
   ((Sexpr loc [(Slid _ "as") se1 se2])
    (let* ((t1 (ctyp_se se1)) (t2 (ctyp_se se2))) <:ctyp< ($t1$ as $t2$) >>))
   ((Sexpr loc [(Slid _ "*") . sel])
    (let ((tl (anti_list_map ctyp_se sel))) <:ctyp< ($_list:tl$) >>))
   ((Sexpr loc [(Slid _ "==") se1 se2])
    (let* ((t1 (ctyp_se se1)) (t2 (ctyp_se se2))) <:ctyp< $t1$ == $t2$ >>))
   ((Sexpr loc [(Slid _ "?") se1 se2])
    (let ((s (anti_lid_or_error se1)) (t (ctyp_se se2)))
     <:ctyp< ?$_:s$: $t$ >>))
   ((Sexpr loc [(Slid _ "~") se1 se2])
    (let ((s (anti_lid_or_error se1)) (t (ctyp_se se2)))
     <:ctyp< ~$_:s$: $t$ >>))
   ((Sexpr loc [(Slid _ "object") . sel])
    (let ((fl (object_field_list_se sel))) <:ctyp< < $_list:fl$ > >>))
   ((Sexpr loc [(Slid _ "objectvar") . sel])
    (let ((fl (object_field_list_se sel))) <:ctyp< < $_list:fl$ .. > >>))
   ((Sexpr loc [se . sel])
    (List.fold_left
     (lambda (t se) (let ((t2 (ctyp_se se))) <:ctyp< $t$ $t2$ >>))
     (ctyp_se se) sel))
   ((Sacc loc se1 se2)
    (let* ((t1 (ctyp_se se1)) (t2 (ctyp_se se2))) <:ctyp< $t1$ . $t2$ >>))
   ((Slid loc "_") <:ctyp< _ >>)
   ((Slid loc s)
    (if (= s.[0] ''')
     (let ((s (String.sub s 1 (- (String.length s) 1)))) <:ctyp< '$s$ >>)
     <:ctyp< $lid:(rename_id s)$ >>))
   ((Slidv loc s) <:ctyp< $_lid:s$ >>)
   ((Suid loc s) <:ctyp< $uid:(rename_id s)$ >>)
   ((Suidv loc s) <:ctyp< $_uid:s$ >>)
   ((Santi loc "" s) <:ctyp< $xtr:s$ >>)
   (se (error se "ctyp"))))
 ((object_field_list_se sel)
  (anti_list_map
   (lambda_match
    ((Sexpr loc [(Slid _ s) se]) (let ((t (ctyp_se se))) (values s t)))
    (se (error_loc (loc_of_sexpr se) "object field")))
   sel))
 (constructor_declaration_se
  (lambda_match
   ((Sexpr loc [(Suid _ ci) . sel])
    (values loc <:vala< (rename_id ci) >> <:vala< (List.map ctyp_se sel) >>
       None))
   (se (error se "constructor_declaration"))))
 (variant_declaration_se
  (lambda_match
   ((Sexpr loc [(Slid _ "`") (Suid _ s)]) <:poly_variant< ` $s$ >>)
   ((Sexpr loc [(Slid _ "`") (Suid _ s) . sel])
    (let*
     (((values a sel)
       (match sel
        ([(Slid _ "&") . sel] (values True sel))
        (sel (values False sel))))
      (tl (List.map ctyp_se sel)))
     <:poly_variant< ` $s$ of $flag:a$ $list:tl$ >>))
   (se (let* ((t (ctyp_se se)) (loc (loc_of_sexpr se)))
       <:poly_variant< $t$ >>))))
 (label_declaration_se
  (lambda_match
   ((Sexpr loc [(Slid _ lab) (Slid _ "mutable") se])
    (values loc (rename_id lab) True (ctyp_se se)))
   ((Sexpr loc [(Slid _ lab) se])
    (values loc (rename_id lab) False (ctyp_se se)))
   (se (error se "label_declaration"))))
 (class_sig_item_se
  (lambda_match
   ((Sexpr loc [(Slid _ "method") (Slid _ n) se])
    (let ((t (ctyp_se se))) <:class_sig_item< method $n$ : $t$ >>))
   ((Sexpr loc [(Slid _ "value") (Slid _ "mutable") (Slid _ n) se])
    (let ((t (ctyp_se se))) <:class_sig_item< value mutable $n$ : $t$ >>))
   (se (error se "class_sig_item"))))
 (class_str_item_se
  (lambda_match
   ((Sexpr loc [(Slid _ "inherit") se (Slid _ s)])
    (let ((ce (class_expr_se se)))
     <:class_str_item< inherit $ce$ $opt:(Some s)$ >>))
   ((Sexpr loc [(Slid _ "inherit") se])
    (let ((ce (class_expr_se se))) <:class_str_item< inherit $ce$ >>))
   ((Sexpr loc [(Slid _ "initializer") se])
    (let ((e (expr_se se))) <:class_str_item< initializer $e$ >>))
   ((Sexpr loc [(Slid _ "method") (Slid _ "virtual") (Slid _ n) se])
    (let ((t (ctyp_se se))) <:class_str_item< method virtual $n$ : $t$ >>))
   ((Sexpr loc [(Slid _ "method") (Slid _ "private") (Slid _ n) se])
    (let ((e (expr_se se))) <:class_str_item< method private $n$ = $e$ >>))
   ((Sexpr loc
      [(Slid _ "method") (Slid _ "private") (Sexpr _ [(Slid _ n) . sel]) se])
    (let
     ((e
       (List.fold_right
        (lambda (se e) (let ((p (patt_se se))) <:expr< fun $p$ -> $e$ >>)) sel
        (expr_se se))))
     <:class_str_item< method private $n$ = $e$ >>))
   ((Sexpr loc [(Slid _ "method") (Slid _ n) se])
    (let ((e (expr_se se))) <:class_str_item< method $n$ = $e$ >>))
   ((Sexpr loc [(Slid _ "method") (Sexpr _ [(Slid _ n) . sel]) se])
    (let
     ((e
       (List.fold_right
        (lambda (se e) (let ((p (patt_se se))) <:expr< fun $p$ -> $e$ >>)) sel
        (expr_se se))))
     <:class_str_item< method $n$ = $e$ >>))
   ((Sexpr loc [(Slid _ "value") (Slid _ "mutable") (Slid _ n) se])
    (let ((e (expr_se se))) <:class_str_item< value mutable $n$ = $e$ >>))
   ((Sexpr loc [(Slid _ "value") (Slid _ n) se])
    (let ((e (expr_se se))) <:class_str_item< value $n$ = $e$ >>))
   (se (error se "class_str_item"))))
 (class_type_se
  (lambda_match
   ((Sexpr loc [(Slid _ "->") se . sel])
    (letrec
     ((loop
       (lambda_match
        ([] (assert False))
        ([se] (class_type_se se))
        ([se . sel]
         (let* ((t (ctyp_se se)) (ct (loop sel)))
          <:class_type< [ $t$ ] -> $ct$ >>)))))
     (loop [se . sel])))
   ((Sexpr loc [(Slid _ "object") . sel])
    (let ((csl (List.map class_sig_item_se sel)))
     <:class_type< object $list:csl$ end >>))
   (se (error se "class_type_se"))))
 (class_expr_se
  (lambda_match
   ((Sexpr loc [(Slid _ "let") (Sexpr _ sel) se])
    (let* ((lbl (anti_list_map let_binding_se sel)) (ce (class_expr_se se)))
     <:class_expr< let $_list:lbl$ in $ce$ >>))
   ((Sexpr loc [(Slid _ "lambda") se1 se2])
    (let ((ce (class_expr_se se2)))
     (match (ipatt_opt_se se1)
      ((Left p) <:class_expr< fun $p$ -> $ce$ >>)
      ((Right (values se sel))
       (List.fold_right
        (lambda (se ce)
         (let ((p (ipatt_se se))) <:class_expr< fun $p$ -> $ce$ >>))
        [se . sel] ce)))))
   ((Sexpr loc [(Slid _ "object") se . sel])
    (let*
     ((p (match se ((Sexpr _ []) None) (se (Some (patt_se se)))))
      (csl (List.map class_str_item_se sel)))
     <:class_expr< object $opt:p$ $list:csl$ end >>))
   ((Sexpr loc [se . sel])
    (letrec
     (((loop ce)
       (lambda_match
        ([se . sel]
         (let ((e (expr_se se))) (loop <:class_expr< $ce$ $e$ >> sel)))
        ([] ce))))
     (loop (class_expr_se se) sel)))
   (se
    (let* ((sl (longident_se se)) (loc (loc_of_sexpr se)))
     <:class_expr< $list:sl$ >>)))))

(define directive_se
 (lambda_match
  ((Sexpr _ [(Slid _ s)]) (values s None))
  ((Sexpr _ [(Slid _ s) se]) (let ((e (expr_se se))) (values s (Some e))))
  (se (error se "directive"))))

; Parser

(:= Pcaml.syntax_name.val "Scheme")
(:= Pcaml.no_constructors_arity.val False)

(begin
 (Grammar.Unsafe.gram_reinit gram (lexer_gmake ()))
 (Grammar.Unsafe.clear_entry interf)
 (Grammar.Unsafe.clear_entry implem)
 (Grammar.Unsafe.clear_entry top_phrase)
 (Grammar.Unsafe.clear_entry use_file)
 (Grammar.Unsafe.clear_entry expr)
 (Grammar.Unsafe.clear_entry patt)
 (Grammar.Unsafe.clear_entry ctyp)
 (Grammar.Unsafe.clear_entry str_item)
 (Grammar.Unsafe.clear_entry sig_item)
 (Grammar.Unsafe.clear_entry module_expr)
 (Grammar.Unsafe.clear_entry module_type)
 (Grammar.Unsafe.clear_entry with_constr)
 (Grammar.Unsafe.clear_entry let_binding)
 (Grammar.Unsafe.clear_entry type_decl)
 (Grammar.Unsafe.clear_entry class_type)
 (Grammar.Unsafe.clear_entry class_expr)
 (Grammar.Unsafe.clear_entry class_sig_item)
 (Grammar.Unsafe.clear_entry class_str_item))

(:= Pcaml.parse_interf.val (Grammar.Entry.parse interf))
(:= Pcaml.parse_implem.val (Grammar.Entry.parse implem))

(define sexpr (Grammar.Entry.create gram "sexpr"))

EXTEND
  GLOBAL : implem interf top_phrase use_file expr patt ctyp str_item sig_item
    module_expr module_type with_constr sexpr /
  implem :
    [ [ "#" / se = sexpr ->
          (let (((values n dp) (directive_se se)))
             (values [(values <:str_item< # $lid:n$ $opt:dp$ >> loc)] None))
      | si = str_item / x = SELF ->
          (let* (((values sil stopped) x)
                 (loc (MLast.loc_of_str_item si)))
             (values [(values si loc) . sil] stopped))
      | EOI -> (values [] (Some loc)) ] ]
  /
  interf :
    [ [ "#" / se = sexpr ->
          (let (((values n dp) (directive_se se)))
             (values [(values <:sig_item< # $lid:n$ $opt:dp$ >> loc)] None))
      | si = sig_item / x = SELF ->
          (let* (((values sil stopped) x)
                 (loc (MLast.loc_of_sig_item si)))
             (values [(values si loc) . sil] stopped))
      | EOI -> (values [] (Some loc)) ] ]
  /
  top_phrase :
    [ [ "#" / se = sexpr ->
          (let (((values n dp) (directive_se se)))
             (Some <:str_item< # $lid:n$ $opt:dp$ >>))
      | se = sexpr -> (Some (str_item_se se))
      | EOI -> None ] ]
  /
  use_file :
    [ [ "#" / se = sexpr ->
          (let (((values n dp) (directive_se se)))
             (values [<:str_item< # $lid:n$ $opt:dp$ >>] True))
      | si = str_item / x = SELF ->
          (let (((values sil stopped) x)) (values [si . sil] stopped))
      | EOI -> (values [] False) ] ]
  /
  expr :
    [ "top"
      [ se = sexpr -> (expr_se se) ] ]
  /
  patt :
    [ [ se = sexpr -> (patt_se se) ] ]
  /
  ctyp :
    [ [ se = sexpr -> (ctyp_se se) ] ]
  /
  str_item :
    [ [ se = sexpr -> (str_item_se se)
      | e = expr -> <:str_item< $exp:e$ >> ] ]
  /
  sig_item :
    [ [ se = sexpr -> (sig_item_se se) ] ]
  /
  module_expr :
    [ [ se = sexpr -> (module_expr_se se) ] ]
  /
  module_type :
    [ [ se = sexpr -> (module_type_se se) ] ]
  /
  with_constr :
    [ [ se = sexpr -> (with_constr_se se) ] ]
  /
  sexpr :
    [ [ se1 = sexpr / DOT / se2 = sexpr -> (Sacc loc se1 se2) ]
    | [ "(" / sl = LIST0 sexpr / ")" -> (Sexpr loc sl)
      | "[" / sl = LIST0 sexpr / "]" -> (Slist loc sl)
      | "{" / sl = LIST0 sexpr / "}" -> (Srec loc sl)
      | "#(" / sl = V (LIST0 sexpr) / ")" -> (Sarr loc sl)
      | a = pa_extend_keyword -> (Slid loc a)
      | s = V LIDENT ->
         (Pcaml.vala_mapa (lambda s (Slid loc s))
          (lambda s (Slidv loc <:vala< $s$ >>)) s)
      | s = V UIDENT ->
         (Pcaml.vala_mapa (lambda s (Suid loc s))
          (lambda s (Suidv loc <:vala< $s$ >>)) s)
      | s = V INT -> (Sint loc s)
      | s = V INT_l -> (Sint_l loc s)
      | s = V INT_L -> (Sint_L loc s)
      | s = V INT_n -> (Sint_n loc s)
      | s = V FLOAT -> (Sfloat loc s)
      | s = V CHAR -> (Schar loc s)
      | s = V STRING -> (Sstring loc s)
      | s = SPACEDOT -> (Slid loc ".")
      | s = QUOT ->
          (let* ((i (String.index s ':'))
                 (typ (String.sub s 0 i))
                 (txt (String.sub s (+ i 1) (- (- (String.length s) i) 1))))
            (Squot loc typ txt))
      | s = ANTIQUOT_LOC -> (Santi loc "" s)
      | s = ANTIQUOT_LOC "_" -> (Santi loc "_" s)
      | s = ANTIQUOT_LOC "list" -> (Santi loc "list" s)
      | s = ANTIQUOT_LOC "_list" -> (Santi loc "_list" s)
      | NL / s = sexpr -> s
      | NL -> (raise Stream.Failure) ] ]
  /
  pa_extend_keyword :
    [ [ "_" -> "_"
      | "," -> ","
      | "=" -> "="
      | ":" -> ":"
      | "/" -> "/"
      | "#" -> "#" ] ]
  /
END
