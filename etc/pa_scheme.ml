; camlp5 ./pa_schemer.cmo pa_extend.cmo q_MLast.cmo pr_dump.cmo
; $Id: pa_scheme.ml,v 1.44 2007/10/07 01:31:00 deraugla Exp $
; Copyright (c) INRIA 2007

(open Pcaml)

(type (choice 'a 'b) (sum (Left 'a) (Right 'b)))

; Buffer

(module Buff
 (struct
  (define buff (ref (String.create 80)))
  (define (store len x)
    (if (>= len (String.length buff.val))
        (:= buff.val (^ buff.val (String.create (String.length buff.val)))))
    (:= buff.val.[len] x)
    (succ len))
  (define (mstore len s)
   (letrec
    (((add_rec len i)
      (if (== i (String.length s)) len (add_rec (store len s.[i]) (succ i)))))
    (add_rec len 0)))
  (define (get len) (String.sub buff.val 0 len))))

(define (rename_id s)
  (if (&& (> (String.length s) 0) (= s.[(- (String.length s) 1)] '#'))
    (String.sub s 0 (- (String.length s) 1))
    (Pcaml.rename_id.val s)))

; Lexer

(definerec skip_to_eol
  (parser
   (((` (or '\n' '\r'))) ())
   (((` _) s) (skip_to_eol s))))

(define no_ident ['(' ')' '[' ']' '{' '}' ' ' '\t' '\n' '\r' ';' '.'])

(definerec (ident len)
  (parser
   (((` x (not (List.mem x no_ident))) s) (ident (Buff.store len x) s))
   (() len)))

(define (identifier kwt s)
  (let ((con
          (try (begin (: (Hashtbl.find kwt s) unit) "")
           (Not_found
            (match s.[0]
             ((range 'A' 'Z') "UIDENT")
             (_ "LIDENT"))))))
     (values con s)))

(definerec (string len)
  (parser
   (((` '"')) (Buff.get len))
   (((` '\\') (` c) s) (string (Buff.store (Buff.store len '\\') c) s))
   (((` x) s) (string (Buff.store len x) s))))

(definerec (end_exponent_part_under len)
  (parser
   (((` (as (range '0' '9') c)) s)
    (end_exponent_part_under (Buff.store len c) s))
   (() (values "FLOAT" (Buff.get len)))))

(define (end_exponent_part len)
  (parser
   (((` (as (range '0' '9') c)) s)
    (end_exponent_part_under (Buff.store len c) s))
   (() (raise (Stream.Error "ill-formed floating-point constant")))))

(define (exponent_part len)
  (parser
   (((` (as (or '+' '-') c)) s) (end_exponent_part (Buff.store len c) s))
   (((a (end_exponent_part len))) a)))

(definerec (decimal_part len)
  (parser
   (((` (as (range '0' '9') c)) s) (decimal_part (Buff.store len c) s))
   (((` (or 'e' 'E')) s) (exponent_part (Buff.store len 'E') s))
   (() (values "FLOAT" (Buff.get len)))))

(definerec (number len)
  (parser
   (((` (as (range '0' '9') c)) s) (number (Buff.store len c) s))
   (((` '.') s) (decimal_part (Buff.store len '.') s))
   (((` (or 'e' 'E')) s) (exponent_part (Buff.store len 'E') s))
   (((` 'l')) (values "INT_l" (Buff.get len)))
   (((` 'L')) (values "INT_L" (Buff.get len)))
   (((` 'n')) (values "INT_n" (Buff.get len)))
   (() (values "INT" (Buff.get len)))))

(define binary
  (parser
   (((` (as (range '0' '1') c))) c)))

(define octal
  (parser
   (((` (as (range '0' '7') c))) c)))

(define hexa
  (parser
   (((` (as (or (range '0' '9') (range 'a' 'f') (range 'A' 'F')) c))) c)))

(definerec (digits_under kind len)
  (parser
   (((d kind) s) (digits_under kind (Buff.store len d) s))
   (((` '_') s) (digits_under kind (Buff.store len '_') s))
   (((` 'l')) (values "INT_l" (Buff.get len)))
   (((` 'L')) (values "INT_L" (Buff.get len)))
   (((` 'n')) (values "INT_n" (Buff.get len)))
   (() (values "INT" (Buff.get len)))))

(define (digits kind bp len)
  (parser
   (((d kind) (tok (digits_under kind (Buff.store len d)))) tok)
   (() ep
    (Ploc.raise (Ploc.make_unlined (values bp ep))
                (Failure "ill-formed integer constant")))))

(define (base_number kwt bp len)
  (parser
   (((` (or 'b' 'B')) s) (digits binary bp (Buff.store len 'b') s))
   (((` (or 'o' 'O')) s) (digits octal bp (Buff.store len 'o') s))
   (((` (or 'x' 'X')) s) (digits hexa bp (Buff.store len 'x') s))
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
        (let* ((len (Buff.store (Buff.store 0 ''') x))
               (s (Buff.get (ident len s))))
          (values "LIDENT" s))))))

(definerec (char len)
  (parser
   (((` ''')) len)
   (((` x) s) (char (Buff.store len x) s))))

(define quote
  (parser
   (((` '\\') (` c) (len (char (Buff.store (Buff.store 0 '\\') c))))
    (values "CHAR" (Buff.get len)))
   (((` x) s) (char_or_quote_id x s))))

(definerec*
  ((lexer kwt)
    (parser bp
     (((` (or '\t' '\r')) s) (lexer kwt s))
     (((` ' ') s) (after_space kwt s))
     (((` ';') (_ skip_to_eol) s) (lexer kwt s))
     (((` '\n') s)
      (if Sys.interactive.val
       (values (values "NL" "") (values bp (+ bp 1)))
       (lexer kwt s)))
     (((` '(')) (values (values "" "(") (values bp (+ bp 1))))
     (((` ')')) (values (values "" ")") (values bp (+ bp 1))))
     (((` '[')) (values (values "" "[") (values bp (+ bp 1))))
     (((` ']')) (values (values "" "]") (values bp (+ bp 1))))
     (((` '{')) (values (values "" "{") (values bp (+ bp 1))))
     (((` '}')) (values (values "" "}") (values bp (+ bp 1))))
     (((` '.')) (values (values "DOT" "") (values bp (+ bp 1))))
     (((` '"') (s (string 0))) ep
      (values (values "STRING" s) (values bp ep)))
     (((` ''') (tok quote)) ep (values tok (values bp ep)))
     (((` '<') (tok (less kwt))) ep (values tok (values bp ep)))
     (((` '-') (tok (minus bp kwt))) ep (values tok (values bp ep)))
     (((` '#') (tok (sharp bp kwt))) ep (values tok (values bp ep)))
     (((` '~') (tok tilde)) ep (values tok (values bp ep)))
     (((` '?') (tok question)) ep (values tok (values bp ep)))
     (((` (as (range '0' '9') c)) (tok (number (Buff.store 0 c)))) ep
      (values tok (values bp ep)))
     (((` (as (or '+' '*' '/') c)) (len (ident (Buff.store 0 c)))
       (len (operator len)))
      ep
      (values (identifier kwt (Buff.get len)) (values bp ep)))
     (((` x) (len (ident (Buff.store 0 x)))) ep
      (values (identifier kwt (Buff.get len)) (values bp ep)))
     (() (values (values "EOI" "") (values bp (+ bp 1))))))
  ((after_space kwt)
    (parser
     (((` '.')) ep (values (values "SPACEDOT" "") (values (- ep 1) ep)))
     (((x (lexer kwt))) x)))
  (tilde
    (parser
     (((` (as (range 'a' 'z') c)) (len (ident (Buff.store 0 c))))
      (values "TILDEIDENT" (Buff.get len)))
     (((len (ident (Buff.store 0 '~'))) (len (operator len)))
      (values "LIDENT" (Buff.get len)))))
  (question
    (parser
     (((` (as (range 'a' 'z') c)) (len (ident (Buff.store 0 c))))
      (values "QUESTIONIDENT" (Buff.get len)))
     (() (values "LIDENT" "?"))))
  ((sharp bp kwt)
   (parser
     (((` '(')) (values "" "#("))
     (((tok (base_number kwt bp (Buff.store 0 '0')))) tok)))
  ((minus bp kwt)
    (parser
     (((` '.')) (identifier kwt "-."))
     (((` (as (range '0' '9') c))
      (n (number (Buff.store (Buff.store 0 '-') c)))) n)
     (((` '#')
      (n (base_number kwt bp (Buff.mstore 0 "-0")))) n)
     (((len (ident (Buff.store 0 '-')))) (identifier kwt (Buff.get len)))))
  ((less kwt)
    (parser
     (((` ':') (lab (label 0)) (? (` '<') "'<' expected") (q (quotation 0)))
      (values "QUOT" (^ lab ":" q)))
     (((len (ident (Buff.store 0 '<')))) (identifier kwt (Buff.get len)))))
  ((label len)
    (parser
     (((` (as (or (range 'a' 'z') (range 'A' 'Z') '_') c)) s)
      (label (Buff.store len c) s))
     (() (Buff.get len))))
  ((quotation len)
    (parser
     (((` '>') s) (quotation_greater len s))
     (((` x) s) (quotation (Buff.store len x) s))
     (() (failwith "quotation not terminated"))))
  ((quotation_greater len)
    (parser
     (((` '>')) (Buff.get len))
     (((a (quotation (Buff.store len '>')))) a))))

(define (lexer_using kwt (values con prm))
  (match con
   ((or "CHAR" "DOT" "EOI" "INT" "INT_l" "INT_L" "INT_n" "FLOAT" "LIDENT" "NL"
     "QUESTIONIDENT" "QUOT" "SPACEDOT" "STRING" "TILDEIDENT" "UIDENT")
    ())
   ((or "ANTIQUOT" "ANTIQUOT_LOC") ())
   ("" (try (Hashtbl.find kwt prm) (Not_found (Hashtbl.add kwt prm ()))))
   (_
    (raise
     (Plexing.Error
      (^ "the constructor \"" con "\" is not recognized by Plexer"))))))

(define (lexer_text (values con prm))
  (cond
   ((= con "") (^ "'"prm "'"))
   ((= prm "") con)
   (else (^ con " \"" prm "\""))))

(define (lexer_gmake ())
  (let ((kwt (Hashtbl.create 89))
        (lexer2
         (lambda (kwt (values s _ _))
           (let (((values t loc) (lexer kwt s)))
             (values t (Ploc.make_unlined loc))))))
     {(Plexing.tok_func (Plexing.lexer_func_of_parser (lexer2 kwt)))
      (Plexing.tok_using (lexer_using kwt))
      (Plexing.tok_removing (lambda))
      (Plexing.tok_match Plexing.default_match)
      (Plexing.tok_text lexer_text)
      (Plexing.tok_comm None)}))

; Building AST

(type sexpr
 (sum
  (Sacc MLast.loc sexpr sexpr)
  (Sarr MLast.loc (list sexpr))
  (Schar MLast.loc string)
  (Sexpr MLast.loc (list sexpr))
  (Sint MLast.loc string)
  (Sint_l MLast.loc string)
  (Sint_L MLast.loc string)
  (Sint_n MLast.loc string)
  (Sfloat MLast.loc string)
  (Slid MLast.loc string)
  (Slist MLast.loc (list sexpr))
  (Sqid MLast.loc string)
  (Squot MLast.loc string string)
  (Srec MLast.loc (list sexpr))
  (Sstring MLast.loc string)
  (Stid MLast.loc string)
  (Suid MLast.loc string)))

(define loc_of_sexpr
  (lambda_match
   ((or (Sacc loc _ _) (Sarr loc _) (Schar loc _) (Sexpr loc _) (Sint loc _)
     (Sint_l loc _) (Sint_L loc _) (Sint_n loc _) (Sfloat loc _) (Slid loc _)
     (Slist loc _) (Sqid loc _) (Squot loc _ _) (Srec loc _) (Sstring loc _)
     (Stid loc _) (Suid loc _))
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
     ((Sstring loc s) s)
     (se (error se "string"))))

(definerec mod_ident_se
  (lambda_match
   ((Sacc _ se1 se2) (@ (mod_ident_se se1) (mod_ident_se se2)))
   ((Suid _ s) [(rename_id s)])
   ((Slid _ s) [(rename_id s)])
   (se (error se "mod_ident"))))

(define (lident_expr loc s)
  (if (&& (> (String.length s) 1) (= s.[0] '`'))
     (let ((s (String.sub s 1 (- (String.length s) 1)))) <:expr< ` $s$ >>)
     <:expr< $lid:(rename_id s)$ >>))

(definerec*
  (module_expr_se
    (lambda_match
     ((Sexpr loc [(Slid _ "functor") (Suid _ s) se1 se2])
      (let* ((s (rename_id s))
             (mt (module_type_se se1))
             (me (module_expr_se se2)))
         <:module_expr< functor ($uid:s$ : $mt$) -> $me$ >>))
     ((Sexpr loc [(Slid _ "struct") . sl])
      (let ((mel (List.map str_item_se sl)))
         <:module_expr< struct $list:mel$ end >>))
     ((Sexpr loc [se1 se2])
      (let* ((me1 (module_expr_se se1))
             (me2 (module_expr_se se2)))
         <:module_expr< $me1$ $me2$ >>))
     ((Sexpr loc [(Slid _ ":") se1 se2])
      (let* ((me (module_expr_se se1))
             (mt (module_type_se se2)))
         <:module_expr< ($me$ : $mt$) >>))
     ((Sacc loc se1 se2)
      (let* ((me1 (module_expr_se se1))
             (me2 (module_expr_se se2)))
         <:module_expr< $me1$ . $me2$ >>))
     ((Suid loc s) <:module_expr< $uid:(rename_id s)$ >>)
     (se (error se "module expr"))))
  (module_type_se
    (lambda_match
     ((Sexpr loc [(Slid _ "functor") (Suid _ s) se1 se2])
      (let* ((s (rename_id s))
             (mt1 (module_type_se se1))
             (mt2 (module_type_se se2)))
         <:module_type< functor ($uid:s$ : $mt1$) -> $mt2$ >>))
     ((Sexpr loc [(Slid _ "sig") . sel])
      (let ((sil (List.map sig_item_se sel)))
         <:module_type< sig $list:sil$ end >>))
     ((Sexpr loc [(Slid _ "with") se . sel])
      (let* ((mt (module_type_se se))
             (wcl (List.map with_constr_se sel)))
         <:module_type< $mt$ with $list:wcl$ >>))
     ((Sacc loc se1 se2)
      (let* ((mt1 (module_type_se se1))
             (mt2 (module_type_se se2)))
         <:module_type< $mt1$ . $mt2$ >>))
     ((Suid loc s) <:module_type< $uid:(rename_id s)$ >>)
     (se (error se "module type"))))
  (with_constr_se
    (lambda_match
     ((Sexpr loc [(Slid _ "type") se1 se2])
      (let* ((tn (mod_ident_se se1))
             (te (ctyp_se se2)))
         <:with_constr< type $tn$ = $te$ >>))
     (se (error se "with constr"))))
  (sig_item_se
    (lambda_match
     ((Sexpr loc [(Slid _ "open") se])
      (let ((s (mod_ident_se se))) <:sig_item< open $s$ >>))
     ((Sexpr loc [(Slid _ "type") . sel])
      (let ((tdl (type_declaration_list_se sel)))
         <:sig_item< type $list:tdl$ >>))
     ((Sexpr loc [(Slid _ "type*") . sel])
      (let ((tdl (List.map type_declaration_se sel)))
         <:sig_item< type $list:tdl$ >>))
     ((Sexpr loc [(Slid _ "exception") (Suid _ c) . sel])
      (let* ((c (rename_id c))
             (tl (List.map ctyp_se sel)))
         <:sig_item< exception $uid:c$ of $list:tl$ >>))
     ((Sexpr loc [(Slid _ "value") (Slid _ s) se])
      (let* ((s (rename_id s))
             (t (ctyp_se se)))
         <:sig_item< value $lid:s$ : $t$ >>))
     ((Sexpr loc [(Slid _ "external") (Slid _ i) se . sel])
      (let* ((i (rename_id i))
             (pd (List.map string_se sel))
             (t (ctyp_se se)))
         <:sig_item< external $lid:i$ : $t$ = $list:pd$ >>))
     ((Sexpr loc [(Slid _ "module") (Suid _ s) se])
      (let* ((s (rename_id s))
             (mb (module_type_se se)))
         <:sig_item< module $uid:s$ : $mb$ >>))
     ((Sexpr loc [(Slid _ "moduletype") (Suid _ s) se])
      (let* ((s (rename_id s))
             (mt (module_type_se se)))
         <:sig_item< module type $uid:s$ = $mt$ >>))
     (se (error se "sig item"))))
  ((str_item_se se)
    (match se
     ((Sexpr loc [(Slid _ "open") se])
      (let ((s (mod_ident_se se))) <:str_item< open $s$ >>))
     ((Sexpr loc [(Slid _ "type") . sel])
      (let ((tdl (type_declaration_list_se sel)))
         <:str_item< type $list:tdl$ >>))
     ((Sexpr loc [(Slid _ "type*") . sel])
      (let ((tdl (List.map type_declaration_se sel)))
         <:str_item< type $list:tdl$ >>))
     ((Sexpr loc [(Slid _ "exception") (Suid _ c) . sel])
      (let* ((c (rename_id c))
             (tl (List.map ctyp_se sel)))
         <:str_item< exception $uid:c$ of $list:tl$ >>))
     ((Sexpr loc [(Slid _ "exceptionrebind") (Suid _ c) se])
      (let* ((c (rename_id c))
             (id (mod_ident_se se)))
         <:str_item< exception $uid:c$ = $id$ >>))
     ((Sexpr loc [(Slid _ (as (or "define" "definerec") r)) se . sel])
      (let* ((r (= r "definerec"))
             ((values p e) (fun_binding_se se (begin_se loc sel))))
         <:str_item< value $flag:r$ $p$ = $e$ >>))
     ((Sexpr loc [(Slid _ (as (or "define*" "definerec*") r)) . sel])
      (let* ((r (= r "definerec*"))
             (lbs (List.map let_binding_se sel)))
         <:str_item< value $flag:r$ $list:lbs$ >>))
     ((Sexpr loc [(Slid _ "external") (Slid _ i) se . sel])
      (let* ((i (rename_id i))
             (pd (List.map string_se sel))
             (t (ctyp_se se)))
         <:str_item< external $lid:i$ : $t$ = $list:pd$ >>))
     ((Sexpr loc [(Slid _ "module") (Suid _ i) se])
      (let* ((i (rename_id i))
             (mb (module_binding_se se)))
         <:str_item< module $uid:i$ = $mb$ >>))
     ((Sexpr loc [(Slid _ "moduletype") (Suid _ s) se])
      (let* ((s (rename_id s))
             (mt (module_type_se se)))
         <:str_item< module type $uid:s$ = $mt$ >>))
     ((Sexpr loc [(Slid _ "#") (Slid _ s) se])
      (let* ((s (rename_id s))
             (e (expr_se se)))
         <:str_item< # $lid:s$ $e$ >>))
     (_
      (let* ((loc (loc_of_sexpr se))
             (e (expr_se se)))
         <:str_item< $exp:e$ >>))))
  ((module_binding_se se) (module_expr_se se))
  (expr_se
   (lambda_match
    ((Sacc loc se1 se2)
     (let ((e1 (expr_se se1)))
        (match se2
         ((Slist loc [se2])
          (let ((e2 (expr_se se2))) <:expr< $e1$ .[ $e2$ ] >>))
         ((Sexpr loc [se2])
          (let ((e2 (expr_se se2))) <:expr< $e1$ .( $e2$ ) >>))
         (_ (let ((e2 (expr_se se2))) <:expr< $e1$ . $e2$ >>)))))
    ((Slid loc s) (lident_expr loc s))
    ((Suid loc s) <:expr< $uid:(rename_id s)$ >>)
    ((Sint loc s) <:expr< $int:s$ >>)
    ((Sint_l loc s) <:expr< $int32:s$ >>)
    ((Sint_L loc s) <:expr< $int64:s$ >>)
    ((Sint_n loc s) <:expr< $nativeint:s$ >>)
    ((Sfloat loc s) <:expr< $flo:s$ >>)
    ((Schar loc s) <:expr< $chr:s$ >>)
    ((Sstring loc s) <:expr< $str:s$ >>)
    ((Stid loc s) <:expr< ~$(rename_id s)$ >>)
    ((Sqid loc s) <:expr< ?$(rename_id s)$ >>)
    ((Sexpr loc [(Sqid _ s) se])
     (let* ((s (rename_id s)) (e (expr_se se))) <:expr< ?$s$: $e$ >>))
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
           (let* ((a1 (op_apply loc e1 e2 s))
                  (a2 (loop el)))
              <:expr< $a1$ && $a2$ >>)))))
      (loop (List.map expr_se sel))))
    ((Sexpr loc [(Stid _ s) se])
     (let ((e (expr_se se))) <:expr< ~$s$: $e$ >>))
    ((Sexpr loc [(Slid _ "-") se])
     (let ((e (expr_se se))) <:expr< - $e$ >>))
    ((Sexpr loc [(Slid _ "-.") se])
     (let ((e (expr_se se))) <:expr< -. $e$ >>))
    ((Sexpr loc [(Slid _ "if") se se1])
     (let* ((e (expr_se se))
            (e1 (expr_se se1)))
        <:expr< if $e$ then $e1$ else () >>))
    ((Sexpr loc [(Slid _ "if") se se1 se2])
     (let* ((e (expr_se se))
            (e1 (expr_se se1))
            (e2 (expr_se se2)))
        <:expr< if $e$ then $e1$ else $e2$ >>))
    ((Sexpr loc [(Slid _ "cond") . sel])
     (letrec
      ((loop
         (lambda_match
          ([(Sexpr loc [(Slid _ "else") . sel])] (begin_se loc sel))
          ([(Sexpr loc [se1 . sel1]) . sel]
           (let* ((e1 (expr_se se1))
                  (e2 (begin_se loc sel1))
                  (e3 (loop sel)))
              <:expr< if $e1$ then $e2$ else $e3$ >>))
          ([] <:expr< () >>)
          ([se . _] (error se "cond clause")))))
      (loop sel)))
    ((Sexpr loc [(Slid _ "while") se . sel])
     (let* ((e (expr_se se))
            (el (List.map expr_se sel)))
        <:expr< while $e$ do { $list:el$ } >>))
    ((Sexpr loc [(Slid _ "for") (Slid _ i) se1 se2 . sel])
     (let* ((i (rename_id i))
            (e1 (expr_se se1))
            (e2 (expr_se se2))
            (el (List.map expr_se sel)))
        <:expr< for $lid:i$ = $e1$ to $e2$ do { $list:el$ } >>))
    ((Sexpr loc [(Slid _ "fordown") (Slid _ i) se1 se2 . sel])
     (let* ((i (rename_id i))
            (e1 (expr_se se1))
            (e2 (expr_se se2))
            (el (List.map expr_se sel)))
        <:expr< for $lid:i$ = $e1$ downto $e2$ do { $list:el$ } >>))
    ((Sexpr loc [(Slid loc1 "lambda")]) <:expr< fun [] >>)
    ((Sexpr loc [(Slid loc1 "lambda") sep . sel])
     (let ((e (begin_se loc1 sel)))
        (match (ipatt_opt_se sep)
         ((Left p) <:expr< fun $p$ -> $e$ >>)
         ((Right (values se sel))
          (List.fold_right
           (lambda (se e)
             (let ((p (ipatt_se se))) <:expr< fun $p$ -> $e$ >>))
           [se . sel] e)))))
    ((Sexpr loc [(Slid _ "lambda_match") . sel])
     (let ((pel (List.map (match_case loc) sel)))
        <:expr< fun [ $list:pel$ ] >>))
    ((Sexpr loc [(Slid _ (as (or "let" "letrec") r)) . sel])
     (match sel
      ([(Sexpr _ sel1) . sel2]
       (let* ((r (= r "letrec"))
              (lbs (List.map let_binding_se sel1))
              (e (begin_se loc sel2)))
          <:expr< let $flag:r$ $list:lbs$ in $e$ >>))
      ([(Slid _ n) (Sexpr _ sl) . sel]
       (let* ((n (rename_id n))
              ((values pl el)
                (List.fold_right
                 (lambda (se (values pl el))
                   (match se
                          ((Sexpr _ [se1 se2])
                           (values [(patt_se se1) . pl]
                                   [(expr_se se2) . el]))
                          (se (error se "named let"))))
                 sl (values [] [])))
              (e1
                (List.fold_right
                 (lambda (p e) <:expr< fun $p$ -> $e$ >>)
                 pl (begin_se loc sel)))
              (e2
                (List.fold_left
                 (lambda (e1 e2) <:expr< $e1$ $e2$ >>)
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
    ((Sexpr loc [(Slid _ "letmodule") (Suid _ s) se1 se2])
     (let* ((me (module_expr_se se1))
            (e (expr_se se2)))
        <:expr< let module $s$ = $me$ in $e$ >>))
    ((Sexpr loc [(Slid _ "match") se . sel])
     (let* ((e (expr_se se))
            (pel (List.map (match_case loc) sel)))
        <:expr< match $e$ with [ $list:pel$ ] >>))
    ((Sexpr loc [(Slid _ "parser") . sel])
     (let ((e
             (match sel
              ([(as (Slid _ _) se) . sel]
               (let* ((p (patt_se se))
                      (pc (parser_cases_se loc sel)))
                  <:expr< let $p$ = Stream.count $lid:strm_n$ in $pc$ >>))
              (_ (parser_cases_se loc sel)))))
        <:expr< fun ($lid:strm_n$ : Stream.t _) -> $e$ >>))
    ((Sexpr loc [(Slid _ "match_with_parser") se . sel])
     (let* ((me (expr_se se))
            ((values bpo sel)
              (match sel
               ([(as (Slid _ _) se) . sel] (values (Some (patt_se se)) sel))
               (_ (values None sel))))
            (pc (parser_cases_se loc sel))
            (e
              (match bpo
               ((Some bp)
                <:expr< let $bp$ = Stream.count $lid:strm_n$ in $pc$ >>)
               (None pc))))
        (match me
         ((when <:expr< $lid:x$ >> (= x strm_n)) e)
         (_ <:expr< let ($lid:strm_n$ : Stream.t _) = $me$ in $e$ >>))))
    ((Sexpr loc [(Slid _ "try") se . sel])
     (let* ((e (expr_se se))
            (pel (List.map (match_case loc) sel)))
        <:expr< try $e$ with [ $list:pel$ ] >>))
    ((Sexpr loc [(Slid _ "begin") . sel])
     (let ((el (List.map expr_se sel))) <:expr< do { $list:el$ } >>))
    ((Sexpr loc [(Slid _ ":=") se1 se2])
     (let* ((e1 (expr_se se1))
            (e2 (expr_se se2)))
        <:expr< $e1$ := $e2$ >>))
    ((Sarr loc sel)
     (let ((el (List.map expr_se sel))) <:expr< [| $list:el$ |] >>))
    ((Sexpr loc [(Slid _ "values") . sel])
     (let ((el (List.map expr_se sel))) <:expr< ( $list:el$ ) >>))
    ((Srec loc [(Slid _ "with") se . sel])
     (let* ((e (expr_se se))
            (lel (List.map (label_expr_se loc) sel)))
        <:expr< { ($e$) with $list:lel$ } >>))
    ((Srec loc sel)
     (let ((lel (List.map (label_expr_se loc) sel)))
        <:expr< { $list:lel$ } >>))
    ((Sexpr loc [(Slid _ ":") se1 se2])
     (let* ((e (expr_se se1)) (t (ctyp_se se2))) <:expr< ( $e$ : $t$ ) >>))
    ((Sexpr loc [se]) (let ((e (expr_se se))) <:expr< $e$ () >>))
    ((Sexpr loc [(Slid _ "assert") se])
       (let ((e (expr_se se))) <:expr< assert $e$ >>))
    ((Sexpr loc [(Slid _ "lazy") se])
       (let ((e (expr_se se))) <:expr< lazy $e$ >>))
    ((Sexpr loc [se . sel])
     (List.fold_left
      (lambda (e se) (let ((e1 (expr_se se))) <:expr< $e$ $e1$ >>))
      (expr_se se) sel))
    ((Slist loc sel)
     (letrec ((loop
                (lambda_match
                 ([] <:expr< [] >>)
                 ([se1 (Slid _ ".") se2]
                  (let* ((e (expr_se se1))
                         (el (expr_se se2)))
                    <:expr< [$e$ :: $el$] >>))
                 ([se . sel]
                  (let* ((e (expr_se se))
                         (el (loop sel)))
                    <:expr< [$e$ :: $el$] >>)))))
          (loop sel)))
    ((Squot loc typ txt)
     (Pcaml.handle_expr_quotation loc (values typ txt)))))
  ((begin_se loc)
   (lambda_match
    ([] <:expr< () >>)
    ([se] (expr_se se))
    ((sel)
      (let* ((el (List.map expr_se sel))
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
                   ((loc
                     (Ploc.encl (loc_of_sexpr se) (MLast.loc_of_expr e)))
                    (p (ipatt_se se)))
                   <:expr< fun $p$ -> $e$ >>))
                  sel e)))
             (values p e)))
            ((Right _) (values (ipatt_se se) e))))
          ((_) (values (ipatt_se se) e))))
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
  ((parser_cases_se loc)
   (lambda_match
    ([] <:expr< raise Stream.Failure >>)
    ([(Sexpr loc [(Sexpr _ spsel) . act]) . sel]
      (let* ((ekont (lambda _ (parser_cases_se loc sel)))
             (act (match act
                         ([se] (expr_se se))
                         ([sep se]
                               (let* ((p (patt_se sep))
                                      (e (expr_se se)))
                        <:expr< let $p$ = Stream.count $lid:strm_n$ in $e$ >>))
                         (_ (error_loc loc "parser_case")))))
        (stream_pattern_se loc act ekont spsel)))
    ([se . _]
         (error se "parser_case"))))
  ((stream_pattern_se loc act ekont)
   (lambda_match
    ([] act)
    ([se . sel]
         (let* ((ckont (lambda err <:expr< raise (Stream.Error $err$) >>))
                (skont (stream_pattern_se loc act ckont sel)))
           (stream_pattern_component skont ekont <:expr< "" >> se)))))
  ((stream_pattern_component skont ekont err)
   (lambda_match
    ((Sexpr loc [(Slid _ "`") se . wol])
     (let* ((wo (match wol
                       ([se] (Some (expr_se se)))
                       ([] None)
                       (_ (error_loc loc "stream_pattern_component"))))
            (e (peek_fun loc))
            (p (patt_se se))
            (j (junk_fun loc))
            (k (ekont err)))
       <:expr< match $e$ $lid:strm_n$ with
               [ Some $p$ $opt:wo$ -> do { $j$ $lid:strm_n$ ; $skont$ }
               | _ -> $k$ ] >>))
    ((Sexpr loc [se1 se2])
     (let* ((p (patt_se se1))
            (e (let ((e (expr_se se2)))
       <:expr< try Some ($e$ $lid:strm_n$) with [ Stream.Failure -> None ] >>))
            (k (ekont err)))
       <:expr< match $e$ with [ Some $p$ -> $skont$ | _ -> $k$ ] >>))
    ((Sexpr loc [(Slid _ "?") se1 se2])
     (stream_pattern_component skont ekont (expr_se se2) se1))
    ((Slid loc s)
     (let ((s (rename_id s)))
        <:expr< let $lid:s$ = $lid:strm_n$ in $skont$ >>))
    (se
     (error se "stream_pattern_component"))))
  (patt_se
   (lambda_match
    ((Sacc loc se1 se2)
     (let* ((p1 (patt_se se1)) (p2 (patt_se se2))) <:patt< $p1$ . $p2$ >>))
    ((Slid loc "_") <:patt< _ >>)
    ((Slid loc s) <:patt< $lid:(rename_id s)$ >>)
    ((Suid loc s) <:patt< $uid:(rename_id s)$ >>)
    ((Sint loc s) <:patt< $int:s$ >>)
    ((Sint_l loc s) <:patt< $int32:s$ >>)
    ((Sint_L loc s) <:patt< $int64:s$ >>)
    ((Sint_n loc s) <:patt< $nativeint:s$ >>)
    ((Sfloat loc s) <:patt< $flo:s$ >>)
    ((Schar loc s) <:patt< $chr:s$ >>)
    ((Sstring loc s) <:patt< $str:s$ >>)
    ((Stid loc s) (error_loc loc "patt"))
    ((Sqid loc _) (error_loc loc "patt"))
    ((Srec loc sel)
     (let ((lpl (List.map (label_patt_se loc) sel)))
        <:patt< { $list:lpl$ } >>))
    ((Sexpr loc [(Slid _ ":") se1 se2])
     (let* ((p (patt_se se1)) (t (ctyp_se se2))) <:patt< ($p$ : $t$) >>))
    ((Sexpr loc [(Slid _ "or") se . sel])
     (List.fold_left
      (lambda (p se) (let ((p1 (patt_se se))) <:patt< $p$ | $p1$ >>))
      (patt_se se) sel))
    ((Sexpr loc [(Slid _ "range") se1 se2])
     (let* ((p1 (patt_se se1)) (p2 (patt_se se2))) <:patt< $p1$ .. $p2$ >>))
    ((Sarr loc sel)
     (let ((pl (List.map patt_se sel))) <:patt< [| $list:pl$ |] >>))
    ((Sexpr loc [(Slid _ "values") . sel])
     (let ((pl (List.map patt_se sel))) <:patt< ( $list:pl$ ) >>))
    ((Sexpr loc [(Slid _ "as") se1 se2])
     (let* ((p1 (patt_se se1))
            (p2 (patt_se se2)))
       <:patt< ($p1$ as $p2$) >>))
    ((Sexpr loc [se . sel])
     (List.fold_left
      (lambda (p se) (let ((p1 (patt_se se))) <:patt< $p$ $p1$ >>))
      (patt_se se) sel))
    ((Sexpr loc []) <:patt< () >>)
    ((Slist loc sel)
     (letrec ((loop
                (lambda_match
                 ([] <:patt< [] >>)
                 ([se1 (Slid _ ".") se2]
                  (let* ((p (patt_se se1))
                         (pl (patt_se se2)))
                    <:patt< [$p$ :: $pl$] >>))
                 ([se . sel]
                  (let* ((p (patt_se se))
                         (pl (loop sel)))
                    <:patt< [$p$ :: $pl$] >>)))))
          (loop sel)))
    ((Squot loc typ txt)
     (Pcaml.handle_patt_quotation loc (values typ txt)))))
  ((ipatt_se se)
   (match (ipatt_opt_se se)
          ((Left p) p)
          ((Right (values se _)) (error se "ipatt"))))
  (ipatt_opt_se
   (lambda_match
    ((Slid loc "_") (Left <:patt< _ >>))
    ((Slid loc s) (Left <:patt< $lid:(rename_id s)$ >>))
    ((Stid loc s) (Left <:patt< ~$(rename_id s)$ >>))
    ((Sqid loc s) (Left <:patt< ?$(rename_id s)$ >>))
    ((Sexpr loc [(Sqid _ s) se])
     (let* ((s (rename_id s))
            (e (expr_se se)))
        (Left <:patt< ? ( $lid:s$ = $e$ ) >>)))
    ((Sexpr loc [(Stid _ s) se])
     (let* ((s (rename_id s))
            (p (patt_se se)))
        (Left <:patt< ~$s$:$p$ >>)))
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
     (let (((values n1 loc1 tpl)
            (match se1
                   ((Sexpr _ [(Slid loc n) . sel])
                    (values (rename_id n) loc (List.map type_param_se sel)))
                   ((Slid loc n)
                    (values (rename_id n) loc []))
                   ((se)
                    (error se "type declaration")))))
       {(MLast.tdNam (values loc1 <:vala< n1 >>))
        (MLast.tdPrm <:vala< tpl >>) (MLast.tdPrv <:vala< False >>)
        (MLast.tdDef (ctyp_se se2)) (MLast.tdCon <:vala< [] >>)}))
    (se (error se "type_declaration"))))
  (type_declaration_list_se
   (lambda_match
    ([se1 se2 . sel]
     (let (((values n1 loc1 tpl)
            (match se1
                   ((Sexpr _ [(Slid loc n) . sel])
                    (values (rename_id n) loc (List.map type_param_se sel)))
                   ((Slid loc n)
                    (values (rename_id n) loc []))
                   ((se)
                    (error se "type declaration")))))
       (let ((td {(MLast.tdNam (values loc1 <:vala< n1 >>))
                  (MLast.tdPrm <:vala< tpl >>) (MLast.tdPrv <:vala< False >>)
                  (MLast.tdDef (ctyp_se se2)) (MLast.tdCon <:vala< [] >>)}))
            [td . (type_declaration_list_se sel)])))
    ([] [])
    ([se . _] (error se "type_declaration"))))
  ((type_param_se se)
   (match se
    ((when (Slid _ s) (and (>= (String.length s) 2) (= s.[0] ''')))
      (let ((s (String.sub s 1 (- (String.length s) 1))))
       (values <:vala< s >> (values False False))))
    ((when (Slid _ s) (and (>= (String.length s) 3) (= s.[1] ''')))
      (let
       ((vara
         (cond
          ((= s.[0] '+') (values True False))
          ((= s.[0] '-') (values False True))
          (else (error se "type_param"))))
        (s (String.sub s 2 (- (String.length s) 2))))
       (values <:vala< s >> vara)))
    (se
     (error se "type_param"))))
  (ctyp_se
   (lambda_match
    ((Sexpr loc [(Slid _ "sum") . sel])
     (let ((cdl (List.map constructor_declaration_se sel)))
       <:ctyp< [ $list:cdl$ ] >>))
    ((Srec loc sel)
     (let ((ldl (List.map label_declaration_se sel)))
       <:ctyp< { $list:ldl$ } >>))
    ((Sexpr loc [(Slid _ "->") . (as [_ _ . _] sel)])
     (letrec
        ((loop
            (lambda_match
             ([] (assert False))
             ([se] (ctyp_se se))
             ([se . sel]
               (let* ((t1 (ctyp_se se))
                      (loc (Ploc.encl (loc_of_sexpr se) loc))
                      (t2 (loop sel)))
                   <:ctyp< $t1$ -> $t2$ >>)))))
        (loop sel)))
    ((Sexpr loc [(Slid _ "*") . sel])
     (let ((tl (List.map ctyp_se sel))) <:ctyp< ($list:tl$) >>))
    ((Sexpr loc [(Slid _ "==") se1 se2])
     (let* ((t1 (ctyp_se se1)) (t2 (ctyp_se se2))) <:ctyp< $t1$ == $t2$ >>))
    ((Sexpr loc [(Slid _ "objectvar")]) <:ctyp< < .. > >>)
    ((Sexpr loc [se . sel])
     (List.fold_left
      (lambda (t se) (let ((t2 (ctyp_se se))) <:ctyp< $t$ $t2$ >>))
      (ctyp_se se) sel))
    ((Sacc loc se1 se2)
     (let* ((t1 (ctyp_se se1)) (t2 (ctyp_se se2))) <:ctyp< $t1$ . $t2$ >>))
    ((Slid loc "_") <:ctyp< _ >>)
    ((Slid loc s)
     (if (= s.[0] ''')
         (let ((s (String.sub s 1 (- (String.length s) 1))))
           <:ctyp< '$s$ >>)
         <:ctyp< $lid:(rename_id s)$ >>))
    ((Suid loc s) <:ctyp< $uid:(rename_id s)$ >>)
    (se (error se "ctyp"))))
  (constructor_declaration_se
   (lambda_match
    ((Sexpr loc [(Suid _ ci) . sel])
     (values loc <:vala< (rename_id ci) >>
        <:vala< (List.map ctyp_se sel) >>))
    (se
     (error se "constructor_declaration"))))
  (label_declaration_se
   (lambda_match
    ((Sexpr loc [(Slid _ lab) (Slid _ "mutable") se])
     (values loc (rename_id lab) True (ctyp_se se)))
    ((Sexpr loc [(Slid _ lab) se])
     (values loc (rename_id lab) False (ctyp_se se)))
    (se
     (error se "label_declaration")))))

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
 (Grammar.Unsafe.clear_entry module_type)
 (Grammar.Unsafe.clear_entry module_expr)
 (Grammar.Unsafe.clear_entry sig_item)
 (Grammar.Unsafe.clear_entry str_item)
 (Grammar.Unsafe.clear_entry expr)
 (Grammar.Unsafe.clear_entry patt)
 (Grammar.Unsafe.clear_entry ctyp)
 (Grammar.Unsafe.clear_entry let_binding)
 (Grammar.Unsafe.clear_entry type_declaration)
 (Grammar.Unsafe.clear_entry class_type)
 (Grammar.Unsafe.clear_entry class_expr)
 (Grammar.Unsafe.clear_entry class_sig_item)
 (Grammar.Unsafe.clear_entry class_str_item))

(:= Pcaml.parse_interf.val (Grammar.Entry.parse interf))
(:= Pcaml.parse_implem.val (Grammar.Entry.parse implem))

(define sexpr (Grammar.Entry.create gram "sexpr"))

EXTEND
  GLOBAL : implem interf top_phrase use_file str_item sig_item expr
    patt sexpr /
  implem :
    [ [ "#" / se = sexpr ->
          (let (((values n dp) (directive_se se)))
             (values [(values <:str_item< # $lid:n$ $opt:dp$ >> loc)] True))
      | si = str_item / x = SELF ->
          (let* (((values sil stopped) x)
                 (loc (MLast.loc_of_str_item si)))
             (values [(values si loc) . sil] stopped))
      | EOI -> (values [] False) ] ]
  /
  interf :
    [ [ "#" / se = sexpr ->
          (let (((values n dp) (directive_se se)))
             (values [(values <:sig_item< # $lid:n$ $opt:dp$ >> loc)] True))
      | si = sig_item / x = SELF ->
          (let* (((values sil stopped) x)
                 (loc (MLast.loc_of_sig_item si)))
             (values [(values si loc) . sil] stopped))
      | EOI -> (values [] False) ] ]
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
  str_item :
    [ [ se = sexpr -> (str_item_se se)
      | e = expr -> <:str_item< $exp:e$ >> ] ]
  /
  sig_item :
    [ [ se = sexpr -> (sig_item_se se) ] ]
  /
  expr :
    [ "top"
      [ se = sexpr -> (expr_se se) ] ]
  /
  patt :
    [ [ se = sexpr -> (patt_se se) ] ]
  /
  sexpr :
    [ [ se1 = sexpr / DOT / se2 = sexpr -> (Sacc loc se1 se2) ]
    | [ "(" / sl = LIST0 sexpr / ")" -> (Sexpr loc sl)
      | "[" / sl = LIST0 sexpr / "]" -> (Slist loc sl)
      | "{" / sl = LIST0 sexpr / "}" -> (Srec loc sl)
      | "#(" / sl = LIST0 sexpr / ")" -> (Sarr loc sl)
      | a = pa_extend_keyword -> (Slid loc a)
      | s = LIDENT -> (Slid loc s)
      | s = UIDENT -> (Suid loc s)
      | s = TILDEIDENT -> (Stid loc s)
      | s = QUESTIONIDENT -> (Sqid loc s)
      | s = INT -> (Sint loc s)
      | s = INT_l -> (Sint_l loc s)
      | s = INT_L -> (Sint_L loc s)
      | s = INT_n -> (Sint_n loc s)
      | s = FLOAT -> (Sfloat loc s)
      | s = CHAR -> (Schar loc s)
      | s = STRING -> (Sstring loc s)
      | s = SPACEDOT -> (Slid loc ".")
      | s = QUOT ->
          (let* ((i (String.index s ':'))
                 (typ (String.sub s 0 i))
                 (txt (String.sub s (+ i 1) (- (- (String.length s) i) 1))))
            (Squot loc typ txt))
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
