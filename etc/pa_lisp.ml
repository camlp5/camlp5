;; camlp5 ./pa_lispr.cmo pa_extend.cmo q_MLast.cmo pr_dump.cmo
;; pa_lisp.ml,v
;; Copyright (c) INRIA 2007-2017

(open Pcaml)
(open Versdep)

;; Buffer

(module Buff
 (struct
  (value buff (ref (string_create 80)))
  (value store (lambda (len x)
                 (if (>= len (string_length buff.val))
                     (:= buff.val
                         (string_cat buff.val
                            (string_create (string_length buff.val)))))
                 (string_set buff.val len x)
                 (succ len)))
  (value get (lambda len (bytes_to_string (string_sub buff.val 0 len))))))

;; Lexer

(value rec skip_to_eol
       (lambda len
        (parser
         (((` (as (or '\n' '\r') c))) (Buff.store len c))
         (((` c) s) (skip_to_eol (Buff.store len c) s)))))

(value no_ident (list '(' ')' ' ' '\t' '\n' '\r' ';'))

(value rec ident
       (lambda len
         (parser
          (((` x (not (List.mem x no_ident))) s)
           (ident (Buff.store len x) s))
          (()
           (Buff.get len)))))

(value rec
       string (lambda len
                (parser
                 (((` '"')) (Buff.get len))
                 (((` '\\') (` c) s)
                  (string (Buff.store (Buff.store len '\\') c) s))
                 (((` x) s) (string (Buff.store len x) s)))))

(value rec
       number (lambda len
                (parser
                 (((` (as (range '0' '9') c)) s)
                  (number (Buff.store len c) s))
                 (()
                  (, "INT" (Buff.get len))))))

(value char_or_quote_id
       (lambda x
         (parser
          (((` ''')) (, "CHAR" (String.make 1 x)))
          ((s)
           (let ((len (Buff.store (Buff.store 0 ''') x)))
             (, "LIDENT" (ident len s)))))))

(value rec char
       (lambda len
         (parser
          (((` ''')) len)
          (((` x) s) (char (Buff.store len x) s)))))

(value quote
       (parser
        (((` '\\') (len (char (Buff.store 0 '\\'))))
         (, "CHAR" (Buff.get len)))
        (((` x) s) (char_or_quote_id x s))))

(value rec
 next_token_after_spaces
 (lambda kwt
   (parser bp
           (((` '(')) (, (, "" "(") (, bp (+ bp 1))))
           (((` ')')) (, (, "" ")") (, bp (+ bp 1))))
           (((` '"') (s (string 0))) ep (, (, "STRING" s) (, bp ep)))
           (((` ''') (tok quote)) ep (, tok (, bp ep)))
           (((` '<') (tok less)) ep (, tok (, bp ep)))
           (((` (as (range '0' '9') c)) (n (number (Buff.store 0 c)))) ep
            (, n (, bp ep)))
           (((` x) (s (ident (Buff.store 0 x)))) ep
            (let ((con (try (progn (: (Hashtbl.find kwt s) unit) "")
                            (Not_found
                             (match x
                                    ((range 'A' 'Z') "UIDENT")
                                    ((_) "LIDENT"))))))
              (, (, con s) (, bp ep))))
           (() (, (, "EOI" "") (, bp (+ bp 1))))))
 less
 (parser
  (((` ':') (lab (label 0)) (? (` '<') "'<' expected") (q (quotation 0)))
   (, "QUOT" (^ lab (^ ":" q))))
  (() (, "LIDENT" "<")))
 label
 (lambda len
   (parser
    (((` (as (or (range 'a' 'z') (range 'A' 'Z') '_') c)) s)
     (label (Buff.store len c) s))
    (() (Buff.get len))))
 quotation
 (lambda len
   (parser
    (((` '>') s) (quotation_greater len s))
    (((` x) s) (quotation (Buff.store len x) s))
    (() (failwith "quotation not terminated"))))
 quotation_greater
 (lambda len
   (parser
    (((` '>')) (Buff.get len))
    (((a (quotation (Buff.store len '>')))) a))))

(value get_buff (lambda (len _) (Buff.get len)))

(value rec
 lexer
 (lambda (len kwt)
  (parser bp
   (((` (as (or ' ' '\t' '\n' '\r') c)) s) (lexer (Buff.store len c) kwt s))
   (((` ';') (a (semi (Buff.store len ';') kwt bp))) a)
   (((comm  (get_buff len)) (a (next_token_after_spaces kwt))) (, comm a))))
 semi
 (lambda (len kwt bp)
   (parser
    (((` ';') (len (skip_to_eol (Buff.store len ';'))) s) (lexer len kwt s))
    (() ep (, (Buff.get len) (, (, "" ";") (, bp ep)))))))

(value lexer_using
       (lambda (kwt (, con prm))
         (match con
                ((or "CHAR" "EOI" "INT" "LIDENT" "QUOT" "STRING" "UIDENT") ())
                ((or "ANTIQUOT" "ANTIQUOT_LOC") ())
                (("")
                 (try (Hashtbl.find kwt prm)
                      (Not_found (Hashtbl.add kwt prm ()))))
                (_ (raise
                    (Plexing.Error
                     (^ "the constructor \""
                        (^ con "\" is not recognized by Plexer"))))))))

(value lexer_text
       (lambda (, con prm)
         (if (= con "") (^ "'" (^ prm "'"))
           (if (= prm "") con
             (^ con (^ " \"" (^ prm "\"")))))))

(value lexer_gmake
       (lambda ()
         (let ((kwt (Hashtbl.create 89))
               (lexer2
                (lambda (kwt (, s _ _))
                  (let (((, comm (, t loc)) (lexer 0 kwt s)))
                    (, t
                       (Ploc.make_loc Plexing.input_file.val 0 0 loc comm))))))
           ({}
            (Plexing.tok_func (Plexing.lexer_func_of_parser (lexer2 kwt)))
            (Plexing.tok_using (lexer_using kwt))
            (Plexing.tok_removing (lambda))
            (Plexing.tok_match Plexing.default_match)
            (Plexing.tok_text lexer_text)
            (Plexing.tok_comm None)
            (Plexing.kwds (Hashtbl.create 23))))))

;; Building AST

(type sexpr (sum
             (Sexpr MLast.loc (list sexpr))
             (Satom MLast.loc atom string)
             (Squot MLast.loc string string))
      atom (sum (Alid) (Auid) (Aint) (Achar) (Astring)))

(value error_loc
       (lambda (loc err)
         (Ploc.raise loc (Stream.Error (^ err " expected")))))
(value error
       (lambda (se err)
         (let ((loc (match se
                           ((or (Satom loc _ _) (Sexpr loc _) (Squot loc _ _))
                            loc))))
           (error_loc loc err))))

(value expr_id
       (lambda (loc s)
         (match ([] s 0)
                ((range 'A' 'Z') <:expr< $uid:s$ >>)
                (_ <:expr< $lid:s$ >>))))

(value patt_id
       (lambda (loc s)
         (match ([] s 0)
                ((range 'A' 'Z') <:patt< $uid:s$ >>)
                (_ <:patt< $lid:s$ >>))))

(value ctyp_id
       (lambda (loc s)
         (match ([] s 0)
                (''' (let ((s (String.sub s 1 (- (String.length s) 1))))
                       <:ctyp< '$s$ >>))
                ((range 'A' 'Z')
                   (failwith "must not call ctyp_id with UIDs"))
                (_ <:ctyp< $lid:s$ >>))))

(value split_at_dots
  (lambda (loc s)
   (let rec
     ((loop (lambda (ibeg i)
              (if (= i (String.length s))
                  (if (> i ibeg)
                      (list (String.sub s ibeg (- i ibeg)))
                    (Ploc.raise (Ploc.sub loc (- i 1) 1)
                                    (Stream.Error "ctyp expected")))
                (if (= ([] s i) '.')
                    (if (> i ibeg)
                        (let* ((t1 (list (String.sub s ibeg (- i ibeg))))
                               (t2 (loop (+ i 1) (+ i 1))))
                          (List.append t1 t2))
                      (Ploc.raise (Ploc.sub loc (- i 1) 1)
                                      (Stream.Error "ctyp expected")))
                  (loop ibeg (+ i 1)))))))
     (loop 0 0))
  ))

(value split_last
  (lambda (l)
    (match (List.rev l)
      ((list) (failwith "split_last: empty list"))
      ((list h :: t) (, (List.rev t) h))
    )
  ))

(value capitalized
  (lambda (s)
     (match ([] s 0) ((range 'A' 'Z') True) (_ False))
  ))

(value strm_n "strm__")
(value peek_fun (lambda loc <:expr< Stream.peek >>))
(value junk_fun (lambda loc <:expr< Stream.junk >>))

(value rec
 module_expr_se
 (lambda_match
  ((Sexpr loc (list (Satom _ Alid "struct") :: sl))
   (let ((mel (List.map str_item_se sl)))
     <:module_expr< struct $list:mel$ end >>))
  ((Satom loc Auid s)
   <:module_expr< $uid:s$ >>)
  ((se)
   (error se "module expr")))
 str_item_se
 (lambda se
   (match se
          ((or (Satom loc _ _) (Squot loc _ _))
           (let ((e (expr_se se))) <:str_item< $exp:e$ >>))
          ((Sexpr loc (list (Satom _ Alid "module") (Satom _ Auid i) se))
           (let ((mb (module_binding_se se)))
             <:str_item< module $uid:i$ = $mb$ >>))
          ((Sexpr loc (list (Satom _ Alid "open") (Satom _ Auid s)))
             <:str_item< open $uid:s$ >>)
          ((Sexpr loc (list (Satom _ Alid "type") :: sel))
           (let ((tdl (type_declaration_list_se sel)))
             <:str_item< type $list:tdl$ >>))
          ((Sexpr loc (list (Satom _ Alid "value") :: sel))
           (let* (((, r sel)
                   (match sel
                          ((list (Satom _ Alid "rec") :: sel) (, True sel))
                          ((_) (, False sel))))
                  (lbs (value_binding_se sel)))
             <:str_item< value $flag:r$ $list:lbs$ >>))
          ((Sexpr loc _)
           (let ((e (expr_se se)))
             <:str_item< $exp:e$ >>))))
 value_binding_se
 (lambda_match
  ((list se1 se2 :: sel)
   (list (, (ipatt_se se1) (expr_se se2) <:vala< (list) >>) :: (value_binding_se sel)))
  ((list) (list))
  ((list se :: _) (error se "value_binding")))
 module_binding_se
 (lambda se (module_expr_se se))
 expr_se
 (lambda_match
  ((Satom loc (or Alid Auid) s)
   (expr_ident_se loc s))
  ((Satom loc Aint s)
   <:expr< $int:s$ >>)
  ((Satom loc Achar s)
   (<:expr< $chr:s$ >>))
  ((Satom loc Astring s)
   <:expr< $str:s$ >>)
  ((Sexpr loc (list))
   <:expr< () >>)
  ((Sexpr loc (list (Satom _ Alid "if") se se1))
   (let* ((e (expr_se se))
          (e1 (expr_se se1)))
     <:expr< if $e$ then $e1$ else () >>))
  ((Sexpr loc (list (Satom _ Alid "if") se se1 se2))
   (let* ((e (expr_se se))
          (e1 (expr_se se1))
          (e2 (expr_se se2)))
     <:expr< if $e$ then $e1$ else $e2$ >>))
  ((Sexpr loc (list (Satom loc1 Alid "lambda"))) <:expr< fun [] >>)
  ((Sexpr loc (list (Satom loc1 Alid "lambda") sep :: sel))
   (let ((e (progn_se loc1 sel)))
     (match (ipatt_opt_se sep)
            ((Left p) <:expr< fun $p$ -> $e$ >>)
            ((Right (, se sel))
             (List.fold_right
              (lambda (se e)
                (let ((p (ipatt_se se))) <:expr< fun $p$ -> $e$ >>))
              (list se :: sel) e)))))
  ((Sexpr loc (list (Satom _ Alid "lambda_match") :: sel))
   (let ((pel (List.map (match_case loc) sel)))
     <:expr< fun [ $list:pel$ ] >>))
  ((Sexpr loc (list (Satom _ Alid "let") :: sel))
   (let (((, r sel)
          (match sel
                 ((list (Satom _ Alid "rec") :: sel) (, True sel))
                 ((_) (, False sel)))))
     (match sel
            ((list (Sexpr _ sel1) :: sel2)
             (let* ((lbs (List.map let_binding_se sel1))
                    (e (progn_se loc sel2)))
               <:expr< let $flag:r$ $list:lbs$ in $e$ >>))
            ((list se :: _) (error se "let_binding"))
            ((_) (error_loc loc "let_binding")))))
  ((Sexpr loc (list (Satom _ Alid "let*") :: sel))
   (match sel
          ((list (Sexpr _ sel1) :: sel2)
           (List.fold_right
            (lambda (se ek)
              (let (((, p e _) (let_binding_se se)))
                <:expr< let $p$ = $e$ in $ek$ >>))
            sel1 (progn_se loc sel2)))
          ((list se :: _) (error se "let_binding"))
          ((_) (error_loc loc "let_binding"))))
  ((Sexpr loc (list (Satom _ Alid "match") se :: sel))
   (let* ((e (expr_se se))
          (pel (List.map (match_case loc) sel)))
     <:expr< match $e$ with [ $list:pel$ ] >>))
  ((Sexpr loc (list (Satom _ Alid "parser") :: sel))
   (let ((e (match sel
                   ((list (as (Satom _ _ _) se) :: sel)
                    (let* ((p (patt_se se))
                           (pc (parser_cases_se loc sel)))
                      <:expr< let $p$ = Stream.count $lid:strm_n$ in $pc$ >>))
                   (_ (parser_cases_se loc sel)))))
     <:expr< fun ($lid:strm_n$ : Stream.t _) -> $e$ >>))
  ((Sexpr loc (list (Satom _ Alid "try") se :: sel))
   (let* ((e (expr_se se))
          (pel (List.map (match_case loc) sel)))
     <:expr< try $e$ with [ $list:pel$ ] >>))
  ((Sexpr loc (list (Satom _ Alid "progn") :: sel))
   (let ((el (List.map expr_se sel)))
     <:expr< do { $list:el$ } >>))
  ((Sexpr loc (list (Satom _ Alid "while") se :: sel))
   (let* ((e (expr_se se))
          (el (List.map expr_se sel)))
     <:expr< while $e$ do { $list:el$ } >>))
  ((Sexpr loc (list (Satom _ Alid ":=") se1 se2))
   (let ((e2 (expr_se se2)))
     (match (expr_se se1)
            (<:expr< $uid:"()"$ $e1$ $i$ >> <:expr< $e1$.($i$) := $e2$ >>)
            (e1 <:expr< $e1$ := $e2$ >>))))
  ((Sexpr loc (list (Satom _ Alid "[]") se1 se2))
   (let* ((e1 (expr_se se1)) (e2 (expr_se se2))) <:expr< $e1$.[$e2$] >>))
  ((Sexpr loc (list (Satom _ Alid ",") :: sel))
   (let ((el (List.map expr_se sel))) <:expr< ( $list:el$ ) >>))
  ((Sexpr loc (list (Satom _ Alid "{}") :: sel))
   (let ((lel (List.map (label_expr_se loc) sel))) <:expr< { $list:lel$ } >>))
  ((Sexpr loc (list (Satom _ Alid ":") se1 se2))
   (let* ((e (expr_se se1))
          (t (ctyp_se se2)))
     <:expr< ( $e$ : $t$ ) >>))
  ((Sexpr loc (list (Satom _ Alid "list") :: sel))
   (let rec ((loop
              (lambda_match
               ((list) <:expr< [] >>)
               ((list se1 (Satom _ Alid "::") se2)
                (let* ((e (expr_se se1))
                       (el (expr_se se2)))
                  <:expr< [$e$ :: $el$] >>))
               ((list se :: sel)
                (let* ((e (expr_se se))
                       (el (loop sel)))
                  <:expr< [$e$ :: $el$] >>)))))
        (loop sel)))
  ((Sexpr loc (list se :: sel))
   (List.fold_left
    (lambda (e se) (let ((e1 (expr_se se))) <:expr< $e$ $e1$ >>))
    (expr_se se) sel))
  ((Squot loc typ txt)
   (Pcaml.handle_expr_quotation loc (, typ txt))))
 progn_se
 (lambda loc
    (lambda_match
     ((list) <:expr< () >>)
     ((list se) (expr_se se))
     ((sel) (let ((el (List.map expr_se sel))) <:expr< do { $list:el$ } >>))))
 let_binding_se
 (lambda_match
  ((Sexpr loc (list se1 se2)) (, (ipatt_se se1) (expr_se se2) <:vala< (list)>>))
  (se (error se "let_binding")))
 match_case
 (lambda loc
   (lambda_match
    ((Sexpr _ (list se1 se2))
     (, (patt_se se1) <:vala< None >> (expr_se se2)))
    ((Sexpr _ (list se1 sew se2))
     (, (patt_se se1) <:vala< (Some (expr_se sew)) >> (expr_se se2)))
    (se (error se "match_case"))))
 label_expr_se
 (lambda loc
   (lambda_match
    ((Sexpr _ (list se1 se2)) (, (patt_se se1) (expr_se se2)))
    (se (error se ("label_expr")))))
 expr_ident_se
 (lambda (loc s)
   (if (= ([] s 0) '<')
       <:expr< $lid:s$ >>
       (let ((l (Versdep.split_on_char '.' s)))
            (Asttools.expr_of_string_list loc l))
   ))
 parser_cases_se
 (lambda loc
   (lambda_match
    ((list) <:expr< raise Stream.Failure >>)
    ((list (Sexpr loc (list (Sexpr _ spsel) :: act)) :: sel)
     (let* ((ekont (lambda _ (parser_cases_se loc sel)))
            (act (match act
                        ((list se) (expr_se se))
                        ((list sep se)
                         (let* ((p (patt_se sep))
                                (e (expr_se se)))
                       <:expr< let $p$ = Stream.count $lid:strm_n$ in $e$ >>))
                        (_ (error_loc loc "parser_case")))))
       (stream_pattern_se loc act ekont spsel)))
    ((list se :: _)
     (error se "parser_case"))))
 stream_pattern_se
 (lambda (loc act ekont)
   (lambda_match
    ((list) act)
    ((list se :: sel)
     (let* ((ckont (lambda err <:expr< raise (Stream.Error $err$) >>))
            (skont (stream_pattern_se loc act ckont sel)))
       (stream_pattern_component skont ekont <:expr< "" >> se)))))
 stream_pattern_component
 (lambda (skont ekont err)
   (lambda_match
    ((Sexpr loc (list (Satom _ Alid "`") se :: wol))
     (let* ((wo (match wol
                       ((list se) (Some (expr_se se)))
                       ((list) None)
                       (_ (error_loc loc "stream_pattern_component"))))
            (e (peek_fun loc))
            (p (patt_se se))
            (j (junk_fun loc))
            (k (ekont err)))
       <:expr< match $e$ $lid:strm_n$ with
       [ Some $p$ $opt:wo$ -> do { $j$ $lid:strm_n$ ; $skont$ }
       | _ -> $k$ ] >>))
     ((Sexpr loc (list se1 se2))
      (let* ((p (patt_se se1))
             (e (let ((e (expr_se se2)))
     <:expr< try Some ($e$ $lid:strm_n$) with [ Stream.Failure -> None ] >>))
             (k (ekont err)))
        <:expr< match $e$ with [ Some $p$ -> $skont$ | _ -> $k$ ] >>))
    ((Sexpr loc (list (Satom _ Alid "?") se1 se2))
     (stream_pattern_component skont ekont (expr_se se2) se1))
    ((Satom loc Alid s)
     <:expr< let $lid:s$ = $lid:strm_n$ in $skont$ >>)
    (se
     (error se "stream_pattern_component"))))
 patt_se
 (lambda_match
  ((Satom loc Alid "_") <:patt< _ >>)
  ((Satom loc (or Alid Auid) s) (patt_ident_se loc s))
  ((Satom loc Aint s)
   <:patt< $int:s$ >>)
  ((Satom loc Achar s)
   (<:patt< $chr:s$ >>))
  ((Satom loc Astring s)
   <:patt< $str:s$ >>)
  ((Sexpr loc (list (Satom _ Alid "or") se :: sel))
   (List.fold_left
    (lambda (p se) (let ((p1 (patt_se se))) <:patt< $p$ | $p1$ >>))
    (patt_se se) sel))
  ((Sexpr loc (list (Satom _ Alid "range") se1 se2))
   (let* ((p1 (patt_se se1))
          (p2 (patt_se se2)))
     <:patt< $p1$ .. $p2$ >>))
  ((Sexpr loc (list (Satom _ Alid ",") :: sel))
   (let ((pl (List.map patt_se sel))) <:patt< ( $list:pl$ ) >>))
  ((Sexpr loc (list (Satom _ Alid "as") se1 se2))
   (let* ((p1 (patt_se se1))
          (p2 (patt_se se2)))
     <:patt< ($p1$ as $p2$) >>))
  ((Sexpr loc (list (Satom _ Alid "list") :: sel))
   (let rec ((loop
              (lambda_match
               ((list) <:patt< [] >>)
               ((list se1 (Satom _ Alid "::") se2)
                (let* ((p (patt_se se1))
                       (pl (patt_se se2)))
                  <:patt< [$p$ :: $pl$] >>))
               ((list se :: sel)
                (let* ((p (patt_se se))
                       (pl (loop sel)))
                  <:patt< [$p$ :: $pl$] >>)))))
        (loop sel)))
  ((Sexpr loc (list se :: sel))
   (List.fold_left
    (lambda (p se) (let ((p1 (patt_se se))) <:patt< $p$ $p1$ >>))
    (patt_se se) sel))
  ((Sexpr loc (list)) <:patt< () >>)
  ((Squot loc typ txt) (Pcaml.handle_patt_quotation loc (, typ txt))))
 patt_ident_se
 (lambda (loc s)
  (let* ((sl (split_at_dots loc s))
         ((, hdl lid) (split_last sl)))
         (if (not (List.for_all capitalized hdl))
             (Ploc.raise loc (Stream.Error "patt expected, but components aren't capitalized"))
             ())
         (match hdl
                  ((list) (patt_id loc lid))
                  ((list h :: t)
                     (let ((me (List.fold_left (lambda (me uid) <:extended_longident< $longid:me$ . $uid:uid$ >>)
                                  <:extended_longident< $uid:h$ >> t)))
                         (<:patt< $longid:me$ . $lid:lid$ >>))
                  )
         )
  )
  )
 ipatt_se
 (lambda se
   (match (ipatt_opt_se se)
          ((Left p) p)
          ((Right (, se _))
           (error se "ipatt"))))
 ipatt_opt_se
 (lambda_match
  ((Satom loc Alid "_") (Left <:patt< _ >>))
  ((Satom loc Alid s) (Left <:patt< $lid:s$ >>))
  ((Sexpr loc (list (Satom _ Alid ",") :: sel))
   (let ((pl (List.map ipatt_se sel))) (Left <:patt< ( $list:pl$ ) >>)))
  ((Sexpr loc (list)) (Left <:patt< () >>))
  ((Sexpr loc (list se :: sel)) (Right (, se sel)))
  (se (error se "ipatt")))
 type_declaration_list_se
 (lambda_match
  ((list se1 se2 :: sel)
   (let (((, n1 loc1 tpl)
          (match se1
                 ((Sexpr _ (list (Satom loc Alid n) :: sel))
                  (, n loc (List.map type_parameter_se sel)))
                 ((Satom loc Alid n)
                  (, n loc (list)))
                 ((se)
                  (error se "type declaration")))))
     (let* ((empty (list))
            (n (, loc1 <:vala< n1 >>))
            (td ({} (MLast.tdIsDecl <:vala< True >>)(MLast.tdNam <:vala< n >>)
                    (MLast.tdPrm <:vala< tpl >>) (MLast.tdPrv <:vala< False >>)
                    (MLast.tdDef (ctyp_se se2))
                    (MLast.tdCon <:vala< empty >>)
                    (MLast.tdAttributes <:vala< empty >>))))
          (list td :: (type_declaration_list_se sel)))))
  ((list) (list))
  ((list se :: _) (error se "type_decl")))
 type_parameter_se
 (lambda_match
  ((Satom _ Alid s) (&& (>= (String.length s) 2) (= ([] s 0) '''))
   (let ((s (String.sub s 1 (- (String.length s) 1))))
      (, <:vala< (Some s) >> (, None False))))
  (se
   (error se "type_parameter")))
 ctyp_se
 (lambda_match
  ((Sexpr loc (list (Satom _ Alid "sum") :: sel))
   (let ((cdl (List.map constructor_declaration_se sel)))
     <:ctyp< [ $list:cdl$ ] >>))
  ((Sexpr loc (list se :: sel))
   (List.fold_left
    (lambda (t se) (let ((t2 (ctyp_se se))) <:ctyp< $t$ $t2$ >>))
    (ctyp_se se) sel))
  ((Satom loc (or Alid Auid) s)
   (ctyp_ident_se loc s))
  (se
   (error se "ctyp")))
 ctyp_ident_se
 (lambda (loc s)
  (let* ((sl (split_at_dots loc s))
         ((, hdl lid) (split_last sl)))
         (if (not (List.for_all capitalized hdl))
             (Ploc.raise loc (Stream.Error "ctyp expected, but components aren't capitalized"))
             ())
         (match hdl
                  ((list) (ctyp_id loc lid))
                  ((list h :: t)
                     (let ((me (List.fold_left (lambda (me uid) <:extended_longident< $longid:me$ . $uid:uid$ >>)
                                  <:extended_longident< $uid:h$ >> t)))
                         (<:ctyp< $longid:me$ . $lid:lid$ >>))
                  )
         )
  )
)
 constructor_declaration_se
 (lambda_match
  ((Sexpr loc (list (Satom _ Auid ci) :: sel))
   (, loc <:vala< ci >> <:vala< (list) >> <:vala< (List.map ctyp_se sel) >> <:vala< None >> <:vala< (list) >>))
  (se
   (error se "constructor_declaration"))))

(value top_phrase_se
       (lambda se
         (match se
                ((or (Satom loc _ _) (Squot loc _ _)) (str_item_se se))
                ((Sexpr loc (list (Satom _ Alid s) :: sl))
                 (if (= ([] s 0) '#')
                     (let ((n (String.sub s 1 (- (String.length s) 1))))
                       (match sl
                              ((list (Satom _ Astring s))
                               (<:str_item< # $lid:n$ $str:s$ >>))
                              (_ (match ()))))
                   (str_item_se se)))
                ((Sexpr loc _) (str_item_se se)))))

;; Parser

(value phony_quot (ref False))
(Pcaml.add_option "-phony_quot" (Arg.Set phony_quot) "phony quotations")

(:= Pcaml.no_constructors_arity.val False)

(progn
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
 (Grammar.Unsafe.clear_entry class_type)
 (Grammar.Unsafe.clear_entry class_expr)
 (Grammar.Unsafe.clear_entry class_sig_item)
 (Grammar.Unsafe.clear_entry class_str_item))

(Pcaml.set_ast_parse Pcaml.transduce_interf (Grammar.Entry.parse interf))
(Pcaml.set_ast_parse Pcaml.transduce_implem (Grammar.Entry.parse implem))
(Pcaml.set_ast_parse Pcaml.transduce_top_phrase (Grammar.Entry.parse top_phrase))
(Pcaml.set_ast_parse Pcaml.transduce_use_file (Grammar.Entry.parse use_file))

(value sexpr (Grammar.Entry.create gram "sexpr"))
(value atom (Grammar.Entry.create gram "atom"))

EXTEND
  implem :
    [ [ st = LIST0 [ s = str_item -> (, s loc) ];
        eoi_loc = [ EOI -> loc ] -> (, st (Some eoi_loc)) ] ]
  ;
  top_phrase :
    [ [ se = sexpr -> (Some (top_phrase_se se))
      | EOI -> None ] ]
  ;
  use_file :
    [ [ l = LIST0 sexpr; EOI -> (, (List.map top_phrase_se l) False) ] ]
  ;
  str_item :
    [ [ se = sexpr -> (str_item_se se)
      | e = expr -> <:str_item< $exp:e$ >> ] ]
  ;
  expr :
    [ "top"
      [ se = sexpr -> (expr_se se) ] ]
  ;
  patt :
    [ [ se = sexpr -> (patt_se se) ] ]
  ;
  sexpr :
    [ [ "("; sl = LIST0 sexpr; ")" -> (Sexpr loc sl)
      | a = atom -> (Satom loc Alid a)
      | s = LIDENT -> (Satom loc Alid s)
      | s = UIDENT -> (Satom loc Auid s)
      | s = INT -> (Satom loc Aint s)
      | s = CHAR -> (Satom loc Achar s)
      | s = STRING -> (Satom loc Astring s)
      | s = QUOT ->
          (let* ((i (String.index s ':'))
                 (typ (String.sub s 0 i))
                 (txt (String.sub s (+ i 1) (- (- (String.length s) i) 1))))
            (if phony_quot.val
                (Satom loc Alid (^ "<:" (^ typ (^ "<" (^ txt ">>")))))
                (Squot loc typ txt))) ] ]
  ;
  atom :
    [ [ "_" -> "_"
      | "," -> ","
      | "=" -> "="
      | ":" -> ":"
      | "." -> "." ] ]
  ;
END
