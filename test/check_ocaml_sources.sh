#!/bin/sh
# $Id: check_ocaml_sources.sh,v 6.7 2010/09/19 09:56:37 deraugla Exp $

dir='../ocaml/trunk'

getfiles () {
  files="$(find $dir -type f -name '*.ml' -print)"
}
getfiles

usage () {
  echo "Usage: check_ocaml_sources.sh <options> [<file>]"
  echo "<options> are:"
  echo "  -d <dir>    Change testing directory"
  echo "  -h          Display this list of options"
  echo
  echo "Testing directory: $dir"
  echo "Files: $files"
}
while getopts ":d:h" name; do
  case "$name" in
  'd') dir="$OPTARG"; getfiles;;
  'h') usage; exit 0;;
  '?') echo "Invalid option -$OPTARG"; echo "Use option -h for help"; exit 2;;
  esac
done

if [ $(($OPTIND-1)) -ne $# ]; then
  shift $(($OPTIND-1))
  files="$1"
fi

for i in $files; do
  echo ===============================
  echo $i
  bname=$(basename $i)
  idir=$(basename $(dirname $i))
  pdir=$(basename $(dirname $(dirname $i)))
  if [ "$bname" = "frx_fileinput.ml" -o \
       "$pdir" = "unmaintained" -o \
       "$idir" = "builtin" -o \
       "$idir" = "Struct" -o "$idir" = "Grammar" -o \
       "$idir/$bname" = "Camlp4/Debug.ml" -o \
       "$idir/$bname" = "Camlp4/ErrorHandler.ml" -o \
       "$idir/$bname" = "Camlp4/OCamlInitSyntax.ml" -o \
       "$idir/$bname" = "Camlp4/Register.ml" -o \
       "$idir/$bname" = "Camlp4/Sig.ml" -o \
       "$idir/$bname" = "examples/apply_operator.ml" -o \
       "$idir/$bname" = "examples/arith.ml" -o \
       "$idir/$bname" = "examples/debug_extension.ml" -o \
       "$idir/$bname" = "examples/ex_str.ml" -o \
       "$idir/$bname" = "examples/ex_str_test.ml" -o \
       "$idir/$bname" = "examples/expression_closure.ml" -o \
       "$idir/$bname" = "examples/expression_closure_filter.ml" -o \
       "$idir/$bname" = "examples/fancy_lambda_quot.ml" -o \
       "$idir/$bname" = "examples/fancy_lambda_quot_test.ml" -o \
       "$idir/$bname" = "examples/free_vars_test.ml" -o \
       "$idir/$bname" = "examples/gen_match_case.ml" -o \
       "$idir/$bname" = "examples/gen_type_N.ml" -o \
       "$idir/$bname" = "examples/global_handler.ml" -o \
       "$idir/$bname" = "examples/lambda_parser.ml" -o \
       "$idir/$bname" = "examples/lambda_quot.ml" -o \
       "$idir/$bname" = "examples/lambda_quot_expr.ml" -o \
       "$idir/$bname" = "examples/lambda_quot_patt.ml" -o \
       "$idir/$bname" = "examples/lambda_test.ml" -o \
       "$idir/$bname" = "examples/macros.ml" -o \
       "$idir/$bname" = "examples/parse_files.ml" -o \
       "$idir/$bname" = "examples/test_type_quotation.ml" -o \
       "$idir/$bname" = "examples/type_quotation.ml" -o \
       "$idir/$bname" = "fixtures/bug_escaping_quot.ml" -o \
       "$idir/$bname" = "fixtures/class_expr_quot.ml" -o \
       "$idir/$bname" = "fixtures/exception-with-eqn-bug.ml" -o \
       "$idir/$bname" = "fixtures/functor-perf3.ml" -o \
       "$idir/$bname" = "fixtures/gram-list.ml" -o \
       "$idir/$bname" = "fixtures/gram-sub-rule.ml" -o \
       "$idir/$bname" = "fixtures/gram-tree2.ml" -o \
       "$idir/$bname" = "fixtures/lambda_free.ml" -o \
       "$idir/$bname" = "fixtures/method_private_virtual.ml" -o \
       "$idir/$bname" = "fixtures/pr4314gram2.ml" -o \
       "$idir/$bname" = "fixtures/pr4329.ml" -o \
       "$idir/$bname" = "fixtures/pr4357.ml" -o \
       "$idir/$bname" = "fixtures/pr4452.ml" -o \
       "$idir/$bname" = "fixtures/simplify_r.ml" -o \
       "$idir/$bname" = "fixtures/transform-examples.ml" -o \
       "$idir/$bname" = "Camlp4Filters/Camlp4AstLifter.ml" -o \
       "$idir/$bname" = "Camlp4Filters/Camlp4ExceptionTracer.ml" -o \
       "$idir/$bname" = "Camlp4Filters/Camlp4FoldGenerator.ml" -o \
       "$idir/$bname" = "Camlp4Filters/Camlp4MetaGenerator.ml" -o \
       "$idir/$bname" = "Camlp4Filters/Camlp4Profiler.ml" -o \
       "$idir/$bname" = "Camlp4Filters/Camlp4TrashRemover.ml" -o \
       "$idir/$bname" = "Camlp4Parsers/Camlp4AstLoader.ml" -o \
       "$idir/$bname" = "Camlp4Parsers/Camlp4DebugParser.ml" -o \
       "$idir/$bname" = "Camlp4Parsers/Camlp4GrammarParser.ml" -o \
       "$idir/$bname" = "Camlp4Parsers/Camlp4ListComprehension.ml" -o \
       "$idir/$bname" = "Camlp4Parsers/Camlp4MacroParser.ml" -o \
       "$idir/$bname" = "Camlp4Parsers/Camlp4OCamlParser.ml" -o \
       "$idir/$bname" = "Camlp4Parsers/Camlp4OCamlParserParser.ml" -o \
       "$idir/$bname" = "Camlp4Parsers/Camlp4OCamlReloadedParser.ml" -o \
       "$idir/$bname" = "Camlp4Parsers/Camlp4OCamlRevisedParser.ml" -o \
       "$idir/$bname" = "Camlp4Parsers/Camlp4OCamlRevisedParserParser.ml" -o \
       "$idir/$bname" = "Camlp4Parsers/Camlp4QuotationCommon.ml" -o \
       "$idir/$bname" = "Printers/DumpCamlp4Ast.ml" -o \
       "$idir/$bname" = "Printers/DumpOCamlAst.ml" -o \
       "$idir/$bname" = "Printers/Null.ml" -o \
       "$idir/$bname" = "Printers/OCaml.ml" -o \
       "$idir/$bname" = "Printers/OCamlr.ml" ]
  then
    echo "skipping $bname"
  else
    syntax="etc/pa_o.cmo etc/pa_op.cmo"
    altsyntax="meta/pa_r.cmo"
    syntname="normal syntax"
    altsyntname="revised syntax"
    opt=1
    if [ "$idir" = "Camlp4" -o \
         "$idir" = "Camlp4Filters" -o \
         "$idir" = "Camlp4Parsers" -o \
         "$idir" = "Camlp4Printers" -o \
         "$idir" = "Printers" -o \
         "$idir/$bname" = "boot/Camlp4Ast.ml" -o \
         "$idir/$bname" = "camlp4/camlp4prof.ml" -o \
         "$idir/$bname" = "camlp4/mkcamlp4.ml" -o \
         "$idir/$bname" = "fixtures/meta_multi_term.ml" -o \
         "$idir/$bname" = "fixtures/parser.ml" -o \
         "$idir/$bname" = "fixtures/type.ml" ]
    then
      syntax="meta/pa_r.cmo meta/pa_rp.cmo etc/q_phony.cmo"
      altsyntax="etc/pa_o.cmo"
      syntname="revised syntax"
      altsyntname="normal syntax"
      opt=0
    fi
    echo "*** testing $syntname to revised syntax (t1.ml)"
    main/camlp5 $syntax -I etc pr_r.cmo pr_ro.cmo "$i" > /tmp/t1.ml
    echo "*** testing revised syntax on itself"
    main/camlp5 meta/pa_r.cmo -I etc pr_r.cmo pr_ro.cmo /tmp/t1.ml |
    diff -c /tmp/t1.ml -
    echo "*** testing revised syntax to normal syntax (t2.ml)"
    main/camlp5 -nolib meta/pa_r.cmo -I etc pr_o.cmo /tmp/t1.ml > /tmp/t2.ml
    echo "*** testing $syntname to normal syntax (result: t3.ml)"
    main/camlp5 $syntax -I etc pr_o.cmo "$i" > /tmp/t3.ml
    echo "*** testing normal syntax on itself"
    main/camlp5 etc/pa_o.cmo -I etc pr_o.cmo /tmp/t3.ml | diff /tmp/t3.ml -
    echo "*** comparing t2.ml and t3.ml"
    diff /tmp/t2.ml /tmp/t3.ml || :
    echo "*** testing $syntname to OCaml parse tree"
    time main/camlp5 $syntax meta/pr_dump.cmo "$i" 2>&1 >/dev/null
    if [ "$opt" = "1" ]; then
      echo "*** testing normal syntax with opt"
      time compile/camlp5o.fast.opt "$i" 2>&1 >/dev/null
    fi
    echo "*** testing revised syntax (t1.ml) to OCaml parse tree"
    main/camlp5 meta/pa_r.cmo meta/pr_dump.cmo /tmp/t1.ml > /dev/null
    echo "*** testing normal syntax (t2.ml) to OCaml parse tree"
    main/camlp5 etc/pa_o.cmo meta/pr_dump.cmo /tmp/t2.ml > /dev/null
  fi
done
# rm -f /tmp/t1.ml /tmp/t2.ml /tmp/t3.ml
