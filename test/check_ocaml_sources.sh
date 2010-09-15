#!/bin/sh
# $Id: check_ocaml_sources.sh,v 6.1 2010/09/15 16:00:48 deraugla Exp $

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
  if [ "$bname" = "frx_fileinput.ml" -o "$idir" = "builtin" -o \
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
       "$idir/$bname" = "fixtures/exception-with-eqn-bug.ml" -o \
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
    if [ "$idir" = "Camlp4" -o \
         "$idir" = "Camlp4Parsers" -o \
         "$idir" = "Camlp4Printers" -o \
         "$idir" = "Printers" -o \
         "$idir/$bname" = "boot/Camlp4Ast.ml" -o \
         "$idir/$bname" = "camlp4/camlp4prof.ml" -o \
         "$idir/$bname" = "camlp4/mkcamlp4.ml" ]
    then
      syntax="meta/pa_r.cmo meta/pa_rp.cmo etc/q_phony.cmo"
      altsyntax="etc/pa_o.cmo"
      syntname="revised syntax"
      altsyntname="normal syntax"
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
    main/camlp5 $syntax meta/pr_dump.cmo "$i" > /dev/null
  fi
done
# rm -f /tmp/t1.ml /tmp/t2.ml /tmp/t3.ml
