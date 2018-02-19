#!/bin/sh
# From top:
# test/check_ocaml_sources.sh

dir='../../ocaml_src/trunk'
suff=ml

getfiles () {
  files="$(find $dir -type f -name "*.$suff" -print)"
}
getfiles

usage () {
  echo "Usage: check_ocaml_sources.sh <options> [<file>]"
  echo "<options> are:"
  echo "  -d <dir>    Change testing directory"
  echo "  -h          Display this list of options"
  echo "  -i          Interfaces (.mli files)"
  echo
  echo "Testing directory: $dir"
  echo "Files: $files"
}
while getopts ":d:hi" name; do
  case "$name" in
  'd') dir="$OPTARG"; getfiles;;
  'h') usage; exit 0;;
  'i') suff=mli; getfiles;;
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
       "$idir/$bname" = "camlp4/Camlp4Bin.ml" -o \
       "$idir/$bname" = "Camlp4/Debug.ml" -o \
       "$idir/$bname" = "Camlp4/ErrorHandler.ml" -o \
       "$idir/$bname" = "Camlp4/OCamlInitSyntax.ml" -o \
       "$idir/$bname" = "Camlp4/Register.ml" -o \
       "$idir/$bname" = "Camlp4/Sig.ml" -o \
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
       "$idir/$bname" = "Camlp4Top/Top.ml" -o \
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
       "$idir/$bname" = "fixtures/backquoted_irrefutable_tuple.ml" -o \
       "$idir/$bname" = "fixtures/backquoted_record.ml" -o \
       "$idir/$bname" = "fixtures/backquoted_tuple.ml" -o \
       "$idir/$bname" = "fixtures/bug_escaping_quot.ml" -o \
       "$idir/$bname" = "fixtures/class_expr_quot.ml" -o \
       "$idir/$bname" = "fixtures/default_quotation.ml" -o \
       "$idir/$bname" = "fixtures/exception-with-eqn-bug.ml" -o \
       "$idir/$bname" = "fixtures/functor-perf2.ml" -o \
       "$idir/$bname" = "fixtures/functor-perf3.ml" -o \
       "$idir/$bname" = "fixtures/gram.ml" -o \
       "$idir/$bname" = "fixtures/gram-fold.ml" -o \
       "$idir/$bname" = "fixtures/gram-list.ml" -o \
       "$idir/$bname" = "fixtures/gram-loc-lost.ml" -o \
       "$idir/$bname" = "fixtures/gram-sub-rule.ml" -o \
       "$idir/$bname" = "fixtures/gram-tree.ml" -o \
       "$idir/$bname" = "fixtures/gram-tree2.ml" -o \
       "$idir/$bname" = "fixtures/gram-tree3.ml" -o \
       "$idir/$bname" = "fixtures/label.ml" -o \
       "$idir/$bname" = "fixtures/lambda_free.ml" -o \
       "$idir/$bname" = "fixtures/loc-bug.ml" -o \
       "$idir/$bname" = "fixtures/macrotest.mli" -o \
       "$idir/$bname" = "fixtures/make_extend.ml" -o \
       "$idir/$bname" = "fixtures/match_parser.ml" -o \
       "$idir/$bname" = "fixtures/metalib.ml" -o \
       "$idir/$bname" = "fixtures/method_private_virtual.ml" -o \
       "$idir/$bname" = "fixtures/pp_let_in.ml" -o \
       "$idir/$bname" = "fixtures/pprecordtyp.ml" -o \
       "$idir/$bname" = "fixtures/pr4314gram1.ml" -o \
       "$idir/$bname" = "fixtures/pr4314gram2.ml" -o \
       "$idir/$bname" = "fixtures/pr4314gram3.ml" -o \
       "$idir/$bname" = "fixtures/pr4314gram4.ml" -o \
       "$idir/$bname" = "fixtures/pr4314gram5.ml" -o \
       "$idir/$bname" = "fixtures/pr4329.ml" -o \
       "$idir/$bname" = "fixtures/pr4330.ml" -o \
       "$idir/$bname" = "fixtures/pr4357.ml" -o \
       "$idir/$bname" = "fixtures/pr4357sample.ml" -o \
       "$idir/$bname" = "fixtures/pr4357sample2.ml" -o \
       "$idir/$bname" = "fixtures/pr4452.ml" -o \
       "$idir/$bname" = "fixtures/simplify.ml" -o \
       "$idir/$bname" = "fixtures/simplify_r.ml" -o \
       "$idir/$bname" = "fixtures/superfluous.ml" -o \
       "$idir/$bname" = "fixtures/transform-examples.ml" -o \
       "$idir/$bname" = "fixtures/tuple_as_retval.ml" -o \
       "$idir/$bname" = "fixtures/unit.ml" -o \
       "$idir/$bname" = "fixtures/use.ml" -o \
       "$idir/$bname" = "frx/frx_lbutton.mli" -o \
       "$idir/$bname" = "Printers/DumpCamlp4Ast.ml" -o \
       "$idir/$bname" = "Printers/DumpOCamlAst.ml" -o \
       "$idir/$bname" = "Printers/Null.ml" -o \
       "$idir/$bname" = "Printers/OCaml.ml" -o \
       "$idir/$bname" = "Printers/OCamlr.ml" -o \
       "$idir/$bname" = "Printers/OCamlr.mli" -o \
       "$idir/$bname" = "testlabl/multimatch.ml" -o \
       "$idir/$bname" = "testlabl/tests.ml" -o \
       "$idir/$bname" = "testlabl/varunion.ml" ]
  then
    echo "skipping $bname"
  else
    syntax="etc/pa_o.cmo etc/pa_op.cmo"
    altsyntax="meta/pa_r.cmo"
    syntname="normal syntax"
    altsyntname="revised syntax"
    c5o=-no_quot
    opt=1
    if [ "$idir" = "Camlp4" -o \
         "$idir" = "Camlp4Filters" -o \
         "$idir" = "Camlp4Parsers" -o \
         "$idir" = "Camlp4Printers" -o \
         "$idir" = "Printers" -o \
         "$idir/$bname" = "boot/Camlp4Ast.ml" -o \
         "$idir/$bname" = "camlp4/camlp4prof.ml" -o \
         "$idir/$bname" = "camlp4/camlp4prof.mli" -o \
         "$idir/$bname" = "camlp4/mkcamlp4.ml" -o \
         "$idir/$bname" = "Camlp4Top/Rprint.ml" -o \
         "$idir/$bname" = "fixtures/external.ml" -o \
         "$idir/$bname" = "fixtures/fun.ml" -o \
         "$idir/$bname" = "fixtures/meta_multi_term.ml" -o \
         "$idir/$bname" = "fixtures/mod2.ml" -o \
         "$idir/$bname" = "fixtures/outside-scope.ml" -o \
         "$idir/$bname" = "fixtures/parser.ml" -o \
         "$idir/$bname" = "fixtures/rec.ml" -o \
         "$idir/$bname" = "fixtures/seq.ml" -o \
         "$idir/$bname" = "fixtures/seq2.ml" -o \
         "$idir/$bname" = "fixtures/type.ml" ]
    then
      syntax="meta/pa_r.cmo meta/pa_rp.cmo etc/q_phony.cmo"
      altsyntax="etc/pa_o.cmo"
      syntname="revised syntax"
      altsyntname="normal syntax"
      c5o=
      opt=0
    fi
    echo "*** testing $syntname to revised syntax (t1.$suff)"
    main/camlp5 $syntax -I etc pr_r.cmo pr_ro.cmo $c5o "$i" > /tmp/t1.$suff
    echo "*** testing revised syntax on itself"
    main/camlp5 meta/pa_r.cmo -I etc pr_r.cmo pr_ro.cmo /tmp/t1.$suff |
    diff -c /tmp/t1.$suff -
    echo "*** testing revised syntax to normal syntax (t2.$suff)"
    main/camlp5 -nolib meta/pa_r.cmo -I etc pr_o.cmo /tmp/t1.$suff > /tmp/t2.$suff
    echo "*** testing $syntname to normal syntax (result: t3.$suff)"
    main/camlp5 $syntax -I etc pr_o.cmo $c5o "$i" > /tmp/t3.$suff
    echo "*** testing normal syntax on itself"
    main/camlp5 -nolib etc/pa_o.cmo etc/pa_op.cmo -I etc pr_o.cmo -no_quot /tmp/t3.$suff | diff /tmp/t3.$suff -
    echo "*** comparing t2.$suff and t3.$suff"
    diff /tmp/t2.$suff /tmp/t3.$suff || :
    echo "*** testing $syntname to OCaml parse tree"
    main/camlp5 $syntax meta/pr_dump.cmo $c5o "$i" >/dev/null
    if [ "$opt" = "1" ]; then
      echo "*** testing normal syntax with opt"
      compile/camlp5o.fast.opt -no_quot "$i" >/dev/null
    fi
    echo "*** testing revised syntax (t1.$suff) to OCaml parse tree"
    main/camlp5 meta/pa_r.cmo meta/pr_dump.cmo /tmp/t1.$suff > /dev/null
    echo "*** testing normal syntax (t2.$suff) to OCaml parse tree"
    main/camlp5 etc/pa_o.cmo meta/pr_dump.cmo -no_quot /tmp/t2.$suff > /dev/null
  fi
done
# /bin/rm -f /tmp/t1.$suff /tmp/t2.$suff /tmp/t3.$suff
