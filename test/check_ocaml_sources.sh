#!/bin/sh
# $Id: check_ocaml_sources.sh,v 1.13 2010/09/13 18:39:07 deraugla Exp $

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
       "$idir/$bname" = "examples/apply_operator.ml" -o \
       "$idir/$bname" = "examples/expression_closure_filter.ml" -o \
       "$idir/$bname" = "examples/free_vars_test.ml" -o \
       "$idir/$bname" = "examples/global_handler.ml" -o \
       "$idir/$bname" = "Camlp4/Debug.ml" -o \
       "$idir/$bname" = "Camlp4/ErrorHandler.ml" -o \
       "$idir/$bname" = "Camlp4/OCamlInitSyntax.ml" -o \
       "$idir/$bname" = "Camlp4/Register.ml" -o \
       "$idir/$bname" = "Camlp4/Sig.ml" -o \
       "$idir/$bname" = "Printers/DumpCamlp4Ast.ml" -o \
       "$idir/$bname" = "Printers/DumpOCamlAst.ml" -o \
       "$idir/$bname" = "Printers/OCaml.ml" -o \
       "$idir/$bname" = "Printers/OCamlr.ml" ]
  then
    echo "skipping $bname"
  else
    syntax="etc/pa_o.cmo etc/pa_op.cmo"
    altsyntax="meta/pa_r.cmo"
    syntname="normal syntax"
    altsyntname="revised syntax"
    if [ "$idir" = "Camlp4" -o "$idir" = "Camlp4Printers" -o \
         "$idir" = "Printers" -o \
         "$idir/$bname" = "boot/Camlp4Ast.ml" ]
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
    main/camlp5 meta/pa_r.cmo -I etc pr_o.cmo /tmp/t1.ml > /tmp/t2.ml
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
