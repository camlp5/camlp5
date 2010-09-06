#!/bin/sh -e
# $Id: check_ocaml_sources.sh,v 1.3 2010/09/06 08:32:33 deraugla Exp $

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
  idir=$(basename $(dirname $i))
  syntax="etc/pa_o.cmo"
  altsyntax="meta/pa_r.cmo"
  if [ "$idir" = "Camlp4Printers" ]; then
    syntax="meta/pa_r.cmo"
    altsyntax="etc/pa_o.cmo"
  fi
  echo '*** 1'
  main/camlp5 $syntax -I etc pr_r.cmo pr_ro.cmo "$i" > /tmp/t1.ml
  echo '*** 2'
  main/camlp5 meta/pa_r.cmo -I etc pr_r.cmo pr_ro.cmo /tmp/t1.ml |
  diff /tmp/t1.ml -
  echo '*** 3'
  main/camlp5 meta/pa_r.cmo -I etc pr_o.cmo /tmp/t1.ml > /tmp/t2.ml
  echo '*** 4'
  main/camlp5 $syntax -I etc pr_o.cmo "$i" > /tmp/t3.ml
  echo '*** 5'
  main/camlp5 etc/pa_o.cmo -I etc pr_o.cmo /tmp/t3.ml | diff /tmp/t3.ml -
  echo '*** 6'
  diff /tmp/t2.ml /tmp/t3.ml || :
  echo '*** 7'
  main/camlp5 $syntax meta/pr_dump.cmo "$i" > /dev/null
done
