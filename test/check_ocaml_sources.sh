#!/bin/sh -e
# $Id: check_ocaml_sources.sh,v 1.1 2010/09/06 01:50:22 deraugla Exp $

files="$(find ../ocaml/trunk -type f -name '*.ml' -print)"

if [ "$1" != "" ]; then
  files="$1"
fi

for i in $files; do
  echo ===============================
  echo $i
  echo '*** 1'
  main/camlp5 etc/pa_o.cmo -I etc pr_r.cmo pr_ro.cmo "$i" > /tmp/t1.ml
  echo '*** 2'
  main/camlp5 meta/pa_r.cmo -I etc pr_r.cmo pr_ro.cmo /tmp/t1.ml |
  diff /tmp/t1.ml -
  echo '*** 3'
  main/camlp5 meta/pa_r.cmo -I etc pr_o.cmo /tmp/t1.ml > /tmp/t2.ml
  echo '*** 4'
  main/camlp5 etc/pa_o.cmo -I etc pr_o.cmo "$i" > /tmp/t3.ml
  echo '*** 5'
  main/camlp5 etc/pa_o.cmo -I etc pr_o.cmo /tmp/t3.ml | diff /tmp/t3.ml -
  echo '*** 6'
  diff /tmp/t2.ml /tmp/t3.ml || :
done
