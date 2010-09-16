#!/bin/sh
# $Id: mktrans.sh,v 6.8 2010/09/16 09:33:30 deraugla Exp $

top=../..
file=$top/test/quot_r.ml
quotation_list="$*"
if [ "$quotation_list" = "" ]; then
  quotation_list="expr patt ctyp str_item sig_item module_expr module_type class_expr class_type class_str_item class_sig_item with_constr poly_variant"
fi

for q in $quotation_list; do

  n=4
  if [ "$q" = "expr" -o "$q" = "patt" -o "$q" = "ctyp" ]; then
    n=3
  fi

  echo "<h$n>$q</h$n>"
  echo

  h="$(grep $q: $file | sed -e 's/^.*: //; s/...$//')"
  if [ "$h" != "" ]; then
    echo "<p>$h</p>"
    echo
  fi

  echo '<table border="1">'
  echo '  <tr>'
  echo '    <th>Node</th>'
  echo "    <th><tt>&lt;:$q&lt; ... >></tt></th>"
  echo '    <th>Comment</th>'
  echo '  </tr>'
  echo '  <tr>'

  $top/meta/camlp5r -nolib $top/meta/q_MLast.cmo $top/etc/pr_r.cmo -mode T -l200 -impl $file |
  paste - $file |
  sed -e 's/(\*.*\*)	//; /\*)$/N; s/\*)./*)/' |
  grep "<:$q<" |
  grep -v '$_' |
  sed -e 's/\((\*.*\*)\)\(.*\)$/\2	\1/; s/ < / \&lt; /g; s/ {< / {\&lt; /g; s/>>;/>>/; s/<:[^<]*< /    <td align="center"><tt>/; s|;|</tt></td>|; s/^MLast./    <td><tt>/; s| >>|</tt></td>|; s|$|	  </tr>	  <tr>|; s/(\* /    <td>/;s| \*)|</td>|; $s|	  <tr>||' |
  tr '\t' '\n'

  echo '</table>'
done
