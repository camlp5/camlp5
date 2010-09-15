#!/bin/sh
# $Id: mktrans.sh,v 6.4 2010/09/15 20:33:23 deraugla Exp $

top=../..
quotation="$1"
file=$top/test/quot_r.ml

echo '<table border="1">'
echo '  <tr>'
echo '    <th>Node</th>'
echo "    <th><tt>&lt;:${quotation}&lt; ... >></tt></th>"
echo '    <th>Comment</th>'
echo '  </tr>'
echo '  <tr>'

$top/meta/camlp5r -nolib $top/meta/q_MLast.cmo $top/etc/pr_r.cmo -mode T -l200 -impl $file |
paste - $file |
sed -e 's/(\*.*\*)	//; /\*)$/N; s/\*)./*)/' |
grep "<:$quotation<" |
grep -v '$_' |
sed -e 's/\((\*.*\*)\)\(.*\)$/\2	\1/; s/ < / \&lt; /g; s/>>;/>>/; s/<:[^<]*< /    <td align="center"><tt>/; s|;|</tt></td>|; s/^MLast./    <td><tt>/; s| >>|</tt></td>|; s|$|	  </tr>	  <tr>|; s/(\* /    <td>/;s| \*)|</td>|; $s|	  <tr>||' |
tr '\t' '\n'

echo '</table>'
