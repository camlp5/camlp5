#!/bin/sh
# $Id: mktrans.sh,v 6.1 2010/09/15 16:49:47 deraugla Exp $

top=../..
quotation="$1"

echo '<table border="1">'
echo '  <tr>'

$top/meta/camlp5r -nolib $top/meta/q_MLast.cmo $top/etc/pr_r.cmo -mode T -l200 -impl $top/test/quot_r.ml |
paste - $top/test/quot_r.ml |
grep "<:$quotation<" |
grep -v '$_' |
sed -e 's/;$//; s/<:[^<]*< /    <td align="center"><tt>/; s|;|</tt></td>|; s/^MLast./    <td><tt>/; s| >>|</tt></td>|; s|$|	    <td>...</td>	  </tr>	  <tr>|' |
tr '\t' '\n'
