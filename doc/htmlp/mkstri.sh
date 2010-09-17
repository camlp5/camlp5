#!/bin/sh
# $Id: mkstri.sh,v 6.2 2010/09/17 01:35:32 deraugla Exp $

top=../..
file=$top/test/quot_r.ml
quotation_list="$*"
if [ "$quotation_list" = "" ]; then
  quotation_list="expr patt ctyp str_item sig_item module_expr module_type class_expr class_type class_str_item class_sig_item with_constr poly_variant"
fi

for q in $quotation_list; do

  echo

  $top/meta/camlp5r $top/meta/q_MLast.cmo $top/etc/pr_r.cmo -l200 -impl $top/test/quot_r.ml |
  paste $top/test/quot_r.ml - |
  grep "<:$q<" |
  sed -e 's/;$//; s/&/&amp;/g; s/</\&lt;/g; s/^/    <tt style="color:blue">/; s/MLast/    <tt style="color:red">MLast/; s|>>;|>></tt><br/>|; s|$|</tt>aaaa|; $s/aaaa//; s|aaaa|	  </dd>	</dl>	<dl class="nodelist">	  <dt>- aaa</dt>	  <dd>|' |
  tr '\t' '\n'

done

