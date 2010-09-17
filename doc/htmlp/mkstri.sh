#!/bin/sh
# $Id: mkstri.sh,v 6.4 2010/09/17 02:22:31 deraugla Exp $

top=../..
file=$top/test/quot_r.ml
quotation_list="$*"
if [ "$quotation_list" = "" ]; then
  quotation_list="expr patt ctyp str_item sig_item module_expr module_type class_expr class_type class_str_item class_sig_item with_constr poly_variant"
fi

for q in $quotation_list; do

  echo

  $top/meta/camlp5r $top/meta/q_MLast.cmo $top/etc/pr_r.cmo -l200 -impl $top/test/quot_r.ml |
  paste -d@ $top/test/quot_r.ml - |
  sed -e 's/(\*.*\*)@//; /\*)$/N; s/\*)./*)/' |
  grep "<:$q<" |
  sed -e 's/;$//; s/&/&amp;/g; s/<:/\&lt;:/g; s/< /\&lt; /g' |
  sed -e 's/^/<dl class="nodelist">@/' |
  sed -e 's|(\* |  <dt>- |; s| \*)|</dt>@|' |
  sed -e 's/@&/@  <dd>@    <tt style="color:blue">\&/' |
  sed -e 's/MLast/    <tt style="color:red">MLast/' |
  sed -e 's|>>;|>></tt><br/>|' |
  sed -e 's|$|</tt>@  </dd>@</dl>|' |
  tr '@' '\n'

done

