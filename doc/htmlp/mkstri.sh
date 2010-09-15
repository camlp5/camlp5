#!/bin/sh
# $Id: mkstri.sh,v 1.1 2010/09/15 03:39:01 deraugla Exp $

top=../..
quotation="$1"

$top/meta/camlp5r $top/meta/q_MLast.cmo $top/etc/pr_r.cmo -l200 -impl $top/test/quot_r.ml |
paste $top/test/quot_r.ml - |
grep "<:$quotation<" |
sed -e 's/;$//; s/</\&lt;/g; s/^/    <tt style="color:blue">/; s/MLast/    <tt style="color:red">MLast/; s|>>;|>></tt><br/>|; s|$|</tt><br/>          <br/>|' |
tr '\t' '\n'
