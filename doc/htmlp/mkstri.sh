#!/bin/sh
# $Id: mkstri.sh,v 1.4 2010/09/15 08:03:39 deraugla Exp $

top=../..
quotation="$1"

$top/meta/camlp5r $top/meta/q_MLast.cmo $top/etc/pr_r.cmo -l200 -impl $top/test/quot_r.ml |
paste $top/test/quot_r.ml - |
grep "<:$quotation<" |
sed -e 's/;$//; s/&/&amp;/g; s/</\&lt;/g; s/^/    <tt style="color:blue">/; s/MLast/    <tt style="color:red">MLast/; s|>>;|>></tt><br/>|; s|$|</tt>aaaa|; $s/aaaa//; s|aaaa|<br/>	    <br/>|' |
tr '\t' '\n'
