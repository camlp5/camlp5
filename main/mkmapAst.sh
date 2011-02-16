#!/bin/sh
# $Id: mkmapAst.sh,v 6.1 2011/02/16 19:06:26 deraugla Exp $

IFILE=pa_r.ml
OFILE=mapAst.ml
(
sed -e '/^type map =/,$d' $OFILE
echo "type map ="
ocamlrun ../meta/camlp5r -nolib -I ../meta -I ../etc pa_mapAst.cmo pr_r.cmo -flag D -impl mLast.mli |
sed -e '/| ..Xtr/{N; N; s/\n */@/g}' |
sed -e 's/| \(..Xtr.*\) ]$/| IFDEF STRICT THEN\n        \1\n      END ]/' |
sed -e 's/@/\n          /g' |
sed -e '1,/type map =/d;/external/,$d'
)
