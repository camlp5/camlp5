#!/bin/sh
# $Id: mkmapAst.sh,v 6.2 2011/02/16 20:39:55 deraugla Exp $

IFILE=pa_r.ml
OFILE=mapAst.ml
(
sed -e '/^type map_f =/,$d' $OFILE
echo "type map_f ="
ocamlrun ../meta/camlp5r -nolib -I ../meta -I ../etc pa_mapAst.cmo pr_r.cmo -flag D -impl mLast.mli |
sed -e '/| ..Xtr/{N; N; s/\n */@/g}' |
sed -e 's/| \(..Xtr.*\) ]$/| IFDEF STRICT THEN\n        \1\n      END ]/' |
sed -e 's/@/\n          /g' |
sed -e '1,/type map_f =/d;/external/,$d'
)
