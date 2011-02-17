#!/bin/sh
# $Id: mkmapAst.sh,v 6.4 2011/02/17 09:17:07 deraugla Exp $

IFILE=pa_r.ml
OFILE=mapAst.ml
(
sed -e '/^type map_f =/,$d' $OFILE
echo "type map_f ="
ocamlrun ../meta/camlp5r -nolib -I ../meta -I ../etc pa_mapAst.cmo pr_r.cmo -flag D -impl mLast.mli |
sed -e '1,/type map_f =/d;/external/,$d'
)
