#!/bin/sh
# $Id: mkreloc.sh,v 1.2 2010/09/07 20:27:39 deraugla Exp $

IFILE=pa_r.ml
OFILE=reloc.ml
(
sed -e '/^value rec ctyp/,$d' $OFILE
echo "value rec ctyp floc sh ="
ocamlrun ../meta/camlp5r -nolib ../meta/pa_macro.cmo ../etc/pa_reloc.cmo ../etc/pr_r.cmo -ignloaddir -impl mLast.mli | sed -e 's/\(..Xtr .*\) \]$/IFDEF STRICT THEN\n        \1\n      END ]/' | sed -e '1,/value rec ctyp/d;/external/,$d'
echo '(* Equality over syntax trees *)'
sed -e '1,/Equality over syntax trees/d' $OFILE
)
