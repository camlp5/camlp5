#!/bin/sh
# mkreloc.sh,v

IFILE=pa_r.ml
OFILE=reloc.ml
(
sed -e '/^value rec ctyp/,$d' $OFILE
echo "value rec ctyp floc sh ="
${OCAMLN}run ../meta/${CAMLP5N}r -nolib -I ../meta -I ../etc pa_reloc.cmo pr_r.cmo -impl mLast.mli |
sed -e '1,/value rec ctyp/d;/external/,$d'
echo '(* Equality over syntax trees *)'
sed -e '1,/Equality over syntax trees/d' $OFILE
)
