#!/bin/sh
# $Id: mk_q_MLast.sh,v 6.2 2012/03/06 11:00:53 deraugla Exp $

IFILE=pa_r.ml
OFILE=q_MLast.ml
(
sed -e '/^EXTEND$/,$d' $OFILE
echo EXTEND
${OCAMLN}run ./${CAMLP5N}r -nolib -I . -I ../etc pa_macro.cmo q_MLast.cmo pa_extend.cmo pr_r.cmo pr_extend.cmo -ignloaddir -quotify $IFILE | sed -e '1,/^EXTEND$/d' -e '/^END;$/,$d'
echo '  (* Antiquotations for local entries *)'
sed -e '1,/Antiquotations for local entries/d' $OFILE
)
