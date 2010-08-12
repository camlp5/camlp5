#!/bin/sh
# $Id: mk_q_MLast.sh,v 1.7 2010/08/12 11:39:42 deraugla Exp $

IFILE=pa_r.ml
OFILE=q_MLast.ml
if [ "$NAME" = "" ]; then NAME=camlp5; fi
(
sed -e '/^EXTEND$/,$d' $OFILE
echo EXTEND
ocamlrun ./${NAME}r -nolib -I . -I ../etc pa_macro.cmo q_MLast.cmo pa_extend.cmo pr_r.cmo pr_extend.cmo -ignloaddir -quotify $IFILE | sed -e '1,/^EXTEND$/d' -e '/^END;$/,$d'
echo '  (* Antiquotations for local entries *)'
sed -e '1,/Antiquotations for local entries/d' $OFILE
)
