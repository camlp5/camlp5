#!/bin/sh
# $Id: mk_q_MLast.sh,v 1.1 2006/09/29 04:45:49 deraugla Exp $

IFILE=pa_r.ml
OFILE=q_MLast.ml
(
sed -e '/^EXTEND$/,$d' $OFILE
echo EXTEND
ocamlrun ./camlp4r -I . -I ../etc q_MLast.cmo pa_extend.cmo pr_r.cmo pr_extend.cmo -cip -quotify $IFILE | sed -e '1,/^EXTEND$/d' -e '/^END;$/,$d'
echo '  (* Antiquotations for local entries *)'
sed -e '1,/Antiquotations for local entries/d' $OFILE
)
