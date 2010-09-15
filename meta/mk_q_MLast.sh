#!/bin/sh
# $Id: mk_q_MLast.sh,v 6.1 2010/09/15 16:00:25 deraugla Exp $

IFILE=pa_r.ml
OFILE=q_MLast.ml
(
sed -e '/^EXTEND$/,$d' $OFILE
echo EXTEND
ocamlrun ./camlp5r -nolib -I . -I ../etc pa_macro.cmo q_MLast.cmo pa_extend.cmo pr_r.cmo pr_extend.cmo -ignloaddir -quotify $IFILE | sed -e '1,/^EXTEND$/d' -e '/^END;$/,$d'
echo '  (* Antiquotations for local entries *)'
sed -e '1,/Antiquotations for local entries/d' $OFILE
)
