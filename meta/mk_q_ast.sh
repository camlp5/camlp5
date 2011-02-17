#!/bin/sh
# $Id: mk_q_ast.sh,v 6.2 2011/02/17 09:17:07 deraugla Exp $

IFILE=pa_r.ml
OFILE=q_ast.ml
(
sed -e '/^    value rec ctyp =$/,$d' $OFILE
ocamlrun ./camlp5r -nolib -I . -I ../etc pa_mkast.cmo pr_r.cmo -impl ../main/mLast.mli |
sed -e '1,/^  struct/d;/external/,$d'
grep 'value anti_anti n' $OFILE
sed -e '1,/anti_anti/d' $OFILE
)
