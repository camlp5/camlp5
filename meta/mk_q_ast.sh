#!/bin/sh
# $Id: mk_q_ast.sh,v 1.1 2010/09/08 03:03:39 deraugla Exp $

IFILE=pa_r.ml
OFILE=q_ast.ml
(
sed -e '/^    value rec ctyp =$/,$d' $OFILE
ocamlrun ./camlp5r -nolib ./pa_macro.cmo ../etc/pa_mkast.cmo ../etc/pr_r.cmo -flag E -ignloaddir -impl ../main/mLast.mli |
sed -e 's/\(..Xtr .*\) ->$/IFDEF STRICT THEN/' |
sed -e 's/C.node "\(..\)Xtr".*$/\1Xtr loc s _ -> C.xtr loc s\n        END ]/' |
sed -e '1,/^  struct/d;/external/,$d'
echo '  (* Antiquotations for local entries *)'
sed -e '1,/Antiquotations for local entries/d' $OFILE
)
