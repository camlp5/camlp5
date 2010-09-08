#!/bin/sh
# $Id: mk_q_ast.sh,v 1.4 2010/09/08 10:01:00 deraugla Exp $

IFILE=pa_r.ml
OFILE=q_ast.ml
(
sed -e '/^    value rec ctyp =$/,$d' $OFILE
ocamlrun ./camlp5r -nolib -I . -I ../etc pa_mkast.cmo pr_r.cmo -impl ../main/mLast.mli |
sed -e 's/\(..Xtr .*\) ->$/IFDEF STRICT THEN/' |
sed -e 's/C.node "PaXtr".*$/PaXtr loc s _ -> C.xtr_or_anti loc (fun r -> C.node "PaAnt" [r]) s\n        END ]/; s/C.node "ExXtr".*$/ExXtr loc s _ -> C.xtr_or_anti loc (fun r -> C.node "ExAnt" [r]) s\n        END ]/; s/C.node "\(..\)Xtr".*$/\1Xtr loc s _ -> C.xtr loc s\n        END ]/' |
sed -e '1,/^  struct/d;/external/,$d'
grep 'value anti_anti n' $OFILE
sed -e '1,/anti_anti/d' $OFILE
)
