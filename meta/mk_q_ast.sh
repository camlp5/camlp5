#!/bin/sh

IFILE=pa_r.ml
OFILE=q_ast.ml
(
sed -e '/^    value rec ctyp =$/,$d' $OFILE
${OCAMLN}run ./camlp5r -nolib -I . -I ../etc pa_mkast.cmo pr_r.cmo -impl ../main/mLast.mli |
sed -e 's/\(..Xtr .*\) →$//' |
sed -e 's/C.node "PaXtr".*$/PaXtr loc s _ → C.xtr_or_anti loc (fun r → C.node "PaAnt" [r]) s ]/; s/C.node "ExXtr".*$/ExXtr loc s _ → C.xtr_or_anti loc (fun r → C.node "ExAnt" [r]) s ]/; s/C.node "\(..\)Xtr".*$/\1Xtr loc s _ → C.xtr loc s ]/' |
sed -e '1,/^  struct/d;/external/,$d'
grep 'value anti_anti n' $OFILE
sed -e '1,/anti_anti/d' $OFILE
)
