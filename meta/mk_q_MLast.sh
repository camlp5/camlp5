#!/bin/sh
# $Id: mk_q_MLast.sh,v 6.3 2012/03/09 12:43:14 deraugla Exp $

IFILE=pa_r.ml
OFILE=q_MLast.ml
TEXTBEG="-- begin copy from pa_r to q_MLast --"
TEXTEND="-- end copy from pa_r to q_MLast --"
D='$'

(
sed -e "/$TEXTBEG/,${D}d" $OFILE
echo "(* $TEXTBEG *)"
${OCAMLN}run ./${CAMLP5N}r -nolib -I . -I ../etc pa_macro.cmo q_MLast.cmo pa_extend.cmo pr_r.cmo pr_extend.cmo -ignloaddir -quotify $IFILE | sed -e "1,/$TEXTBEG/d" -e "/$TEXTEND/,${D}d" | sed -e "/-- cut 1 begin --/,/-- cut 1 end --/d" | sed -e "/-- cut 2 begin --/,/-- cut 2 end --/d"
echo "  (* $TEXTEND *)"
sed -e "1,/$TEXTEND/d" $OFILE
)
