#!/bin/sh

IFILE=pa_r.ml
OFILE=q_MLast.ml
TEXTBEG="-- begin copy from pa_r to q_MLast --"
TEXTEND="-- end copy from pa_r to q_MLast --"
D='$'

(
sed -e "/$TEXTBEG/,${D}d" $OFILE
echo "(* $TEXTBEG *)"
${OCAMLN}run ./camlp5r -nolib -I . -I ../etc pa_macro.cmo q_MLast.cmo pa_extend.cmo pr_r.cmo pr_extend.cmo -DJOCAML -ignloaddir -quotify $IFILE | sed -e "1,/$TEXTBEG/d" -e "/$TEXTEND/,${D}d" | sed -e "/-- cut 1 begin --/,/-- cut 1 end --/d" | sed -e "/-- cut 2 begin --/,/-- cut 2 end --/d"
echo "  (* $TEXTEND *)"
sed -e "1,/$TEXTEND/d" $OFILE
)
