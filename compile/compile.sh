#!/bin/sh -e

ARGS=
FILES=
ENTRIES=
while test "" != "$1"; do
	case $1 in
        -e)
           shift;
           if test "$ENTRIES" != ""; then ENTRIES="$ENTRIES; "; fi
           ENTRIES="$ENTRIES$1";;
	*.ml*) FILES="$FILES $1";;
	*) ARGS="$ARGS $1";;
	esac
	shift
done

cat $FILES | sed -e 's/Pcaml.parse_i.*$//' -e 's|/; ||g' |
grep -v '#load' > tmp.ml
echo "Compile.entries.val := [$ENTRIES];" >> tmp.ml
> tmp.mli
echo "${OCAMLN}c -c tmp.mli" 1>&2
${OCAMLN}c -c tmp.mli
echo "${OCAMLN}run$EXE ../meta/${CAMLP5N}r$EXE -nolib -I ../meta pa_macro.cmo pa_extend.cmo q_MLast.cmo -meta_action tmp.ml -o tmp.ppo" 1>&2
${OCAMLN}run$EXE ../meta/${CAMLP5N}r$EXE -nolib -I ../meta pa_macro.cmo pa_extend.cmo q_MLast.cmo -meta_action tmp.ml -o tmp.ppo
echo "${OCAMLN}c -I ../lib -I ../main -c -impl tmp.ppo" 1>&2
${OCAMLN}c -I ../lib -I ../main -c -impl tmp.ppo
echo "/bin/rm tmp.ppo" 1>&2
/bin/rm tmp.ppo
echo "${OCAMLN}run$EXE ../main/${CAMLP5N}$EXE ./compile.cmo ./tmp.cmo ../etc/pr_r.cmo ../etc/pr_rp.cmo $ARGS -sep "\n\n" -impl - < /dev/null" 1>&2
${OCAMLN}run$EXE ../main/${CAMLP5N}$EXE ./compile.cmo ./tmp.cmo ../etc/pr_r.cmo ../etc/pr_rp.cmo $ARGS -sep "\n\n" -impl - < /dev/null
/bin/rm tmp.*
