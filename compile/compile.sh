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

cat $FILES | sed -e 's/Pcaml.parse_i.*$//' | grep -v '#load' > tmp.ml
echo "Compile.entries.val := [$ENTRIES];" >> tmp.ml
> tmp.mli
echo "ocamlc -I $OTOP/boot -c tmp.mli" 1>&2
ocamlc -I $OTOP/boot -c tmp.mli
echo "ocamlrun$EXE ../meta/camlp5r$EXE -nolib -I ../meta pa_macro.cmo pa_extend.cmo q_MLast.cmo -meta_action tmp.ml -o tmp.ppo" 1>&2
ocamlrun$EXE ../meta/camlp5r$EXE -nolib -I ../meta pa_macro.cmo pa_extend.cmo q_MLast.cmo -meta_action tmp.ml -o tmp.ppo
echo "ocamlc -I $OTOP/boot -I ../lib -I ../main -c -impl tmp.ppo" 1>&2
ocamlc -I $OTOP/boot -I ../lib -I ../main -c -impl tmp.ppo
echo "rm tmp.ppo" 1>&2
rm tmp.ppo
echo "ocamlrun$EXE ../main/camlp5$EXE ./compile.cmo ./tmp.cmo ../etc/pr_r.cmo ../etc/pr_rp.cmo $ARGS -sep "\n\n" -impl - < /dev/null" 1>&2
ocamlrun$EXE ../main/camlp5$EXE ./compile.cmo ./tmp.cmo ../etc/pr_r.cmo ../etc/pr_rp.cmo $ARGS -sep "\n\n" -impl - < /dev/null
rm tmp.*
