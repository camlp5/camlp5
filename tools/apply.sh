#!/bin/sh
# apply.sh,v

ARGS1=
ARGS2=
ARGS3=
FILE=
while [ $# -gt 0 ]; do
	case "$1" in
	*.ml*) FILE=$1;;
	*.cm[oa]) ARGS2="$ARGS2 $1";;
	-I) ARGS2="$ARGS2 $1 $2"; shift;;
        '') ARGS3="$ARGS3 ''";;
	*) ARGS3="$ARGS3 $1";;
	esac
	shift
done

head -1 "$FILE" >/dev/null || exit 1

set - `head -1 $FILE`
if test "$2" = "camlp5r" -o "$2" = "camlp5"; then
	COMM="../boot/$2 -nolib -I ../boot -I ../etc"
	shift; shift
	ARGS1=`echo $* | sed -e "s/[()*]//g"`
else
	COMM="../boot/camlp5 -nolib -I ../boot -I ../etc pa_o.cmo"
	ARGS1=
fi

ocamlrun $COMM $ARGS1 $ARGS2 $ARGS3 $FILE
