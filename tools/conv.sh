#!/bin/bash

DIR=$(expr "$0" : "\(.*\)/.*" "|" ".")
INCL=
FILE=
OPTS="-mode T"
PR_O=$1
shift
while test "" != "$1"; do
	case $1 in
	-I) INCL="$INCL -I $2"; shift;;
	-D*) OPTS="$OPTS $1";;
	-U*) OPTS="$OPTS $1";;
	*) FILE=$1;;
	esac
	shift
done

set - $(head -1 $FILE)
if test "$2" = "camlp5r" -o "$2" = "camlp5"; then
	WHAT="$(echo $2 | sed -e "s/camlp5/$NAME/")"
	COMM="ocamlrun $DIR/../boot/$WHAT -nolib -I $DIR/../boot $INCL $DIR/../etc/$PR_O"
        if test "$(basename "$(dirname $OTOP)")" != "ocaml_stuff"; then
            COMM="$OTOP/boot/$COMM"
        fi
	shift; shift
	ARGS=$(echo $* | sed -e "s/[()*]//g")
	$COMM $ARGS $OPTS -ss $FILE
else
	cat $FILE
fi
