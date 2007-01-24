#!/bin/bash

DIR=$(expr "$0" : "\(.*\)/.*" "|" ".")
INCL=
FILE=
OPTS=
while test "" != "$1"; do
	case $1 in
	-I) INCL="$INCL -I $2"; shift;;
	-D*) OPTS="$OPTS $1";;
	*) FILE=$1;;
	esac
	shift
done

set - $(head -1 $FILE)
if test "$2" = "camlp4r" -o "$2" = "camlp4"; then
	COMM="ocamlrun $DIR/../boot/$2 -nolib -I $DIR/../boot $INCL $DIR/../etc/pr_o.cmo"
        if test "$(basename "$(dirname $OTOP)")" != "ocaml_stuff"; then
            COMM="$OTOP/boot/$COMM"
        fi
	shift; shift
	ARGS=$(echo $* | sed -e "s/[()*]//g")
	$COMM $ARGS $OPTS -ss $FILE
else
	cat $FILE
fi
