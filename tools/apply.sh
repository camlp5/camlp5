#!/bin/sh
# $Id: apply.sh,v 1.6 2007/06/13 08:48:45 deraugla Exp $

ARGS1=
ARGS3=
FILE=
while test "" != "$1"; do
	case $1 in
	*.ml*) FILE=$1;;
	*.cm[oa]) ARGS1="$ARGS1 $1";;
	-I) ARGS1="$ARGS1 $1 $2"; shift;;
	*) ARGS3="$ARGS3 $1";;
	esac
	shift
done

head -1 $FILE >/dev/null || exit 1

set - `head -1 $FILE`
if test "$2" = "camlp4r" -o "$2" = "camlp4"; then
	COMM="../boot/$2 -nolib -I ../boot -I ../etc"
	shift; shift
	ARGS2=`echo $* | sed -e "s/[()*]//g"`
else
	COMM="../boot/camlp4 -nolib -I ../boot -I ../etc pa_o.cmo"
	ARGS2=
fi

OTOP=../..
echo ocamlrun $COMM $ARGS1 $ARGS2 $ARGS3 $FILE 1>&2
ocamlrun $COMM $ARGS1 $ARGS2 $ARGS3 $FILE
