#!/bin/sh
# $Id: depend.sh,v 1.2 2007/07/11 09:46:18 deraugla Exp $

ARGS1="pr_depend.cmo --"
FILE=
while test "" != "$1"; do
	case $1 in
	*.ml*) FILE=$1;;
	*) ARGS1="$ARGS1 $1";;
	esac
	shift
done

head -1 $FILE >/dev/null || exit 1

set - `head -1 $FILE`
if test "$2" = "camlp4r" -o "$2" = "camlp4"; then
	WHAT="$(echo $2 | sed -e "s/camlp4/$NAME/")"
	COMM="../boot/$WHAT -nolib -I ../boot -I ../etc"
	shift; shift
	ARGS2=`echo $* | sed -e "s/[()*]//g"`
else
	COMM="../boot/main -nolib -I ../boot -I ../etc pa_o.cmo"
	ARGS2=
fi

OTOP=../..
echo ocamlrun $COMM $ARGS2 $ARGS1 $FILE 1>&2
ocamlrun $COMM $ARGS2 $ARGS1 $FILE
