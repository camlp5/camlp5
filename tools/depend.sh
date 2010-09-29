#!/bin/sh
# $Id: depend.sh,v 6.2 2010/09/29 12:22:11 deraugla Exp $

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
if test "$2" = "camlp5r" -o "$2" = "camlp5"; then
  WHAT="$2"
  case "$WHAT" in
  camlp5) COMM="../main/$WHAT -nolib -I ../meta -I ../etc";;
  camlp5r) COMM="../meta/$WHAT -nolib -I ../meta -I ../etc";;
  *) echo "internal error: bad value of WHAT" 1>&2; exit 2;;
  esac
  shift; shift
  ARGS2=`echo $* | sed -e "s/[()*]//g"`
else
  COMM="../boot/camlp5 -nolib -I ../boot -I ../etc pa_o.cmo"
  ARGS2=
fi

echo ocamlrun $COMM $ARGS2 $ARGS1 $FILE 1>&2
ocamlrun $COMM $ARGS2 $ARGS1 $FILE
