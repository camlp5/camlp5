#!/bin/sh
# depend.sh,v

ARGS1="pr_depend.cmo --"
FILE=
CAMLP5N=camlp5
while test "" != "$1"; do
  case $1 in
  -name) CAMLP5N="$2"; shift;;
  *.ml*) FILE=$1;;
  *) ARGS1="$ARGS1 $1";;
  esac
  shift
done

head -1 $FILE >/dev/null || exit 1

set - `head -1 $FILE`
if test "$2" = "camlp5r" -o "$2" = "camlp5"; then
  if [ "$2" = "camlp5r" ]; then WHAT="${CAMLP5N}r"
  else WHAT="${CAMLP5N}"; fi
  case "$WHAT" in
  ${CAMLP5N}) COMM="../main/$WHAT -nolib -I ../meta -I ../etc";;
  ${CAMLP5N}r) COMM="../meta/$WHAT -nolib -I ../meta -I ../etc";;
  *) echo "internal error: bad value of WHAT" 1>&2; exit 2;;
  esac
  shift; shift
  ARGS2=`echo $* | sed -e "s/[()*]//g"`
else
  COMM="../boot/${CAMLP5N} -nolib -I ../boot -I ../etc pa_o.cmo"
  ARGS2=
fi

echo ocamlrun $COMM $ARGS2 $ARGS1 $FILE 1>&2
ocamlrun $COMM $ARGS2 $ARGS1 $FILE
