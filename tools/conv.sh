#!/bin/bash

DIR=`expr "$0" : "\(.*\)/.*" "|" "."`
INCL=
FILE=
OPTS="-mode T"
PR_O=$1
if [ "$PR_O" = "pr_o.cmo" ]; then KWD_O="o_keywords.cmo"; fi
if [ "$PR_O" = "pr_r.cmo" ]; then KWD_O="r_keywords.cmo"; fi
DEF=
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

set - `head -1 $FILE`
if test "$2" = "camlp5r" -o "$2" = "camlp5"; then
  if [ "$2" = "camlp5r" ]; then WHAT="${CAMLP5N}r"; else WHAT="${CAMLP5N}"; fi
  case "$WHAT" in
  ${CAMLP5N}r)
    COMM="${OCAMLN}run$EXE $DIR/../meta/$WHAT -nolib -I $DIR/../meta $INCL $DIR/../etc/$KWD_O $DIR/../etc/$PR_O";;
  *) echo "not impl $WHAT" 1>&2; exit 2;;
  esac
  shift; shift
  ARGS=`echo $* | sed -e "s/[()*]//g"`
  $COMM $ARGS $OPTS -flag M $FILE
else
  cat $FILE
fi
