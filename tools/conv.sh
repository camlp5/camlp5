#!/bin/bash

DIR=`expr "$0" : "\(.*\)/.*" "|" "."`
INCL=
FILE=
OPTS="-mode T"
PR_O=$1
if [ "$PR_O" = "pr_o.cmo" ]; then
  KWD_O="$DIR/../etc/o_keywords.cmo";
  PR_O="$DIR/../etc/print_o.cmo $DIR/../etc/pr_o.cmo" ;
 fi
if [ "$PR_O" = "pr_r.cmo" ]; then
  KWD_O="$DIR/../etc/r_keywords.cmo";
  PR_O="$DIR/../etc/print_r.cmo $DIR/../etc/pr_r.cmo" ;
 fi
DEF=
shift
while test "" != "$1"; do
  case $1 in
  -I) INCL="$INCL -I $2"; shift;;
  -D*) OPTS="$OPTS $1";;
  -defined) OPTS="$OPTS $1";;
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
    COMM="${OCAMLN}run$EXE $DIR/../meta/$WHAT -nolib -I $DIR/../meta $INCL $KWD_O $PR_O";;
  *) echo "not impl $WHAT" 1>&2; exit 2;;
  esac
  shift; shift
  ARGS=`echo $* | sed -e "s/[()*]//g"`
  echo $COMM $ARGS $OPTS -flag M $FILE >&2
  $COMM $ARGS $OPTS -flag M $FILE
else
  cat $FILE
fi
