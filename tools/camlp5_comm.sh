#!/bin/sh
# $Id: camlp5_comm.sh,v 6.1 2010/09/15 16:00:48 deraugla Exp $

ARGS1="-mode $MODE"
FILE=
QUIET=no
while test "" != "$1"; do
  case $1 in
  -q) QUIET=yes;;
  *.ml*) FILE=$1;;
  *) ARGS1="$ARGS1 $1";;
  esac
  shift
done

head -1 $FILE >/dev/null || exit 1

set - `head -1 $FILE`
if test "$2" = "camlp5r" -o "$2" = "camlp5"; then
  WHAT="$2"
  case "$COMPWITH/$WHAT" in
  old/*)
    COMM="ocamlrun$EXE ../boot/$WHAT$EXE -nolib -I ../boot";;
  new/camlp5)
    COMM="ocamlrun$EXE ../main/$WHAT$EXE -nolib -I ../meta -I ../etc";;
  new/camlp5r)
    COMM="ocamlrun$EXE ../meta/$WHAT$EXE -nolib -I ../meta -I ../etc";;
  *)
    echo "internal error: bad value of COMPWITH/WHAT" 1>&2; exit 2;;
  esac
  shift; shift
  ARGS2=`echo $* | sed -e "s/[()*]//g"`
  if test "$QUIET" = "no"; then echo $COMM $ARGS2 $ARGS1 $FILE; fi
  $COMM $ARGS2 $ARGS1 $FILE
else
  if test "`basename $FILE .mli`.mli" = "$FILE"; then
    OFILE=`basename $FILE .mli`.ppi
  else
    OFILE=`basename $FILE .ml`.ppo
  fi
  if test "$QUIET" = "no"; then echo cp $FILE $OFILE; fi
  echo "# 1 \"$FILE\"" > $OFILE
  echo cat $FILE ">" $OFILE
  cat $FILE >> $OFILE
fi
