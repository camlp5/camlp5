#!/bin/sh
# camlp5_comm.sh,v

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
  if [ "$2" = "camlp5r" ]; then WHAT="${CAMLP5N}r"
  else WHAT="${CAMLP5N}"; fi
  case "$COMPWITH/$WHAT" in
  old/*)
    COMM="${OCAMLN}run$EXE ../boot/$WHAT$EXE -nolib -I ../boot";;
  new/${CAMLP5N})
    COMM="${OCAMLN}run$EXE ../main/$WHAT$EXE -nolib -I ../meta -I ../etc";;
  new/${CAMLP5N}r)
    COMM="${OCAMLN}run$EXE ../meta/$WHAT$EXE -nolib -I ../meta -I ../etc";;
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
