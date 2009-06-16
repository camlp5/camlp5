#!/bin/sh
# $Id: camlp5_comm.sh,v 1.10 2008/06/05 11:56:12 deraugla Exp $

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
	WHAT=`echo $2 | sed -e "s/camlp5/$NAME/"`
	COMM="ocamlrun$EXE ../boot/$WHAT$EXE -nolib -I ../boot"
        dir=`dirname $OTOP`
        if test "`basename $dir`" != "ocaml_stuff"; then
            COMM="$OTOP/boot/$COMM"
        fi
	shift; shift
	ARGS2=`echo $* | sed -e "s/[()*]//g"`
#	ARGS2=`echo $ARGS2 | sed -e "s/q_MLast.cmo/q_ast.cmo/"`
#	ARGS1="$ARGS1 -verbose"
	if test "$QUIET" = "no"; then echo $COMM $ARGS2 $ARGS1 $FILE; fi
	$COMM $ARGS2 $ARGS1 $FILE
else
	if test "`basename $FILE .mli`.mli" = "$FILE"; then
		OFILE=`basename $FILE .mli`.ppi
	else
		OFILE=`basename $FILE .ml`.ppo
	fi
	if test "$QUIET" = "no"; then echo cp $FILE $OFILE; fi
	cp $FILE $OFILE
fi
