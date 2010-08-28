#!/bin/sh

FILE=
while test "" != "$1"; do
	case "$1" in
	*.ml*) FILE=$1; break;;
	esac
	shift
done

if test "`basename $FILE .mli`.mli" = "$FILE"; then
  OFILE=`basename $FILE .mli`.ppi
else
  OFILE=`basename $FILE .ml`.ppo
fi
echo "# 1 \"$FILE\"" > $OFILE
echo cat $FILE ">" $OFILE
cat $FILE >> $OFILE
