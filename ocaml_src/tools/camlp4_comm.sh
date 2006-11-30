#!/bin/sh

FILE=
while test "" != "$1"; do
	case "$1" in
	*.ml*) FILE=$1; break;;
	esac
	shift
done

if test "$(basename $FILE .mli).mli" = "$FILE"; then
  echo cp $FILE $(basename $FILE .mli).ppi
  cp $FILE $(basename $FILE .mli).ppi
else
  echo cp $FILE $(basename $FILE .ml).ppo
  cp $FILE $(basename $FILE .ml).ppo
fi
