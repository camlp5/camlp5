#!/bin/bash

FILE=
while test "" != "$1"; do
	case "$1" in
	*.ml*) FILE=$1; break;;
	esac
	shift
done

CP="ln -sf"
CP=cp
if test "$(basename $FILE .mli).mli" = "$FILE"; then
  echo $CP $FILE $(basename $FILE .mli).ppi
  $CP $FILE $(basename $FILE .mli).ppi
else
  echo $CP $FILE $(basename $FILE .ml).ppo
  $CP $FILE $(basename $FILE .ml).ppo
fi
