#!/bin/sh
# mkcamlp5.sh.tpl,v

OLIB=`OCAMLNc -where`
LIB=LIBDIR/CAMLP5N

INTERFACES=
OPTS=
INCL="-I ."
while test "" != "$1"; do
    case $1 in
    -I) INCL="$INCL -I $2"; shift;;
    -help)
        echo "Usage: mkCAMLP5N [options] [files]"
        echo "Options:"
        echo "  -I <dir>   Add directory in search patch for object files"
        echo
        echo "All options of OCAMLNc are also available"
        echo
        echo "Files:"
        echo "  .cmi file  Add visible interface for possible future loading"
        echo "  .cmo file  Load this file in core"
        echo "  .cma file  Load this file in core"
        exit 0;;
    -*) OPTS="$OPTS $1";;
    *)
	j=`basename $1 .cmi`
	if test "$j.cmi" = "$1"; then
	    first="`expr "$j" : '\(.\)' | tr 'a-z' 'A-Z'`"
	    rest="`expr "$j" : '.\(.*\)'`"
	    INTERFACES="$INTERFACES $first$rest"
	else
	    OPTS="$OPTS $1"
	fi;;
    esac
    shift
done

CRC=crc_$$
set -e
trap 'rm -f $CRC.ml $CRC.cmi $CRC.cmo' 0 2
$OLIB/extract_crc -I $OLIB $INCL $INTERFACES > $CRC.ml
echo "let _ = Dynlink.add_available_units crc_unit_list" >> $CRC.ml
OCAMLNc -I $LIB odyl.cma CAMLP5N.cma $CRC.ml $INCL $OPTS odyl.cmo -linkall
rm -f $CRC.ml $CRC.cmi $CRC.cmo
