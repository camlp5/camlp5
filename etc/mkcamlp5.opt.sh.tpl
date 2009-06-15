#!/bin/sh
# $Id: mkcamlp5.opt.sh.tpl,v 1.1 2007/11/20 02:55:15 deraugla Exp $

OLIB=`ocamlc -where`
LIB=LIBDIR/camlp5

INTERFACES=
OPTS=
INCL="-I ."
while test "" != "$1"; do
    case $1 in
    -I) INCL="$INCL -I $2"; shift;;
    *) OPTS="$OPTS $1";;
    esac
    shift
done

set -e
ocamlopt -I $LIB odyl.cmxa camlp5.cmxa $INCL $OPTS odyl.cmx -linkall
