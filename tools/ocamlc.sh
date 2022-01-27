#!/bin/sh -e

COMM=${OCAMLN}c
if [ "$OVERSION" "<" "4.14" ]; then
  PACK=compiler-libs
else
  PACK=camlp-streams,compiler-libs
fi

echo ocamlfind $COMM -package $PACK $*
ocamlfind $COMM -package $PACK $*
