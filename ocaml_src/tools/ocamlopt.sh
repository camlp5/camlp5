#!/bin/sh -e

COMM=${OCAMLN}opt
if [ "$OVERSION" "<" "4.14" ]; then
  PACK=compiler-libs
else
  PACK=camlp-streams,compiler-libs
fi

echo ocamlfind $COMM -package $C5PACKAGES $*
ocamlfind $COMM -package $C5PACKAGES $*
