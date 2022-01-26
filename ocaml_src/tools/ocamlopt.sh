#!/bin/sh -e

COMM=${OCAMLN}opt
echo ocamlfind $COMM -package camlp-streams $*
ocamlfind $COMM -package camlp-streams $*
