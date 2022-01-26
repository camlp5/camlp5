#!/bin/sh -e

COMM=${OCAMLN}c
echo ocamlfind $COMM -package camlp-streams $*
ocamlfind $COMM -package camlp-streams $*
