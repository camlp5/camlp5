# $Id: Makefile,v 1.1 2006/12/01 10:37:34 deraugla Exp $

FILES=asttypes.cmi location.cmi longident.cmi parsetree.cmi
INCL=-I ../utils

all: $(FILES)

clean:
	rm -f *.cmi

depend:
	ocamldep $(INCL) *.ml* > .depend

.SUFFIXES: .mli .cmi

.mli.cmi:
	ocamlc $(INCL) -c $<

include .depend
