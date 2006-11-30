# $Id: Makefile,v 1.1 2006/11/30 14:32:03 deraugla Exp $

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
