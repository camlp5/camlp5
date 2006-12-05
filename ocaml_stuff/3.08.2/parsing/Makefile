# $Id: Makefile,v 1.1 2006/12/05 13:35:11 deraugla Exp $

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
