# $Id: Makefile,v 1.2 2010/09/01 17:07:42 deraugla Exp $

FILES=asttypes.cmi location.cmi longident.cmi parsetree.cmi
INCL=-I ../utils

all: $(FILES)

clean:
	rm -f *.cmi

depend:
	ocamldep $(INCL) *.ml* | sed -e 's/  *$$//' > .depend

.SUFFIXES: .mli .cmi

.mli.cmi:
	ocamlc $(INCL) -c $<

include .depend
