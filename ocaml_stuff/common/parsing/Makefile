# $Id: Makefile,v 6.2 2012/03/02 16:03:59 deraugla Exp $

FILES=asttypes.cmi location.cmi longident.cmi parsetree.cmi
INCL=-I ../utils

all: $(FILES)

clean:
	rm -f *.cmi

depend:
	ocamldep $(INCL) *.ml* | sed -e 's/  *$$//' > .depend

.SUFFIXES: .mli .cmi

.mli.cmi:
	$(OCC) $(INCL) -c $<

include .depend
