# Makefile,v

FILES=asttypes.cmi location.cmi longident.cmi parsetree.cmi
INCL=-I ../utils

all: $(FILES)

clean:
	rm -f *.cmi

depend:
	ocamldep $(INCL) *.ml* | sed -e 's/  *$$//' > .depend

.SUFFIXES: .mli .cmi

.mli.cmi:
	$(OCAMLN)c $(INCL) -c $<

include .depend
