# $Id: Makefile,v 6.2 2012/03/02 16:03:59 deraugla Exp $

FILES=warnings.cmi pconfig.cmo
INCL=

all: $(FILES)

opt: pconfig.cmx

clean:
	rm -f *.cm[oix] *.o

depend:
	ocamldep $(INCL) *.ml* | sed -e 's/  *$$//' > .depend

.SUFFIXES: .mli .cmi .ml .cmo .cmx

.mli.cmi:
	$(OCC) $(INCL) -c $<

.ml.cmo:
	$(OCC) $(INCL) -c $<

.ml.cmx:
	$(OCOPT) $(INCL) -c $<

include .depend
