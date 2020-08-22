# Makefile,v

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
	$(OCAMLN)c -g $(INCL) -c $<

.ml.cmo:
	$(OCAMLN)c -g $(INCL) -c $<

.ml.cmx:
	$(OCAMLN)opt -g $(INCL) -c $<

include .depend
