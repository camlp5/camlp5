# $Id: Makefile,v 1.2 2010/09/01 17:07:42 deraugla Exp $

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
	ocamlc $(INCL) -c $<

.ml.cmo:
	ocamlc $(INCL) -c $<

.ml.cmx:
	ocamlopt $(INCL) -c $<

include .depend
