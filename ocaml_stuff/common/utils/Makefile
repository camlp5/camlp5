# $Id: Makefile,v 1.1 2006/11/30 13:26:52 deraugla Exp $

FILES=warnings.cmi pconfig.cmo
INCL=

all: $(FILES)

opt: pconfig.cmx

clean:
	rm -f *.cm[oix] *.o

depend:
	ocamldep $(INCL) *.ml* > .depend

.SUFFIXES: .mli .cmi .ml .cmo .cmx

.mli.cmi:
	ocamlc $(INCL) -c $<

.ml.cmo:
	ocamlc $(INCL) -c $<

.ml.cmx:
	ocamlopt $(INCL) -c $<

include .depend
