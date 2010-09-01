# Id

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
