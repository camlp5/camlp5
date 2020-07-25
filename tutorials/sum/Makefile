
OCAMLFIND=ocamlfind
NOT_OCAMLFIND=not-ocamlfind
PACKAGES=fmt,camlp5.extend,camlp5.extfold,camlp5.quotations

all: sum_revised.cmo sum_original.cmo


.SUFFIXES: .ml .cmo .cmx

sum_original.cmo: sum_original.ml
	$(OCAMLFIND) ocamlc $(DEBUG) -package $(PACKAGES) -syntax camlp5o -c $<

sum_revised.cmo: sum_revised.ml
	$(OCAMLFIND) ocamlc $(DEBUG) -package $(PACKAGES) -syntax camlp5r -c $<

clean:
	rm -f  *.cm* *.o *.ppo.ml

