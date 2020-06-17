
TOP=../..

LAUNCH=env TOP=$(TOP) $(TOP)/tools/LAUNCH
OCAMLFIND=$(LAUNCH) ocamlfind
NOT_OCAMLFIND=$(LAUNCH) not-ocamlfind
PACKAGES=camlp5,fmt

all: calc calc.opt

calc: calc.cmo
	$(OCAMLFIND) ocamlc $(DEBUG) -package $(PACKAGES) -linkall -linkpkg -syntax camlp5r $^ -o $@

calc.opt: calc.cmx
	$(OCAMLFIND) ocamlopt $(DEBUG) -package $(PACKAGES) -linkall -linkpkg -syntax camlp5r $^ -o $@

.SUFFIXES: .ml .cmo .cmx

calc.cmo: calc.ml
	$(OCAMLFIND) ocamlc $(DEBUG) -package $(PACKAGES) -linkall -linkpkg -syntax camlp5r -c $<

calc.cmx: calc.ml
	$(OCAMLFIND) ocamlopt $(DEBUG) -package $(PACKAGES) -linkall -linkpkg -syntax camlp5r -c $<

clean:
	rm -f calc calc.opt *.cm* *.o *.ppo.ml

