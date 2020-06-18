
TOP=../..

LAUNCH=env TOP=$(TOP) $(TOP)/tools/LAUNCH
OCAMLFIND=$(LAUNCH) ocamlfind
PACKAGES=camlp5,fmt,camlp5.extprint,camlp5.extend,camlp5.pprintf,pcre

all: calc calc.opt

calc: calclexer.cmo calc.cmo
	$(OCAMLFIND) ocamlc $(DEBUG) -package $(PACKAGES) -linkall -linkpkg -syntax camlp5r $^ -o $@

calc.opt: calclexer.cmx calc.cmx
	$(OCAMLFIND) ocamlopt $(DEBUG) -package $(PACKAGES) -linkall -linkpkg -syntax camlp5r $^ -o $@

.SUFFIXES: .mll .ml .cmo .cmx

calclexer.cmo: calclexer.ml
	$(OCAMLFIND) ocamlc $(DEBUG) -package $(PACKAGES) -linkall -linkpkg -syntax camlp5o -c $<

calclexer.cmx: calclexer.ml
	$(OCAMLFIND) ocamlopt $(DEBUG) -package $(PACKAGES) -linkall -linkpkg -syntax camlp5o -c $<

calc.cmo: calc.ml
	$(OCAMLFIND) ocamlc $(DEBUG) -package $(PACKAGES) -linkall -linkpkg -syntax camlp5r -c $<

calc.cmx: calc.ml
	$(OCAMLFIND) ocamlopt $(DEBUG) -package $(PACKAGES) -linkall -linkpkg -syntax camlp5r -c $<

.mll.ml:
	ocamllex $<

clean:
	rm -f calc calc.opt *.cm* *.o


depend::
	$(OCAMLFIND) ocamldep $(DEBUG) -package $(PACKAGES) -syntax camlp5o calclexer.ml > .depend.NEW || true
	$(OCAMLFIND) ocamldep $(DEBUG) -package $(PACKAGES) -syntax camlp5r calc.ml >> .depend.NEW \
		&& mv .depend.NEW .depend

-include .depend
