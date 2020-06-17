
TOP=../..

LAUNCH=env TOP=$(TOP) $(TOP)/tools/LAUNCH
OCAMLFIND=$(LAUNCH) ocamlfind
NOT_OCAMLFIND=$(LAUNCH) not-ocamlfind
PACKAGES=camlp5,fmt,camlp5.extprint,camlp5.extend,camlp5.lexer,camlp5.pprintf,pcre

all: calc calc.opt

calc: calc.cmo
	$(OCAMLFIND) ocamlc $(DEBUG) -package $(PACKAGES) -linkall -linkpkg -syntax camlp5r $^ -o $@

calc.opt: calc.cmx
	$(OCAMLFIND) ocamlopt $(DEBUG) -package $(PACKAGES) -linkall -linkpkg -syntax camlp5r $^ -o $@

.SUFFIXES: .ml .cmo .cmx

calc.cmo: calc.ml
	$(NOT_OCAMLFIND) preprocess -package $(PACKAGES),camlp5.pr_r -syntax camlp5r $< > calc.ppo.ml
	$(OCAMLFIND) ocamlc $(DEBUG) -package $(PACKAGES) -syntax camlp5r -c $<

calc.cmx: calc.ml
	$(OCAMLFIND) ocamlopt $(DEBUG) -package $(PACKAGES) -syntax camlp5r -c $<

clean:
	rm -f calc calc.opt *.cm* *.o *.ppo.ml

