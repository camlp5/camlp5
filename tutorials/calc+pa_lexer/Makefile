
TOP=../..

LAUNCH=env TOP=$(TOP) $(TOP)/tools/LAUNCH
OCAMLFIND=$(LAUNCH) ocamlfind
NOT_OCAMLFIND=$(LAUNCH) not-ocamlfind
PACKAGES=camlp5,fmt

all: calc calc.opt

calc: calc_lexer.cmo calc.cmo
	$(OCAMLFIND) ocamlc $(DEBUG) -package $(PACKAGES) -linkall -linkpkg -syntax camlp5r $^ -o $@

calc.opt: calc_lexer.cmx calc.cmx
	$(OCAMLFIND) ocamlopt $(DEBUG) -package $(PACKAGES) -linkall -linkpkg -syntax camlp5r $^ -o $@

.SUFFIXES: .ml .cmo .cmx

calc.cmo: calc.ml
	$(OCAMLFIND) ocamlc $(DEBUG) -package $(PACKAGES) -linkall -linkpkg -syntax camlp5r -c $<

calc.cmx: calc.ml
	$(OCAMLFIND) ocamlopt $(DEBUG) -package $(PACKAGES) -linkall -linkpkg -syntax camlp5r -c $<

calc_lexer.cmo: calc_lexer.ml
	$(NOT_OCAMLFIND) preprocess -package $(PACKAGES) -syntax camlp5r $< > calc_lexer.ppo.ml
	$(OCAMLFIND) ocamlc $(DEBUG) -package $(PACKAGES) -linkall -linkpkg -syntax camlp5r -c $<

calc_lexer.cmx: calc_lexer.ml
	$(OCAMLFIND) ocamlopt $(DEBUG) -package $(PACKAGES) -linkall -linkpkg -syntax camlp5r -c $<

clean:
	rm -f calc calc.opt *.cm* *.o *.ppo.ml

