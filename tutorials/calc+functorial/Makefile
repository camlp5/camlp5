
OCAMLFIND=ocamlfind
PACKAGES=fmt,camlp5.extend

all: calc calc.opt

calc: calclexer.cmo calc.cmo
	$(OCAMLFIND) ocamlc $(DEBUG) -package $(PACKAGES) -linkpkg -syntax camlp5r $^ -o $@

calc.opt: calclexer.cmx calc.cmx
	$(OCAMLFIND) ocamlopt $(DEBUG) -package $(PACKAGES) -linkpkg -syntax camlp5r $^ -o $@

.SUFFIXES: .mll .ml .cmo .cmx

calclexer.cmo: calclexer.ml
	$(OCAMLFIND) ocamlc $(DEBUG) -package $(PACKAGES) -syntax camlp5o -c $<

calclexer.cmx: calclexer.ml
	$(OCAMLFIND) ocamlopt $(DEBUG) -package $(PACKAGES) -syntax camlp5o -c $<

calc.cmo: calc.ml
	$(OCAMLFIND) ocamlc $(DEBUG) -package $(PACKAGES) -syntax camlp5r -c $<

calc.cmx: calc.ml
	$(OCAMLFIND) ocamlopt $(DEBUG) -package $(PACKAGES) -syntax camlp5r -c $<

test:: all
	./calc '1+1' '1 - 1' '1 + (2 * 3)'

.mll.ml:
	ocamllex $<

clean:
	rm -f calc calc.opt *.cm* *.o calclexer.ml

