
OCAMLFIND=ocamlfind
PACKAGES=fmt,camlp5.extend

all: calc calc.opt

calc: calc.ml
	$(OCAMLFIND) ocamlc -package $(PACKAGES) -linkpkg -syntax camlp5r calc.ml -o $@

calc.opt: calc.ml
	$(OCAMLFIND) ocamlopt -package $(PACKAGES) -linkpkg -syntax camlp5r calc.ml -o $@

test:: all
	./calc '1+1' '1 - 1' '1 + (2 * 3)'

clean:
	rm -f calc calc.opt *.cm* *.o

