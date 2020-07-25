
OCAMLFIND=ocamlfind
PACKAGES=camlp5,fmt

all: streams streams.opt

streams: streams.ml
	$(OCAMLFIND) ocamlc -package $(PACKAGES) -linkpkg -syntax camlp5r streams.ml -o $@

streams.opt: streams.ml
	$(OCAMLFIND) ocamlopt -package $(PACKAGES) -linkpkg -syntax camlp5r streams.ml -o $@

test:: all
	./streams '1+1' '1 - 1' '1 + (2 * 3)'

clean:
	rm -f streams streams.opt *.cm* *.o

