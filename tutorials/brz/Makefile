
export TOP = ../..

OCAMLFIND=../../tools/LAUNCH ocamlfind
PACKAGES=fmt,camlp5,camlp5.extend

all: brz.cmo sbrz.cmo

brz.cmo: brz.ml
	$(OCAMLFIND) ocamlc -package $(PACKAGES) -c -syntax camlp5r $<

sbrz.cmo: sbrz.ml
	$(OCAMLFIND) ocamlc -package $(PACKAGES) -c -syntax camlp5r $<

clean:
	rm -f *.cm* *.o

