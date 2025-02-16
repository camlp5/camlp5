TOP=../..

LAUNCH=env TOP=$(TOP) ocamlfind camlp5-buildscripts/LAUNCH --
OCAMLFIND=$(LAUNCH) ocamlfind
NOT_OCAMLFIND=$(LAUNCH) not-ocamlfind
PACKAGES=camlp5,fmt,ounit2

all: streams streams.opt

streams.cmo: streams.ml
	$(OCAMLFIND) ocamlc -package $(PACKAGES) -c -syntax camlp5r streams.ml

streams: streams.cmo
	$(OCAMLFIND) ocamlc -package $(PACKAGES) -linkpkg -syntax camlp5r streams.cmo -o $@

streams_ppo.ml: streams.ml
	$(NOT_OCAMLFIND) preprocess -package $(PACKAGES),camlp5.pr_o  -syntax camlp5r streams.ml > $@

streams.opt: streams.ml
	$(OCAMLFIND) ocamlopt -package $(PACKAGES) -linkpkg -syntax camlp5r streams.ml -o $@

test:: all
	mkdir -p _build
	./streams

clean:
	rm -rf streams streams.opt *.cm* *.o *_ppo.ml _build

