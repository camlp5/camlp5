
TOP=../..
include $(TOP)/config/Makefile

LAUNCH=env TOP=$(TOP) $(TOP)/tools/LAUNCH
OCAMLFIND=$(LAUNCH) ocamlfind
PACKAGES=camlp5,fmt

all: streams streams.opt

streams: streams.ml
	$(OCAMLFIND) ocamlc -package $(PACKAGES) -linkall -linkpkg -syntax camlp5o streams.ml -o $@

streams.opt: streams.ml
	$(OCAMLFIND) ocamlopt -package $(PACKAGES) -linkall -linkpkg -syntax camlp5o streams.ml -o $@

clean:
	rm -f streams streams.opt *.cm* *.o

