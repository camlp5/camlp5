
TOP=../..
include $(TOP)/config/Makefile

LAUNCH=env TOP=$(TOP) $(TOP)/tools/LAUNCH
OCAMLFIND=$(LAUNCH) ocamlfind
PACKAGES=camlp5,fmt

all: calc calc.opt

calc: calc.ml
	$(OCAMLFIND) ocamlc -package $(PACKAGES) -linkall -linkpkg -syntax camlp5r calc.ml -o $@

calc.opt: calc.ml calclexer.ml
	$(OCAMLFIND) ocamlopt -package $(PACKAGES) -linkall -linkpkg -syntax camlp5r calc.ml -o $@

.SUFFIXES: .mll

.mll.ml:
	ocamllex $<

clean:
	rm -f calc calc.opt *.cm* *.o

