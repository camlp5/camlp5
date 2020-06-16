
TOP=../..
include $(TOP)/config/Makefile

LAUNCH=env TOP=$(TOP) $(TOP)/tools/LAUNCH
OCAMLFIND=$(LAUNCH) ocamlfind

all: calc calc.opt

calc: calc.ml
	$(OCAMLFIND) ocamlc -package camlp5 -linkall -linkpkg -syntax camlp5r calc.ml -o $@

calc.opt: calc.ml
	$(OCAMLFIND) ocamlopt -package camlp5 -linkall -linkpkg -syntax camlp5r calc.ml -o $@

clean:
	rm -f calc calc.opt *.cm* *.o

