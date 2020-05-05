# Makefile,v
# Copyright (c) INRIA 2007-2017

TOP=..
include $(TOP)/config/Makefile


all: papr_official.exe

DEBUG := -g
RM=rm
LAUNCH=env TOP=$(TOP) $(TOP)/tools/LAUNCH
CAMLP5LIB=$(shell $(OCAMLFIND) query camlp5)
CAMLP5R=$(LAUNCH) camlp5r -I $(CAMLP5LIB)
OCAMLFIND=$(LAUNCH) ocamlfind

.PRECIOUS: papr_official.ppo.ml

papr_official.ppo.ml: papr_official.ml
	$(CAMLP5R) pr_o.cmo -I . -mode S -o papr_official.ppo.ml papr_official.ml

papr_official.exe: papr_official.ppo.ml
	$(OCAMLFIND) ocamlc $(DEBUG) -custom -package compiler-libs.common,str,fmt,unix -linkall -linkpkg papr_official.ppo.ml -o papr_official.exe

install: all
	cp papr_official.exe "$(DESTDIR)$(LIBDIR)/$(CAMLP5N)/."

clean:
	$(RM) -f *.cm* *.exe

realclean: clean
	$(RM) -f papr_official.ppo.ml
