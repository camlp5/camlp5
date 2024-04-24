# Makefile,v
# Copyright (c) INRIA 2007-2017

TOP=..
include $(TOP)/config/Makefile

DIFF=diff -Bwi -u20
RM=rm

TOOLS=o_lexer_kwds r_lexer_kwds

export LC_ALL=C

all: o_lexer_kwds.byte \
	r_lexer_kwds.byte \

OCAMLFIND=$(LAUNCH) ocamlfind
OCAMLTOPLEVEL=$(LAUNCH) ocaml
CAMLP5LIB=$(shell $(OCAMLFIND) query camlp5)
MKCAMLP5=$(LAUNCH) mkcamlp5 -verbose
MKCAMLP5OPT=$(LAUNCH) mkcamlp5.opt -verbose
CAMLP5R=$(LAUNCH) camlp5r -I $(CAMLP5LIB)
INCLUDES=-I $(CAMLP5LIB)
OCAMLCFLAGS=$(DEBUG) $(WARNERR) $(INCLUDES)
COMPILERLIBS= -I +compiler-libs ocamlcommon.cma ocamlbytecomp.cma ocamltoplevel.cma
PACKAGES_NOCAMLP5=rresult,fmt,pcre2,ounit2,compiler-libs.common,$(C5PACKAGES)
PACKAGES=$(PACKAGES_NOCAMLP5),camlp5,camlp5.macro


o_lexer_kwds:: o_lexer_kwds.byte
	$(NOVERBOSE) mkdir -p _build
	./o_lexer_kwds.byte $(TESTARGS)

o_lexer_kwds.byte: lexer_kwds.ml
	$(OCAMLFIND) ocamlc $(DEBUG) -package $(PACKAGES),ounit2,camlp5.extend,camlp5.extprint,camlp5.extfun,camlp5.pprintf,camlp5.pa_o.link,camlp5.quotations -syntax camlp5r -I ../main -linkall -linkpkg lexer_kwds.ml -o o_lexer_kwds.byte

r_lexer_kwds:: r_lexer_kwds.byte
	$(NOVERBOSE) mkdir -p _build
	./r_lexer_kwds.byte $(TESTARGS)

r_lexer_kwds.byte: lexer_kwds.ml
	$(OCAMLFIND) ocamlc $(DEBUG) -package $(PACKAGES),ounit2,camlp5.extend,camlp5.extprint,camlp5.extfun,camlp5.pprintf,camlp5.pa_r.link,camlp5.quotations -syntax camlp5r -I ../main -linkall -linkpkg lexer_kwds.ml -o r_lexer_kwds.byte

clean:
	$(RM) -f *.cm* *.byte *.log *.cache *.ppo tools/*.byte link*

realclean: clean
