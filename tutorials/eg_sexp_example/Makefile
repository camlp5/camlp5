# Makefile,v
# Copyright (c) INRIA 2007-2017

include Makefile.include

PACKAGES := $(PACKAGES),fmt,sexp_example.parser

ML=\
	eg_quotations.ml eg_parsing.ml eg_q_ast.ml \

CMO := $(ML:.ml=.cmo)
CMI := $(ML:.ml=.cmi)
CMX := $(ML:.ml=.cmx)
CMT := $(ML:.ml=.cmt)
CMTI := $(MLI:.mli=.cmti)

all: $(CMO) $(CMX)

test:

doc: $(CMT) $(CMTI)

eg_quotations.cmo: eg_quotations.ml
eg_parsing.cmo: eg_parsing.ml
eg_q_ast.cmo: eg_q_ast.ml

.ml.cmo:
	$(LAUNCH) $(YAWRAP) $(OCAMLFIND) ocamlc $(DEBUG) $(OCAMLCFLAGS) -package $(PACKAGES) -c $<

.ml.cmx:
	$(LAUNCH) $(YAWRAP) $(OCAMLFIND) ocamlopt $(DEBUG) $(OCAMLCFLAGS) -package $(PACKAGES) -c $<


.SUFFIXES: .cmo .cmi .ml .mli .cmx .cma .cmxa .cmt .cmti

clean::
	rm -rf META *.cm* *.o

EXTERNAL := $(shell $(LAUNCH) $(OCAMLFIND) query -predicates byte -format '%m' $(PACKAGES) | grep local-install)
$(CMO) $(CMI) $(CMX): $(EXTERNAL)

depend::
	echo "$(CMO) $(CMI) $(CMX): $(EXTERNAL)" > .depend.NEW
	$(LAUNCH) $(YAWRAP) $(OCAMLFIND) ocamldep $(DEBUG) -package $(PACKAGES) -syntax $(SYNTAX) *.ml >> .depend.NEW \
		&& mv .depend.NEW .depend

-include .depend
