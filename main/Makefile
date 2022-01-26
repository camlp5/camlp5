# Makefile,v

TOP=..
include $(TOP)/config/Makefile

SHELL=/bin/sh

INCLUDES=-I ../odyl -I $(TOP)/boot -I $(TOP)/lib
OCAMLCFLAGS=$(DEBUG) $(WARNERR) $(INCLUDES)
LINKFLAGS=$(DEBUG) $(INCLUDES)
CAMLP5_OBJS_0=$(TOP)/boot/versdep.cmo $(TOP)/boot/ploc.cmo $(TOP)/boot/plexing.cmo $(TOP)/boot/plexer.cmo $(TOP)/boot/fstream.cmo $(TOP)/boot/gramext.cmo $(TOP)/boot/grammar.cmo $(TOP)/boot/diff.cmo $(TOP)/boot/extfold.cmo $(TOP)/boot/extfun.cmo $(TOP)/boot/pretty.cmo $(TOP)/boot/pprintf.cmo $(TOP)/boot/eprinter.cmo $(OTOPU)/pconfig.cmo asttools.cmo quotation.cmo prtools.cmo reloc.cmo pp_debug.cmo pcaml.cmo ast2pt.cmo mlsyntax.cmo exparser.cmo parserify.cmo argl.cmo $(TOP)/boot/stdpp.cmo $(TOP)/boot/token.cmo
CAMLP5_OBJS=$(CAMLP5_OBJS_0) main.cmo
CAMLP5_XOBJS=../lib/versdep.cmx ../lib/ploc.cmx ../lib/plexing.cmx ../lib/plexer.cmx ../lib/fstream.cmx ../lib/gramext.cmx ../lib/grammar.cmx ../lib/diff.cmx ../lib/extfold.cmx ../lib/extfun.cmx ../lib/pretty.cmx ../lib/pprintf.cmx ../lib/eprinter.cmx $(OTOPU)/pconfig.cmx asttools.cmx quotation.cmx prtools.cmx reloc.cmx pp_debug.cmx pcaml.cmx ast2pt.cmx mlsyntax.cmx exparser.cmx parserify.cmx argl.cmx ../lib/stdpp.cmx ../lib/token.cmx main.cmx
OBJS=../odyl/odyl.cma $(CAMLP5N).cma
CAMLP5M=

CAMLP5=$(CAMLP5N)$(EXE)
CAMLP5OPT=phony

all: $(CAMLP5)
opt: $(OBJS:.cma=.cmxa)
optp5: $(CAMLP5OPT)

$(CAMLP5): $(OBJS) ../odyl/odyl.cmo
	$(OCAMLC) $(DEBUG) $(OBJS) $(CAMLP5M) ../odyl/odyl.cmo -linkall -linkpkg -o $(CAMLP5)

$(CAMLP5OPT): $(OBJS:.cma=.cmxa) ../odyl/odyl.cmx
	$(OCAMLOPT) $(DEBUG) $(OBJS:.cma=.cmxa) $(CAMLP5M) ../odyl/odyl.cmx -linkall -linkpkg -o $(CAMLP5OPT)

$(CAMLP5N).cma: $(CAMLP5_OBJS)
	$(OCAMLC) $(LINKFLAGS) $(CAMLP5_OBJS) -a -o $(CAMLP5N).cma

$(CAMLP5N).cmxa: $(CAMLP5_XOBJS)
	$(OCAMLOPT) $(LINKFLAGS) $(CAMLP5_XOBJS) -a -o $(CAMLP5N).cmxa

clean::
	$(RM) -f *.cm* *.pp[io] *.[ao] *.obj *.lib *.bak .*.bak *.out *.opt
	$(RM) -f $(CAMLP5)

depend:
	cp .depend .depend.bak
	> .depend
	@export LC_ALL=C; for i in $$(ls *.mli *.ml); do \
	  ../tools/depend.sh $(INCLUDES) -name $(CAMLP5N) $$i \
	  >> .depend; \
	done

promote:
	cp $(CAMLP5) $(TOP)/boot/.

compare:
	@for j in $(CAMLP5); do \
		if cmp $$j $(TOP)/boot/$$j; then :; else exit 1; fi; \
	done

bootstrap_reloc:
	cd ../etc; $(MAKE) pa_reloc.cmo pr_r.cmo
	OCAMLN=$(OCAMLN) CAMLP5N=$(CAMLP5N) ./mkreloc.sh > tmp
	mv tmp reloc.ml

compare_reloc:
	cd ../etc; $(MAKE) pa_reloc.cmo pr_r.cmo
	OCAMLN=$(OCAMLN) CAMLP5N=$(CAMLP5N) ./mkreloc.sh | diff -c reloc.ml -

install:
	-$(MKDIR) "$(DESTDIR)$(BINDIR)"
	-$(MKDIR) "$(DESTDIR)$(LIBDIR)/$(CAMLP5N)"
	cp $(CAMLP5) "$(DESTDIR)$(BINDIR)/."
	cp ast2pt.mli mLast.mli quotation.mli pcaml.mli prtools.mli reloc.mli "$(DESTDIR)$(LIBDIR)/$(CAMLP5N)/."
	cp asttools.cmi ast2pt.cmi mLast.cmi mlsyntax.cmi quotation.cmi pcaml.cmi prtools.cmi reloc.cmi pp_debug.cmi "$(DESTDIR)$(LIBDIR)/$(CAMLP5N)/."
	cp asttools.cmx ast2pt.cmx mlsyntax.cmx quotation.cmx pcaml.cmx prtools.cmx reloc.cmx pp_debug.cmx "$(DESTDIR)$(LIBDIR)/$(CAMLP5N)/."
	cp $(CAMLP5N).cma "$(DESTDIR)$(LIBDIR)/$(CAMLP5N)/."
	if test -f $(CAMLP5N).cmxa; then \
	  cp $(CAMLP5N).cmxa "$(DESTDIR)$(LIBDIR)/$(CAMLP5N)/."; \
	  cp $(CAMLP5N)$(EXT_LIB) "$(DESTDIR)$(LIBDIR)/$(CAMLP5N)/."; \
	fi

include .depend
