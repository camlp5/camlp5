# Makefile,v

include ../config/Makefile

SHELL=/bin/bash

INCLUDES=-I ../main -I ../boot -I ../odyl -I ../lib
OCAMLCFLAGS=$(DEBUG) $(WARNERR) $(INCLUDES)
LINKFLAGS=$(DEBUG) $(INCLUDES)
OBJS=ocpp.cmo

all: ocpp$(EXE)

ocpp$(EXE): $(OBJS)
	$(OCAMLC) $(LINKFLAGS) ../lib/gramlib.cma ../main/pp_debug.cmo ../main/mlsyntax.cmo ../main/pcamlbase.cmo ../main/reloc.cmo ../main/quotation.cmo ../main/prtools.cmo ../main/pcaml.cmo ../odyl/odyl.cma $(OBJS) ../odyl/odyl.cmo -linkall -linkpkg -o ocpp$(EXE)

clean::
	$(RM) -f *.cm[ioa] *.pp[io] *.[ao] *.obj *.lib *.out *.bak .*.bak
	$(RM) -f ocpp$(EXE)

install:
	-$(MKDIR) "$(DESTDIR)$(LIBDIR)/$(CAMLP5N)" "$(DESTDIR)$(BINDIR)"
	cp $(OBJS) "$(DESTDIR)$(LIBDIR)/$(CAMLP5N)/."
	cp ocpp$(EXE) "$(DESTDIR)$(BINDIR)/ocpp5$(EXE)"

depend:
