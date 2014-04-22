# Makefile,v

include ../config/Makefile

SHELL=/bin/sh

INCLUDES=-I ../main -I ../boot -I ../odyl
OCAMLCFLAGS=$(WARNERR) $(INCLUDES)
LINKFLAGS=$(INCLUDES)
OBJS=ocpp.cmo

all: ocpp$(EXE)

ocpp$(EXE): $(OBJS)
	$(OCAMLC) $(LINKFLAGS) ../boot/ploc.cmo ../boot/stdpp.cmo ../main/quotation.cmo ../odyl/odyl.cma $(OBJS) ../odyl/odyl.cmo -linkall -o ocpp$(EXE)

clean::
	rm -f *.cm[ioa] *.pp[io] *.[ao] *.obj *.lib *.out *.bak .*.bak
	rm -f ocpp$(EXE)

install:
	-$(MKDIR) "$(DESTDIR)$(LIBDIR)/$(CAMLP5N)" "$(DESTDIR)$(BINDIR)"
	cp $(OBJS) "$(DESTDIR)$(LIBDIR)/$(CAMLP5N)/."
	cp ocpp$(EXE) "$(DESTDIR)$(BINDIR)/ocpp5$(EXE)"

depend:
