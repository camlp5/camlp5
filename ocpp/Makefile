# $Id: Makefile,v 1.3 2007/07/10 14:09:06 deraugla Exp $

include ../config/Makefile

SHELL=/bin/sh

INCLUDES=-I ../camlp4 -I ../boot -I ../odyl
OCAMLCFLAGS=-warn-error A $(INCLUDES)
LINKFLAGS=$(INCLUDES)
OBJS=ocpp.cmo

all: ocpp$(EXE)

ocpp$(EXE): $(OBJS)
	$(OCAMLC) $(LINKFLAGS) ../boot/stdpp.cmo ../camlp4/quotation.cmo ../odyl/odyl.cma $(OBJS) ../odyl/odyl.cmo -linkall -o ocpp$(EXE)

clean::
	rm -f *.cm[ioa] *.pp[io] *.o *.out *.bak .*.bak ocpp$(EXE)

install:
	-$(MKDIR) "$(LIBDIR)/$(NAME)" "$(BINDIR)"
	cp $(OBJS) "$(LIBDIR)/$(NAME)/."
	cp ocpp$(EXE) "$(BINDIR)/."

depend:
