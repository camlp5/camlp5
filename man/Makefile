# $Id: Makefile,v 6.1 2010/09/15 16:00:24 deraugla Exp $

include ../config/Makefile

TARGET=camlp5.1

all: $(TARGET)

clean::
	rm -f $(TARGET)

depend:

get_promote:

install:
	-$(MKDIR) "$(DESTDIR)$(MANDIR)/man1"
	-cp $(TARGET) "$(DESTDIR)$(MANDIR)/man1/."
	for i in camlp5o.1 camlp5r.1 camlp5sch.1 mkcamlp5.1 ocpp5.1; do \
	  cd "$(DESTDIR)$(MANDIR)/man1"; rm -f $$i; ln -s $(TARGET) $$i; \
	done
	for i in camlp5o.opt.1 camlp5r.opt.1 mkcamlp5.opt.1; do \
	  cd "$(DESTDIR)$(MANDIR)/man1"; rm -f $$i; ln -s $(TARGET) $$i; \
	done

camlp5.1: camlp5.1.tpl
	sed -e "s'LIBDIR'$(LIBDIR)'g" camlp5.1.tpl > camlp5.1
