# $Id: Makefile,v 6.2 2012/03/01 03:33:18 deraugla Exp $

include ../config/Makefile

TARGET=$(CAMLP5N).1

all: $(TARGET)

clean::
	rm -f $(TARGET)

depend:

get_promote:

install:
	-$(MKDIR) "$(DESTDIR)$(MANDIR)/man1"
	-cp $(TARGET) "$(DESTDIR)$(MANDIR)/man1/."
	for i in $(CAMLP5N)o.1 $(CAMLP5N)r.1 $(CAMLP5N)sch.1 mk$(CAMLP5N).1 ocpp5.1; do \
	  cd "$(DESTDIR)$(MANDIR)/man1"; rm -f $$i; ln -s $(TARGET) $$i; \
	done
	for i in $(CAMLP5N)o.opt.1 $(CAMLP5N)r.opt.1 mk$(CAMLP5N).opt.1; do \
	  cd "$(DESTDIR)$(MANDIR)/man1"; rm -f $$i; ln -s $(TARGET) $$i; \
	done

$(CAMLP5N).1: camlp5.1.tpl
	sed -e "s'LIBDIR'$(LIBDIR)'g" -e "s/camlp5n/$(CAMLP5N)/g" camlp5.1.tpl > $(CAMLP5N).1
