# $Id: Makefile,v 1.9 2008/01/13 22:37:19 deraugla Exp $

include ../config/Makefile

TARGET=$(NAME).1

all: $(TARGET)

clean::
	rm -f $(TARGET)

depend:

get_promote:

install:
	-$(MKDIR) "$(DESTDIR)$(MANDIR)/man1"
	-cp $(TARGET) "$(DESTDIR)$(MANDIR)/man1/."
	for i in $(NAME)o.1 $(NAME)r.1 $(NAME)sch.1 mkcamlp5.1 ocpp5.1; do \
	  cd "$(DESTDIR)$(MANDIR)/man1"; rm -f $$i; ln -s $(TARGET) $$i; \
	done
	for i in $(NAME)o.opt.1 $(NAME)r.opt.1 mkcamlp5.opt.1; do \
	  cd "$(DESTDIR)$(MANDIR)/man1"; rm -f $$i; ln -s $(TARGET) $$i; \
	done

$(NAME).1: camlp5.1.tpl
	sed -e "s'LIBDIR'$(LIBDIR)'g" -e "s/camlp5/$(NAME)/g" camlp5.1.tpl > $(NAME).1
