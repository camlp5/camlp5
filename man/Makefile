# $Id: Makefile,v 1.7 2007/08/31 10:41:10 deraugla Exp $

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
	-cd "$(DESTDIR)$(MANDIR)/man1"; rm -f $(NAME)o.1; ln -s $(TARGET) $(NAME)o.1
	-cd "$(DESTDIR)$(MANDIR)/man1"; rm -f $(NAME)r.1; ln -s $(TARGET) $(NAME)r.1
	-cd "$(DESTDIR)$(MANDIR)/man1"; rm -f ocpp.1; ln -s $(TARGET) ocpp.1
	-cd "$(DESTDIR)$(MANDIR)/man1"; rm -f $(NAME)o.opt.1; ln -s $(TARGET) $(NAME)o.opt.1
	-cd "$(DESTDIR)$(MANDIR)/man1"; rm -f $(NAME)r.opt.1; ln -s $(TARGET) $(NAME)r.opt.1

$(NAME).1: camlp5.1.tpl
	sed -e "s'LIBDIR'$(LIBDIR)'g" -e "s/camlp5/$(NAME)/g" camlp5.1.tpl > $(NAME).1
