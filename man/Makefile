# $Id: Makefile,v 1.6 2007/07/11 12:01:39 deraugla Exp $

include ../config/Makefile

TARGET=$(NAME).1

all: $(TARGET)

clean::
	rm -f $(TARGET)

depend:

get_promote:

install:
	-$(MKDIR) "$(MANDIR)/man1"
	-cp $(TARGET) "$(MANDIR)/man1/."
	-cd "$(MANDIR)/man1"; rm -f $(NAME)o.1; ln -s $(TARGET) $(NAME)o.1
	-cd "$(MANDIR)/man1"; rm -f $(NAME)r.1; ln -s $(TARGET) $(NAME)r.1
	-cd "$(MANDIR)/man1"; rm -f ocpp.1; ln -s $(TARGET) ocpp.1
	-cd "$(MANDIR)/man1"; rm -f $(NAME)o.opt.1; ln -s $(TARGET) $(NAME)o.opt.1
	-cd "$(MANDIR)/man1"; rm -f $(NAME)r.opt.1; ln -s $(TARGET) $(NAME)r.opt.1

$(NAME).1: camlp5.1.tpl
	sed -e "s'LIBDIR'$(LIBDIR)'g" -e "s/camlp5/$(NAME)/g" camlp5.1.tpl > $(NAME).1
