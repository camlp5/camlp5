# $Id: Makefile,v 1.3 2007/07/10 14:40:10 deraugla Exp $

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
	-cd "$(MANDIR)/man1"; rm -f mk$(NAME).1; ln -s $(TARGET) mk$(NAME).1
	-cd "$(MANDIR)/man1"; rm -f ocpp.1; ln -s $(TARGET) ocpp.1
	-cd "$(MANDIR)/man1"; rm -f $(NAME)o.opt.1; ln -s $(TARGET) $(NAME)o.opt.1
	-cd "$(MANDIR)/man1"; rm -f $(NAME)r.opt.1; ln -s $(TARGET) $(NAME)r.opt.1

$(NAME).1: camlp4.1.tpl
	sed -e "s'LIBDIR'$(LIBDIR)'g" -e "s/camlp4/$(NAME)/g" camlp4.1.tpl > $(NAME).1
