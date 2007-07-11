# $Id$

OBJS=index.html extfun.html lexers.html opretty.html pragma.html fparsers.html ml_ast.html  parsers.html pretty.html


all: $(OBJS)

$(OBJS): menu.html
	@(sed -e '/<div id="menu">/,$$d' $@; \
	 cat menu.html; \
	 sed -e '1,/<\/div>/d' $@) > tmp
	@mv tmp $@
	@echo $@ done
