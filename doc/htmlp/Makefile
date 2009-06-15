# $Id: Makefile,v 1.7 2007/07/14 03:50:43 deraugla Exp $

# $Id: Makefile,v 1.7 2007/07/14 03:50:43 deraugla Exp $

OBJS=../html/index.html ../html/extfun.html ../html/fparsers.html ../html/grammars.html ../html/lexers.html ../html/ml_ast.html ../html/opretty.html ../html/parsers.html ../html/pragma.html ../html/pretty.html ../html/ptools.html

INDEX=index.html

all: $(OBJS)

clean:
	rm -f $(OBJS)

../html/%.html: %.html menu.html trailer.html
	@rm -f $@
	@cat $< | \
	 sed \
	   -e '/<div id="menu">/i\aaa' \
	   -e '/<div id="menu">/,/^<\/div>/d' | \
	 sed -e '/aaa/r menu.html' -e '/aaa/d' | \
	 sed \
	   -e '/<div class="trailer">/i\aaa' \
	   -e '/<div class="trailer">/,/^<\/div>/d' | \
	 sed -e '/aaa/r trailer.html' -e '/aaa/d' > tmp
	@mv tmp $@
	@chmod 444 $@
	@echo $@ done
