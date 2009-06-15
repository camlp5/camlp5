# $Id: Makefile,v 1.27 2007/09/16 05:58:46 deraugla Exp $

H=../html
OBJS=$H/index.html $H/about.html $H/commands.html $H/conclusion.html $H/extfun.html $H/fparsers.html $H/grammars.html $H/lexers.html $H/library.html $H/locations.html $H/macros.html $H/ml_ast.html $H/opretty.html $H/parsers.html $H/pcaml.html $H/pragma.html $H/pretty.html $H/printers.html $H/ptools.html $H/quot.html $H/revsynt.html $H/scheme.html $H/sources.html $H/strict.html $H/syntext.html
INDEX=index.html

all: $(OBJS)

info:
	@$(MAKE) --no-print-directory camlp5.info H=.

tex:
	@$(MAKE) --no-print-directory camlp5.dvi H=.

camlp5.info: html2texi $(OBJS)
	./html2texi > camlp5.texi
	makeinfo --force camlp5.texi

camlp5.dvi: camlp5.tex $(OBJS)
	latex camlp5.tex
	latex camlp5.tex

camlp5.tex: html2latex
	./html2latex > camlp5.tex

clean:
	rm -f $(OBJS)
	rm -f camlp5.texi camlp5.info*
	rm -f camlp5.tex camlp5.dvi camlp5.log camlp5.toc camlp5.aux

../html/%.html: %.html menu.html trailer.html
	@rm -f $@
	./htmlp2html $< > $@
	@chmod 444 $@
