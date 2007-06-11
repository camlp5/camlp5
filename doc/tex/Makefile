# $Id$

all: lexer.dvi lexer.bbl

lexer.dvi: always

clean:
	rm -f *.aux *.bbl *.blg *.dvi *.log

always:

%.dvi: %.tex
	latex $<

%.bbl: %.tex
	bibtex $*
