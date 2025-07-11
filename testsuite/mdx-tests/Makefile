export TOP=../..
include $(TOP)/config/Makefile

TESTS=ocamlc.asciidoc.TEST ocamlc.asciidoc.TEST

all: $(TESTS)

clean:
	$(RM) -f fixtures/*.cm* *.cm* *.byte *.log *.cache *.ppo tools/*.byte tools/*.opt link* *.corrected

realclean: clean

ocamlc.asciidoc.corrected: $(shell ls fixtures/*.ml)
