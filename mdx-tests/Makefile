export TOP=..
include $(TOP)/config/Makefile

TESTS=simplest.asciidoc.TEST ocamlc.asciidoc.TEST official_toplevel.asciidoc.TEST revised_toplevel.asciidoc.TEST

all: $(TESTS)

clean:
	$(RM) -f fixtures/*.cm* *.cm* *.byte *.log *.cache *.ppo tools/*.byte tools/*.opt link* *.corrected

realclean: clean

ocamlc.asciidoc.corrected: $(shell ls fixtures/*.ml)
official_toplevel.asciidoc.corrected: $(shell ls fixtures/*.ml)
revised_toplevel.asciidoc.corrected: $(shell ls fixtures/*.ml)


%_toplevel.asciidoc.TEST: %_toplevel.asciidoc.corrected %_toplevel.asciidoc
	perl -n -i -e 'print unless (s,.*: added to search path.*,,)' $<
	perl -n -i -e 'print unless (s,.*: loaded.*,,)' $<
	perl -n -i -e 'print unless (s,OCaml version,,)' $<
	perl -n -i -e 'print unless (s,#help,,)' $<
	diff -U 10 -Bwiu $^
