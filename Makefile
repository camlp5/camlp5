# Makefile,v

include config/Makefile

DIRS=lib odyl main meta etc top ocpp man
FDIRS=lib odyl main meta
OPTDIRS=ocaml_stuff lib odyl main meta etc
OPTOPTDIRS=compile
SHELL=/bin/sh
COLD_FILES=ocaml_src/main/argl.ml ocaml_src/main/mLast.mli ocaml_src/main/pcaml.ml ocaml_src/main/pcaml.mli ocaml_src/main/quotation.ml ocaml_src/main/quotation.mli ocaml_src/main/reloc.ml ocaml_src/main/reloc.mli ocaml_src/lib/extfun.ml ocaml_src/lib/extfun.mli ocaml_src/lib/fstream.ml ocaml_src/lib/fstream.mli ocaml_src/lib/gramext.ml ocaml_src/lib/gramext.mli ocaml_src/lib/grammar.ml ocaml_src/lib/grammar.mli ocaml_src/lib/plexer.ml ocaml_src/lib/plexer.mli ocaml_src/lib/stdpp.ml ocaml_src/lib/stdpp.mli ocaml_src/lib/token.ml ocaml_src/lib/token.mli ocaml_src/lib/versdep.ml ocaml_src/meta/pa_extend.ml ocaml_src/meta/pa_extend_m.ml ocaml_src/meta/pa_macro.ml ocaml_src/meta/pa_r.ml ocaml_src/meta/pa_rp.ml ocaml_src/meta/pr_dump.ml ocaml_src/meta/q_MLast.ml ocaml_src/odyl/odyl_main.ml ocaml_src/odyl/odyl_main.mli ocaml_src/odyl/odyl.ml
PR_O=pr_o.cmo
DIFF_OPT=
# For possible installation in a fake root directory
# by "make install DESTDIR=..."
DESTDIR=

all: world.opt

out: boot/$(CAMLP5N)$(EXE)
	set -e; cd ocaml_stuff; $(MAKE); cd ..
	set -e; for i in $(DIRS); do cd $$i; $(MAKE) all; cd ..; done

opt:
	set -e; for i in $(OPTDIRS); do cd $$i; $(MAKE) opt; cd ..; done

opt.opt: opt
	cd compile; $(MAKE) opt; cd ..

ocaml_src/lib/versdep.ml:
	@echo "Please run 'configure' first"; exit 2

boot/$(CAMLP5N)$(EXE): $(COLD_FILES)
	set -e; cd ocaml_stuff; $(MAKE); cd ..
	$(MAKE) clean_cold
	$(MAKE) library_cold
	$(MAKE) compile_cold
	$(MAKE) promote_cold
	$(MAKE) clean_cold
	$(MAKE) clean_hot
	$(MAKE) library

clean_hot:
	cd ocaml_stuff; $(MAKE) clean; cd ..
	for i in $(DIRS) compile; do (cd $$i; $(MAKE) clean; cd ..); done

depend:
	cd etc; $(MAKE) pr_depend.cmo; cd ..
	cd ocaml_stuff; $(MAKE) depend; cd ..
	for i in $(DIRS) compile; do (cd $$i; $(MAKE) depend; cd ..); done

install:
	@if test -z "$(LIBDIR)"; then \
	  echo "*** Variable LIBDIR not set"; exit 1; fi
	@if test -z "$(CAMLP5N)"; then \
	  echo "*** Variable CAMLP5N not set"; exit 1; fi
	$(RM) -rf "$(DESTDIR)$(LIBDIR)/$(CAMLP5N)"
	for i in $(DIRS) compile; do \
	  (cd $$i; $(MAKE) install DESTDIR=$(DESTDIR); cd ..); \
	done

uninstall:
	@if test -z "$(LIBDIR)"; then \
	  echo "*** Variable LIBDIR not set"; exit 1; fi
	@if test -z "$(CAMLP5N)"; then \
	  echo "*** Variable CAMLP5N not set"; exit 1; fi
	$(RM) -rf "$(DESTDIR)$(LIBDIR)/$(CAMLP5N)"
	cd "$(DESTDIR)$(BINDIR)"; $(RM) -f *$(CAMLP5N)* odyl ocpp; cd ..
	cd "$(DESTDIR)$(MANDIR)/man1"; $(RM) -f *$(CAMLP5N)* odyl ocpp

clean::
	$(MAKE) clean_hot clean_cold
	$(RM) -f boot/*.cm[oi] boot/$(CAMLP5N)*
	$(RM) -rf boot/SAVED
	cd test; $(MAKE) clean; cd ..

scratch: clean

always:

# Normal bootstrap

bootstrap:
	$(MAKE) backup
	$(MAKE) promote
	$(MAKE) clean_hot
	$(MAKE) out
	$(MAKE) compare

backup:
	mkdir boot.new
	$(MAKE) mv_git FROM=boot TO=boot.new
	mv boot boot.new/SAVED
	mv boot.new boot

restore:
	mv boot/SAVED boot.new
	$(MAKE) mv_git FROM=boot TO=boot.new
	$(RM) -rf boot
	mv boot.new boot

promote:
	for i in $(FDIRS); do (cd $$i; $(MAKE) promote; cd ..); done

compare:
	@if (for i in $(FDIRS); do \
		cd $$i; \
		if $(MAKE) compare 2>/dev/null; then cd ..; \
		else exit 1; fi; \
	     done); \
	then echo "Fixpoint reached, bootstrap succeeded."; \
	else echo "Fixpoint not reached, try one more bootstrapping cycle."; \
	fi

compare_test:
	@(for i in $(FDIRS); do \
		cd $$i; \
		if $(MAKE) compare 2>/dev/null; then cd ..; \
		else exit 1; fi; \
	done)

cleanboot:
	$(RM) -rf boot/SAVED/SAVED


# Core and core bootstrap

coreboot:
	$(MAKE) backup
	$(MAKE) promote
	$(MAKE) clean_hot
	$(MAKE) core
	$(MAKE) compare

core: boot/$(CAMLP5N)$(EXE)
	cd ocaml_stuff; $(MAKE) all; cd ..
	set -e; for i in $(FDIRS); do cd $$i; $(MAKE) all; cd ..; done

clean_core:
	for i in $(FDIRS); do (cd $$i; $(MAKE) clean; cd ..); done


# Everything in one command

world:
	$(MAKE) core
	$(MAKE) compare_test || $(MAKE) coreboot
	$(MAKE) out

world.opt:
	$(MAKE) core
	$(MAKE) compare_test || $(MAKE) coreboot
	$(MAKE) out
	$(MAKE) opt
	$(MAKE) opt.opt

library:
	set -e; cd ocaml_stuff; $(MAKE); cd ..
	set -e; cd lib; $(MAKE) all; cd ..
	set -e; cd lib; $(MAKE) promote; cd ..

# Cold start using pure Objective Caml sources

library_cold:
	set -e; cd ocaml_src/lib; $(MAKE) all; cd ../..
	set -e; cd ocaml_src/lib; $(MAKE) promote; cd ../..

compile_cold:
	cd ocaml_src; set -e; \
	for i in $(FDIRS); do \
	  cd $$i; $(MAKE) all; cd ..; \
	done; cd ..

promote_cold:
	for i in $(FDIRS); do \
		(cd ocaml_src/$$i; $(MAKE) promote; cd ../..); \
	done

clean_cold:
	for i in $(FDIRS); do \
		(cd ocaml_src/$$i; $(MAKE) clean; cd ../..); \
	done

# Stealing some Ocaml compiler sources

steal:
	cd ocaml_stuff; $(MAKE) steal; cd ..

compare_stolen:
	cd ocaml_stuff; $(MAKE) compare_stolen; cd ..

# Bootstrap the sources

bootstrap_sources:
	$(RM) -rf ocaml_src.new
	mkdir ocaml_src.new
	$(MAKE) new_sources
	$(MAKE) untouch_sources
	$(MAKE) promote_sources
	$(MAKE) clean_sources

bootstrap_source:
	$(RM) -rf ocaml_src.new
	mkdir -p ocaml_src.new/$$DIR
	$(MAKE) new_source DIR=$$DIR FILE=$$FILE
	mv ocaml_src.new/$$DIR/$$FILE ocaml_src/$$DIR/$$FILE
	rmdir ocaml_src.new/$$DIR
	rmdir ocaml_src.new

new_sources: oprinter
	@-for i in $(FDIRS); do \
	   mkdir ocaml_src.new/$$i; \
	   $(MAKE) $(NO_PR_DIR) new_source DIR=$$i FILE=Makefile; \
	   echo ============================================; \
	   echo ocaml_src.new/$$i/.depend; \
           (cd ocaml_src.new/$$i; cp ../../$$i/.depend .); \
	 done
	@-mkdir ocaml_src.new/lib/versdep
	@-(cd ocaml_src/lib/versdep; \
	   cp *.ml ../../../ocaml_src.new/lib/versdep/.)
	@-mkdir ocaml_src.new/lib/versdep/jocaml
	@-(cd ocaml_src/lib/versdep/jocaml; \
	   cp *.ml ../../../../ocaml_src.new/lib/versdep/jocaml)
	@-for i in $(FDIRS); do \
          files="$$(cd $$i; ls *.ml*)"; \
	  for j in $$files; do \
	    if [ "$$j" != "odyl_config.ml" ]; then \
	      $(MAKE) $(NO_PR_DIR) new_source DIR=$$i FILE=$$j; \
	    fi; \
	  done; \
	done

new_source:
	@cd $$DIR; k=$$FILE; opt=""; \
	if [ "$$k" = "versdep.ml" ]; then \
	  k=versdep$(VERSDIR)/$(OVERSION).ml; \
	  VERSDIR="$(OCAMLN)"; \
	else \
	  VERSDIR=""; \
	fi; \
	echo ============================================; \
	echo ocaml_src.new/$$DIR/$$k; \
	if [ "$$k" = "Makefile" ]; then \
	  sed 's-^TOP=..$$-TOP=../..-' Makefile; \
	else \
	  OCAMLN=$(OCAMLN) CAMLP5N=$(CAMLP5N) VERSDIR=$$VERSDIR \
	    ../tools/conv.sh $(PR_O) $$opt $$FILE; \
	fi > \
	../ocaml_src.new/$$DIR/$$k

compare_sources: oprinter
	@-for i in $(FDIRS); do \
	   $(MAKE) $(NO_PR_DIR) compare_source DIR=$$i FILE=Makefile; \
	   echo ============================================; \
	   echo ocaml_src/$$i/.depend; \
	   (cd ocaml_src/$$i; diff $(DIFF_OPT) . ../../$$i/.depend); \
	 done
	@-for i in $(FDIRS); do \
          files="$$(cd $$i; ls *.ml*)"; \
	  for j in $$files; do \
	    if [ "$$j" != "odyl_config.ml" ]; then \
	      $(MAKE) $(NO_PR_DIR) compare_source DIR=$$i FILE=$$j; \
	    fi; \
	  done; \
	done

compare_source:
	@cd $$DIR; k=$$FILE; opt=""; \
	if [ "$$k" = "versdep.ml" ]; then \
	  k=versdep$(VERSDIR)/$(OVERSION).ml; \
	  VERSDIR="$(OCAMLN)"; \
	else \
	  VERSDIR=""; \
	fi; \
	echo ============================================; \
	echo ocaml_src/$$DIR/$$k; \
	if [ "$$k" = "Makefile" ]; then \
	  sed 's-^TOP=..$$-TOP=../..-' Makefile; \
	else \
	  OCAMLN=$(OCAMLN) CAMLP5N=$(CAMLP5N) VERSDIR=$$VERSDIR \
	    ../tools/conv.sh $(PR_O) $$opt $$FILE; \
	fi | \
	diff $(DIFF_OPT) ../ocaml_src/$$DIR/$$k - || :

bootstrap_all_versdep: oprinter
	@-for i in ocaml_src/lib/versdep/*.ml; do \
	  $(MAKE) $(NO_PR_DIR) bootstrap_versdep i=$$i n=ocaml; \
	done; \
	for i in ocaml_src/lib/versdep/*/*.ml; do \
	  n="$$(basename $$(dirname $$i))"; \
	  $(MAKE) $(NO_PR_DIR) bootstrap_versdep i=$$i n=$$n; \
	done

bootstrap_versdep:
	@cd lib; \
	echo ============================================; \
	echo $$i; \
	j=$$(echo $$(basename $$i) | \
	     sed -e 's/^/OCAML_/;s/.ml//' -e 's/[.-]/_/g'); \
	k=$$(echo OCAML_$(OVERSION) | sed -e 's/[.-]/_/g'); \
	m=$$(echo $(OCAMLN) | tr a-z A-Z); \
	n=$$(echo $$n | tr a-z A-Z); \
	opt="-U$$k -U$$m -D$$j -D$$n"; \
	OCAMLN=$(OCAMLN) CAMLP5N=$(CAMLP5N) ../tools/conv.sh $(PR_O) $$opt \
	  versdep.ml > ../$$i

compare_all_versdep: oprinter
	@-for i in ocaml_src/lib/versdep/*.ml; do \
	  $(MAKE) $(NO_PR_DIR) compare_versdep i=$$i n=ocaml; \
	done; \
	for i in ocaml_src/lib/versdep/*/*.ml; do \
	  n="$$(basename $$(dirname $$i))"; \
	  $(MAKE) $(NO_PR_DIR) compare_versdep i=$$i n=$$n; \
	done

compare_versdep:
	@cd lib; \
	echo ============================================; \
	echo $$i; \
	j=$$(echo $$(basename $$i) | \
	  sed -e 's/^/OCAML_/;s/.ml//' -e 's/[.-]/_/g'); \
	k=$$(echo OCAML_$(OVERSION) | sed -e 's/[.-]/_/g'); \
	m=$$(echo $(OCAMLN) | tr a-z A-Z); \
	n=$$(echo $$n | tr a-z A-Z); \
	opt="-U$$k -U$$m -D$$j -D$$n"; \
	OCAMLN=$(OCAMLN) CAMLP5N=$(CAMLP5N) \
	  ../tools/conv.sh $(PR_O) $$opt versdep.ml | \
	diff $(DIFF_OPT) ../$$i -

oprinter:
	cd etc; $(MAKE) $(PR_O)

untouch_sources:
	@-cd ocaml_src; \
	for i in $(FDIRS) lib/versdep; do \
	  for j in $$i/*.ml* $$i/Makefile*; do \
	    if cmp -s $$j ../ocaml_src.new/$$j 2>/dev/null; then \
	      cp -p $$j ../ocaml_src.new/$$j; \
	    fi; \
	  done; \
	done

promote_sources:
	$(MAKE) mv_git FROM=ocaml_src TO=ocaml_src.new
	for i in $(FDIRS) lib/versdep lib/versdep/jocaml; do \
	  $(MAKE) mv_git FROM=ocaml_src/$$i TO=ocaml_src.new/$$i; \
	done
	mv ocaml_src/tools ocaml_src.new/.
	mv ocaml_src ocaml_src.new/SAVED
	mv ocaml_src.new ocaml_src

unpromote_sources:
	mv ocaml_src ocaml_src.new
	mv ocaml_src.new/SAVED ocaml_src
	mv ocaml_src.new/tools ocaml_src/.
	for i in $(FDIRS) lib/versdep lib/versdep/jocaml; do \
	  $(MAKE) mv_git FROM=ocaml_src.new/$$i TO=ocaml_src/$$i; \
	done
	$(MAKE) mv_git FROM=ocaml_src.new TO=ocaml_src

clean_sources:
	$(RM) -rf ocaml_src/SAVED/SAVED

printer:
	cd etc; $(MAKE) $(PR_O)

# Utility

mv_cvs:
	test ! -d $(FROM)/CVS || mv $(FROM)/CVS $(TO)/.
	test ! -f $(FROM)/.cvsignore || mv $(FROM)/.cvsignore $(TO)/.

mv_svn:
	test ! -d $(FROM)/.svn || mv $(FROM)/.svn $(TO)/.
	test ! -f $(FROM)/.cvsignore || mv $(FROM)/.cvsignore $(TO)/.

mv_git:
	test ! -f $(FROM)/.gitignore || mv $(FROM)/.gitignore $(TO)/.

.PHONY: install
