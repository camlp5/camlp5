# $Id: Makefile,v 6.4 2012/03/02 16:03:59 deraugla Exp $

TOP=..
include ../config/Makefile

VERSDIR=.$(VERSPFX)/$(OVERSION)
DIRS=$(VERSDIR)/utils $(VERSDIR)/parsing

all:
	set -e; \
	for i in $(DIRS); do \
	  (cd $$i; $(MAKE) all EXE=$(EXE) OCC=$(OCC)); \
        done

opt:
	cd $(VERSDIR)/utils; $(MAKE) opt; cd ../..

clean:
	set -e; \
	for i in $(DIRS); do \
	  (cd $$i; $(MAKE) clean EXE=$(EXE)); \
	done

depend:
	set -e; for i in $(DIRS); do cd $$i; $(MAKE) depend; cd ../..; done

steal:
	@if test "$(OCAML_SRC)" = ""; then \
		echo "usage: $(MAKE) steal OCAML_SRC=..."; exit 1; \
	fi
	@$(MAKE) real_steal OCAML_SRC="$$(cd ..; cd $(OCAML_SRC); pwd)"

real_steal:
	mkdir -p "$(VERSDIR)"
	cd "$(VERSDIR)"; mkdir -p utils parsing
	cp common/utils/pconfig.mli $(VERSDIR)/utils/.
	sed 's/\$$Id.*\$$/Id/' common/utils/Makefile > \
	  $(VERSDIR)/utils/Makefile
	cp common/utils/.cvsignore $(VERSDIR)/utils/.
	cp common/utils/.depend $(VERSDIR)/utils/.
	sed 's/\$$Id.*\$$/Id/' common/parsing/Makefile > \
	  $(VERSDIR)/parsing/Makefile
	cp common/parsing/.cvsignore $(VERSDIR)/parsing/.
	cp common/parsing/.depend $(VERSDIR)/parsing/.
	(echo "let ocaml_version = \"$(OVERSION)\""; \
	 grep "ast_.*_magic_number" $(OCAML_SRC)/utils/config.mlp | \
	 sed -e 's/^and/let/') > $(VERSDIR)/utils/pconfig.ml
	$(MAKE) copy_steal FILE=utils/warnings.mli
	$(MAKE) copy_steal FILE=parsing/asttypes.mli
	$(MAKE) copy_steal FILE=parsing/location.mli
	$(MAKE) copy_steal FILE=parsing/longident.mli
	$(MAKE) copy_steal FILE=parsing/parsetree.mli

copy_steal:
	if [ -f "$(OCAML_SRC)/$(FILE)" ]; then \
	  sed 's/\$$Id.*\$$/Id/' $(OCAML_SRC)/$(FILE); \
	fi > $(VERSDIR)/$(FILE)

compare_stolen:
	@if test "$(OCAML_SRC)" = ""; then \
		echo "usage: make compare_stolen OCAML_SRC=..."; exit 1; \
	fi
	$(MAKE) real_compare_stolen OCAML_SRC="$$(cd ..; cd $(OCAML_SRC); pwd)"

real_compare_stolen:
	@echo =================================================
	@echo warnings.mli
	@if [ -f "$(OCAML_SRC)/utils/warnings.mli" ]; then \
           sed 's/\$$Id.*\$$/Id/' $(OCAML_SRC)/utils/warnings.mli | \
	   diff $(VERSDIR)/utils/warnings.mli -; exit 0; fi
	@echo =================================================
	@echo pconfig.ml
	@(echo "let ocaml_version = \"$(OVERSION)\""; \
	  grep "ast_.*_magic_number" $(OCAML_SRC)/utils/config.mlp) | \
	sed -e 's/^and/let/' | diff $(VERSDIR)/utils/pconfig.ml -; exit 0
	@echo =================================================
	@echo asttypes.mli
	@sed 's/\$$Id.*\$$/Id/' $(OCAML_SRC)/parsing/asttypes.mli | \
	diff $(VERSDIR)/parsing/asttypes.mli -; exit 0
	@echo =================================================
	@echo location.mli
	@sed 's/\$$Id.*\$$/Id/' $(OCAML_SRC)/parsing/location.mli | \
	diff $(VERSDIR)/parsing/location.mli -; exit 0
	@echo =================================================
	@echo longident.mli
	@sed 's/\$$Id.*\$$/Id/' $(OCAML_SRC)/parsing/longident.mli | \
	diff $(VERSDIR)/parsing/longident.mli -; exit 0
	@echo =================================================
	@echo parsetree.mli
	@sed 's/\$$Id.*\$$/Id/' $(OCAML_SRC)/parsing/parsetree.mli | \
	diff $(VERSDIR)/parsing/parsetree.mli -; exit 0
