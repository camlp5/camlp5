# $Id: Makefile,v 1.11 2010/09/01 17:32:17 deraugla Exp $

TOP=..
include ../config/Makefile

DIRS=$(OVERSION)/utils $(OVERSION)/parsing

all:
	set -e; \
	for i in $(DIRS); do \
	  cd $$i; $(MAKE) all EXE=$(EXE); cd ../..; \
        done

opt:
	cd $(OVERSION)/utils; $(MAKE) opt

clean:
	set -e; \
	for i in $(DIRS); do \
	  cd $$i; $(MAKE) clean EXE=$(EXE); cd ../..; \
	done

depend:
	set -e; for i in $(DIRS); do cd $$i; $(MAKE) depend; cd ../..; done

steal:
	@if test "$(OCAML_SRC)" = ""; then \
		echo "usage: $(MAKE) steal OCAML_SRC=..."; exit 1; \
	fi
	@$(MAKE) real_steal OCAML_SRC="$$(cd ..; cd $(OCAML_SRC); pwd)"

real_steal:
	mkdir -p "$(OVERSION)"
	cd "$(OVERSION)"; mkdir -p utils parsing
	cp common/utils/pconfig.mli $(OVERSION)/utils/.
	sed 's/\$$Id.*\$$/Id/' common/utils/Makefile > \
	  $(OVERSION)/utils/Makefile
	cp common/utils/.cvsignore $(OVERSION)/utils/.
	cp common/utils/.depend $(OVERSION)/utils/.
	sed 's/\$$Id.*\$$/Id/' common/parsing/Makefile > \
	  $(OVERSION)/parsing/Makefile
	cp common/parsing/.cvsignore $(OVERSION)/parsing/.
	cp common/parsing/.depend $(OVERSION)/parsing/.
	(echo "let ocaml_version = \"$(OVERSION)\""; \
	 grep "ast_.*_magic_number" $(OCAML_SRC)/utils/config.ml | \
	 sed -e 's/^and/let/') > $(OVERSION)/utils/pconfig.ml
	$(MAKE) copy_steal FILE=utils/warnings.mli
	$(MAKE) copy_steal FILE=parsing/asttypes.mli
	$(MAKE) copy_steal FILE=parsing/location.mli
	$(MAKE) copy_steal FILE=parsing/longident.mli
	$(MAKE) copy_steal FILE=parsing/parsetree.mli

copy_steal:
	if [ -f "$(OCAML_SRC)/$(FILE)" ]; then \
	  sed 's/\$$Id.*\$$/Id/' $(OCAML_SRC)/$(FILE); \
	fi > $(OVERSION)/$(FILE)

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
	   diff $(OVERSION)/utils/warnings.mli -; exit 0; fi
	@echo =================================================
	@echo pconfig.ml
	@(echo "let ocaml_version = \"$(OVERSION)\""; \
	  grep "ast_.*_magic_number" $(OCAML_SRC)/utils/config.ml) | \
	sed -e 's/^and/let/' | diff $(OVERSION)/utils/pconfig.ml -; exit 0
	@echo =================================================
	@echo asttypes.mli
	@sed 's/\$$Id.*\$$/Id/' $(OCAML_SRC)/parsing/asttypes.mli | \
	diff $(OVERSION)/parsing/asttypes.mli -; exit 0
	@echo =================================================
	@echo location.mli
	@sed 's/\$$Id.*\$$/Id/' $(OCAML_SRC)/parsing/location.mli | \
	diff $(OVERSION)/parsing/location.mli -; exit 0
	@echo =================================================
	@echo longident.mli
	@sed 's/\$$Id.*\$$/Id/' $(OCAML_SRC)/parsing/longident.mli | \
	diff $(OVERSION)/parsing/longident.mli -; exit 0
	@echo =================================================
	@echo parsetree.mli
	@sed 's/\$$Id.*\$$/Id/' $(OCAML_SRC)/parsing/parsetree.mli | \
	diff $(OVERSION)/parsing/parsetree.mli -; exit 0
