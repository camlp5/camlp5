# $Id: Makefile,v 1.3 2006/11/30 13:26:52 deraugla Exp $

include ../config/Makefile

DIRS=$(OVERSION)/utils $(OVERSION)/parsing

all:
	if test "$(OTOP)" = "../ocaml_stuff/$(OVERSION)"; then \
	  set -e; \
	  for i in $(DIRS); do \
	    cd $$i; $(MAKE) all EXE=$(EXE); cd ../..; \
          done; \
	fi

opt:
	cd $(OVERSION)/utils; $(MAKE) opt

clean:
	if test "$(OTOP)" = "../ocaml_stuff/$(OVERSION)"; then \
	  set -e; \
	  for i in $(DIRS); do \
	    cd $$i; $(MAKE) clean EXE=$(EXE); cd ../..; \
	  done; \
	fi

depend:
	set -e; for i in $(DIRS); do cd $$i; $(MAKE) depend; cd ..; done

steal:
	@if test "$(OCAML_SRC)" = ""; then \
		echo "usage: make steal OCAML_SRC=..."; exit 1; \
	fi
	mkdir -p "$(OVERSION)"
	cd "$(OVERSION)"; mkdir -p utils parsing
	cp common/utils/pconfig.mli $(OVERSION)/utils/.
	cp common/utils/Makefile $(OVERSION)/utils/.
	cp common/utils/.cvsignore $(OVERSION)/utils/.
	cp common/utils/.depend $(OVERSION)/utils/.
	cp common/parsing/Makefile $(OVERSION)/parsing/.
	cp common/parsing/.cvsignore $(OVERSION)/parsing/.
	cp common/parsing/.depend $(OVERSION)/parsing/.
	grep "ast_.*_magic_number" $(OCAML_SRC)/utils/config.ml | \
	sed -e 's/^and/let/' > $(OVERSION)/utils/pconfig.ml
	$(MAKE) copy_steal FILE=utils/warnings.mli
	$(MAKE) copy_steal FILE=parsing/asttypes.mli
	$(MAKE) copy_steal FILE=parsing/location.mli
	$(MAKE) copy_steal FILE=parsing/longident.mli
	$(MAKE) copy_steal FILE=parsing/parsetree.mli

copy_steal:
	sed 's/\$$Id.*\$$/Id/' $(OCAML_SRC)/$(FILE) > $(OVERSION)/$(FILE)

compare_stolen:
	@if test "$(OCAML_SRC)" = ""; then \
		echo "usage: make compare_stolen OCAML_SRC=..."; exit 1; \
	fi
	@echo =================================================
	@echo warnings.ml
	@sed 's/\$$Id.*\$$/Id/' $(OCAML_SRC)/utils/warnings.mli | \
	diff $(OVERSION)/utils/warnings.mli -; exit 0
	@echo =================================================
	@echo pconfig.ml
	@grep "ast_.*_magic_number" $(OCAML_SRC)/utils/config.ml | \
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
