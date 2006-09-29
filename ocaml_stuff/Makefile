# $Id: Makefile,v 1.1 2006/09/29 04:45:49 deraugla Exp $

include ../config/Makefile

DIRS=utils parsing

all:
	if test "$(OTOP)" = "../ocaml_stuff"; then \
	  set -e; \
	  for i in $(DIRS); do cd $$i; $(MAKE) all EXE=$(EXE); cd ..; done; \
	fi

opt:
	cd utils; $(MAKE) opt

clean:
	if test "$(OTOP)" = "../ocaml_stuff"; then \
	  set -e; \
	  for i in $(DIRS); do cd $$i; $(MAKE) clean EXE=$(EXE); cd ..; done; \
	fi

depend:
	set -e; for i in $(DIRS); do cd $$i; $(MAKE) depend; cd ..; done

steal:
	@if test "$(OCAML_SRC)" = ""; then \
		echo "usage: make steal OCAML_SRC=..."; exit 1; \
	fi
	grep "ast_.*_magic_number" $(OCAML_SRC)/utils/config.ml | \
	sed -e 's/^and/let/' > utils/pconfig.ml
	$(MAKE) copy_steal FILE=utils/warnings.mli
	$(MAKE) copy_steal FILE=parsing/asttypes.mli
	$(MAKE) copy_steal FILE=parsing/location.mli
	$(MAKE) copy_steal FILE=parsing/longident.mli
	$(MAKE) copy_steal FILE=parsing/parsetree.mli

copy_steal:
	sed 's/\$$Id.*\$$/Id/' $(OCAML_SRC)/$(FILE) > $(FILE)

compare_stolen:
	@if test "$(OCAML_SRC)" = ""; then \
		echo "usage: make compare_stolen OCAML_SRC=..."; exit 1; \
	fi
	@echo =================================================
	@echo warnings.ml
	@sed 's/\$$Id.*\$$/Id/' $(OCAML_SRC)/utils/warnings.mli | \
	diff utils/warnings.mli -; exit 0
	@echo =================================================
	@echo pconfig.ml
	@grep "ast_.*_magic_number" $(OCAML_SRC)/utils/config.ml | \
	sed -e 's/^and/let/' | diff utils/pconfig.ml -; exit 0
	@echo =================================================
	@echo asttypes.mli
	@sed 's/\$$Id.*\$$/Id/' $(OCAML_SRC)/parsing/asttypes.mli | \
	diff parsing/asttypes.mli -; exit 0
	@echo =================================================
	@echo location.mli
	@sed 's/\$$Id.*\$$/Id/' $(OCAML_SRC)/parsing/location.mli | \
	diff parsing/location.mli -; exit 0
	@echo =================================================
	@echo longident.mli
	@sed 's/\$$Id.*\$$/Id/' $(OCAML_SRC)/parsing/longident.mli | \
	diff parsing/longident.mli -; exit 0
	@echo =================================================
	@echo parsetree.mli
	@sed 's/\$$Id.*\$$/Id/' $(OCAML_SRC)/parsing/parsetree.mli | \
	diff parsing/parsetree.mli -; exit 0
