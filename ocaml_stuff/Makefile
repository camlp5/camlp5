# Makefile,v

TOP=..
include ../config/Makefile

VERSSDIR=.$(VERSDIR)/$(OVERSION)
DIRS=$(VERSSDIR)/utils $(VERSSDIR)/parsing

all:
	set -e; \
	for i in $(DIRS); do \
	  cwd=`pwd`; \
	  cd $$i; $(MAKE) all EXE=$(EXE) OCAMLN=$(OCAMLN); \
	  cd $$cwd; \
        done

opt:
	cd $(VERSSDIR)/utils; $(MAKE) OCAMLN=$(OCAMLN) opt; cd ../..

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
	mkdir -p "$(VERSSDIR)"
	cd "$(VERSSDIR)"; mkdir -p utils parsing
	cp common/utils/pconfig.mli $(VERSSDIR)/utils/.
	sed 's/\$$Id.*\$$/Id/' common/utils/Makefile > \
	  $(VERSSDIR)/utils/Makefile
	cp common/utils/.gitignore $(VERSSDIR)/utils/.
	cp common/utils/.depend $(VERSSDIR)/utils/.
	sed 's/\$$Id.*\$$/Id/' common/parsing/Makefile > \
	  $(VERSSDIR)/parsing/Makefile
	cp common/parsing/.gitignore $(VERSSDIR)/parsing/.
	cp common/parsing/.depend $(VERSSDIR)/parsing/.
	(echo "let ocaml_version = \"$(OVERSION)\""; \
	 echo "let ocaml_name = \"$(OCAMLN)\""; \
	 grep "and ast_.*_magic_number" $(OCAML_SRC)/utils/config.mlp | \
	 sed -e 's/^and/let/') > $(VERSSDIR)/utils/pconfig.ml
	$(MAKE) copy_steal FILE=utils/warnings.mli
	$(MAKE) copy_steal FILE=parsing/asttypes.mli
	$(MAKE) copy_steal FILE=parsing/location.mli
	$(MAKE) copy_steal FILE=parsing/longident.mli
	$(MAKE) copy_steal FILE=parsing/parsetree.mli

copy_steal:
	if [ -f "$(OCAML_SRC)/$(FILE)" ]; then \
	  sed 's/\$$Id.*\$$/Id/' $(OCAML_SRC)/$(FILE); \
	fi > $(VERSSDIR)/$(FILE)

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
	   diff $(VERSSDIR)/utils/warnings.mli -; exit 0; fi
	@echo =================================================
	@echo pconfig.ml
	@(echo "let ocaml_version = \"$(OVERSION)\""; \
	  echo "let ocaml_name = \"$(OCAMLN)\""; \
	  grep "and ast_.*_magic_number" $(OCAML_SRC)/utils/config.mlp) | \
	sed -e 's/^and/let/' | diff $(VERSSDIR)/utils/pconfig.ml -; exit 0
	@echo =================================================
	@echo asttypes.mli
	@sed 's/\$$Id.*\$$/Id/' $(OCAML_SRC)/parsing/asttypes.mli | \
	diff $(VERSSDIR)/parsing/asttypes.mli -; exit 0
	@echo =================================================
	@echo location.mli
	@sed 's/\$$Id.*\$$/Id/' $(OCAML_SRC)/parsing/location.mli | \
	diff $(VERSSDIR)/parsing/location.mli -; exit 0
	@echo =================================================
	@echo longident.mli
	@sed 's/\$$Id.*\$$/Id/' $(OCAML_SRC)/parsing/longident.mli | \
	diff $(VERSSDIR)/parsing/longident.mli -; exit 0
	@echo =================================================
	@echo parsetree.mli
	@sed 's/\$$Id.*\$$/Id/' $(OCAML_SRC)/parsing/parsetree.mli | \
	diff $(VERSSDIR)/parsing/parsetree.mli -; exit 0
