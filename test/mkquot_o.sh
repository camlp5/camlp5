#!/bin/sh
# mkquot_o.sh,v

head -n2 quot_o.ml
../meta/camlp5r -nolib -I ../meta ../etc/pa_mktest.cmo ../meta/pa_macro.cmo ../etc/pr_o.cmo \
	-pa_mktest-ignore-type class_infos \
	-pa_mktest-ignore-type case_branch \
	-pa_mktest-ignore-type longid_lident \
	-pa_mktest-ignore-type payload \
	-pa_mktest-expand-type attributes \
	-pa_mktest-expand-type payload \
	-pa_mktest-expand-type generic_constructor \
	-pa_mktest-expand-type extension_constructor \
	-pa_mktest-expand-type type_extension \
	-l 400 -flag M -sep '\n' -impl ../main/mLast.mli
