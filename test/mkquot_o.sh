#!/bin/sh
# $Id: mkquot_o.sh,v 1.2 2010/09/13 13:46:36 deraugla Exp $

../meta/camlp5r -nolib -I ../meta ../etc/pa_mktest.cmo ../etc/pr_o.cmo -flag M -impl ../main/mLast.mli |
sed -e '1,/begin_stuff/d; /end_stuff/,$d'
