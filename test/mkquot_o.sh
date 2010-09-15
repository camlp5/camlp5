#!/bin/sh
# $Id: mkquot_o.sh,v 6.1 2010/09/15 16:00:48 deraugla Exp $

../meta/camlp5r -nolib -I ../meta ../etc/pa_mktest.cmo ../etc/pr_o.cmo -flag M -impl ../main/mLast.mli |
sed -e '1,/begin_stuff/d; /end_stuff/,$d'
