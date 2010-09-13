#!/bin/sh
# $Id: mkquot.sh,v 1.1 2010/09/13 10:05:31 deraugla Exp $

../meta/camlp5r ../etc/pa_mktest.cmo ../etc/pr_r.cmo -flag D -impl ../main/mLast.mli |
sed -e '1,/begin_stuff/d; /end_stuff/,$d'
