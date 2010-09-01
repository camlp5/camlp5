#!/bin/sh -e
# $Id: mkcrc.sh,v 1.16 2010/09/01 09:31:15 deraugla Exp $

MOD_OLIB="arg array buffer char format hashtbl lexing list obj pervasives printf stream string sys"
MOD_MAIN="ast2pt exparser mLast parserify pcaml prtools quotation reloc"
MOD_5LIB="diff eprinter extfun fstream gramext grammar plexer plexing ploc pprintf pretty versdep"
MOD_PARS="asttypes location longident parsetree"
MOD_UTIL="pconfig warnings"
OFILE=crc.tmp

> $OFILE
V=$OVERSION
if [ "$V" = "2.02" -o "$V" = "2.03" -o "$V" = "2.04" -o "$V" = "2.99" -o \
     "$V" = "3.00" -o "$V" = "3.01" -o "$V" = "3.02" -o "$V" = "3.03" -o \
     "$V" = "3.04" -o "$V" = "3.05" -o "$V" = "3.06" ]
then
  (cd $OLIBDIR; $OLIBDIR/extract_crc $MOD_OLIB) >> $OFILE
  echo "in Dynlink.add_available_units crc_unit_list;;" >> $OFILE
  if [ "$V" = "2.03" -o "$V" = "2.04" -o "$V" = "2.99" ]; then
    (cd $OLIBDIR; $OLIBDIR/extract_crc sort) >> $OFILE
    echo "in Dynlink.add_available_units crc_unit_list;;" >> $OFILE
  fi
  (cd ../main; $OLIBDIR/extract_crc $MOD_MAIN) >> $OFILE
  echo "in Dynlink.add_available_units crc_unit_list;;" >> $OFILE
  (cd ../lib; $OLIBDIR/extract_crc $MOD_5LIB) >> $OFILE
  echo "in Dynlink.add_available_units crc_unit_list;;" >> $OFILE
  (cd $OTOP/parsing; $OLIBDIR/extract_crc $MOD_PARS) >> $OFILE
  echo "in Dynlink.add_available_units crc_unit_list;;" >> $OFILE
  (cd $OTOP/utils; $OLIBDIR/extract_crc $MOD_UTIL) >> $OFILE
  echo "in Dynlink.add_available_units crc_unit_list;;" >> $OFILE
fi
