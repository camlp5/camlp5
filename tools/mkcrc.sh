#!/bin/sh -e
# $Id: mkcrc.sh,v 1.1 2010/08/26 19:09:13 deraugla Exp $

MOD1="arg buffer char format hashtbl lexing list obj pervasives printf stream string sys"
MOD2="exparser mLast pcaml quotation reloc"
MOD3="eprinter extfun fstream gramext grammar plexer plexing ploc pprintf"
MOD4="pconfig"
OFILE=crc.tmp

> $OFILE
if [ "$OVERSION" = "3.05" ]; then
  (cd $OLIBDIR; $OLIBDIR/extract_crc $MOD1) >> $OFILE
  echo "in Dynlink.add_available_units crc_unit_list;;" >> $OFILE
  $OLIBDIR/extract_crc $MOD2 >> $OFILE
  echo "in Dynlink.add_available_units crc_unit_list;;" >> $OFILE
  (cd ../lib; $OLIBDIR/extract_crc $MOD3) >> $OFILE
  echo "in Dynlink.add_available_units crc_unit_list;;" >> $OFILE
  (cd $OTOP/utils; $OLIBDIR/extract_crc $MOD4) >> $OFILE
  echo "in Dynlink.add_available_units crc_unit_list;;" >> $OFILE
fi
