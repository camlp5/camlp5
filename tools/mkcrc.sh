#!/bin/sh -e
# mkcrc.sh,v

V=$OVERSION

MOD_OLIB="arg array"
if [ "$V" != "1.06" -a "$V" != "1.07" -a "$V" != "2.00" -a "$V" != "2.01" ]
then
  MOD_OLIB="$MOD_OLIB buffer"
fi
MOD_OLIB="$MOD_OLIB char filename format hashtbl lexing list obj pervasives printf set sort stream string sys"
MOD_MAIN="ast2pt exparser mLast parserify pcaml prtools quotation reloc"
MOD_5LIB="diff eprinter extfun fstream gramext grammar plexer plexing ploc pprintf pretty versdep"
MOD_PARS="asttypes location longident parsetree"
MOD_UTIL="pconfig warnings"
OFILE=crc.tmp

in_add_available_units () {
  if [ "$V" = "1.06" -o "$V" = "1.07" ]; then
    echo "in Dynlink.add_available_units (List.map (fun (m, s) -> (String.capitalize m, s)) crc_unit_list);;"
  else
    echo "in Dynlink.add_available_units crc_unit_list;;"
  fi
}

> $OFILE
if [ "$V" = "1.06" -o "$V" = "1.07" -o "$V" = "2.00" -o "$V" = "2.01" -o \
     "$V" = "2.02" -o "$V" = "2.03" -o "$V" = "2.04" -o "$V" = "2.99" -o \
     "$V" = "3.00" -o "$V" = "3.01" -o "$V" = "3.02" -o "$V" = "3.03" -o \
     "$V" = "3.04" -o "$V" = "3.05" -o "$V" = "3.06" ]
then
  (cd $OLIBDIR; $OLIBDIR/extract_crc $MOD_OLIB) >> $OFILE
  in_add_available_units >> $OFILE
  if [ "$V" = "2.03" -o "$V" = "2.04" -o "$V" = "2.99" ]; then
    (cd $OLIBDIR; $OLIBDIR/extract_crc sort) >> $OFILE
    in_add_available_units >> $OFILE
  fi
  (cd ../main; $OLIBDIR/extract_crc $MOD_MAIN) >> $OFILE
  in_add_available_units >> $OFILE
  (cd ../lib; $OLIBDIR/extract_crc $MOD_5LIB) >> $OFILE
  in_add_available_units >> $OFILE
  (cd $OTOPP; $OLIBDIR/extract_crc $MOD_PARS) >> $OFILE
  in_add_available_units >> $OFILE
  (cd $OTOPU; $OLIBDIR/extract_crc $MOD_UTIL) >> $OFILE
  in_add_available_units >> $OFILE
fi
