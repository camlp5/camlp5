#!/bin/sh -e
# check_ocaml_versions.sh,v

TOP=$HOME/work
DEST=$TOP/usr
OCAMLSDIR=$TOP/ocaml_src/trunk
CAMLP5DIR=$TOP/camlp5_src/master
OCAMLWDIR=$TOP/camlp5_src/test_ocaml_version
MODE=--strict
DOOPT=1
ARCH64=0

wd=$(pwd)
cd $DEST
PATH=$(pwd)/bin:$PATH

getvers () {
  cd "$OCAMLSDIR"
  if [ "$ARCH64" = "0" ]; then
    vers="$(git tag | grep -v csl | grep -v '^1.0[0-5]')"
  else
    vers="$(git tag | grep -v csl | grep -v '^[1|2]' | grep -v '^3.0[0-6]')"
  fi
  vers=$(echo $vers | tr '\n' ' ')
}

exclude () {
  e="$OPTARG"
  vers1=""
  for i in $vers; do
    if [ "$i" "<" "$e" ]; then :; else vers1="$vers1$i "; fi
  done
  vers="$vers1"
}

usage () {
  echo "Usage: check_ocaml_versions.sh <options>"
  echo "<options> are:"
  echo "  -d <dir>    Change directory of versions"
  echo "  -e <vers>   Exclude all versions before that version"
  echo "  -h          Display this list of options"
  echo "  -n          No opt (only bytecode)"
  echo "  -t          Camlp5 transitional mode"
  echo "  -v <vers>   Only that version (can be used several times)."
  echo "  -6          This is a 64 bits machine"
  echo
  echo "Directory of versions: $OCAMLSDIR"
  if [ "$versopt" != "" ]; then
    echo "Versions:$versopt"
  else
    echo "Available versions: $vers"
  fi
}
getvers
versopt=""
while getopts ":d:e:hntv:6" name; do
  case "$name" in
  'd') D="$OPTARG"; OCAMLSDIR=$(cd "$wd"; cd "$D"; pwd); getvers;;
  'e') exclude;;
  'h') usage; exit 0;;
  'n') DOOPT=0;;
  't') MODE="--transitional";;
  'v') versopt="$versopt $OPTARG";;
  '6') ARCH64=1; getvers;;
  '?') echo "Invalid option -$OPTARG"; echo "Use option -h for help"; exit 2;;
  esac
done

if [ $(($OPTIND-1)) -ne $# ]; then
  shift $(($OPTIND-1))
  echo "Don't know what to do with '$1'"
  exit 2
fi

if [ "$versopt" != "" ]; then vers="$versopt"; fi

echo =====================
echo $vers
for i in $vers; do
  echo =====================
  echo date: $(date) version: $i
  echo "+++++ cd $OCAMLSDIR"
  cd $OCAMLSDIR
  echo "+++++ /bin/rm -rf $OCAMLWDIR"
  /bin/rm -rf $OCAMLWDIR
  echo "+++++ git worktree prune"
  git worktree prune
  echo "+++++ git worktree add $OCAMLWDIR tags/$i"
  git worktree add $OCAMLWDIR tags/$i
  echo "+++++ cd $OCAMLWDIR"
  cd $OCAMLWDIR
  if [ "$i" "<" "4.00" ]; then
    sed -e 's/ camlp4o[a-z]* / /g' Makefile | grep -v partial-install.sh |
    grep -v 'cd ocamldoc' | grep -v 'cd camlp4' |
    sed -e 's/ ocamlbuild.byte / /g' |  sed -e 's/ ocamlbuild.native / /g' |
    grep -v '$(MAKE) ocamlbuildlib.native'  > tmp
    mv Makefile Makefile.bak
    mv tmp Makefile
    touch config/Makefile
    config_extra_opt=
  elif [ "$i" "<" "4.02.0" ]; then
    config_extra_opt="-no-camlp4"
  else
    config_extra_opt="--no-ocamldoc"
  fi
  if [ "$i" = "1.05" -o "$i" = "1.06" ]; then
    sed -i -e '/fpu_control.h/d;/setfpucw/d' byterun/floats.c
  fi
  echo "+++++ ./configure -bindir $TOP/usr/bin -libdir $TOP/usr/lib/ocaml -mandir $TOP/usr/man/man1" $config_extra_opt
  ./configure -bindir $DEST/bin -libdir $DEST/lib/ocaml -mandir $DEST/man/man1 $config_extra_opt
  sed -i -e 's/ graph//' -e 's/ labltk//' -e 's/ num / /' config/Makefile
  sed -i -e 's/define HAS_MEMMOVE/undef HAS_MEMMOVE/' config/s.h
  if [ "$DOOPT" = "0" ]; then
    echo "+++++ time make world"
    time make world
  elif [ "$i" = "1.06" -o "$i" = "1.07" -o "$i" = "2.00" -o "$i" = "2.01" -o \
         "$i" = "2.02" -o "$i" = "2.03" -o "$i" = "2.04" -o "$i" = "2.99" -o \
         "$i" = "3.00" ]
  then
    echo "+++++ time make world opt"
    time make world opt
  elif [ "$i" = "3.01" -o "$i" = "3.02" -o "$i" = "3.03-alpha" -o \
         "$i" = "3.04" ]
  then
    echo "+++++ time make world opt opt.opt"
    time make world opt opt.opt
  else
    echo "+++++ time make world.opt"
    time make world.opt
  fi
  echo "+++++ make install"
  /bin/rm -rf $TOP/usr/lib/ocaml
  make install
  echo "+++++ make clean"
  if [ -f "Makefile.bak" ]; then mv Makefile.bak Makefile; fi
  make clean
  echo "+++++ cd $CAMLP5DIR"
  cd $CAMLP5DIR
  echo "+++++ make clean"
  make clean
  echo "+++++ ./configure $MODE"
  ./configure $MODE
  if [ "$DOOPT" = "0" ]; then
    echo "+++++ time make world"
    time make -j2 world
  else
    echo "+++++ time make world.opt"
    time make -j2 world.opt
  fi
  echo "+++++ make install"
  make install
  echo "+++++ make clean"
  make clean
done 2>&1

echo date: $(date) end
