#!/bin/sh

set -e

TARGET=test_suite
#FLAGS="-verbose 100 -lflags -g -cflags -g -libs bigarray,unix"
FLAGS="-verbose 100 -lflags -g -cflags -g "
OCAMLBUILD=ocamlbuild

ocb()
{
  $OCAMLBUILD $FLAGS $*
}

rule() {
  case $1 in
    clean)   ocb -clean;;
    native)  ocb $TARGET.native;;
    byte)    ocb $TARGET.byte;;
    profile) ocb $TARGET.p.native $TARGET.d.byte;;
    all)     ocb $TARGET.native $TARGET.byte;;
    depend) echo "Not needed.";;
    *)      echo "Unknown action $1";;
  esac;
}

if [ $# -eq 0 ]; then
  rule all
else
  while [ $# -gt 0 ]; do
    rule $1;
    shift
  done
fi
