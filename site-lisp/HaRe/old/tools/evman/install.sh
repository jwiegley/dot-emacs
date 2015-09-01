#!/bin/sh

L=../lib/Programatica
C=$L/types/certificate
S=../../../../../evman/servers

for server ; do
  mkdir -p $C/$server
  (cd $C/$server; ln -s $S/$server/* .; rm -f CVS)
done
