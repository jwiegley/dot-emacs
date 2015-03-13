#!/bin/bash 

if [ -r "hi/pfeserver" ] ; then
  read port <hi/pfeserver
  { echo "$*" >&3; cat <&3; } 3<>"/dev/tcp/localhost/$port"
else
  echo >&2 "No PFE server available"
  exit 1
fi
