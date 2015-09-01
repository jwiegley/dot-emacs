#!/bin/bash

# Wrapper script for pfebrowser, to set the PROGRAMATICA environment variable.

defaultPROGRAMATICA="/home/project/pacsoft/tools/lib/Programatica"
PROGRAMATICA="${PROGRAMATICA-$defaultPROGRAMATICA}"
export PROGRAMATICA

exec "$PROGRAMATICA/bin/pfebrowser" "$@"
