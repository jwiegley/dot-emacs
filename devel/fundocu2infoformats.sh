#!/bin/bash
 # -- extract and convert documentation from Emacs Lisp files

# Author: Andreas Röhler <andreas.roehler@online.de>

# This program is free software; you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 3 of the License, or
# (at your option) any later version.
# This program is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU General Public License for more details.
# You should have received a copy of the GNU General Public License
# along with this program.  If not, see <http://www.gnu.org/licenses/>.
# Commentary:

#  tests Emacs python-mode
#
# Code:

# Edit the vars pointing to the directories/files
# holding your python-mode for test

# assumes python-mode files in current directory

# the path
# needs being in `test' directory
PDIR=`pwd`


# write PATH-TO-EMACS source code directory here
# EMACS_SOURCE_DIR="$HOME/emacs-20110426"
EMACS_SOURCE_DIR=$HOME/emacs-23.4

# python-mode file to load
if [ -s "../python-components-mode.el" ];
    then
    PYTHONMODE="../python-components-mode.el"
    else
    PYTHONMODE="../python-mode.el"
fi

if [ $1 ]; then
    EINGABE=$1
fi


if [ $EMACS_SOURCE_DIR ]; then

EMACS="${EMACS_SOURCE_DIR}/src/emacs"

# else
# EMACS=emacs
# when installed Emacs shall be used, CCCMDS must be set
# CCCMDS="${EMACS_SOURCE_DIR}/lisp/progmodes/cc-cmds.el"

# ERG=$(echo $LOGNAME | sed 's/^s\(.*\)/m/')
# if [ $ERG == "m" ]; then

    # EMACS_SOURCE_DIR="$HOME/emacs-20110426"
# else

    # EMACS_SOURCE_DIR="~/emacs-20110426"
# fi

HIGHL="../highlight-indentation.el"

CLMACS="${EMACS_SOURCE_DIR}/lisp/emacs-lisp/cl-macs.el"
BYTECOMP="${EMACS_SOURCE_DIR}/lisp/emacs-lisp/bytecomp.el"
CUSTOM="${EMACS_SOURCE_DIR}/lisp/custom.el"
ANSICOLOR="${EMACS_SOURCE_DIR}/lisp/ansi-color.el"
COMINT="${EMACS_SOURCE_DIR}/lisp/comint.el"
CCCMDS="${EMACS_SOURCE_DIR}/lisp/progmodes/cc-cmds.el"
SHELL="${EMACS_SOURCE_DIR}/lisp/shell.el"
PYMACS="../pymacs.el"
# file holding the tests
TESTFILE="py-bug-numbered-tests.el"
TESTFILE2="python-mode-test.el"
DOCU=/tools/fundocu2infoformats.el

echo "\$PYMACS: $PYMACS"

$EMACS -Q --batch --eval "(message (emacs-version))" --eval "(when (featurep 'python-mode)(unload-feature 'python-mode t))" --eval "(add-to-list 'load-path \"$PDIR/\")" --eval "(setq py-install-directory \".\")" -load "$PYMACS" -load $CCCMDS -load $COMINT -load $SHELL -load $ANSICOLOR -load $CLMACS -load $BYTECOMP -load $CUSTOM -load $PYTHONMODE \
--funcall finds-from-programm \


else

cat    <<EOF
usage: ${0##*/} EMACS_SOURCE_DIR

Runs from tools dir
This script write commands-lists from python-mode files.

EOF

fi

