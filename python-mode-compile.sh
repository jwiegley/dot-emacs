#!/bin/bash
 # --

# Author: Andreas Roehler <andreas.roehler@online.de>

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
EMACS_SOURCE_DIR=
EMACS_SOURCE_DIR="$HOME/emacs-23.4"

# python-mode file to load
if [ -s "python-components-mode.el" ];
    then
    PYTHONMODE="python-components-mode.el"
    else
    PYTHONMODE="python-mode.el"
fi

if [ $1 ]; then
    EMACS_SOURCE_DIR=$1
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

HIGHL="highlight-indentation.el"
CLMACS="${EMACS_SOURCE_DIR}/lisp/emacs-lisp/cl-macs.el"
BYTECOMP="${EMACS_SOURCE_DIR}/lisp/emacs-lisp/bytecomp.el"
CUSTOM="${EMACS_SOURCE_DIR}/lisp/custom.el"
ANSICOLOR="${EMACS_SOURCE_DIR}/lisp/ansi-color.el"
COMINT="${EMACS_SOURCE_DIR}/lisp/comint.el"
CCCMDS="${EMACS_SOURCE_DIR}/lisp/progmodes/cc-cmds.el"
SHELL="${EMACS_SOURCE_DIR}/lisp/shell.el"
SKEL="${EMACS_SOURCE_DIR}/lisp/skeleton.el"
PYMACS="pymacs.el"
# file holding the tests
TESTFILE="test/py-bug-numbered-tests.el"
TESTFILE2="test/python-mode-test.el"
CEXEC="python-extended-executes.el"

echo "\$PYMACS: $PYMACS"
echo "\$PYTHONMODE: $PYTHONMODE"
echo "\$PDIR/\$TESTFILE: $PDIR/$TESTFILE"

$EMACS -Q --batch --eval "(message (emacs-version))" --eval "(when (featurep 'python)(unload-feature 'python t))" --eval "(when (featurep 'python-mode)(unload-feature 'python-mode t))" --eval "(add-to-list 'load-path \"$PDIR/\")" --eval "(add-to-list 'load-path \"$TESTDIR/\")" --eval "(setq py-install-directory \".\")" -load "$PYMACS" -load $CCCMDS -load $COMINT -load $SHELL -load $ANSICOLOR -load $CLMACS -load $CUSTOM -load $SKEL -load "${EMACS_SOURCE_DIR}/extensions/$HIGHL" -load $PYTHONMODE --eval "(quietly-read-abbrev-file (expand-file-name \"~/.abbrev_defs\"))" \
--eval "(byte-compile-file (expand-file-name \"~/arbeit/emacs/python-modes/components-python-mode/python-components-mode.el\"))" \
--eval "(byte-compile-file (expand-file-name \"~/arbeit/emacs/python-modes/components-python-mode/column-marker.el\"))" \
--eval "(byte-compile-file (expand-file-name \"~/arbeit/emacs/python-modes/components-python-mode/highlight-indentation.el\"))" \
--eval "(byte-compile-file (expand-file-name \"~/arbeit/emacs/python-modes/components-python-mode/pymacs.el\"))" \
--eval "(byte-compile-file (expand-file-name \"~/arbeit/emacs/python-modes/components-python-mode/python-components-completion.el\"))" \
--eval "(byte-compile-file (expand-file-name \"~/arbeit/emacs/python-modes/components-python-mode/python-components-edit.el\"))" \
--eval "(byte-compile-file (expand-file-name \"~/arbeit/emacs/python-modes/components-python-mode/python-components-electric.el\"))" \
--eval "(byte-compile-file (expand-file-name \"~/arbeit/emacs/python-modes/components-python-mode/python-components-exec-forms.el\"))" \
--eval "(byte-compile-file (expand-file-name \"~/arbeit/emacs/python-modes/components-python-mode/python-components-execute.el\"))" \
--eval "(byte-compile-file (expand-file-name \"~/arbeit/emacs/python-modes/components-python-mode/python-components-extensions.el\"))" \
--eval "(byte-compile-file (expand-file-name \"~/arbeit/emacs/python-modes/components-python-mode/python-components-help.el\"))" \
--eval "(byte-compile-file (expand-file-name \"~/arbeit/emacs/python-modes/components-python-mode/python-components-imenu.el\"))" \
--eval "(byte-compile-file (expand-file-name \"~/arbeit/emacs/python-modes/components-python-mode/python-components-intern.el\"))" \
--eval "(byte-compile-file (expand-file-name \"~/arbeit/emacs/python-modes/components-python-mode/python-components-macros.el\"))" \
--eval "(byte-compile-file (expand-file-name \"~/arbeit/emacs/python-modes/components-python-mode/python-components-mode.el\"))" \
--eval "(byte-compile-file (expand-file-name \"~/arbeit/emacs/python-modes/components-python-mode/feg-python-el-extracts.el\"))" \
--eval "(byte-compile-file (expand-file-name \"~/arbeit/emacs/python-modes/components-python-mode/python-components-move.el\"))" \
--eval "(byte-compile-file (expand-file-name \"~/arbeit/emacs/python-modes/components-python-mode/python-components-named-shells.el\"))" \
--eval "(byte-compile-file (expand-file-name \"~/arbeit/emacs/python-modes/components-python-mode/python-components-pdb.el\"))" \
--eval "(byte-compile-file (expand-file-name \"~/arbeit/emacs/python-modes/components-python-mode/python-components-re-forms.el\"))" \
--eval "(byte-compile-file (expand-file-name \"~/arbeit/emacs/python-modes/components-python-mode/python-components-send.el\"))" \
--eval "(byte-compile-file (expand-file-name \"~/arbeit/emacs/python-modes/components-python-mode/python-components-shell-complete.el\"))" \
--eval "(byte-compile-file (expand-file-name \"~/arbeit/emacs/python-modes/components-python-mode/python-components-skeletons.el\"))" \
--eval "(byte-compile-file (expand-file-name \"~/arbeit/emacs/python-modes/components-python-mode/python-extended-executes.el\"))" \
\
--eval "(byte-compile-file (expand-file-name \"~/arbeit/emacs/python-modes/components-python-mode/test/py-bug-numbered-tests.el\"))" \
--eval "(byte-compile-file (expand-file-name \"~/arbeit/emacs/python-modes/components-python-mode/test/python-mode-test.el\"))" \
--eval "(byte-compile-file (expand-file-name \"~/arbeit/emacs/python-modes/components-python-mode/test/python-executes-test.el\"))" \

else

cat    <<EOF
usage: ${0##*/} EMACS_SOURCE_DIR

This script tests python-mode with non-installed Emacsen in a Bash.

It assumes being in directory "test" below python-mode.el and relies on source-code directories as delivered by bzr branch.

Edit \$EMACS_SOURCE_DIR to specify an Emacs or put "PATH-TO-EMACS-SOURCES" as shell argument.

To run tests with installed Emacs, load available test-files like "py-bug-numbered-tests.el" and do "M-x py-run-bug-numbered-tests". Alternatively you may edit variables making it point according to you installation.

EOF

fi

