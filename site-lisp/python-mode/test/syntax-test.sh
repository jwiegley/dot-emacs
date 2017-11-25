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

# Check resp. edit the vars pointing to the directories/files
# holding your python-mode and Emacsen for test

# alternativly select Emacs by giving $EMACS_SOURCE_DIR
# as shell arg
# ./syntax-test.sh EMACS_SOURCE_DIR
# Emacs will be looked up: ${EMACS_SOURCE_DIR}/src/emacs

# assumes test files in current directory

# the path
PDIR=`pwd`

# write PATH-TO-EMACS source code directory here
# EMACS_SOURCE_DIR="$HOME/emacs-20110426"
EMACS_SOURCE_DIR=

# python-mode file to load
if [ -s "../python-components-mode.el" ];
    then
    PYTHONMODE="../python-components-mode.el"
    else
    PYTHONMODE="../python-mode.el"
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

MODEDIR=${PDIR%%/test}
echo "\$MODEDIR: $MODEDIR"

CCCMDS="${EMACS_SOURCE_DIR}/lisp/progmodes/cc-cmds.el"
# file holding the tests
TESTFILE="py-bug-numbered-tests.el"
TESTFILE2="python-mode-test.el"

EMACS23="$HOME/emacs-23.3/src/emacs-23.3.1"
EMACS23python="$HOME/emacs-23.3/lisp/progmodes/python.el"
EMACS24python="$HOME/emacs-20110426/lisp/progmodes/python.el"

CCCMDS="${EMACS_VERZEICHNIS}/lisp/progmodes/cc-cmds.el"
# file holding the tests
TESTFILE="py-bug-numbered-tests.el"
TESTFILE2="python-mode-test.el"
TESTFILE3="python-mode-syntax-test.el"
EMACS="${EMACS_VERZEICHNIS}/src/emacs"
HIL="../highlight-indentation.el"

if [ ${MODEDIR%%*modes/} == "components-python-mode" ];
    then

    $EMACS -Q --batch --eval "(message (emacs-version))" --eval "(when (featurep 'python)(unload-feature 'python t))" --eval "(when (featurep 'python-mode)(unload-feature 'python-mode t))"  --eval "(add-to-list 'load-path \"$PDIR/\")" -load "$MODEDIR/misc-utils.el" -load "$MODEDIR/beg-end.el" -load "$MODEDIR/sh-beg-end.el" -load "$MODEDIR/thingatpt-highlight.el" -load "$MODEDIR/thingatpt-utils-base.el" -load "$MODEDIR/thing-at-point-utils.el" -load "$MODEDIR/ar-comment-lor.el" -load "$MODEDIR/thingatpt-python-expressions.el" -load "$MODEDIR/highlight-indentation" -load "$MODEDIR/hungry-delete.el" \
-load "$MODEDIR/python-components-edit.el" -load "$MODEDIR/python-components-intern.el" -load "$MODEDIR/python-components-move.el" -load "$MODEDIR/python-mode-execute.el" -load "$MODEDIR/python-mode-send.el" -load "$MODEDIR/python-components-pdb.el" -load "$MODEDIR/python-components-skeletons.el" -load "$MODEDIR/python-components-help.el" -load "$MODEDIR/python-components-extensions.el" -load "$MODEDIR/python-components-imenu.el" -load "$MODEDIR/python-components-mode.el" -load "$PCOT/py-bug-numbered-tests.el" -load "$PCOT/python-mode-test.el" -load "$PDIR/$TESTFILE3" -load $CCCMDS --eval "(quietly-read-abbrev-file (expand-file-name \"~/.abbrev_defs\"))" \
--funcall erste-tqs-syntax-test

    $EMACS23 -Q --batch --eval "(message (emacs-version))" --eval "(when (featurep 'python)(unload-feature 'python t))" --eval "(when (featurep 'python-mode)(unload-feature 'python-mode t))"  --eval "(add-to-list 'load-path \"$PDIR/\")" -load "$MODEDIR/misc-utils.el" -load "$MODEDIR/beg-end.el" -load "$MODEDIR/sh-beg-end.el" -load "$MODEDIR/thingatpt-highlight.el" -load "$MODEDIR/thingatpt-utils-base.el" -load "$MODEDIR/thing-at-point-utils.el" -load "$MODEDIR/ar-comment-lor.el" -load "$MODEDIR/thingatpt-python-expressions.el" -load "$MODEDIR/highlight-indentation" -load "$MODEDIR/hungry-delete.el" \
-load "$MODEDIR/python-components-edit.el" -load "$MODEDIR/python-components-intern.el" -load "$MODEDIR/python-components-move.el" -load "$MODEDIR/python-mode-execute.el" -load "$MODEDIR/python-mode-send.el" -load "$MODEDIR/python-components-pdb.el" -load "$MODEDIR/python-components-skeletons.el" -load "$MODEDIR/python-components-help.el" -load "$MODEDIR/python-components-extensions.el" -load "$MODEDIR/python-components-imenu.el" -load "$MODEDIR/python-components-mode.el" -load "$PCOT/py-bug-numbered-tests.el" -load "$PCOT/python-mode-test.el" -load "$PDIR/$TESTFILE3" -load $CCCMDS --eval "(quietly-read-abbrev-file (expand-file-name \"~/.abbrev_defs\"))" \
--funcall erste-tqs-syntax-test

else
    echo "\$EMACS24python: $EMACS24python"
    $EMACS -Q --batch --eval "(message (emacs-version))" -load "$PDIR/$TESTFILE3" --load $EMACS24python --funcall erste-tqs-syntax-test
    echo
    echo "\$EMACS23python: $EMACS23python"
    $EMACS23 -Q --batch --eval "(message (emacs-version))" -load "$PDIR/$TESTFILE3" -load $EMACS23python --eval "(sit-for 0.1)" --funcall erste-tqs-syntax-test
    echo
    echo "unloading before"
    echo "\$EMACS23python: $EMACS23python"
    $EMACS23 -Q --batch --eval "(message (emacs-version))"  -load "$PDIR/$TESTFILE3" --eval "(when (featurep 'python)(unload-feature 'python t))" -load $EMACS23python --eval "(sit-for 0.1)" --funcall erste-tqs-syntax-test
    echo
    echo "\$MODEDIR/python-mode.el: $MODEDIR/python-mode.el"
    $EMACS -Q --batch --eval "(message (emacs-version))" -load "$PDIR/$TESTFILE3" --load $MODEDIR/python-mode.el --eval "(sit-for 0.1)" --funcall erste-tqs-syntax-test
    echo
    echo "\$MODEDIR/python-mode.el: $MODEDIR/python-mode.el"
    $EMACS23 -Q --batch --eval "(message (emacs-version))" --eval "(when (featurep 'python)(unload-feature 'python t))" -load "$PDIR/$TESTFILE3" --load $MODEDIR/python-mode.el --eval "(sit-for 0.1)" --funcall erste-tqs-syntax-test

fi
