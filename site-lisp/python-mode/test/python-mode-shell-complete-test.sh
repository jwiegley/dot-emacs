#!/bin/bash
 # --

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
EMACS_SOURCE_DIR=
EMACS_SOURCE_DIR="$HOME/emacs-23.4"

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
PYMACS="../pymacs.el"
# file holding the tests
TESTFILE="py-bug-numbered-tests.el"
TESTFILE2="python-mode-test.el"
TESTFILE3="python-extended-executes-test.el"
TESTFILE4="python-executes-test.el"
TESTFILE5="py-completion-tests.el"
CEXEC="python-extended-executes.el"
PDIR="../"
PCOT="."

echo "\$PYMACS: $PYMACS"
echo "\$PYTHONMODE: $PYTHONMODE"
echo "\$PDIR/\$TESTFILE: $PDIR/$TESTFILE"

$EMACS -Q --batch --eval "(message (emacs-version))" --eval "(when (featurep 'python)(unload-feature 'python t))" --eval "(when (featurep 'python-mode)(unload-feature 'python-mode t))" --eval "(add-to-list 'load-path \"$PDIR/\")" --eval "(add-to-list 'load-path \"$TESTDIR/\")" --eval "(setq py-install-directory \"..\")" -load "$PYMACS" -load $CCCMDS -load $COMINT -load $SHELL -load $ANSICOLOR -load $CLMACS -load $BYTECOMP -load $CUSTOM -load $SKEL -load $PYTHONMODE -load "$PCOT/$TESTFILE" -load "$PCOT/$TESTFILE5" --eval "(quietly-read-abbrev-file (expand-file-name \"~/.abbrev_defs\"))" \
--funcall python-shell-complete-test \
--funcall usr-bin-python-shell-complete-test \
--funcall usr-bin-python2.7-shell-complete-test \
--funcall home-speck-arbeit-python-epdfree-epd_free-7.2-2-rh5-x86-bin-python2.7-shell-complete-test \
--funcall usr-bin-python3.1-shell-complete-test \
--funcall ipython-shell-complete-test \
--funcall usr-bin-ipython-shell-complete-test \
--funcall home-speck-arbeit-python-epd_free-7.1-2-rh5-x86-bin-ipython-shell-complete-test \
# --funcall usr-bin-python3-shell-complete-test \

else

cat    <<EOF
usage: ${0##*/} EMACS_SOURCE_DIR

This script tests python-mode with non-installed Emacsen in a Bash.

It assumes being in directory "test" below python-mode.el and relies on source-code directories as delivered by bzr branch.

Edit \$EMACS_SOURCE_DIR to specify an Emacs or put "PATH-TO-EMACS-SOURCES" as shell argument.

To run tests with installed Emacs, load available test-files like "py-bug-numbered-tests.el" and do "M-x py-run-bug-numbered-tests". Alternatively you may edit variables making it point according to you installation.

EOF

fi

