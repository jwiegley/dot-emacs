#!/bin/sh

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

# This script tests functions from python-mode.el.

# Code:

PDIR=$PWD
echo "\$PWD: $PWD"
# WERKSTATT set in .bashrc, thus unset remotly
WERKSTATT=${WERKSTATT:=1}
echo "\$WERKSTATT: $WERKSTATT"

TESTDIR=$PDIR/test
export TESTDIR

# echo "\$1: $1"

# if $1; then
# PYTHONMODE=$PDIR/$1
if [ -s $PDIR/python-mode.el ]; then
    PYTHONMODE=$PDIR/python-mode.el
elif [ -s $PDIR/python-components-mode.el ]; then
    PYTHONMODE=$PDIR/python-components-mode.el
fi

echo "\$PYTHONMODE: $PYTHONMODE"

SETUP=$TESTDIR/setup-ert-tests.el

TEST1=$TESTDIR/py-ert-tests-1.el
TEST2=$TESTDIR/py-ert-tests-2.el
TEST3=$TESTDIR/py-ert-always-split-lp-1361531-tests.el
TEST4=$TESTDIR/py-ert-just-two-split-lp-1361531-tests.el
TEST5=$TESTDIR/py-ert-beginning-tests.el
TEST6=$TESTDIR/py-ert-forward-tests.el
TEST7=$TESTDIR/py-ert-function-tests.el
TEST8=$TESTDIR/py-ert-variablen-tests.el
TEST9=$TESTDIR/py-shell-arg-ert-tests.el
TEST10=$TESTDIR/py-ert-execute-block-test.el
TEST11=$TESTDIR/py-ert-execute-region-test.el
TEST12=$TESTDIR/py-execute-region-commandp-test.el
TEST13=$TESTDIR/py-ert-tests-2.el
TEST14=$TESTDIR/py-ert-tests-3.el
TEST15=$TESTDIR/py-ert-forward-tests.el
TEST16=$TESTDIR/py-ert-tests-4.el
TEST17=$TESTDIR/py-extra-tests.el

if [ -s emacs24 ]; then
    EMACS=emacs24
else
    EMACS=emacs
fi

echo "\$EMACS: $EMACS"

PYCO="$PDIR/completion/pycomplete.el"

hier() {
    $EMACS -Q --batch \
--eval "(message (emacs-version))" \
--eval "(setq py-debug-p nil)" \
--eval "(add-to-list 'load-path \"$PDIR/\")" \
--eval "(add-to-list 'load-path \"$TESTDIR/\")" \
-load $SETUP \
-load $PYTHONMODE \
-l $TEST1 \
-l $TEST2 \
-l $TEST4 \
-l $TEST5 \
-l $TEST6 \
-l $TEST7 \
-l $TEST8 \
-l $TEST12 \
-l $TEST13 \
-l $TEST14 \
-l $TEST15 \
-l $TEST16 \
-f ert-run-tests-batch-and-exit
}

entfernt() {
$EMACS -Q --batch \
--eval "(message (emacs-version))" \
--eval "(add-to-list 'load-path \"$PDIR/\")" \
--eval "(add-to-list 'load-path \"$TESTDIR/\")" \
-load $SETUP \
-load $PYTHONMODE \
-l $TEST1 \
-l $TEST2 \
-l $TEST4 \
-l $TEST5 \
-l $TEST6 \
-l $TEST7 \
-l $TEST8 \
-l $TEST12 \
-l $TEST13 \
-l $TEST14 \
-l $TEST15 \
-l $TEST16 \
--eval "(setq py-debug-p nil)" \
-f ert-run-tests-batch-and-exit
}

if [ $WERKSTATT -eq 0 ]; then
    hier
    echo "Lade \$DIR6 und \$DIR7"
else
    echo "entfernt"
    echo "\$WERKSTATT: $WERKSTATT"
    echo "Lade testumgebung \"ENTFERNT\""
    entfernt
fi
