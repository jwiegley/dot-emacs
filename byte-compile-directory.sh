#!/bin/bash
 # -- byte-compile Emacs Lisp files delivered with python-mode.el

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

# Commentary:  Edit the vars pointing to the directories/files
# holding your python-mode for test
# assumes python-mode files in or below current directory

# Code:


# the path 
PDIR=`pwd`

# python-mode file to load
if [ -s "python-components-mode.el" ];
    then
    PYTHONMODE='python-components-mode.el'
    else
    PYTHONMODE='python-mode.el'
fi

EMACS=emacs
PYMACSDIR=Pymacs

$EMACS -Q --batch --eval "(message (emacs-version))" --eval "(when (featurep 'python-mode)(unload-feature 'python-mode t))" --eval "(add-to-list 'load-path \"$PDIR/\")" --eval "(add-to-list 'load-path \"$PYMACSDIR/\")" -load "$PDIR/pymacs.el" -load "$PDIR/$PYTHONMODE" --eval '(byte-recompile-directory default-directory 1 t)'


