#!/bin/bash

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

# This script tests Emacs python-mode.

# Caveats:
#
# needs being started in `test' directory
# optional shell argument PATH/TO/EMACS-SOURCE-DIRECTORY might be given
#
# If testing with emacs-24 please be aware of bug 11984 [0], for the
# time being the patch will need to be added manually.
#
# IPython 0.12 due to a bug in argparse requires a patch [1] to work.
#
# 0. http://debbugs.gnu.org/cgi/bugreport.cgi?bug=11984
# 1. http://bugs.python.org/issue13720

# Code:

# if [ -n "$BASH" -o -n "$ZSH_VERSION" ] ; then
#     hash -r 2>/dev/null
# fi

# needs being in `test' directory
# PCOT=`pwd`
PCOT=$PWD
# PDIR=".."
PDIR=$(cd ..; pwd)
# the directory that this file is in.
# TESTDIR="$(dirname "$0")"
# PDIR="$TESTDIR/.."

# write PATH-TO-EMACS source code default directory here
EMACS_DEFAULT_DIR="/usr/share/emacs/24.3"

EMACS_DIR=
if [ $1 ]; then
    echo "\$1: $1"
    EMACS_DIR=$1
else
    EMACS_DIR=$EMACS_DEFAULT_DIR
fi

#     else
# cat    <<EOF
# usage: ${0##*/} EMACS_DIR
#
# This script tests python-mode with non-installed Emacsen in a Bash.
#
# It assumes being in directory "test" below python-mode.el and relies on source-code directories as delivered by bzr branch.
#
# Edit \$EMACS_DIR to specify an Emacs or put "PATH-TO-EMACS-SOURCES" as shell argument.
#
# To run tests with installed Emacs, load available test-files like "py-bug-numbered-tests.el" and do "M-x py-run-bug-numbered-tests". Alternatively you may edit variables making it point according to you installation.
#
# EOF
#
# fi

echo "\$EMACS_DIR: $EMACS_DIR"

if [ $1 ]; then
    EMACS="$EMACS_DIR/src/emacs"

else
    EMACS=emacs

fi

echo "\$EMACS: $EMACS"
# EMACS="/usr/bin/emacs"

# python-mode file to load
if [ -s "../python-components-mode.el" ];
then
    PYTHONMODE="../python-components-mode.el"
elif
    [ -s "../python-mode.el" ];
then
    PYTHONMODE="../python-mode.el"
else
    cat    <<EOF
usage: ${0##*/} EMACS_DIR

This script tests python-mode with non-installed Emacsen in a Bash.

It assumes being in directory "test" below python-mode.el and relies on source-code directories as delivered by bzr branch.

Edit \$EMACS_DIR to specify an Emacs or put "PATH-TO-EMACS-SOURCES" as shell argument.

To run tests with installed Emacs, load available test-files like "py-bug-numbered-tests.el" and do "M-x py-run-bug-numbered-tests". Alternatively you may edit variables making it point according to you installation.

EOF

fi

# edit this to get locally installed stuff loaded
MYEXTENSIONS="${HOME}/arbeit/emacs/elisp"

APAIR="${HOME}/arbeit/emacs/autopair/autopair.el"

if [ -s ${HOME}/.emacs.d/elpa/smart-operator-4.0/smart-operator.elc ];then
    SO="${HOME}/.emacs.d/elpa/smart-operator-4.0/smart-operator.elc"
elif [ -s ${HOME}/.emacs.d/elpa/smart-operator-4.0/smart-operator.el ];then
    SO="${HOME}/.emacs.d/elpa/smart-operator-4.0/smart-operator.el"
else
    SO="${MYEXTENSIONS}/smart-operator.el"
fi

COLMK="$PDIR/extensions/column-marker.el"
HIGHL="$PDIR/extensions/highlight-indentation.el"

# CLMACS="${EMACS_DIR}/lisp/emacs-lisp/cl-macs.el"
if [ -s "${EMACS_DIR}/lisp/emacs-lisp/cl-macs.elc" ];then
    CLMACS="${EMACS_DIR}/lisp/emacs-lisp/cl-macs.elc"

elif [ -s "${EMACS_DIR}/lisp/emacs-lisp/cl-macs.el" ];then
    CLMACS="${EMACS_DIR}/lisp/emacs-lisp/cl-macs.el"

else echo "${EMACS_DIR}/lisp/emacs-lisp/cl-macs.el not found"

fi

if [ -s "${EMACS_DIR}/lisp/custom.elc" ];then
    CUSTOM="${EMACS_DIR}/lisp/custom.elc"
else
    CUSTOM="${EMACS_DIR}/lisp/comint.el"
fi

if [ -s "${EMACS_DIR}/lisp/ansi-color.elc" ];then
    ANSICOLOR="${EMACS_DIR}/lisp/ansi-color.elc"
else
    ANSICOLOR="${EMACS_DIR}/lisp/ansi-color.el"
fi

if [ -s "${EMACS_DIR}/lisp/comint.elc" ]; then
    COMINT="${EMACS_DIR}/lisp/comint.elc"
else
    COMINT="${EMACS_DIR}/lisp/comint.el"
fi

# if [ -s "${EMACS_DIR}/lisp/progmodes/cc-cmds.el" ];then
#     CC_CMDS="${EMACS_DIR}/lisp/progmodes/cc-cmds.el"
#     echo "\$CC_CMDS: $CC_CMDS"
# elif [ -s "${EMACS_DIR}/lisp/progmodes/cc-cmds.el.gz" ];then
#     CC_CMDS="${EMACS_DIR}/lisp/progmodes/cc-cmds.el.gz"
#     echo "\$CC_CMDS: $CC_CMDS"
# else
# echo "${EMACS_DIR}/lisp/progmodes/cc-cmds.el not found"
# fi

# SKEL="${EMACS_DIR}/lisp/skeleton.el"
if [ -s "${EMACS_DIR}/lisp/skeleton.elc" ];then
    SKELETON="${EMACS_DIR}/lisp/skeleton.elc"
else
    SKELETON="${EMACS_DIR}/lisp/skeleton.el"
fi

PYCO="$PDIR/completion/pycomplete.el"

# file holding the tests
TESTFILE="py-bug-numbered-tests.el"
TESTFILE2="python-mode-test.el"
TESTFILE3="python-extended-executes-test.el"
# TESTFILE4="python-executes-test.el"
TESTFILE5="py-shell-completion-tests.el"
TESTFILE6="py-split-window-on-execute-lp-1361531-test.el"
TESTFILE7="py-multi-split-window-on-execute-lp-1361531-test.el"
# TESTFILE8="py-always-split-window-on-execute-lp-1361531-test.el"
CEXEC="python-extended-executes.el"

UTILS="devel/python-mode-utils.el"

echo "\$PYMACS: $PYMACS"
echo "\$PYTHONMODE: $PYTHONMODE"
echo "\$PDIR/\$TESTFILE: $PDIR/$TESTFILE"

$EMACS -Q --batch \
--eval "(message (emacs-version))" \
--eval "(setq py-verbose-p t)" \
--eval "(when (featurep 'python)(unload-feature 'python t))" \
--eval "(when (featurep 'python-mode)(unload-feature 'python-mode t))" \
--eval "(add-to-list 'load-path \"$PDIR/\")" \
--eval "(add-to-list 'load-path \"$TESTDIR/\")" \
--eval "(setq py-install-directory \"$PDIR\"))" \
--eval "(message \"py-install-directory: %s\" py-install-directory)" \
--eval "(setq py-load-pymacs-p nil)" \
-load $COMINT \
-load $ANSICOLOR \
-load $CLMACS \
-load $CUSTOM \
-load $SO \
-load $COLMK \
-load $HIGHL \
-load $PYTHONMODE \
 --eval "(message \"py-temp-directory: %s\" py-temp-directory)" \
-load $PCOT/$TESTFILE \
-load $PCOT/$TESTFILE2 \
-load $PCOT/$TESTFILE3 \
-load $PCOT/$TESTFILE5 \
-load $PCOT/$TESTFILE6 \
-load $PCOT/$TESTFILE7 \
-load $PDIR/$UTILS \
-eval "(when (file-exists-p \"~/.abbrev_defs\") (quietly-read-abbrev-file (expand-file-name \"~/.abbrev_defs\")))" \
-eval "(setq enable-local-variables :all)" \
--funcall opening-brace-on-builtins-lp-1400951-test \
--funcall key-binding-tests \
--funcall comment-inside-curly-braces-lp-1395076-test \
--funcall py-execute-region-python3-no-switch-test \
--funcall script-buffer-appears-instead-of-python-shell-buffer-lp-957561-test \
--funcall completion-fails-in-python-script-r989-lp-1004613-test \
--funcall augmented-assigment-test \
--funcall py-fill-string-django-test \
--funcall py-fill-string-onetwo-test \
--funcall py-fill-string-pep-257-test \
--funcall py-fill-string-pep-257-nn-test \
--funcall py-fill-string-symmetric-test \
--funcall forward-sexp-test \
--funcall fill-paragraph-in-docstring-lp-1161232-test \
--funcall ipython-shell-complete-test \
--funcall inconvenient-window-splitting-behavior-ipython-lp-1018996-test \
--funcall does-not-dedent-regions-lp-1072869-test \
--funcall py-execute-buffer-ipython-lp-1252643-test \
--funcall py-ipython-complete-lp-927136-test \
--funcall temporary-files-remain-when-python-raises-exception-lp-1083973-n1-test \
--funcall temporary-files-remain-when-python-raises-exception-lp-1083973-n2-test \
--funcall temporary-files-remain-when-python-raises-exception-lp-1083973-n3-test \
--funcall temporary-files-remain-when-python-raises-exception-lp-1083973-n4-test \
--funcall py-electric-comment-add-space-lp-828398-test \
--funcall py-electric-comment-add-space-t-lp-828398-test \
--funcall switch-windows-on-execute-p-test \
--funcall C-c-C-c-lp-1221310-and-store-result-test \
--funcall execute-region-lp-1294796-test \
--funcall more-docstring-filling-woes-lp-1102296-pep-257-test \
--funcall more-docstring-filling-woes-lp-1102296-pep-257-nn-test \
--funcall py-docstring-style-pep-257-nn-closing-quotes-lp-1241147-test \
--funcall py-execute-block-or-clause-python-test \
--funcall goto-beginning-of-tqs-lp-735328-test \
--funcall previous-statement-lp-637955-test \
--funcall py-shell-name-no-op-lp-1349549-test \
--funcall stop-before-prompt-lp-1331953-test \
--funcall py-describe-symbol-fails-on-modules-lp-919719-test \
--funcall py-execute-buffer-python3-looks-broken-lp-1085386-test \
--funcall UnicodeEncodeError-python3-test \
--funcall execute-buffer-lp-1338134-test \
--funcall py-execute-block-or-clause-python2-test \
--funcall py-split-window-on-execute-lp-1361531-ipython-test \
--funcall py-split-window-on-execute-lp-1361531-bpython-test \
--funcall key-binding-tests \
--funcall automatic-indentation-is-broken-lp-889643-test \
--funcall execute-indented-code-lp-828314-test \
--funcall py-nested-block-or-clause-test \
--funcall py-split-window-on-execute-lp-1361531-python-test \
--funcall py-split-window-on-execute-lp-1361531-python2-test \
--funcall py-split-window-on-execute-lp-1361531-jython-test \
--funcall py-split-window-on-execute-lp-1361531-python3-test \
--funcall py-store-result-test \
--funcall Bogus-whitespace-left-in-docstring-after-wrapping-lp-1178455-test \
--funcall py-shell-invoking-python-lp-835151-test \
--funcall missing-py-variable-name-face-lp-1215791-test \
--funcall inconvenient-window-splitting-behavior-python-lp-1018996-test \
--funcall IndentationError-expected-an-indented-block-when-execute-lp-1055569-test \
--funcall py-electric-delete-test \
--funcall py-execute-buffer-python3-switch-test \
--funcall fails-to-indent-abs-wrong-type-argument-lp-1075673-test \
--funcall python2.7-shell-complete-test \
--funcall python3-shell-complete-test \
--funcall py-execute-buffer-python-switch-test \
--funcall py-execute-buffer-python2-switch-test \
--funcall indent-triplequoted-to-itself-lp-752252-test \
--funcall not-that-useful-completion-lp-1003580-test \
--funcall py-shell-in-a-shell-buffer-doesnt-work-lp-1182696-test \
--funcall completion-at-gentoo-lp-1008842-test \
--funcall wrong-type-argument-inserted-chars-lp-1293172-test \
--funcall py-execute-block-or-clause-python3-test \
--funcall py-object-reference-face-should-inherit-from-lp-1340455-test \
--funcall python-shell-complete-test \
--funcall impossible-to-execute-a-buffer-with-from-future-imports-lp-1063884-test \
--funcall complaint-about-non-ASCII-character-lp-1042949-test \
--funcall interpreter-mode-alist-lp-1355458-test-1 \
--funcall interpreter-mode-alist-lp-1355458-test-2 \
--funcall interpreter-mode-alist-lp-1355458-test-3 \
--funcall interpreter-mode-alist-lp-1355458-test-4 \
--funcall interpreter-mode-alist-lp-1355458-test-5 \
--funcall auto-indent-lp-134258-test \
--funcall dont-complete-empty-line-lp-1340824-test \
--funcall vertical-alignment-lp-1332245-test \
--funcall specify-default-interpreter-lp-1332652-test \
--funcall py-beginning-of-statement-test-1 \
--funcall docstring-style-switches-test \
--funcall complaint-about-non-ASCII-character-lp-1042949-test \
--funcall UnicodeEncodeError-lp-550661-test \
--funcall filename-completion-fails-in-ipython-lp-1027265-n1-test \
--funcall filename-completion-fails-in-ipython-lp-1027265-n2-test \
--funcall master-file-not-honored-lp-794850-test \
--funcall tab-results-in-never-ending-process-lp-1163423-test \
--funcall incorrect-use-of-region-in-py-shift-left-lp-875951-test \
--funcall py-end-of-block-test \
--funcall several-new-bugs-with-paragraph-filling-lp-1066489-test \
--funcall py-shell-invoking-python3-lp-835151-test \
--funcall py-shell-invoking-python2-lp-835151-test \
--funcall py-execute-line-python-test \
--funcall py-execute-line-python3-test \
--funcall py-execute-line-python2-test \
--funcall py-execute-expression-python-test \
--funcall abbrevs-changed-t-when-starting-lp-1270631-test \
--funcall py-empty-line-closes-p-lp-1235324-test \
--funcall infinite-loop-after-tqs-lp-826044-test \
--funcall beginning-of-block-fails-from-wrong-indent-test \
--funcall cascading-indent-lp-1101962-test \
--funcall Bogus-dedent-when-typing-colon-in-dictionary-literal-lp-1197171-test \
--funcall Parens-span-multiple-lines-lp-1191225-test \
--funcall indent-refused-lp-1191133-test \
--funcall return-key-is-broken-lp-1191158-test \
--funcall indentation-doesnt-honor-comment-on-preceding-lp-1190288-test \
--funcall incorrect-indentation-with-tertiary-lp-1189604-test \
--funcall py-end-of-statement-test-1 \
--funcall py-end-of-statement-test-2 \
--funcall nested-if-test-1 \
--funcall incorrect-indentation-of-comments-in-a-multiline-list-lp-1077063-test \
--funcall indentation-wrong-after-multi-line-parameter-list-lp-871698-test \
--funcall indent-after-inline-comment-lp-873372-test \
--funcall honor-comments-indent-test \
--funcall TAB-leaves-point-in-the-wrong-lp-1178453-test \
--funcall loops-on-if-else-lp-328777-test \
--funcall infinite-loop-on-lp-1156426-test \
--funcall line-after-colon-with-inline-comment-lp-1109946-test \
--funcall py-underscore-word-syntax-p-customization-has-no-effect-lp-1100947-test \
--funcall py-up-test-python-el-111-test \
--funcall py-down-python-el-112-test \
--funcall wrong-indentation-after-return-or-pass-keyword-lp-1087499-test \
--funcall wrong-indent-after-asignment-lp-1087404-test \
--funcall fill-paragraph-in-comments-results-in-mess-lp-1084769-test \
--funcall imenu-add-menubar-index-fails-lp-1084503-test \
--funcall spuriously-indents-whole-line-while-making-some-portion-inline-comment-lp-1080973-test \
--funcall fill-paragraph-in-a-comment-does-not-stop-at-empty-comment-lines-lp-1077139-test \
--funcall py-indent-after-assigment-test \
--funcall incorrect-indentation-of-one-line-functions-lp-1067633-test \
--funcall py-highlight-indentation-test \
--funcall py-smart-indentation-test \
--funcall exception-in-except-clause-highlighted-as-keyword-lp-909205-test \
--funcall pyindex-mishandles-class-definitions-lp-1018164-test \
--funcall py-guess-indent-offset-test \
--funcall py-end-of-block-or-clause-test \
--funcall mark-decorators-lp-328851-test \
--funcall py-expression-index-test \
--funcall py-guess-indent-offset-dont-detect-indent-of-2-lp-1027389-test \
--funcall py-narrow-to-defun-lp-1020531-test \
--funcall return-statement-indented-incorrectly-lp-1019601-test \
--funcall converts-tabs-to-spaces-in-indent-tabs-mode-t-lp-1019128-test \
--funcall empty-triple-quote-lp-1009318-test \
--funcall spurious-trailing-whitespace-lp-1008679-test \
--funcall shebang-interpreter-not-detected-lp-1001327-test \
--funcall new-problem-with-py-temp-directory-lp-965762-test \
--funcall new-problem-with-py-temp-directory-lp-965762-test \
--funcall dq-in-tqs-string-lp-328813-test \
--funcall py-current-defun-lp-328846-test \
--funcall flexible-indentation-lp-328842-test \
--funcall hungry-delete-backwards-lp-328853-test \
--funcall hungry-delete-forward-lp-328853-test \
--funcall bullet-lists-in-comments-lp-328782-test \
--funcall imenu-newline-arglist-lp-328783-test \
--funcall nested-indents-lp-328775-test \
--funcall imenu-matches-in-docstring-lp-436285-test \
--funcall exceptions-not-highlighted-lp-473525-test \
--funcall inbound-indentation-multiline-assignment-lp-629916-test \
--funcall indentation-of-continuation-lines-lp-691185-test \
--funcall class-treated-as-keyword-lp-709478-test \
--funcall backslashed-continuation-line-indent-lp-742993-test \
--funcall py-decorators-face-lp-744335-test \
--funcall indent-after-return-lp-745208-test \
--funcall keep-assignments-column-lp-748198-test \
--funcall multiline-listings-indent-lp-761946-test \
--funcall new-page-char-causes-loop-lp-762498-test \
--funcall nested-dicts-indent-lp-763756-test \
--funcall bad-indent-after-except-lp-771289-test \
--funcall indent-open-paren-not-last-lp-771291-test \
--funcall wrong-indent-after-else-lp-772610-test \
--funcall except-indents-wrong-lp-784432-test \
--funcall indent-explicitly-set-in-multiline-tqs-lp-784225-test \
--funcall unbalanced-parentheses-lp-784645-test \
--funcall explicitly-indent-in-list-lp-785018-test \
--funcall explicit-backslashed-continuation-line-indent-lp-785091-test \
--funcall indentation-error-lp-795773-test \
--funcall class-highlighted-as-keywords-lp-798287-test \
--funcall indent-function-arglist-lp-800088-test \
--funcall python-mode-hangs-lp-801780-test \
--funcall stops-backslashed-line-lp-802504-test \
--funcall stops-backslashed-line-lp-802504-test2 \
--funcall py-variable-name-face-lp-798538-test \
--funcall colon-causes-error-lp-818665-test \
--funcall if-indentation-lp-818720-test \
--funcall closing-parenthesis-indent-lp-821820-test \
--funcall py-indent-line-lp-822532-test \
--funcall indent-honor-arglist-whitespaces-lp-822540-test \
--funcall comments-indent-honor-setting-lp-824427-test \
--funcall closing-list-lp-826144-test \
--funcall wrong-indentation-of-function-arguments-lp-840891-test \
--funcall wrong-guess-for-py-indent-offset-lp-852052-test \
--funcall indent-match-import-pkg-lp-852500-test \
--funcall py-hungry-delete-backwards-needs-cc-lp-850595-test \
--funcall py-shift-line-when-no-region-lp-855565-test \
--funcall indentation-of-from-import-continuation-lines-lp-858041-test \
--funcall indentation-after-one-line-suites-lp-858044-test \
--funcall py-compute-indentation-wrong-at-eol-lp-858043-test \
--funcall comment-indentation-level-lp-869854-test \
--funcall no-indent-after-continue-lp-872676-test \
--funcall else-clause-indentation-lp-874470-test \
--funcall indent-after-multiple-except-statements-lp-883815-test \
--funcall wrongly-highlighted-as-keywords-lp-885144-test \
--funcall glitch-when-indenting-lists-lp-886473-test \
--funcall another-indentation-bug-inside-docstrings-lp-900684-test \
--funcall indentation-keyword-lp-885143-test \
--funcall fore-00007F-breaks-indentation-lp-328788-test \
--funcall indent-offset-not-guessed-when-loading-lp-902890-test \
--funcall from-__future__-import-absolute_import-mishighlighted-lp-907084-test \
--funcall chars-uU-preceding-triple-quoted-get-string-face-lp-909517-test \
--funcall py-pychecker-run-missing-lp-910783-test \
--funcall py-forward-into-nomenclature-lp-916818-test \
--funcall py-forward-into-nomenclature-jumps-over-CamelCased-words-lp-919540-test \
--funcall py-backward-into-nomenclature-caps-names-lp-919541-test \
--funcall fourth-level-blocks-indent-incorrectly-lp-939577-test \
--funcall py-mark-expression-marks-too-much-lp-941140-test \
--funcall py-indent-comments-nil-ignored-lp-958721-test \
--funcall tuple-unpacking-highlighted-incorrectly-lp-961496-test \
\
--funcall py-compute-indentation-test \
--funcall py-end-of-def-inline-comment-test \
--funcall before-inline-comment-test \
--funcall toggle-force-py-shell-name-p-test \
--funcall multiline-list-indent-test \
--funcall py-beginning-of-block-or-clause-test \
--funcall py-beginning-of-def-test \
--funcall py-beginning-of-def-or-class-test \
--funcall near-bob-beginning-of-statement-test \
--funcall first-line-offset-test \
--funcall assignment-indent-test \
--funcall if-elif-test \
--funcall if-elif-bob-test \
--funcall try-else-clause-test \
--funcall try-except-test \
--funcall assignment-after-block-test \
--funcall py-beginning-of-clause-test \
--funcall py-end-of-clause-test \
--funcall leave-dict-test \
--funcall eofs-attribut-test \
--funcall args-list-first-line-indent-test \
--funcall close-block-test \
--funcall py-shift-block-test \
--funcall nesting-if-test \
--funcall nested-try-test \
--funcall nested-if-test \
--funcall py-insert-super-python2-test \
--funcall py-smart-indent-eight-test \
--funcall py-insert-super-python2-test \
--funcall nested-try-finally-test \
--funcall py-separator-char-test \
--funcall python-dedicated-test \
\
--funcall py-electric-backspace-test \
--funcall py-insert-super-python3-test \
\
--funcall dict-error-test \
--funcall py-install-directory-path-test \
--funcall py-end-of-print-statement-test \
--funcall py-find-imports-lp-1023236-test \
--funcall py-beginning-of-expression-test \
--funcall py-end-of-expression-test \
--funcall py-partial-expression-test \
--funcall bob-beginning-of-statement-test \
--funcall py-beginning-of-block-test \
--funcall stalls-emacs-probably-due-to-syntax-highlighting-lp-1058261-test \
--funcall tqs-lp-302834-lp-1018994-test \
--funcall py-end-of-def-test \
--funcall py-end-of-def-or-class-test \
--funcall python-mode-slow-lp-803275-test \
--funcall beg-end-of-defun-lp-303622-test \
--funcall indent-region-lp-997958-test \
--funcall wrong-type-argument-lp-901541-test \
--funcall indentation-bug-inside-docstrings-lp-899455-test \
--funcall comments-start-a-new-line-lp-1092847-n1-test \
--funcall nested-dictionaries-indent-lp-328791-test \
--funcall tqs-list-error-test \
--funcall py-smart-operator-test \
--funcall python-mode-very-slow-lp-1107037-test \
--funcall module-docstring-when-following-comment-lp-1102011-test \
--funcall py-newline-and-indent-leaves-eol-whitespace-lp-1100892-test \
--funcall enter-key-does-not-indent-properly-after-return-statement-lp-1098793-test \
--funcall comments-start-a-new-line-lp-1092847-n2-test \
--funcall py-bol-moves-test \
--funcall from-within-py-shell-call-another-instance-lp-1169687-test \
--funcall indent-after-expect-lp-1387329-test \
--funcall py-indent-line-lp-1382799-test \
--funcall split-windows-on-execute-p-test \
--funcall py-shell-complete-test \
--funcall py-if-name-main-permission-lp-326620-test \
