;;; python-mode-test.el --- tests for Emacs python-mode.el

;; Copyright (C) 2011  Andreas Röhler

;; Author: Andreas Röhler <andreas.roehler@online.de>
;; Keywords: lisp, languages

;; This program is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation, either version 3 of the License, or
;; (at your option) any later version.

;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with this program.  If not, see <http://www.gnu.org/licenses/>.

;;; Commentary:

;; A couple of test cases for python-mode.el

;;; Code:
(require 'py-bug-numbered-tests)

(setq python-mode-interactive-tests
      (list
       'opening-brace-on-builtins-lp-1400951-test
       'more-docstring-filling-woes-lp-1102296-nil-test
       'more-docstring-filling-woes-lp-1102296-onetwo-test
       'more-docstring-filling-woes-lp-1102296-django-test
       'more-docstring-filling-woes-lp-1102296-symmetric-test
       'another-broken-font-locking-lp-961231-test
       'py-fill-string-django-test
       'py-fill-string-onetwo-test
       'py-fill-string-pep-257-test
       'py-fill-string-pep-257-nn-test
       'py-describe-symbol-fails-on-modules-lp-919719-test
       'cls-pseudo-keyword-lp-328849-test
       'py-execute-region-error-test
       'py-down-statement-test
       'docstring-style-switches-test
       'py-nested-block-or-clause-test
       'py-highlight-indentation-test
       'py-smart-indentation-test
       'autopair-mode-test
       'py-execute-block-python-test
       'py-execute-statement-error-test
       'py-shell-complete-test
       'py-shell-invoking-ipython-lp-835151-test
       'py-execute-def-ipython-test
       'py-execute-class-ipython-test
       'py-execute-expression-ipython-test
       'py-execute-block-ipython-test
       'py-execute-block-or-clause-ipython-test
       'py-execute-line-ipython-test
       'py-execute-buffer-ipython-switch-test
       'py-execute-region-ipython-test
       'py-execute-statement-ipython-test
       'ipython-complete-lp-1102226-test

       ))

(defun py-run-interactive-tests (&optional arg)
  "Run tests which would work from batch-mode maybe. "
  (interactive "p")
  (dolist (ele python-mode-interactive-tests)
    (funcall ele arg)))

(setq python-mode-tests
      (list
       'py-down-statement-test
       'docstring-style-switches-test
       'py-nested-block-or-clause-test
       'py-fill-string-django-test
       'py-fill-string-onetwo-test
       'py-fill-string-pep-257-test
       'py-fill-string-pep-257-nn-test
       ;;  fails for unknown reasons, interactive call works
       ;; 'py-fill-string-symmetric-test
       'py-highlight-indentation-test
       'py-smart-indentation-test
       'py-execute-partial-expression-python3-test
       'py-execute-partial-expression-python3-switch-test
       'py-execute-partial-expression-python3-noswitch-test
       'py-execute-partial-expression-python3-dedicated-test
       'py-execute-partial-expression-python3-dedicated-switch-test
       'py-execute-partial-expression-python2-test
       'py-execute-partial-expression-python2-switch-test
       'py-execute-partial-expression-python2-noswitch-test
       'py-execute-partial-expression-python2-dedicated-test
       'py-execute-partial-expression-python2-dedicated-switch-test
       'py-execute-partial-expression-python2.7-test
       'py-execute-partial-expression-python2.7-switch-test
       'py-execute-partial-expression-python2.7-noswitch-test
       'py-execute-partial-expression-python2.7-dedicated-test
       'py-execute-partial-expression-python2.7-dedicated-switch-test
       'py-execute-partial-expression-jython-test
       'py-execute-partial-expression-jython-switch-test
       'py-execute-partial-expression-jython-noswitch-test
       'py-execute-partial-expression-jython-dedicated-test
       'py-execute-partial-expression-jython-dedicated-switch-test
       'py-execute-line-python-test
       'py-execute-line-python-switch-test
       'py-execute-line-python-noswitch-test
       'py-execute-line-python-dedicated-test
       'py-execute-line-python-dedicated-switch-test
       'py-execute-line-ipython-test
       'py-execute-line-ipython-switch-test
       'py-execute-line-ipython-noswitch-test
       'py-execute-line-ipython-dedicated-test
       'py-execute-line-ipython-dedicated-switch-test
       'py-execute-line-python3-test
       'py-execute-line-python3-switch-test
       'py-execute-line-python3-noswitch-test
       'py-execute-line-python3-dedicated-test
       'py-execute-line-python3-dedicated-switch-test
       'py-execute-line-python2-test
       'py-execute-line-python2-switch-test
       'py-execute-line-python2-noswitch-test
       'py-execute-line-python2-dedicated-test
       'py-execute-line-python2-dedicated-switch-test
       'py-execute-line-python2.7-test
       'py-execute-line-python2.7-switch-test
       'py-execute-line-python2.7-noswitch-test
       'py-execute-line-python2.7-dedicated-test
       'py-execute-line-python2.7-dedicated-switch-test
       'py-execute-line-jython-test
       'py-execute-line-jython-switch-test
       'py-execute-line-jython-noswitch-test
       'py-execute-line-jython-dedicated-test
       'py-execute-line-jython-dedicated-switch-test
       'py-backward-block-test
       'py-forward-block-test
       'py-backward-block-or-clause-test
       'py-forward-block-or-clause-test
       'py-backward-def-test
       'py-forward-def-test
       'py-backward-def-or-class-test
       'py-forward-def-or-class-test
       'py-electric-backspace-test
       'py-electric-delete-test
       'dict-error-test
       ;;         'py-expand-abbrev-pst-pdb.set_trace-test
       'near-bob-backward-statement-test
       'bob-backward-statement-test
       'honor-comments-indent-test
       'assignment-indent-test
       'if-elif-test
       'if-elif-bob-test
       'try-else-clause-test
       'try-except-test
       'assignment-after-block-test
       'py-backward-clause-test
       'py-forward-clause-test
       'py-backward-expression-test
       'py-forward-expression-test
       'py-expression-index-test
       'py-indent-after-assigment-test
       'leave-dict-test
       'eofs-attribut-test
       'py-insert-super-python2-test
       'py-insert-super-python3-test
       'args-list-first-line-indent-test
       'py-partial-expression-test
       'py-execute-block-test
       'multiline-list-indent-test
       'close-block-test
       'py-shift-block-test
       'nesting-if-test
       'py-forward-print-statement-test
       'nested-try-test
       'nested-if-test
       'nested-try-finally-test
       'py-shell-complete-test
       'python-dedicated-test
       'tqs-list-error-test
       'py-mark-def-commandp-test
       'switch-windows-on-execute-p-test
       'py-install-directory-path-test
       'UnicodeEncodeError-python3-test
       'py-execute-block-python-test

       ))

(defun py-run-tests (&optional arg)
  (interactive "p")
  (dolist (ele python-mode-tests)
    (funcall ele arg)))

(defvar python-mode-teststring "class OrderedDict1(dict):
    \"\"\"
    This implementation of a dictionary keeps track of the order
    in which keys were inserted.
    \"\"\"

    def __init__(self, d={}):
        self._keys = d.keys()
        dict.__init__(self, d)

    def f():
        \"\"\"
        class for in 'for in while with blah'
        \"\"\"
        if a:

            ar_atpt_python_list_roh = ([
                'python-expression',

            # def ar_thingatpt_write_lists (&optional datei):
            'python-partial-expression',
            'python-statement',
            ])
        elif b:
            pass
        else b:
            pass

            ])

''' asdf' asdf asdf asdf asdf asdfasdf asdfasdf a asdf asdf asdf asdfasdfa asdf asdf asdf asdf asdf' asdf asdf asdf asdf asdfasdf asdfasdf a asdf asdf asdf asdfasdfa asdf asdf asdf asdf
'''
"
  "String used for tests by python-mode-test.el")

(setq python-mode-teststring "class OrderedDict1(dict):
    \"\"\"
    This implementation of a dictionary keeps track of the order
    in which keys were inserted.
    \"\"\"

    def __init__(self, d={}):
        self._keys = d.keys()
        dict.__init__(self, d)

    def f():
        \"\"\"
        class for in 'for in while with blah'
        \"\"\"
        if a:

            ar_atpt_python_list_roh = ([
                'python-expression',

            # def ar_thingatpt_write_lists (&optional datei):
            'python-partial-expression',
            'python-statement',
            ])
        elif b:
            pass
        else b:
            pass

''' asdf' asdf asdf asdf asdf asdfasdf asdfasdf a asdf asdf asdf asdfasdfa asdf asdf asdf asdf asdf' asdf asdf asdf asdf asdfasdf asdfasdf a asdf asdf asdf asdfasdfa asdf asdf asdf asdf
'''
")

(defun py-backward-block-test (&optional arg load-branch-function)
  (interactive "p")
  (let ((teststring python-mode-teststring))
    (py-bug-tests-intern 'py-backward-block-test-base arg teststring)))

(defun py-backward-block-test-base (arg)
  (goto-char 627)
  (py-backward-block)
  (assert (eq (point) 325) nil "py-backward-block-test failed"))

(defun py-forward-block-test (&optional arg load-branch-function)
  (interactive "p")
  (let ((teststring "class OrderedDict1(dict):
    \"\"\"
    This implementation of a dictionary keeps track of the order
    in which keys were inserted.
    \"\"\"

    def __init__(self, d={}):
        self._keys = d.keys()
        dict.__init__(self, d)

    def f():
        \"\"\"
        class for in 'for in while with blah'
        \"\"\"
        if foo:

            ar_atpt_python_list_roh = ([
                'python-expression',

            # def ar_thingatpt_write_lists (&optional datei):
            'python-partial-expression',
            'python-statement',
            ])

        elif bar:
            pass
        else:
            pass
 "))
    (py-bug-tests-intern 'py-forward-block-base arg teststring)))

(defun py-forward-block-base (arg)
  (goto-char 326)
  (assert (eq 562 (py-forward-clause)) nil "py-forward-block-test #1 failed")
  (assert (eq 598 (py-forward-clause)) nil "py-forward-block-test #2 failed")
  (assert (eq 629 (py-forward-block)) nil "py-forward-block-test #3 failed"))

(defun py-backward-block-or-clause-test (&optional arg load-branch-function)
  (interactive "p")
  (let ((teststring python-mode-teststring))
    (py-bug-tests-intern 'py-backward-block-or-clause-base arg teststring)))

(defun py-backward-block-or-clause-base (arg)
  (goto-char 627)
  (py-backward-block-or-clause)
  (assert (looking-at "else") nil "py-backward-block-or-clause-test failed")
  (py-backward-block-or-clause)
  (assert (looking-at "elif") nil "py-backward-block-or-clause-test failed")
  (py-backward-block-or-clause)
  (assert (looking-at "if") nil "py-backward-block-or-clause-test failed")

  )

(defun py-forward-block-or-clause-test (&optional arg load-branch-function)
  (interactive "p")
  (let ((teststring python-mode-teststring))
    (py-bug-tests-intern 'py-forward-block-or-clause-base arg teststring)))

(defun py-forward-block-or-clause-base (arg)
  (goto-char 602)
  (py-forward-block-or-clause)
  (assert (eq (point) 626) nil "py-forward-block-or-clause-test failed"))

(defun py-backward-def-test (&optional arg load-branch-function)
  (interactive "p")
  (let ((teststring python-mode-teststring))
    (py-bug-tests-intern 'py-backward-def-base arg teststring)))

(defun py-backward-def-base (arg)
  (goto-char 627)
  (py-backward-def)
  (assert (eq (point) 238) nil "py-backward-def-test failed")
  )

(defun py-forward-def-test (&optional arg load-branch-function)
  (interactive "p")
  (let ((teststring python-mode-teststring))
    (py-bug-tests-intern 'py-forward-def-base arg teststring)))

(defun py-forward-def-base (arg)
  (goto-char 627)
  (py-backward-def)
  (py-forward-def)
  (assert (eq (point) 626) nil "py-forward-def-test failed")
  )

(defun py-backward-def-or-class-test (&optional arg load-branch-function)
  (interactive "p")
  (let ((teststring python-mode-teststring))
    (py-bug-tests-intern 'py-backward-def-or-class-base arg teststring)))

(defun py-backward-def-or-class-base (arg)
  (goto-char 627)
  (py-backward-def-or-class 4)
  (assert (eq (point) 238) nil "py-backward-def-or-class-test failed"))

(defun py-forward-def-or-class-test (&optional arg load-branch-function)
  (interactive "p")
  (let ((teststring python-mode-teststring))
    (py-bug-tests-intern 'py-forward-def-or-class-base arg teststring)))

(defun py-forward-def-or-class-base (arg)
  (goto-char 627)
  (assert (eq 238 (py-backward-def-or-class)) nil "py-forward-def-or-class-test #1 failed")
  (assert (eq 146 (py-backward-def-or-class)) nil "py-forward-def-or-class-test #2 failed")
  (goto-char 201)
  (assert (eq 232 (py-forward-def-or-class)) nil "py-forward-def-or-class-test #3 failed")
  (assert (eq 626 (py-forward-def-or-class '(4))) nil "py-forward-def-or-class-test #4 failed"))

(defun py-electric-backspace-test (&optional arg load-branch-function)
  (interactive "p")
  (let ((teststring python-mode-teststring))
    (py-bug-tests-intern 'py-electric-backspace-base arg teststring)))

(defun py-electric-backspace-base (arg)
  (goto-char 232)
  (py-newline-and-indent)
  ;; (sit-for 0.1)
  (assert (eq 241 (point)) nil "py-electric-backspace-test #1 failed")
  (py-electric-backspace)
  (assert (eq 4 (current-column)) nil "py-electric-backspace-test #2 failed")
  (py-electric-backspace)
  (assert (eq 0 (current-column)) nil "py-electric-backspace-test #3 failed")
  (py-electric-backspace)
  (assert (eq 232 (point)) nil "py-electric-backspace-test #4 failed"))

(defun py-electric-delete-test (&optional arg load-branch-function)
  (interactive "p")
  (let ((teststring python-mode-teststring))
    (py-bug-tests-intern 'py-electric-delete-base arg teststring)))

(defun py-electric-delete-base (arg)
  (when py-debug-p (switch-to-buffer (current-buffer))
	(font-lock-fontify-buffer))
  (goto-char 202)
  (py-electric-delete)
  (assert (eq 4 (length (progn (looking-at "[ \t]+")(match-string-no-properties 0)))) nil "py-electric-delete-test #1 failed")
  (py-electric-delete)
  (assert (not (looking-at "[ \t]+")) nil "py-electric-delete-test #2 failed")
  (py-electric-delete)
  (assert (looking-at "ict") nil "py-electric-delete-test #2 failed"))

(defun UnicodeEncodeError-python3-test (&optional arg load-branch-function)
  (interactive "p")
  (let ((teststring (concat "#! /usr/bin/env python3
# -\*- coding: utf-8 -\*-\n
print(\'\\xA9\')
")))
    (py-bug-tests-intern 'UnicodeEncodeError-python3-base arg teststring)))

(defun UnicodeEncodeError-python3-base (&optional arg)
  (py-execute-region 50 63)
  (set-buffer "*Python3*")
  ;; (sit-for 1 t)
  ;; (switch-to-buffer (current-buffer))
  (if comint-last-output-start
      (goto-char comint-last-output-start)
    (message "UnicodeEncodeError-python3-test: %s" "Dont see comint-last-output-start"))
  (assert (or (eq (char-after) ?\©)(eq (char-before) ?\©)) nil "UnicodeEncodeError-python3-test failed"))

(defun dict-error-test (&optional arg load-branch-function)
  (interactive "p")
  (let ((teststring (concat py-test-shebang "
 # -*- coding: utf-8 -*-

class foo(bar):
	\"\"\"baz\"\"\"
       	_some_extensions = {

		'38': 'asd', #  whatever
		'43': 'ddd',
		'45': 'ddd',
	}
")))
    (py-bug-tests-intern 'dict-error-base arg teststring)))

(defun dict-error-base (arg)
  (goto-char 78)
  (assert (eq 166 (py-forward-statement)) nil "dict-error-test failed"))

(defun py-expand-abbrev-pst-pdb.set_trace-test (&optional arg load-branch-function)
  (interactive "p")
  (let ((teststring (concat py-test-shebang "
# -*- coding: utf-8 -*-
print('\xA9')
pst
")))
    (py-bug-tests-intern 'py-expand-abbrev-pst-pdb.set_trace-base arg teststring)))

(defun py-expand-abbrev-pst-pdb.set_trace-base (arg)
  (forward-char -1)
  (expand-abbrev)
  ;; (sit-for 1)
  ;;  (assert (string= (expand-abbrev) "pst") nil "py-expand-abbrev-pst-pdb.set_trace-test failed"))
  ;; (assert (expand-abbrev) nil "py-expand-abbrev-pst-pdb.set_trace-test failed"))
  (progn (looking-back "pdb.set_trace()")
         ;; (message "Looking back: %s" (match-string-no-properties 0))
         )
  (assert (looking-back "pdb.set_trace()")
          ;;          (message "%s" (match-string-no-properties 1))
          nil "py-expand-abbrev-pst-pdb.set_trace-test failed"))

(defun near-bob-backward-statement-test (&optional arg load-branch-function)
  (interactive "p")
  (let ((teststring (concat py-test-shebang "
 # -*- coding: utf-8 -*-

print u'\xA9'
")))
    (py-bug-tests-intern 'near-bob-backward-statement-base arg teststring)))

(defun near-bob-backward-statement-base (arg)
  (goto-char 50)
  (assert (eq 0 (py-compute-indentation)) nil "near-bob-backward-statement-test failed"))

(defun bob-backward-statement-test (&optional arg load-branch-function)
  (interactive "p")
  (let ((teststring "    #Foo.py
"))
    (py-bug-tests-intern 'bob-backward-statement-base arg teststring)))

(defun bob-backward-statement-base (arg)
  (py-backward-statement)
  (assert (eq 1 (point))  "bob-backward-statement-test failed"))

(defun honor-comments-indent-test (&optional arg load-branch-function)
  (interactive "p")
  (let ((teststring "    #Something.py
    # The purpose of this program is uncertain.
"))
    (py-bug-tests-intern 'honor-comments-indent-base arg teststring)))

(defun honor-comments-indent-base (arg)
  (goto-char 19)
  (assert (eq 4 (py-compute-indentation)) nil "honor-comments-indent-test failed"))

(defun first-line-offset-test (&optional arg load-branch-function)
  (interactive "p")
  (let ((teststring "    #Something.py
    # The purpose of this program is uncertain.
"))
    (py-bug-tests-intern 'first-line-offset-base arg teststring)))

(defun first-line-offset-base (arg)
  (goto-char 18)
  (assert (eq 4 (py-compute-indentation)) nil "first-line-offset-test failed"))

(defun assignment-indent-test (&optional arg load-branch-function)
  (interactive "p")
  (let ((teststring "def foo():
sammlung = []
"))
    (py-bug-tests-intern 'assignment-indent-base arg teststring)))

(defun assignment-indent-base (arg)
  (goto-char 12)
  (assert (eq 4 (py-compute-indentation)) nil "assignment-indent-test failed"))

(defun if-elif-test (&optional arg load-branch-function)
  (interactive "p")
  (let ((teststring "if bar in baz:
    print \"0, baz\"
    abc[1] = \"x\"

elif barr in bazz:
    print \"\"
"))
    (py-bug-tests-intern 'if-elif-base arg teststring)))

(defun if-elif-base (arg)
  (goto-char 76)
  (assert (eq 4 (py-compute-indentation)) nil "if-elif.py-test failed"))

(defun if-elif-bob-test (&optional arg load-branch-function)
  (interactive "p")
  (let ((teststring "if bar in baz:
    print \"0, baz\"
"))
    (py-bug-tests-intern 'if-elif-bob-base arg teststring)))

(defun if-elif-bob-base (arg)
  (goto-char (point-min))
  (assert (eq 0 (py-compute-indentation)) nil "if-elif-bob.py-test failed"))

(defun try-else-clause-test (&optional arg load-branch-function)
  (interactive "p")
  (let ((teststring "
# an example from http://www.thomas-guettler.de
# © 2002-2008 Thomas Güttler. Der Text darf nach belieben kopiert und modifiziert werden, solange dieser Hinweis zum Copyright und ein Links zu dem Original unter www.thomas-guettler.de erhalten bleibt. Es wäre nett, wenn Sie mir Verbesserungsvorschläge mitteilen: guettli@thomas-guettler.de

def _commit_on_success(*args, **kw):
    begin()
    try:
        res = func(*args, **kw)
    except Exception, e:
        rollback()
        raise # Re-raise (aufgefangene Exception erneut werfen)
    else:
        commit()
    return res
"))
    (py-bug-tests-intern 'try-else-clause-base arg teststring)))

(defun try-else-clause-base (arg)
  (goto-char 541)
  (assert (eq 4 (py-compute-indentation)) nil "try-else-clause-test failed"))

(defun try-except-test (&optional arg load-branch-function)
  (interactive "p")
  (let ((teststring "
# an example from http://www.thomas-guettler.de
# © 2002-2008 Thomas Güttler. Der Text darf nach belieben kopiert und modifiziert werden, solange dieser Hinweis zum Copyright und ein Links zu dem Original unter www.thomas-guettler.de erhalten bleibt. Es wäre nett, wenn Sie mir Verbesserungsvorschläge mitteilen: guettli@thomas-guettler.de

def _commit_on_success(*args, **kw):
    begin()
    try:
        res = func(*args, **kw)
    except Exception, e:
        rollback()
        raise # Re-raise (aufgefangene Exception erneut werfen)
    else:
        commit()
    return res
"))
    (py-bug-tests-intern 'try-except-base arg teststring)))

(defun try-except-base (arg)
  (goto-char 434)
  (assert (eq 4 (py-compute-indentation)) nil "try-except-test failed"))

(defun assignment-after-block-test (&optional arg load-branch-function)
  (interactive "p")
  (let ((teststring "
if x > 0:
    for i in range(100):
        print i
    else:
    print \"All done\"

a = \"asdf\"
b = \"asdf\"
"))
    (py-bug-tests-intern 'assignment-after-block-base arg teststring)))

(defun assignment-after-block-base (arg)
  (forward-line -1)
  (assert (eq 0 (py-compute-indentation)) nil "assignment-after-block-test failed"))

(defun py-backward-clause-test (&optional arg load-branch-function)
  (interactive "p")
  (let ((teststring "# Examples from http://diveintopython.org/

def main(argv):
    grammar = \"kant.xml\"
    try:
        opts, args = getopt.getopt(argv, \"hg:d\", [\"help\", \"grammar=\"])
    except getopt.GetoptError:
        usage()
        sys.exit(2)
    for opt, arg in opts:
        if opt in (\"-h\", \"--help\"):
            usage()
            sys.exit()
        elif opt == '-d':
            global _debug
            _debug = 1
        elif opt in (\"-g\", \"--grammar\"):
            grammar = arg
"))
    (py-bug-tests-intern 'py-backward-clause-base arg teststring)))

(defun py-backward-clause-base (arg)
  (goto-char 364)
  (assert (eq 346 (py-backward-clause)) "py-backward-clause-test failed"))

(defun py-forward-clause-test (&optional arg load-branch-function)
  (interactive "p")
  (let ((teststring "# Examples from http://diveintopython.org/

def main(argv):
    grammar = \"kant.xml\"
    try:
        opts, args = getopt.getopt(argv, \"hg:d\", [\"help\", \"grammar=\"])
    except getopt.GetoptError:
        usage()
        sys.exit(2)
    for opt, arg in opts:
        if opt in (\"-h\", \"--help\"):
            usage()
            sys.exit()
        elif opt == '-d':
            global _debug
            _debug = 1
        elif opt in (\"-g\", \"--grammar\"):
            grammar = arg
"))
    (py-bug-tests-intern 'py-forward-clause-base arg teststring)))

(defun py-forward-clause-base (arg)
  (goto-char 364)
  (assert (eq 412 (py-forward-clause)) "py-forward-clause-test failed"))

(defun py-backward-expression-test (&optional arg load-branch-function)
  (interactive "p")
  (let ((teststring "# Examples from http://diveintopython.org/

def main(argv):
    grammar = \"kant.xml\"
    try:
        opts, args = getopt.getopt(argv, \"hg:d\", [\"help\", \"grammar=\"])
    except getopt.GetoptError:
        usage()
        sys.exit(2)
"))
    (py-bug-tests-intern 'py-backward-expression-base arg teststring)))

(defun py-backward-expression-base (arg)
  (goto-char 227)
  (assert (eq 221 (py-backward-expression)) nil "py-backward-expression-test #1 failed")
  (assert (eq 205 (py-backward-expression)) nil "py-backward-expression-test #2 failed")
  (assert (eq 177 (py-backward-expression)) nil "py-backward-expression-test #3 failed")
  (assert (eq 170 (py-backward-expression)) nil "py-backward-expression-test #4 failed")
  (assert (eq 116 (py-backward-expression)) nil "py-backward-expression-test #5 failed")
  (assert (eq 103 (py-backward-expression)) nil "py-backward-expression-test #6 failed")
  (assert (eq 90 (py-backward-expression)) nil "py-backward-expression-test #7 failed")
  (assert (eq 75 (py-backward-expression)) nil "py-backward-expression-test #8 failed")
  (assert (eq 65 (py-backward-expression)) nil "py-backward-expression-test #9 failed")
  (assert (eq 49 (py-backward-expression)) nil "py-backward-expression-test #10 failed")
  (assert (eq 45 (py-backward-expression)) nil "py-backward-expression-test #11 failed"))

(defun py-forward-expression-test (&optional arg load-branch-function)
  (interactive "p")
  (let ((teststring "# Examples from http://diveintopython.org/

def main(argv):
    grammar = \"kant.xml\"
    try:
        opts, args = getopt.getopt(argv, \"hg:d\", [\"help\", \"grammar=\"])
    except getopt.GetoptError:
        usage()
        sys.exit(2)
"))
    (py-bug-tests-intern 'py-forward-expression-base arg teststring)))

(defun py-forward-expression-base (arg)
  (goto-char 49)
  (assert (eq 60 (py-forward-expression)) nil "py-forward-expression-test #1 failed")
  (assert (eq 72 (py-forward-expression)) nil "py-forward-expression-test #2 failed)")
  (assert (eq 85 (py-forward-expression)) nil "py-forward-expression-test #3 failed)")
  (assert (eq 94 (py-forward-expression)) nil "py-forward-expression-test #4 failed)")
  (assert (eq 113 (py-forward-expression)) nil "py-forward-expression-test #5 failed)")
  (assert (eq 165 (py-forward-expression)) nil "py-forward-expression-test #6 failed)")
  (assert (eq 176 (py-forward-expression)) nil "py-forward-expression-test #7 failed)")
  (assert (eq 196 (py-forward-expression)) nil "py-forward-expression-test #8 failed)")
  (assert (eq 212 (py-forward-expression)) nil "py-forward-expression-test #9 failed)")
  (assert (eq 232 (py-forward-expression)) nil "py-forward-expression-test #10 failed)"))

(defun py-expression-index-test (&optional arg load-branch-function)
  (interactive "p")
  (let ((teststring (concat py-test-shebang "
 # -\*- coding: utf-8 -\*-
b = a[0].split(':')[1]
")))
    (py-bug-tests-intern 'py-expression-index-base arg teststring)))

(defun py-expression-index-base (arg)
  (goto-char 58)
  (assert (eq 71 (py-forward-expression)) nil "py-expression-index-test failed")
)

(defun py-insert-super-python2-test (&optional arg load-branch-function)
  (interactive "p")
  (let ((teststring (concat py-test-shebang "
# -\*- coding: utf-8 -\*-
# As example given in Python v3.1 documentation » The Python Standard Library »
#
# class C(B):
#     def method(self, arg):
#         super().method(arg) # This does the same thing as:
#                                # super(C, self).method(arg)\"

class OrderedDict1(dict):
    \"\"\"
    This implementation of a dictionary keeps track of the order
    in which keys were inserted.
    \"\"\"

    def __init__(self, d={}):
        self._keys = d.keys()
        dict.__init__(self, d)
        ")))
    (py-bug-tests-intern 'py-insert-super-python2-base arg teststring)))

(defun py-insert-super-python2-base (arg)
  (ignore-errors (py-insert-super))
  ;; (sit-for 0.1)
  (assert (looking-back "super(OrderedDict1, self).__init__(d={})") nil "py-insert-super-python2-test failed"))

(defun py-insert-super-python3-test (&optional arg load-branch-function)
  (interactive "p")
  (let* ((py-test-shebang "#! /usr/bin/env python3")
         (teststring (concat py-test-shebang "
# -\*- coding: utf-8 -\*-
# As example given in Python v3.1 documentation » The Python Standard Library »
#
# class C(B):
#     def method(self, arg):
#         super().method(arg) # This does the same thing as:
#                                # super(C, self).method(arg)\"

class OrderedDict1(dict):
    \"\"\"
    This implementation of a dictionary keeps track of the order
    in which keys were inserted.
    \"\"\"

    def __init__(self, d={}):
        self._keys = d.keys()
        dict.__init__(self, d)
        ")))
    (py-bug-tests-intern 'py-insert-super-python3-base arg teststring)))

(defun py-insert-super-python3-base (arg)
  (save-excursion
    (py-insert-super))
  ;; (sit-for 0.2)
  (assert (looking-at "super().__init__(d={})") nil "py-insert-super-python3-test failed"))

(defun py-indent-after-assigment-test (&optional arg load-branch-function)
  (interactive "p")
  (let ((teststring (concat py-test-shebang "
# -*- coding: utf-8 -*-

#####################################
def foo( self, bar=False ):  # version 12345
    title = self.barz.attrs['file'].split('.')[ -1 ]
    if asdf:
")))
    (py-bug-tests-intern 'indent-after-assigment-base arg teststring)))

(defun indent-after-assigment-base (arg)
  (goto-char 185)
  (assert (eq 4 (py-compute-indentation)) nil "py-indent-after-assigment-test failed"))

(defun leave-dict-test (&optional arg load-branch-function)
  (interactive "p")
  (let ((teststring "
foo = {
    b\"yyyyt\": \"bxxk\",
    \"bxxk\": { \"yyer\": [\"wxrddef\", \"yytem\", \"hym\",],
              \"wfter\": [], \"xbject\": BxxkTwg, },
    \"yytem\": { \"yyer\": [], \"wfter\": [\"yytem\"], \"xbject\": ItemTwg, },
    \"hym\": { \"yyer\": [], \"wfter\": [\"hym\"], \"xbject\": ItemTwg, },
    \"yyfx\": { \"yyer\": [], \"wfter\": [\"yytem\", \"hym\"], \"xbject\": IfxTwg, },
    \"wxrddef\": { \"yyer\": [], \"wfter\": [\"yyfx\", \"yytem\", \"hym\"], \"xbject\": WxrddefTwg, },
}
"))
    (py-bug-tests-intern 'leave-dict-base arg teststring)))

(defun leave-dict-base (arg)
  (when py-debug-p (switch-to-buffer (current-buffer))
	(font-lock-fontify-buffer))
  (goto-char (point-min))
  (py-forward-statement)
  (assert (eq 431 (point)) nil "leave-dict-test failed"))

(defun eofs-attribut-test (&optional arg load-branch-function)
  (interactive "p")
  (let ((teststring "def foo( baz ):  # version
    return baz.replace(\"\+\",\"§\").replace(\"_\", \" \").replace(\"ﬁ\",\"fr\").replace(
        \"ﬂ\", \"fg\").replace(\"--\", \"ü\")
"))
    (py-bug-tests-intern 'eofs-attribut-base arg teststring)))

(defun eofs-attribut-base (arg)
  (forward-line -2)
  (assert (eq 142 (py-forward-statement))  nil "eofs-attribut-test failed"))

(defun args-list-first-line-indent-test (&optional arg load-branch-function)
  (interactive "p")
  (let ((teststring (concat py-test-shebang "
# -*- coding: utf-8 -*-

if foo:
    bar.append(
        ht(
            T.a('Sorted Foo', href='#Blub', ),
            ' -- foo bar baz--',
            self.Tasdf( afsd ),
            self.Tasdf( asdf ),
            )
    )
")))
    (py-bug-tests-intern 'args-list-first-line-indent-base arg teststring)))

(defun args-list-first-line-indent-base (arg)
  (goto-char 72)
  (assert (eq 4 (py-compute-indentation)) nil "args-list-first-line-indent-test failed"))

(defun py-partial-expression-test (&optional arg load-branch-function)
  (interactive "p")
  (let ((teststring (concat py-test-shebang "
# -*- coding: utf-8 -*-

if foo:
    bar.append(
        ht(
            T.a('Sorted Foo', href='#Blub', ),
            ' -- foo bar baz--',
            self.Tasdf( afsd ),
            self.Tasdf( asdf ),
            )
        )
")))
    (py-bug-tests-intern 'py-partial-expression-base arg teststring)))

(defun py-partial-expression-base (arg)
  (goto-char 104)
  (assert (eq 102 (py-backward-partial-expression)) nil "py-partial-expression-test #1 failed")
  (assert (eq 108 (py-forward-partial-expression)) nil "py-partial-expression-test #2 failed")
  (goto-char 178)
  (assert (eq 177 (py-backward-partial-expression)) nil "py-partial-expression-test #3 failed")
  (assert (eq 195 (py-forward-partial-expression)) nil "py-partial-expression-test #3 failed")
  )

(defun multiline-list-indent-test (&optional arg load-branch-function)
  (interactive "p")
  (let ((teststring "print [1, 2,
    3, 4]"))
    (py-bug-tests-intern 'multiline-list-indent-base arg teststring)))

(defun multiline-list-indent-base (arg)
  (assert (eq 7 (py-compute-indentation)) nil "multiline-list-indent-test failed"))

(defun no-switch-no-split-test (&optional arg load-branch-function)
  (interactive "p")
  (let ((teststring (concat py-test-shebang "
# -*- coding: utf-8 -*-

print u'\\xA9'
")))
    (py-bug-tests-intern 'no-switch-no-split-base arg teststring)))

(defun no-switch-no-split-base (arg)
  (let ((oldbuf (current-buffer))
        py-split-windows-on-execute py-switch-buffers-on-execute-p)
    (goto-char 49)
    (push-mark)
    (end-of-line)
    (py-execute-region (line-beginning-position) (point))
    (assert (window-full-height-p) "no-switch-no-split-test failed")
    (assert (eq (current-buffer) oldbuf))))


(defun py-shift-block-test (&optional arg load-branch-function)
  (interactive "p")
  (let ((teststring (concat py-test-shebang "
# -*- coding: utf-8 -*-

class OrderedDict1(dict):
    \"\"\"
    This implementation of a dictionary keeps track of the order
    in which keys were inserted.
    \"\"\"

    def __init__(self, d={}):
        self._keys = d.keys()
        dict.__init__(self, d)
         ")))
    (py-bug-tests-intern 'py-shift-block-base arg teststring)))

(defun py-shift-block-base (arg)
  (let (py-smart-indentation)
    (goto-char 237)
    (assert (eq 12 (py-shift-block-right)) nil "py-shift-block-test #1 failed")
    (assert (eq 8 (py-shift-block-left)) nil "py-shift-block-test #1 failed")))

(defun nesting-if-test (&optional arg load-branch-function)
  (interactive "p")
  (let ((teststring (concat py-test-shebang "
# -*- coding: utf-8 -*-

if foo:
    if bar:
        pass
    else:
        pass
else:
    pass

")))
    (py-bug-tests-intern 'nesting-if-test-base arg teststring)))

(defun nesting-if-test-base (arg)
  (goto-char 105)
  (assert (eq 0 (py-compute-indentation)) nil "nesting-if-test failed"))

(defun py-forward-print-statement-test (&optional arg load-branch-function)
  (interactive "p")
  (let ((teststring (concat py-test-shebang "
# -*- coding: utf-8 -*-

def usage():
    print \"\"\"Error: %s
somme errors
\"\"\" % (
          os.path.basename(sys.argv[0]))

def usage():
    print '''Error: %s
somme errors
''' % (
          os.path.basename(sys.argv[0]))

")))
    (py-bug-tests-intern 'py-forward-print-statement-base arg teststring)))

(defun py-forward-print-statement-base (arg)
  (when py-debug-p (switch-to-buffer (current-buffer))
	(font-lock-fontify-buffer))
  (goto-char 66)
  ;; (sit-for 0.1)
  (assert (eq 146 (py-forward-statement)) nil "py-forward-print-statement-test #1 failed")

  (assert (eq 160 (py-forward-statement)) nil "py-forward-print-statement-test #2 failed")

  (assert (eq 245 (py-forward-statement)) nil "py-forward-print-statement-test #3 failed")

  )

(defun nested-try-test (&optional arg load-branch-function)
  (interactive "p")
  (let ((teststring (concat py-test-shebang "
# -*- coding: utf-8 -*-

def main(argv):
    grammar = \"foo.xml\"
    try:
        opts, args = getopt.getopt(argv, \"hg:d\", [\"help\", \"grammar=\"])
    except getopt.GetoptError:
        usage()
        try:
            bla
        except getopt.GetoptError:
            asdf()
        finally:
            return \"blub\"
    finally:
        print \"asdf\"

")))
    (py-bug-tests-intern 'nested-try-base arg teststring)))

(defun nested-try-base (arg)
  (goto-char 306)
  (assert (eq 8 (py-compute-indentation)) nil "nested-try-test failed"))

(defun nested-if-test-1 (&optional arg load-branch-function)
  (interactive "p")
  (let ((teststring (concat py-test-shebang "
# -*- coding: utf-8 -*-

if abr:
    if x > 0:
        if foo:
            print \"foo\"
        elif bar:
            print \"abasdf\"
        elif baz:
            for i in range(100):
                print i
            else:
                print \\\"All done\\\"
    elif x < 0:
        print \\\"x is negative\\\"
else:
    print \"asbd\"

")))
    (py-bug-tests-intern 'nested-if-base-1 arg teststring)))

(defun nested-if-base-1 ()
  (goto-char 299)
  (assert (eq 8 (py-compute-indentation)) nil "nested-if-test-1 failed"))

(defun nested-try-finally-test (&optional arg load-branch-function)
  (interactive "p")
  (let ((teststring (concat py-test-shebang "
# -*- coding: utf-8 -*-

# Example from:
# To: python-ideas@python.org
# From: Nikolaus Rath <Nikolaus@rath.org>
# Date: Tue, 18 Oct 2011 22:14:56 -0400
# Message-ID: <87pqhtafrz.fsf@vostro.rath.org>

def my_fun():
    allocate_res1()
    try:
        # do stuff
        allocate_res2()
        try:
            # do stuff
            allocate_res3()
            try:
                do stuff
            finally:
                cleanup_res3()
        finally:
            cleanup_res2()
    finally:
        cleanup_res1()

    return

")))
    (py-bug-tests-intern 'nested-try-finally-base arg teststring)))

(defun nested-try-finally-base (arg)
  (goto-char 431)
  (assert (eq 12 (py-compute-indentation)) nil "nested-try-finally-test failed"))

(defun tqs-list-error-test (&optional arg load-branch-function)
  (interactive "p")
  (let ((teststring (concat py-test-shebang "
# -*- coding: utf-8 -*-
class foo(bar, baz):
    \"\"\"
    foo is an ABC for matrix containers; i.e.,
    \\\"\\\"\\\"containers of a finite number of orig
\"\"\"
    pass
")))
    (py-bug-tests-intern 'tqs-list-error-base 2 teststring)))

(defun tqs-list-error-base (arg)
  (goto-char 90)
  (assert (eq 175   (py-forward-statement)) nil "tqs-list-error-test failed"))

(defun py-smart-indent-eight-test (&optional arg load-branch-function)
  (interactive "p")
  (let ((py-smart-indentation t)
        (teststring (concat py-test-shebang "
# -*- coding: utf-8 -*-
for x in y:
    for z in l:
        for r in t:
        pass
                # <--- indents here. Pressing <backspace> dedents eight spaces (i.e. you can go to column 0 in two presess)
")))
    (py-bug-tests-intern 'py-smart-indent-eight-base arg teststring)))

(defun py-smart-indent-eight-base (arg)
  (goto-char 104)
  (assert (eq 4 (py-guess-indent-offset)) nil "py-smart-indent-eight-test #1 failed")
  (assert (eq 12 (py-compute-indentation)) nil "py-smart-indent-eight-test #2 failed")
)

(defun py-install-directory-path-test (&optional arg)
  (interactive "p")
  (let ((teststring (concat py-test-shebang "
# -*- coding: utf-8 -*-
")))
    (py-bug-tests-intern 'py-install-directory-path-base arg teststring)))

(defun py-install-directory-path-base (arg)
  "See if `py-install-directory' is set when required. "
  (assert (py-install-directory-check) nil "`py-install-directory' not valid. See INSTALL. "))

;;;
(defun switch-windows-on-execute-p-test (&optional arg load-branch-function)
  (interactive "p")
  (let ((teststring (concat py-test-shebang "
# -*- coding: utf-8 -*-
print(\"I'm the switch-windows-on-execute-p-test\")
")))
    (py-bug-tests-intern 'switch-windows-on-execute-p-base arg teststring)))

(defun switch-windows-on-execute-p-base (arg)
  (let ((py-switch-buffers-on-execute-p t)
        (erg (buffer-name)))
    (py-execute-buffer)
    ;; (sit-for 0.1)
    (when py-debug-p (message "current-buffer: %s" (current-buffer)))
    (assert
     (string-match "*Python*" (buffer-name (current-buffer)))
     nil "switch-windows-on-execute-p-test failed")))

;; this test is not valable, as python-mode-map often changes
(defun py-menu-pyshell-test (&optional arg load-branch-function)
  (interactive "p")
  (let ((teststring (concat py-test-shebang "
# -*- coding: utf-8 -*-
print(\"I'm the `py-menu-pyshell-test'\")
")))
    (py-bug-tests-intern 'py-menu-pyshell-base arg teststring)))

(defun py-menu-pyshell-base (arg)
  (assert (string= "PyShell" (prin1-to-string
                              (car (nth 1 (cdr (nth 17 python-mode-map))))
                              ;; (car (nth 2 (nth 1 (cdr python-mode-map))))
                              )) nil "py-menu-pyshell-test failed"))

(defun python-dedicated-test (&optional arg load-branch-function)
  (interactive "p")
  (let ((teststring ""))
    (py-bug-tests-intern 'python-dedicated-base arg teststring)))

(defun python-dedicated-base (arg)
  (set-buffer (python-dedicated))
  ;; (sit-for 0.1)
  (assert (string-match "^\*Python[0-9.]*-[:alnum:]+*" (buffer-name)) nil "python-dedicated-test failed"))

(defun py-separator-char-test (&optional arg load-branch-function)
  (interactive "p")
  (let ((teststring ""))
    (py-bug-tests-intern 'py-separator-char-base arg teststring)))

(defun py-separator-char-base (arg)
  (assert (stringp (py-separator-char)) nil "py-separator-char-test failed"))

(defun toggle-force-py-shell-name-p-test (&optional arg)
  (interactive "p")
  (let ((teststring ""))
    (py-bug-tests-intern 'toggle-force-py-shell-name-p-base arg teststring)))

(defun toggle-force-py-shell-name-p-base (arg)
  (let ((old py-force-py-shell-name-p))
    (assert (not (eq old (toggle-force-py-shell-name-p))) nil "toggle-force-py-shell-name-p-test failed")
    (setq py-force-py-shell-name-p old)))

(defun before-inline-comment-test (&optional arg)
  (interactive "p")
  (let ((teststring "#! /usr/bin/env python
# -*- coding: utf-8 -*-
self._blah_blup = 0xe000 # aka: foo bar baz
self.nult = {}
self.nult['_foobar'] = []
"))
    (py-bug-tests-intern 'before-inline-comment-base arg teststring)))

(defun before-inline-comment-base (arg)
  (goto-char 72)
  (py-forward-statement)
  ;; (sit-for 0.1)
  (assert (eq 106 (point)) nil "before-inline-comment-test failed"))

(defun py-forward-def-inline-comment-test (&optional arg)
  (interactive "p")
  (let ((teststring "#! /usr/bin/env python
# -*- coding: utf-8 -*-

    #####################################
#####################################
def fooBaz( bar ):  # version 2003/9/7
  if \"Foo:\" == bar \\
          or  \"[Foo:]\" == bar \\
          or \"Foo:]\" == bar \\
          or \"Baz:\" == bar:
      return False
  return True
"))
    (py-bug-tests-intern 'py-forward-def-inline-comment-base arg teststring)))

(defun py-forward-def-inline-comment-base (arg)
  (let ((py-smart-indentation t))
    (goto-char 49)
    (py-forward-def-or-class)
    (assert (eq 311 (point)) nil "py-forward-def-inline-comment-test failed")))

(defun py-compute-indentation-test (&optional arg)
  (interactive "p")
  (let ((teststring "#! /usr/bin/env python
# -\*- coding: utf-8 -\*-
with file(\"foo\" + zeit + \".ending\", 'w') as datei:
    for i in range(anzahl):
        bar.dosomething()
        datei.write(str(baz[i]) + \"\\n\")

def foo()
"))
    (py-bug-tests-intern 'py-compute-indentation-base arg teststring)))

(defun py-compute-indentation-base (arg)
  (goto-char 99)
  (assert (eq 4 (py-compute-indentation)) nil "py-compute-indentation-test #1 failed")
  (goto-char 127)
  (assert (eq 8 (py-compute-indentation)) nil "py-compute-indentation-test #2 failed"))

(defun py-forward-statement-test-1 (&optional arg)
  (interactive "p")
  (let ((teststring "#! /usr/bin/python
# -*- coding: utf-8 -*-
print dir()
c = Cat()
c.hello() #causes error, but emacs tracking fails
import sys, os; os.remove('do/something/nasty') # lp:1025000
"))
    (py-bug-tests-intern 'py-forward-statement-1-base arg teststring)))

(defun py-forward-statement-1-base (arg)
  (when py-debug-p (switch-to-buffer (current-buffer))
	(font-lock-fontify-buffer))
  (goto-char (point-min))
  (assert (eq 55 (py-forward-statement)) nil "py-forward-statement-test-1 #1 failed")
  (assert (eq 65 (py-forward-statement)) nil "py-forward-statement-test-1 #2 failed")
  (assert (eq 75 (py-forward-statement)) nil "py-forward-statement-test-1 #2 failed")
  (assert (eq 131 (py-forward-statement)) nil "py-forward-statement-test-1 #3 failed")
  (py-forward-statement)
  (assert (eq 163 (point)) nil "py-forward-statement-test-1 #4 failed"))

(defun py-forward-statement-test-2 (&optional arg)
  (interactive "p")
  (let ((teststring "#! /usr/bin/python
# -*- coding: utf-8 -*-
pdb.set_trace()
# r'\\fB\$\{\\f([BI])([^}]+)\\f\1([^\\]+)\\fB}(.+)$')
result = w_behandlung(aus, i, line, klammer1=w.group(1), klammer2=w.group(2), klammer3=w.group(3), klammer4=w.group(4))
aus.write(result + \"\\n\")
"))
    (py-bug-tests-intern 'py-forward-statement-2-base arg teststring)))

(defun py-forward-statement-2-base (arg)
  (goto-char 59)
  (py-forward-statement)
  (assert (eq 225 (point)) nil "py-forward-statement-test-2 #1 failed"))


(defun key-binding-tests (&optional arg)
  (interactive "p")
  (let ((teststring ""))
    (py-bug-tests-intern 'key-binding-base arg teststring)))

(defun key-binding-base (arg)
  (python-mode)
  (when py-debug-p (switch-to-buffer (current-buffer)))
  (assert (eq (key-binding [(:)]) 'py-electric-colon) nil "py-electric-colon key-binding test failed")
  (assert (eq (key-binding [(\#)]) 'py-electric-comment) nil "py-electric-comment key-binding test failed")
  (assert (eq (key-binding [(delete)]) 'py-electric-delete) nil "py-electric-delete key-binding test failed")
  (assert (eq (key-binding [(backspace)]) 'py-electric-backspace) nil "py-electric-backspace key-binding test failed")
  (assert (eq (key-binding [(control backspace)]) 'py-hungry-delete-backwards) nil "py-hungry-delete-backwards key-binding test failed")
  (assert (eq (key-binding [(control c) (delete)]) 'py-hungry-delete-forward) nil "py-hungry-delete-forward key-binding test failed")
  (assert (eq (key-binding [(control meta a)]) 'py-backward-top-level) nil "py-backward-top-level key-binding test failed")
  (assert (eq (key-binding [(control meta e)]) 'py-forward-top-level) nil "py-forward-def-or-class key-binding test failed")
  (assert (eq (key-binding [(control c)(control l)]) 'py-shift-left) nil "py-shift-left key-binding test failed")
  (assert (eq (key-binding [(control c)(control r)]) 'py-shift-right) nil "py-shift-right key-binding test failed")
  (assert (eq (key-binding [(control c)(<)]) 'py-shift-left) nil "py-shift-left key-binding test failed")
  (assert (eq (key-binding [(control c)(>)]) 'py-shift-right) nil "py-shift-right key-binding test failed")
  (assert (eq (key-binding [(control c)(tab)]) 'py-indent-region) nil "py-indent-region key-binding test failed")
  (assert (eq (key-binding [(control c)(:)]) 'py-guess-indent-offset) nil "py-guess-indent-offset key-binding test failed")

  (assert (eq (key-binding [(control c)(control c)]) 'py-execute-buffer) nil "py-execute-buffer key-binding test failed")
  (assert (eq (key-binding [(control c)(control m)]) 'py-execute-import-or-reload) nil "py-execute-import-or-reload key-binding test failed")
  (assert (eq (key-binding [(control c)(control s)]) 'py-execute-string) nil "py-execute-string key-binding test failed")
  (assert (eq (key-binding [(control c)(|)]) 'py-execute-region) nil "py-execute-region key-binding test failed")
  (assert (eq (key-binding [(control meta x)]) 'py-execute-def-or-class) nil "py-execute-def-or-class key-binding test failed")
  (assert (eq (key-binding [(control c)(!)]) 'py-shell) nil "py-shell key-binding test failed")
  (assert (eq (key-binding [(control c)(control t)]) 'py-toggle-shell) nil "py-toggle-shell key-binding test failed")
  (assert (eq (key-binding [(control meta h)]) 'py-mark-def-or-class) nil "py-mark-def-or-class key-binding test failed")
  (assert (eq (key-binding [(control c)(control k)]) 'py-mark-block-or-clause) nil "py-mark-block-or-clause key-binding test failed")

  (assert (eq (key-binding [(control c)(\.)]) 'py-expression) nil "py-expression key-binding test failed")

  (assert (eq (key-binding [(control c)(control d)]) 'py-pdbtrack-toggle-stack-tracking) nil "py-pdbtrack-toggle-stack-tracking key-binding test failed")
  (assert (eq (key-binding [(control c)(control f)]) 'py-sort-imports) nil "py-sort-imports key-binding test failed")
  (assert (eq (key-binding [(control c)(\#)]) 'py-comment-region) nil "py-comment-region key-binding test failed")
  (assert (eq (key-binding [(control c)(\?)]) 'py-describe-mode) nil "py-describe-mode key-binding test failed")

  (assert (eq (key-binding [(control c)(control e)]) 'py-help-at-point) nil "py-describe-symbol key-binding test failed")
  (assert (eq (key-binding [(control c)(-)]) 'py-up-exception) nil "py-up-exception key-binding test failed")
  (assert (eq (key-binding [(control c)(=)]) 'py-down-exception) nil "py-down-exception key-binding test failed")
  (assert (eq (key-binding [(control x) (n) (d)]) 'py-narrow-to-defun) nil "py-narrow-to-defun key-binding test failed")
  (assert (eq (key-binding [(control c)(control b)]) 'py-submit-bug-report) nil "py-submit-bug-report key-binding test failed")
  (assert (eq (key-binding [(control c)(control v)]) 'py-version) nil "py-version key-binding test failed")
  (assert (eq (key-binding [(control c)(control w)]) 'py-pychecker-run) nil "py-pychecker-run key-binding test failed")
  (assert (eq (key-binding (kbd "TAB")) 'py-indent-or-complete) nil "py-indent-or-complete key-binding test failed")
  (assert (eq (key-binding [(control c)(control p)]) 'py-backward-statement) nil "py-backward-statement key-binding test failed")
  (assert (eq (key-binding [(control c)(control n)]) 'py-forward-statement) nil "py-forward-statement key-binding test failed")
  (assert (eq (key-binding [(control j)]) 'py-newline-and-indent) nil "py-newline-and-indent key-binding test failed")
  ;; (assert (eq (key-binding (kbd "RET")) 'py-newline-and-indent) nil "py-newline-and-indent key-binding test failed")
  )

(defun py-smart-operator-test (&optional arg)
  (interactive "p")
  (let ((teststring "#! /usr/bin/env python
# -*- coding: utf-8 -*-
foo "))
    (py-bug-tests-intern 'py-smart-operator-base arg teststring)))

(defun py-smart-operator-base (arg)
  (python-mode)
  (let ((py-smart-operator-mode-p t))
    (py-smart-operator-mode-p-on)
    (goto-char 52)
    (save-excursion
      (smart-operator-<))
    (assert (looking-at " < ") nil "smart-operator-test \"smart-operator-<\" failed")
    (delete-region (point) (line-end-position))
    (save-excursion
      (smart-operator->))
    (assert (looking-at " > ") nil "smart-operator-test \"smart-operator->\" failed")
    (delete-region (point) (line-end-position))
    (save-excursion (smart-operator-%))
    (assert (looking-at " % ") nil "smart-operator-test \"smart-operator-%\" failed")
    (delete-region (point) (line-end-position))
    (save-excursion (smart-operator-+))
    (assert (looking-at " \\+ ") nil "smart-operator-test \"smart-operator-+\" failed")
    (delete-region (point) (line-end-position))
    (save-excursion (smart-operator--))
    (assert (looking-at " - ") nil "smart-operator-test \"smart-operator--\" failed")
    (delete-region (point) (line-end-position))
    (save-excursion (smart-operator-*))
    (assert (looking-at " * ") nil "smart-operator-test \"smart-operator-*\" failed")
    (delete-region (point) (line-end-position))
    (save-excursion (smart-operator-&))
    (assert (looking-at " & ") nil "smart-operator-test \"smart-operator-&\" failed")
    ;; (delete-region (point) (line-end-position))
    ;; (save-excursion (smart-operator-!))
    ;; (assert (looking-at "! ") nil "smart-operator-test \"smart-operator-!\" failed")
    (delete-region (point) (line-end-position))
    (save-excursion (smart-operator-?))
    (assert (looking-at "? ") nil "smart-operator-test \"smart-operator-?\" failed")
    (delete-region (point) (line-end-position))
    (save-excursion (smart-operator-\,))
    (assert (looking-at ", ") nil "smart-operator-test \"smart-operator-\,\" failed")
    (delete-region (point) (line-end-position))
    (save-excursion (smart-operator-.))
    (assert (looking-at ".") nil "smart-operator-test \"smart-operator-.\" failed")
    (when py-verbose-p (message "%s" "smart-operator-test passed"))))

;; broken
(defun augmented-assigment-test (&optional arg)
  (interactive "p")
  (let ((teststring "#! /usr/bin/env python
# -*- coding: utf-8 -*-
foo"))
    (py-bug-tests-intern 'augmented-assigment-base arg teststring)))

(defun augmented-assigment-base (arg)
  (let ((py-smart-operator-mode-p t))
    (smart-operator-mode-on)
    (goto-char 52)
    (save-excursion
      (smart-operator-<)
      (insert "="))

    (assert (looking-at " <= ") nil "augmented-assigment-test \"smart-operator-<\" failed")
    (delete-region (point) (line-end-position))
    (save-excursion
      (smart-operator->))
    (assert (looking-at " >= ") nil "augmented-assigment-test \"smart-operator->\" failed")
    (delete-region (point) (line-end-position))
    (save-excursion (smart-operator-%))
    (assert (looking-at " %= ") nil "augmented-assigment-test \"smart-operator-%\" failed")
    (delete-region (point) (line-end-position))
    (save-excursion (smart-operator-+))
    (assert (looking-at " \\+= ") nil "augmented-assigment-test \"smart-operator-+\" failed")
    (delete-region (point) (line-end-position))
    (save-excursion (smart-operator--))
    (assert (looking-at " -= ") nil "augmented-assigment-test \"smart-operator--\" failed")
    (delete-region (point) (line-end-position))
    (save-excursion (smart-operator-*))
    (assert (looking-at " \\*= ") nil "augmented-assigment-test \"smart-operator-*\" failed")
    (delete-region (point) (line-end-position))
    (save-excursion (smart-operator-&))
    (assert (looking-at " &= ") nil "augmented-assigment-test \"smart-operator-&\" failed")
    (delete-region (point) (line-end-position))
    (save-excursion (smart-operator-!))
    (assert (looking-at " != ") nil "augmented-assigment-test \"smart-operator-!\" failed")
    (delete-region (point) (line-end-position))
    (save-excursion (smart-operator-?))
    (assert (looking-at " \\?= ") nil "augmented-assigment-test \"smart-operator-?\" failed")
    ;; (delete-region (point) (line-end-position))
    ;; (save-excursion (smart-operator-\,))
    ;; (assert (looking-at " ,= ") nil "augmented-assigment-test \"smart-operator-\,\" failed")
    ;; (delete-region (point) (line-end-position))
    ;; (save-excursion (smart-operator-.))
    ;; (assert (looking-at " .= ") nil "augmented-assigment-test \"smart-operator-.\" failed")
    ;; (assert nil "smart-operator-test failed")
    (when py-verbose-p (message "%s" "augmented-assigment-test passed"))))

(defun py-smart-operator-repeat-test (&optional arg)
  (interactive "p")
  (let ((teststring "#! /usr/bin/env python
# -*- coding: utf-8 -*-
foo "))
    (py-bug-tests-intern 'py-smart-operator-repeat-base arg teststring)))

(defun py-smart-operator-repeat-base (arg)
  (let ((py-smart-operator-mode-p t))
    (py-smart-operator-mode-on)
    (goto-char 52)
    (setq last-command nil)
    (save-excursion
      (call-interactively 'smart-operator-> t)
      (setq last-command 'smart-operator->)
      (setq this-command 'smart-operator->)
      ;; (message "%s" this-command-keys-vector)
      (call-interactively 'smart-operator->))
    (assert (looking-at " >> ") nil "smart-operator-test \"smart-operator->\" failed")
    (delete-region (point) (line-end-position))
    (setq last-command nil)
    (save-excursion
      (call-interactively 'smart-operator-<)
      (setq last-command 'smart-operator-<)
      (setq this-command 'smart-operator-<)
      (call-interactively 'smart-operator-<))
    (assert (looking-at " << ") nil "smart-operator-test \"smart-operator-<\" failed")
    (delete-region (point) (line-end-position))
    (setq last-command nil)
    (save-excursion (smart-operator-%)(setq this-command 'smart-operator-%)(setq last-command 'smart-operator-%)(smart-operator-%))
    (assert (looking-at " %% ") nil "smart-operator-test \"smart-operator-%\" failed")
    (delete-region (point) (line-end-position))
    (setq last-command nil)
    (save-excursion (smart-operator-+)(setq this-command 'smart-operator-+)(setq last-command 'smart-operator-+)(smart-operator-+))
    (assert (looking-at " \\+\\+ ") nil "smart-operator-test \"smart-operator-+\" failed")
    (delete-region (point) (line-end-position))
    (setq last-command nil)
    (save-excursion (smart-operator--)(setq this-command 'smart-operator--)(setq last-command 'smart-operator--)(smart-operator--))
    (assert (looking-at " -- ") nil "smart-operator-test \"smart-operator--\" failed")
    (delete-region (point) (line-end-position))
    (setq last-command nil)
    (save-excursion (smart-operator-*)(setq this-command 'smart-operator-*)(setq last-command 'smart-operator-*)(smart-operator-*))
    (assert (looking-at " ** ") nil "smart-operator-test \"smart-operator-*\" failed")
    (delete-region (point) (line-end-position))
    (setq last-command nil)
    (save-excursion (smart-operator-&)(setq this-command 'smart-operator-&)(setq last-command 'smart-operator-&)(smart-operator-&))
    (assert (looking-at " && ") nil "smart-operator-test \"smart-operator-&\" failed")
    (delete-region (point) (line-end-position))
    (setq last-command nil)
    (save-excursion (smart-operator-!)(setq this-command 'smart-operator-!)(setq last-command 'smart-operator-!)(smart-operator-!))
    (assert (looking-at "!! ") nil "smart-operator-test \"smart-operator-!\" failed")
    (delete-region (point) (line-end-position))
    (setq last-command nil)
    (save-excursion (smart-operator-?)(setq this-command 'smart-operator-?)(setq last-command 'smart-operator-?)(smart-operator-?))
    (assert (looking-at "\\?\\? ") nil "smart-operator-test \"smart-operator-?\" failed")
    (delete-region (point) (line-end-position))
    (setq last-command nil)
    (save-excursion (smart-operator-\,)(setq this-command 'smart-operator-\,)(setq last-command 'smart-operator-\,)(smart-operator-\,))
    (assert (looking-at ",, ") nil "smart-operator-test \"smart-operator-\,\" failed")
    (delete-region (point) (line-end-position))
    (setq last-command nil)
    (save-excursion (smart-operator-.)(setq this-command 'smart-operator-.)(setq last-command 'smart-operator-.)(smart-operator-.))
    (assert (looking-at "..") nil "smart-operator-test \"smart-operator-.\" failed")
    (when py-verbose-p (message "%s" "py-smart-operator-test passed"))))

(defun py-switch-imenu-index-function-test (&optional arg)
  (interactive "p")
  (let ((teststring python-mode-teststring))
  (py-bug-tests-intern 'py-switch-imenu-index-function-base arg teststring)))

(defun py-switch-imenu-index-function-base (arg)
  (assert (listp imenu--index-alist) nil "py-switch-imenu-index-function-test failed")
  (assert (py-switch-imenu-index-function) nil "py-switch-imenu-index-function-test failed")
  (assert (listp imenu--index-alist) nil "py-switch-imenu-index-function-test failed"))

(defun py-bol-moves-test (&optional arg load-branch-function)
  (interactive "p")
  (let ((teststring python-mode-teststring))
    (py-bug-tests-intern 'py-bol-moves-base arg teststring)))

(defun py-bol-moves-base (arg)
  (message "comment-start: %s" comment-start)
  (goto-char 592)
  ;; (sit-for 0.1)
  (assert (eq 561 (py-up-clause-bol)) nil "py-up-clause-bol-test of `py-moves-test' failed")
  (message "%s" "py-up-clause-bol-test of `py-moves-test'  done")
  (goto-char 410)
  ;; (sit-for 0.1)
  (assert (eq 317 (py-up-block-or-clause-bol)) nil "py-up-block-or-clause-bol-test of `py-moves-test' failed")
  (message "%s" "py-up-block-or-clause-bol-test of `py-moves-test'  done")
  (goto-char 410)
  ;; (sit-for 0.1)
  (assert (eq 234 (py-up-def-bol)) nil "py-up-def-bol-test of `py-moves-test' failed")
  (message "%s" "py-up-def-bol-test of `py-moves-test'  done")
  (goto-char 410)
  ;; (sit-for 0.1)
  (assert (eq 1 (py-up-class-bol)) nil "py-up-class-bol-test of `py-moves-test' failed")
  (message "%s" "py-up-class-bol-test of `py-moves-test'  done")
  (goto-char 410)
  ;; (sit-for 0.1)
  (assert (eq 234 (py-up-def-or-class-bol)) nil "py-up-def-or-class-bol-test of `py-moves-test' failed")
  (message "%s" "py-up-def-or-class-bol-test of `py-moves-test'  done")
  (goto-char 410)
  ;; (sit-for 0.1)
  (assert (eq 317 (py-up-block-bol)) nil "py-up-block-bol-test of `py-moves-test' failed")
  (message "%s" "py-up-block-bol-test of `py-moves-test'  done")
  (goto-char 410)
  ;; (sit-for 0.1)
  (assert (eq 317 (py-up-minor-block-bol)) nil "py-up-minor-block-bol-test of `py-moves-test' failed")
  (message "%s" "py-up-minor-block-bol-test of `py-moves-test'  done")
  (goto-char 592)
  ;; (sit-for 0.1)
  (assert (eq 325 (py-up-block)) nil "py-up-block-test of `py-moves-test' failed")
  (message "%s" "py-up-block-test of `py-moves-test'  done")
  (goto-char 410)
  ;; (sit-for 0.1)
  (assert (eq 325 (py-up-minor-block)) nil "py-up-minor-block-test of `py-moves-test' failed")
  (message "%s" "py-up-minor-block-test of `py-moves-test'  done")
  (goto-char 592)
  ;; (sit-for 0.1)
  (assert (eq 569 (py-up-clause)) nil "py-up-clause-test of `py-moves-test' failed")
  (message "%s" "py-up-clause-test of `py-moves-test'  done")
  (goto-char 592)
  ;; (sit-for 0.1)
  (assert (eq 569 (py-up-block-or-clause)) nil "py-up-block-or-clause-test of `py-moves-test' failed")
  (message "%s" "py-up-block-or-clause-test of `py-moves-test'  done")
  (goto-char 410)
  ;; (sit-for 0.1)
  (assert (eq 238 (py-up-def)) nil "py-up-def-test of `py-moves-test' failed")
  (message "%s" "py-up-def-test of `py-moves-test'  done")
  (goto-char 410)
  ;; (sit-for 0.1)
  (assert (eq 1 (py-up-class)) nil "py-up-class-test of `py-moves-test' failed")
  (message "%s" "py-up-class-test of `py-moves-test'  done")
  (goto-char 410)
  ;; (sit-for 0.1)
  (assert (eq 238 (py-up-def-or-class)) nil "py-up-def-or-class-test of `py-moves-test' failed")
  (message "%s" "py-up-def-or-class-test of `py-moves-test'  done")
  (goto-char 264)
  ;; (sit-for 0.1)
  (assert (eq 317 (py-down-block-bol)) nil "py-down-block-bol-test of `py-moves-test' failed")
  (message "%s" "py-down-block-bol-test of `py-moves-test'  done")
  (goto-char 561)
  ;; (sit-for 0.1)
  (assert (eq 594 (py-down-clause-bol)) nil "py-down-clause-bol-test of `py-moves-test' failed")
  (message "%s" "py-down-clause-bol-test of `py-moves-test'  done")
  (goto-char 264)
  ;; (sit-for 0.1)
  (assert (eq 317 (py-down-block-or-clause-bol)) nil "py-down-block-or-clause-bol-test of `py-moves-test' failed")
  (message "%s" "py-down-block-or-clause-bol-test of `py-moves-test'  done")
  (goto-char (point-min))
  (assert (eq 142 (py-down-def-bol)) nil "py-down-def-bol-test of `py-moves-test' failed")
  (message "%s" "py-down-def-bol-test of `py-moves-test'  done")
  (goto-char 410)
  ;; (sit-for 0.1)
  (assert (not (py-down-class-bol)) nil "py-down-class-bol-test of `py-moves-test' failed")
  (message "%s" "py-down-class-bol-test of `py-moves-test'  done")
  (goto-char (point-min))
  (assert (eq 142 (py-down-def-or-class-bol)) nil "py-down-def-or-class-bol-test of `py-moves-test' failed")
  (message "%s" "py-down-def-or-class-bol-test of `py-moves-test'  done")
  (goto-char 264)
  ;; (sit-for 0.1)
  (assert (eq 325 (py-down-block)) nil "py-down-block-test of `py-moves-test' failed")
  (message "%s" "py-down-block-test of `py-moves-test'  done")
  (goto-char 264)
  ;; (sit-for 0.1)
  (assert (eq 317 (py-down-block-bol)) nil "py-down-block-bol-test of `py-moves-test' failed")
  (message "%s" "py-down-block-bol-test of `py-moves-test'  done")

  (goto-char 264)
  ;; (sit-for 0.1)
  (assert (eq 325 (py-down-minor-block)) nil "py-down-minor-block-test of `py-moves-test' failed")
  (message "%s" "py-down-minor-block-test of `py-moves-test'  done")
  (goto-char 264)
  ;; (sit-for 0.1)
  (assert (eq 317 (py-down-minor-block-bol)) nil "py-down-minor-block-bol-test of `py-moves-test' failed")
  (message "%s" "py-down-minor-block-bol-test of `py-moves-test'  done")

  (goto-char 569)
  ;; (sit-for 0.1)
  (assert (eq 602 (py-down-clause)) nil "py-down-clause-test of `py-moves-test' failed")
  (message "%s" "py-down-clause-test of `py-moves-test'  done")
  (goto-char 410)
  ;; (sit-for 0.1)
  (assert (eq 569 (py-down-block-or-clause)) nil "py-down-block-or-clause-test of `py-moves-test' failed")
  (message "%s" "py-down-block-or-clause-test of `py-moves-test'  done")
  (goto-char (point-min))
  (assert (eq 146 (py-down-def)) nil "py-down-def-test of `py-moves-test' failed")
  (message "%s" "py-down-def-test of `py-moves-test'  done")
  (goto-char 410)
  ;; (sit-for 0.1)
  (assert (not (py-down-class)) nil "py-down-class-test of `py-moves-test' failed")
  (message "%s" "py-down-class-test of `py-moves-test'  done")
  (goto-char (point-min))
  (assert (eq 146 (py-down-def-or-class)) nil "py-down-def-or-class-test of `py-moves-test' failed")
  (message "%s" "py-down-def-or-class-test of `py-moves-test'  done")

  (goto-char 410)
  ;; (sit-for 0.1)
  (assert (eq 332 (py-backward-statement-bol)) nil "py-backward-statement-bol-test of `py-moves-test' failed")
  (message "%s" "py-backward-statement-bol-test of `py-moves-test'  done")
  (goto-char 410)
  ;; (sit-for 0.1)
  (assert (eq 317 (py-backward-block-bol)) nil "py-backward-block-bol-test of `py-moves-test' failed")
  (message "%s" "py-backward-block-bol-test of `py-moves-test'  done")
  (goto-char 410)
  ;; (sit-for 0.1)
  (assert (eq 317 (py-backward-clause-bol)) nil "py-backward-clause-bol-test of `py-moves-test' failed")
  (message "%s" "py-backward-clause-bol-test of `py-moves-test'  done")
  (goto-char 410)
  ;; (sit-for 0.1)
  (assert (eq 317 (py-backward-block-or-clause-bol)) nil "py-backward-block-or-clause-bol-test of `py-moves-test' failed")
  (message "%s" "py-backward-block-or-clause-bol-test of `py-moves-test'  done")
  (assert (eq 1 (py-backward-class-bol)) nil "py-backward-class-bol-test of `py-moves-test' failed")
  (message "%s" "py-backward-class-bol-test of `py-moves-test'  done")
  (goto-char 410)
  ;; (sit-for 0.1)
  (assert (eq 234 (py-backward-def-or-class-bol)) nil "py-backward-def-or-class-bol-test of `py-moves-test' failed")
  (message "%s" "py-backward-def-or-class-bol-test of `py-moves-test'  done")
  (message "%s" "py-forward-block-bol-test of `py-moves-test'  done")
  (goto-char 576)
  ;; (sit-for 0.1)
  (assert (eq 594 (py-forward-clause-bol)) nil "py-forward-clause-bol-test of `py-moves-test' failed")
  (message "%s" "py-forward-clause-bol-test of `py-moves-test'  done")
  (goto-char 576)
  ;; (sit-for 0.1)
  (assert (eq 594 (py-forward-block-or-clause-bol)) nil "py-forward-block-or-clause-bol-test of `py-moves-test' failed")
  (message "%s" "py-forward-block-or-clause-bol-test of `py-moves-test'  done")
  (goto-char 410)
  ;; (sit-for 0.1)
  (assert (eq 627 (py-forward-def-bol)) nil "py-forward-def-bol-test of `py-moves-test' failed")
  (message "%s" "py-forward-def-bol-test of `py-moves-test'  done")
  (goto-char 410)
  ;; (sit-for 0.1)
  (assert (eq 627 (py-forward-class-bol)) nil "py-forward-class-bol-test of `py-moves-test' failed")
  (message "%s" "py-forward-class-bol-test of `py-moves-test'  done")
  (goto-char 410)
  ;; (sit-for 0.1)
  (assert (eq 627 (py-forward-def-or-class-bol)) nil "py-forward-def-or-class-bol-test of `py-moves-test' failed")
  (message "%s" "py-forward-def-or-class-bol-test of `py-moves-test'  done")
  (goto-char 410)
  ;; (sit-for 0.1)
  (assert (eq 561 (py-forward-statement-bol)) nil "py-forward-statement-bol-test of `py-moves-test' failed")
  (message "%s" "py-forward-statement-bol-test of `py-moves-test'  done")
  (goto-char 410)
  ;; (sit-for 0.1)
  (assert (eq 234 (py-backward-def-bol)) nil "py-backward-def-bol-test of `py-moves-test' failed")
  (message "%s" "py-backward-def-bol-test of `py-moves-test'  done")
  )

(defun py-guess-indent-offset-test (&optional arg)
  (interactive "p")
  (let (py-smart-indentation
        (teststring "#! /usr/bin/env python
# -*- coding: utf-8 -*-

    #####################################
#####################################
def fooBaz( bar ):  # version 2003/9/7
  if \"Foo:\" == bar \\
          or  \"[Foo:]\" == bar \\
          or \"Foo:]\" == bar \\
          or \"Baz:\" == bar:
      return False
  return True
"))
    (py-bug-tests-intern 'py-guess-indent-offset-base arg teststring)))

(defun py-guess-indent-offset-base (arg)
  (goto-char 49)
  (assert (eq 4 (py-guess-indent-offset)) nil "py-guess-indent-offset-test #1 failed")
  (message "%s" "py-guess-indent-offset-test #1 done")
  (goto-char 168)
  (assert (eq 2 (py-guess-indent-offset)) nil "py-guess-indent-offset-test #2 failed")
  (message "%s" "py-guess-indent-offset-test #2 done")
  (goto-char 251)
  (assert (eq 4 (py-guess-indent-offset)) nil "py-guess-indent-offset-test #3 failed")
  (message "%s" "py-guess-indent-offset-test #3 done")
  (goto-char 280)
  (assert (eq 4 (py-guess-indent-offset)) nil "py-guess-indent-offset-test #4 failed")
  (message "%s" "py-guess-indent-offset-test #4 done")
  (goto-char 298)
  ;; indent might be eithe 4 or 2
  (assert (eq 2 (py-guess-indent-offset)) nil "py-guess-indent-offset-test #5 failed")
  (message "%s" "py-guess-indent-offset-test #5 done"))

(defun autopair-mode-test (&optional arg)
  (interactive "p")
  (let ((teststring "#! /usr/bin/env python
# -*- coding: utf-8 -*-

"))
  (py-bug-tests-intern 'autopair-on-base arg teststring)))

(defun autopair-on-base (arg)
  (assert (py-autopair-mode-on) nil "autopair-mode-test #1 failed")
  (message "%s" "autopair-mode-test #1  done")
  (assert (not (py-toggle-autopair-mode)) nil "autopair-mode-test #2 failed"))
  (message "%s" "autopair-mode-test #2  done")

(defun py-smart-indentation-test (&optional arg)
  (interactive "p")
  (let ((teststring "#! /usr/bin/env python
# -*- coding: utf-8 -*-

"))
  (py-bug-tests-intern 'py-smart-indentation-base arg teststring)))

(defun py-smart-indentation-base (arg)
  (assert (py-smart-indentation-on) nil "smart-indentation-test #1 failed")
  (message "%s" "smart-indentation-test #1  done")
  (assert (not (py-smart-indentation-off)) nil "smart-indentation-test #2 failed")
  (message "%s" "smart-indentation-test #2  done")
  (assert (py-toggle-smart-indentation) nil "smart-indentation-test #3 failed"))
  (message "%s" "smart-indentation-test #3  done")

(defun py-highlight-indentation-test (&optional arg)
  (interactive "p")
  (let ((teststring "#! /usr/bin/env python
# -*- coding: utf-8 -*-

"))
  (py-bug-tests-intern 'py-highlight-indentation-base arg teststring)))

(defun py-highlight-indentation-base (arg)
  (py-highlight-indentation-on)
  (assert highlight-indent-active nil "highlight-indentation-test #1 failed")
  (message "%s" "highlight-indentation-test #1  passed")
  (py-highlight-indentation-off)
  (assert (not highlight-indent-active) nil "highlight-indentation-test #2 failed")
  (message "%s" "highlight-indentation-test #2  passed")
  (py-toggle-highlight-indentation)
  (assert highlight-indent-active nil "highlight-indentation-test #3 failed"))
  (message "%s" "highlight-indentation-test #3  passed")

(defun py-fill-string-django-test (&optional arg)
  (interactive "p")
  (let ((teststring "#! /usr/bin/env python
# -*- coding: utf-8 -*-
def foo()
    ''' asdf' asdf asdf asdf asdf asdfasdf asdfasdf a asdf asdf asdf asdfasdfa asdf asdf asdf asdf'''
"))
    (py-bug-tests-intern 'py-fill-string-django-base arg teststring)))

(defun py-fill-string-django-base (arg)
  (when py-debug-p (switch-to-buffer (current-buffer)))
  (font-lock-fontify-buffer)
  ;; (sit-for 0.1)
  (goto-char 99)
  (py-fill-string-django)
  (beginning-of-line)
  ;; (sit-for 0.1)
  (assert (nth 8 (syntax-ppss)) nil "py-fill-string-django-test #1 failed")
  (goto-char (nth 8 (syntax-ppss)))
  ;; (sit-for 1)
  (assert (looking-at (concat py-string-delim-re "$")) nil "py-fill-string-django-test #2 failed")
)

(defun py-fill-string-onetwo-test (&optional arg)
  (interactive "p")
  (let ((teststring "#! /usr/bin/env python
# -*- coding: utf-8 -*-
def foo()
    ''' asdf' asdf asdf asdf asdf asdfasdf asdfasdf a asdf asdf asdf asdfasdfa asdf asdf asdf asdf'''
"))
  (py-bug-tests-intern 'py-fill-string-onetwo-base arg teststring)))

(defun py-fill-string-onetwo-base (arg)
  (when py-debug-p (switch-to-buffer (current-buffer))
	(font-lock-fontify-buffer))
  ;; (sit-for 0.1)
  (goto-char 99)
  (py-fill-string-onetwo)
  (forward-line 1)
  (assert (empty-line-p) nil "py-fill-string-onetwo-test #1 failed")
  (message "%s" "py-fill-string-onetwo-test #1  passed")
  (forward-line 2)
  (assert (empty-line-p) nil "py-fill-string-onetwo-test #2 failed")
  (message "%s" "py-fill-string-onetwo-test #2  passed")
  (goto-char (nth 8 (syntax-ppss)))
  (assert (looking-at (concat py-string-delim-re "$")) nil "py-fill-string-onetwo-test #3 failed")
  (message "%s" "py-fill-string-onetwo-test #3  passed"))
  (message "%s" "$")

(defun py-fill-string-pep-257-test (&optional arg)
  (interactive "p")
  (let ((teststring "#! /usr/bin/env python
# -*- coding: utf-8 -*-
def foo()
    ''' asdf' asdf asdf asdf asdf asdfasdf asdfasdf a asdf asdf asdf asdfasdfa asdf asdf asdf asdf'''
"))
  (py-bug-tests-intern 'py-fill-string-pep-257-base arg teststring)))

(defun py-fill-string-pep-257-base (arg)
  (when py-debug-p (switch-to-buffer (current-buffer))
	(font-lock-fontify-buffer))
  ;; (sit-for 0.1)
  (goto-char 99)
  (py-fill-string-pep-257)
  (forward-line 1)
  (assert (nth 3 (syntax-ppss)) nil "py-fill-string-pep-257-test #1 failed")
  (message "%s" "py-fill-string-pep-257-test #1 passed")
  (assert (empty-line-p) nil "py-fill-string-pep-257-test #2 failed")
  (message "%s" "py-fill-string-pep-257-test #2 passed")
  (forward-line 2)
  (assert (empty-line-p) nil "py-fill-string-pep-257-test #3 failed")
  (message "%s" "py-fill-string-pep-257-test #3 passed"))

(defun py-fill-string-pep-257-nn-test (&optional arg)
  (interactive "p")
  (let ((teststring "#! /usr/bin/env python
# -*- coding: utf-8 -*-
def foo()
    ''' asdf' asdf asdf asdf asdf asdfasdf asdfasdf a asdf asdf asdf asdfasdfa asdf asdf asdf asdf'''
"))
  (py-bug-tests-intern  'py-fill-string-pep-257-nn-base arg teststring)))

(defun py-fill-string-pep-257-nn-base (arg)
  ;; (switch-to-buffer (current-buffer))
  (font-lock-fontify-buffer)
  ;; (sit-for 0.1)
  (goto-char 99)
  (py-fill-string-pep-257-nn)
  (assert (nth 3 (syntax-ppss))  nil "py-fill-string-pep-257-nn-test #1 failed")
  (message "%s" "py-fill-string-pep-257-nn-test #1  passed")
  (re-search-forward py-string-delim-re nil t 1)
  (goto-char (match-beginning 0))
  (forward-line -1)
  (assert (not (empty-line-p))  nil "py-fill-string-pep-257-non-nil-test #2 failed"))

(defun py-fill-string-symmetric-test (&optional arg)
  (interactive "p")
  (let ((teststring "#! /usr/bin/env python
# -*- coding: utf-8 -*-
def foo():
    ''' asdf' asdf asdf asdf asdf asdfasdf asdfasdf a asdf asdf asdf asdfasdfa asdf asdf asdf asdf asdf' asdf asdf asdf asdf asdfasdf asdfasdf a asdf asdf asdf asdfasdfa asdf asdf asdf asdf

asdf' asdf asdf asdf asdf asdfasdf asdfasdf a asdf asdf asdf asdfasdfa asdf asdf asdf asdf asdf' asdf asdf asdf asdf asdfasdf asdfasdf a asdf asdf asdf asdfasdfa asdf asdf asdf asdf
'''
    pass
"))
  (py-bug-tests-intern 'py-fill-string-symmetric-base arg teststring)))

(defun py-fill-string-symmetric-base (arg)
  (goto-char 84)
  (py-fill-string-symmetric)
  ;; (sit-for 0.1)
  (forward-line -4)
  (assert (empty-line-p) nil "py-fill-string-symmetric-test failed")
  (message "%s" "py-fill-string-symmetric-test passed")
  (re-search-forward py-string-delim-re nil t 3)
  (goto-char (match-beginning 0))
  (assert (looking-at (concat py-string-delim-re "$")) nil "py-fill-string-symmetric-test failed"))

(defun py-electric-yank-test (&optional arg)
  (interactive "p")
  (let ((teststring python-mode-teststring))
    (py-bug-tests-intern 'py-electric-yank-base arg teststring)))

(defun py-electric-yank-base (arg)
  (let ((py-electric-yank-active-p t)
        (kill-new "asdf"))
    (goto-char 610)
    (py-electric-delete)
    (assert (eq 8 (current-indentation))  nil "py-electric-yank-test #1 failed, `py-electric-delete' ")
  (message "%s" "py-electric-yank-test #1 failed, `py-electric-delete' ")
    (end-of-line)
    (py-electric-yank)
    (assert (eq 12 (current-indentation))  nil "py-electric-yank-test #2 failed")))

(defun py-down-statement-test (&optional arg)
  (interactive "p")
  (let ((teststring python-mode-teststring))
  (py-bug-tests-intern 'py-down-statement-base arg teststring)))

(defun py-down-statement-base (arg)
  ;; (switch-to-buffer (current-buffer))
  (goto-char (point-min))
  (font-lock-fontify-buffer)
  (py-down-statement)
  (assert (eq 31 (point)) nil "py-down-statement-test failed"))

(defun py-nested-block-or-clause-test (&optional arg)
  (interactive "p")
  (let ((teststring "#! /usr/bin/env python
# -*- coding: utf-8 -*-
if foo:
    if bar:
        if True:
            pass
        elif False:
            pass
        else:
            pass
    elif baz:
        pass
elif foo2:
    if bar2:
        pass
    elif baz2:
        pass
    else:
        pass
else:
    pass

"))
  (py-bug-tests-intern 'py-nested-block-or-clause-base arg teststring)))

(defun py-nested-block-or-clause-base (arg)
  (goto-char 48)
  (assert (eq 299 (py-forward-block)) nil "py-nested-block-or-clause-test #1 failed")
  (message "%s" "py-nested-block-or-clause-test #1  passed")
  (goto-char 60)
  (assert (eq 196 (py-forward-block)) nil "py-nested-block-or-clause-test #2 failed")
  (message "%s" "py-nested-block-or-clause-test #2  passed")
  (goto-char 76)
  (assert (eq 169 (py-forward-block)) nil "py-nested-block-or-clause-test #3 failed")
  (message "%s" "py-nested-block-or-clause-test #3  passed")
  (goto-char 48)
  (assert (eq 196 (py-forward-clause)) nil "py-nested-block-or-clause-test #4 failed")
  (message "%s" "py-nested-block-or-clause-test #4  passed")
  (goto-char 60)
  (assert (eq 169 (py-forward-clause)) nil "py-nested-block-or-clause-test #5 failed")
  (message "%s" "py-nested-block-or-clause-test #5  passed")
  (goto-char 85)
  (assert (eq 101 (py-forward-clause)) nil "py-nested-block-or-clause-test #6 failed")
  (message "%s" "py-nested-block-or-clause-test #6  passed")
  (goto-char 291)
  (assert (eq 285 (py-backward-clause)) nil "py-nested-block-or-clause-test #7 failed")
  (message "%s" "py-nested-block-or-clause-test #7  passed")
  ;; (sit-for 0.1)
  (assert (eq 197 (py-backward-clause)) nil "py-nested-block-or-clause-test #8 failed")
  (message "%s" "py-nested-block-or-clause-test #8  passed")
  (assert (eq 48 (py-backward-block-or-clause)) nil "py-nested-block-or-clause-test #9 failed")
  (message "%s" "py-nested-block-or-clause-test #9  passed")
  (goto-char 284)
  (assert (eq 266 (py-backward-block-or-clause)) nil "py-nested-block-or-clause-test #10 failed")
  (message "%s" "py-nested-block-or-clause-test #10  passed")
  (assert (eq 238 (py-backward-block-or-clause)) nil "py-nested-block-or-clause-test #11 failed")
  (message "%s" "py-nested-block-or-clause-test #11  passed")
  (assert (eq 212 (py-backward-block-or-clause)) nil "py-nested-block-or-clause-test #12 failed")
  (message "%s" "py-nested-block-or-clause-test #12  passed")
  (assert (eq 197 (py-backward-block-or-clause)) nil "py-nested-block-or-clause-test #13 failed")
  (message "%s" "py-nested-block-or-clause-test #13  passed")
  (goto-char 196)
  (assert (eq 174 (py-backward-block-or-clause)) nil "py-nested-block-or-clause-test #14 failed")
  (message "%s" "py-nested-block-or-clause-test #14  passed")
  (goto-char 169)
  (assert (eq 147 (py-backward-block-or-clause)) nil "py-nested-block-or-clause-test #15 failed")
  (message "%s" "py-nested-block-or-clause-test #15  passed")
  (assert (eq 110 (py-backward-block-or-clause)) nil "py-nested-block-or-clause-test #16 failed")
  (message "%s" "py-nested-block-or-clause-test #16  passed")
  (assert (eq 76 (py-backward-block-or-clause)) nil "py-nested-block-or-clause-test #17 failed")
  (message "%s" "py-nested-block-or-clause-test #17  passed")
  (assert (eq 60 (py-backward-block-or-clause)) nil "py-nested-block-or-clause-test #18 failed")
  (message "%s" "py-nested-block-or-clause-test #18  passed")
  )

(setq py--travel-current-indent-test-start 12)

(defun py--travel-current-indent-test (&optional indent orig)
  (interactive)
  (let ((orig (point))
        (indent (or indent
                    py--travel-current-indent-test-start
                    (string-to-number (read-from-minibuffer "Indent to travel:")))))
    (py--travel-current-indent indent orig)))

(defun docstring-style-switches-test (&optional arg)
  (interactive "p")
  (let ((teststring "#! /usr/bin/env python
# -*- coding: utf-8 -*-

"))
  (py-bug-tests-intern 'docstring-style-switches-base arg teststring)))

(defun docstring-style-switches-base (arg)

  (py-set-django-docstring-style)
  (when
      (assert (eq 'django py-docstring-style) nil "django not py-docstring-style")
    (message "%s" "django not py-docstring-passed"))
  (py-set-onetwo-docstring-style)
  (when
      (assert (eq 'onetwo py-docstring-style) nil "onetwo not py-docstring-style")
    (message "%s" "onetwo not py-docstring-passed"))
  (py-set-pep-257-docstring-style)
  (when
      (assert (eq 'pep-257 py-docstring-style) nil "pep-257 not py-docstring-style")
    (message "%s" "pep-257 not py-docstring-passed"))
  (py-set-pep-257-nn-docstring-style)
  (when
      (assert (eq 'pep-257-nn py-docstring-style) nil "pep-257-nn not py-docstring-style")
    (message "%s" "pep-257-nn not py-docstring-passed"))
  (py-set-symmetric-docstring-style)
  (when
      (assert (eq 'symmetric py-docstring-style) nil "symmetric not py-docstring-style")
    (message "%s" "symmetric not py-docstring-passed")))

(defun forward-sexp-test (&optional arg)
  (interactive "p")
  (let ((teststring "#! /usr/bin/env python
# -*- coding: utf-8 -*-
def usage():
    print(\"\"\"Fehler: %s
Es muß die aufzurufende Ziehungszahl als Argument angegeben werden:
'python roulette.py 1, 'python roulette.py 2', ... 'python roulette.py n'.
\"\"\" % (
          os.path.basename(sys.argv[0])))
"))
  (py-bug-tests-intern 'forward-sexp-base arg teststring)))

(defun forward-sexp-base (arg)
  ;; (message "forward-sexp-function: %s" forward-sexp-function)
  (goto-char 71)
  ;; (sit-for 0.1)
  (forward-sexp 1)
  ;; (sit-for 0.1)
  (when
      (assert (eq 231 (point)) nil "forward-sexp-test failed"))
  (message "%s" "forward-sexp-test passed"))

(defun nested-if-test (&optional arg)
  (interactive "p")
  (let ((teststring "#! /usr/bin/env python
# -*- coding: utf-8 -*-
if foo:
    bar = \"p\"
elif bar:
    if baz == True:
        print(\" \")
else:
    bar = baz
"))
  (py-bug-tests-intern 'nested-if-base arg teststring)))

(defun nested-if-base (arg)
  (goto-char 118)
  (py-backward-block)
  (when
      (assert (eq (char-after) ?i) nil "nested-if-test #1 failed")
    (message "%s" "nested-if-test #1 passed"))
  (py-backward-block)
  (when
      (assert (eq (char-after) ?i) nil "nested-if-test #2 failed")
    (message "%s" "nested-if-test #2 passed"))
  (when
      (assert (not (py-backward-block)) nil "nested-if-test #3 failed"))
  (message "%s" "nested-if-test #3 passed"))

(defun py-execute-region-error-test (&optional arg)
  (interactive "p")
  (let ((teststring "with file(\"roulette-\" + zeit + \".csv\", 'w') as datei:
    for i in range(anzahl):
        klauf.pylauf()
            datei.write(str(spiel[i]) + \"\\n\")
    print(F)
"))
    (py-bug-tests-intern 'py-execute-region-error-base arg teststring)))

(defun py-execute-region-error-base (arg)
  (when py-debug-p (switch-to-buffer (current-buffer)))
  (let (py-exception-buffer (buffer-name (current-buffer)))
    (goto-char 152)
    (push-mark)
    (end-of-line)
    (setq erg (py-execute-region (line-beginning-position) (line-end-position)))
    (message "erg: %s" erg)))

(defun py-execute-statement-error-test (&optional arg)
  (interactive "p")
  (let ((teststring "with file(\"roulette-\" + zeit + \".csv\", 'w') as datei:
    for i in range(anzahl):
        klauf.pylauf()
            datei.write(str(spiel[i]) + \"\\n\")
    print(F)
"))
    (py-bug-tests-intern 'py-execute-statement-error-base arg teststring)))

(defun py-execute-statement-error-base (arg)
  (let (erg)
    (when py-debug-p (switch-to-buffer (current-buffer))
	  (font-lock-fontify-buffer))
    (goto-char 152)
    (push-mark)
    (end-of-line)
    (setq erg (py-execute-statement-python))
    ;; (sit-for 1 t)
    (set-buffer "*Python*")
    ;; (sit-for 0.3 t)
    (when py-debug-p (switch-to-buffer (current-buffer)))
    (assert (search-backward "line 5") nil "py-execute-statement-error-test failed")
    (message "%s" "py-execute-statement-error-test passed")))

(defun backward-block-fails-from-wrong-indent-test (&optional arg)
  (interactive "p")
  (let ((teststring "#! /usr/bin/env python
# -*- coding: utf-8 -*-
with file(\"roulette-\" + zeit + \".csv\", 'w') as datei:
 for i in range(anzahl):
        klauf.pylauf()
            datei.write(str(spiel[i]) + \"\\n\")
"))
  (py-bug-tests-intern 'backward-block-fails-from-wrong-indent-base arg teststring)))

(defun backward-block-fails-from-wrong-indent-base (arg)
    (goto-char 102)
    (assert (eq 48 (py-backward-block)) nil "backward-block-fails-from-wrong-indent-test failed"))

(defun py-store-result-test (&optional arg)
  (interactive "p")
   (let ((teststring "#! /usr/bin/env python
# -*- coding: utf-8 -*-
print(12)"))
  (py-bug-tests-intern 'py-store-result-base arg teststring)))

(defun py-store-result-base (arg)
  ;; (switch-to-buffer (current-buffer))
  (let ((py-store-result-p t))
    (py-execute-statement)
    ;; (sit-for 0.4 t)
    (message "py-result: %s" py-result)
    (assert (string= (car kill-ring) "12")) nil "py-store-result-test failed"))

(defun py-shell-complete-test (&optional arg load-branch-function)
  (interactive "p")
  (let ((teststring (concat py-test-shebang "
# -*- coding: utf-8 -*-
impo")))
    (py-bug-tests-intern 'py-shell-complete-base arg teststring)))

(defun py-shell-complete-base (arg)
  (when  py-debug-p (switch-to-buffer (current-buffer))
	(font-lock-fontify-buffer))
  (py-shell-complete)
  ;; (sit-for 2 t)
  (assert (looking-back "import") nil "py-shell-complete-test failed"))

(defun py-list-settings ()
  "List py-variables with it's current value.

  For debugging "
  (interactive)
  (set-buffer (get-buffer-create "Python-mode-el-settings"))
  (erase-buffer)
  (load (concat (py--normalize-directory py-install-directory) "devel/python-mode-vars.el") nil t)
  (dolist (elt py-variables)
    (insert (concat (prin1-to-string elt) " ==> "))
    (if (stringp (ignore-errors (symbol-value elt)))
        (insert (concat (symbol-value elt) "\n\n"))
      (insert (concat (prin1-to-string (ignore-errors (symbol-value elt))) "\n\n"))))
  ;; (switch-to-buffer (current-buffer))
  )

(provide 'python-mode-test)
