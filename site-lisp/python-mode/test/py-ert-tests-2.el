;; py-ert-tests.el --- Tests, some adapted from python.el -*- lexical-binding: t; -*-

;; Copyright (C) 2014 Andreas Röhler, <andreas.roehler@online.de>

;; GNU Emacs is free software: you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation, either version 3 of the License, or
;; (at your option) any later version.

;; GNU Emacs is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with GNU Emacs.  If not, see <http://www.gnu.org/licenses/>.

;;; Commentary:

;;; Code:

;; tests are expected to run from directory test

(add-to-list 'load-path default-directory)
(load "py-ert-tests-1.el" nil t)

;; (require 'python-mode-test)

;;;
(ert-deftest py-ert-keyword-face-lp-1294742 ()
  (py-test-with-temp-buffer-point-min
      " and as assert break continue del elif else except exec finally for global if in is lambda not or pass raise return while with yield"
    (font-lock-fontify-buffer)
    (while (and (not (eobp))(< 0 (skip-chars-forward " ")))
      (should (eq 'font-lock-keyword-face (get-char-property (point) 'face)))
      (skip-chars-forward "^ \n"))))

(ert-deftest py-ert-builtins-face-lp-1294742 ()
  (let ((py-shell-name "python3"))
    (py-test-with-temp-buffer-point-min
	"_ __doc__ __import__ __name__ __package__ abs all any apply basestring bin bool buffer bytearray bytes callable chr classmethod cmp coerce compile complex delattr dict dir divmod enumerate eval execfile file filter float format frozenset getattr globals hasattr hash help hex id input int intern isinstance issubclass iter len list locals long map max min next object oct open ord pow print property range raw_input reduce reload repr reversed round set setattr slice sorted staticmethod str sum super tuple type unichr unicode vars xrange zip"
      (font-lock-fontify-buffer)
      (when py-debug-p (switch-to-buffer (current-buffer)))

      ;; (when py-debug-p (switch-to-buffer (current-buffer)))
      (should (eq 'py-builtins-face (get-char-property (point) 'face))))))

(ert-deftest py-ert-pseudo-keyword-face-lp-1294742 ()
  (py-test-with-temp-buffer-point-min
      "  Ellipsis True False None  __debug__ NotImplemented"
    (font-lock-fontify-buffer)
    (while (and (not (eobp))(< 0 (skip-chars-forward " ")))
      (should (eq 'py-pseudo-keyword-face (get-char-property (point) 'face)))
      (skip-chars-forward "^ \n"))))

(ert-deftest py-ert-object-reference-face-lp-1294742 ()
  (py-test-with-temp-buffer-point-min
      " self cls"
    (font-lock-fontify-buffer)
    (while (and (not (eobp))(< 0 (skip-chars-forward " ")))
      (should (eq 'py-object-reference-face (get-char-property (point) 'face)))
      (skip-chars-forward "^ \n"))))

(ert-deftest py-ert-borks-all-lp-1294820 ()
  (py-test-with-temp-buffer-point-min
      "# M-q within some code (not in= a docstring) completely borks all previous
# code in the file:
#
# E.g. here, if I M-q within the last function:

def foo(self):
    some_actual_code()

def bar(self):
    some_actual_code()

def baz(self):
    some_actual_code()

# def foo(self): some_actual_code() def bar(self): some_actual_code() def
# baz(self):
#     some_actual_code()
"
    (font-lock-fontify-buffer)
    (search-forward "def baz(self):")
    (fill-paragraph)
    (forward-line -1)
    (should (eq (char-after) ?\n))))

(ert-deftest py-ert-respect-paragraph-1294829 ()

  (py-test-with-temp-buffer-point-min
      "# py-fill-paragraph doesn';t respect existing paragraph breaks when
# reflowing the docstring, e.g.

def foo(self)
    \"\"\"First one-line summary.

    Some other stuff which I don't want a paragraph break inserted into
    the middle of.

    And another para hjkdfgh fdjkg hfdjkg hdfjk ghdfk ghjkdf
    ghjkdf ghjdf ghjdkf k
    \"\"\"

def foo(self)
    \"\"\"Second one-line summary. Some other stuff which I don't want a
paragraph

    break inserted into the middle of. And another para hjkdfgh
fdjkg
    hfdjkg hdfjk ghdfk ghjkdf ghjkdf ghjdf ghjdkf k \"\"\"

# I feel it would be better if it didn't attempt to
# reflow the whole docstring, rather just reflow the
# particular paragraph within it which the point is
# positioned in.

# It would also be good if it could avoid mangling parameter
# descriptions like this:

def foo(self):
    \"\"\"Summary line.

    Foo bar fhgdjkfd hgjfd hgjkfd ghjkdf ghjkdf hgjdf ghjkdf
hgjdf hjgk dfhjkg dfhjkg dfhjkg fdhjkg hjfdkg

    Parameters
    ----------
    endog : array-like
        1-d endogenous response variable. The dependent variable.
    exog : array-like
        A nobs x k array where `nobs` is the number of
observations and `k`
        is the number of regressors. An interecept is not
included by default
        and should be added by the user. See
        `statsmodels.tools.add_constant`.\"\"\"

def foo(self):
    \"\"\"Summary line. Foo bar fhgdjkfdhgjfd hgjkfd ghjkdf ghjkdf
hgjdf

    ghjkdf hgjdf hjgk dfhjkg dfhjkg dfhjkg fdhjkghjfdkg
Parameters
    ---------- endog : array-like 1-d endogenous response
variable. The
    dependent variable. exog : array-like A nobs x karray where
`nobs`
    is the number of observations and `k` is the number of
regressors.
    An interecept is not included by default and should be added
by the
    user. See `statsmodels.tools.add_constant`.
    \"\"\"

# Failing that though, if I can at least choose to
# reflow individual paragraphs in the docstring and
# leave others intact, I can format these things
# manually while still being able to flow other
# paragraphs using M-q.
"
    (when py-debug-p (switch-to-buffer (current-buffer)))
    (font-lock-fontify-buffer)
    (search-forward "Some other" nil t 1)
    (sit-for 0.1 t)
    (fill-paragraph)
    (forward-line -2)
    (should (not (empty-line-p)))
    (forward-line 1)
    (should (eq (char-after) ?\n))
    (search-forward "one-line summary." nil t 1)
    (when py-debug-p (message "fill-column: %s" fill-column))
    (fill-paragraph)
    (forward-line 1)
    (sit-for 0.1 t)
    (should (empty-line-p))
    (search-forward "Foo bar" nil t 1)
    (fill-paragraph)
    (forward-line 2)
    (should (eq (char-after) ?\n))))

(ert-deftest py-ert-backward-same-level-test ()
  (py-test-with-temp-buffer-point-min
      "def foo():
    if True:
        def bar():
            pass
    elif False:
        def baz():
            pass
    else:
        try:
            1 == 1
        except True:
            def foo1():
                if True:
                    def bar1():
                        pass
                elif False:
                    def baz1():
                        pass
                else:
                    try:
                        1 == 1
                    except True:
                        pass
                    else:
                        pass
                    finally:
                        pass
        else True:
            pass
        finally:
            pass
"
    (font-lock-fontify-buffer)
    (goto-char 632)
    (py-backward-same-level)
    (should (looking-at "except"))
    (py-backward-same-level)
    (should (looking-at "try"))))

(ert-deftest py-ert-up-level-test-2 ()
  (py-test-with-temp-buffer-point-min
      "def foo():
    if True:
        def bar():
            pass
    elif False:
        def baz():
            pass
    else:
        try:
            1 == 1
        except True:
            def foo1():
                if True:
                    def bar1():
                        pass
                elif False:
                    def baz1():
                        pass
                else:
                    try:
                        1 == 1
                    except True:
                        pass
                    else True:
                        pass
                    finally:
                        pass
        else True:
            pass
        finally:
            pass
"
    (goto-char 632)
    (py-up-block)
    (should (looking-at "else:"))))


(ert-deftest py-ert-deletes-too-much-lp:1300270 ()
  (py-test-with-temp-buffer "
x = {'abc':'def',
         'ghi':'jkl'}
"
    ;; (when py-debug-p (switch-to-buffer (current-buffer)))
    (goto-char 24)
    (py-electric-delete)
    (should (eq 5 (current-indentation)))))

(ert-deftest py-ert-mark-expression-test ()
    "Avoid infinite loop"
  (py-test-with-temp-buffer
      "assert pycompletions('TestClass.test' , name) == \
          ['testclassmeth', 'testmeth', 'testprop', 'teststaticmeth']"
    (forward-char -1)
    (py-mark-expression)
    (should (eq 119 (mark)))
    (goto-char 44)
    (py-mark-expression)
    (should (eq 46 (mark)))))

(ert-deftest py-dedicated-shell-test ()
  ""
  (let ((erg (py-shell nil t "python")))
    (should (< 8 (length erg)))
    (should (eq 0 (string-match "^*Python" erg)))))

(ert-deftest py-python-shell-test ()
  ""
  (let ((erg (python)))
    (should (bufferp (get-buffer erg)))
    (should (get-buffer-process erg))))

(ert-deftest py-python2-shell-test ()
  ""
  (let ((erg (python2)))
    (should (bufferp (get-buffer erg)))
    (should (get-buffer-process erg))))

(ert-deftest py-python3-shell-test ()
  ""
  (let ((erg (python3)))
    (should (bufferp (get-buffer erg)))
    (should (get-buffer-process erg))))

(ert-deftest py-keep-windows-configuration-test ()
  (py-test-with-temp-buffer
      "print('py-keep-windows-configuration-test-string')"
    (delete-other-windows)
    (let ((py-keep-windows-configuration t)
	  (py-split-window-on-execute t)
	  (full-height (window-height)))
      (py-execute-statement)
      (should (eq (window-height) full-height)))))

(ert-deftest py-compute-indentation-after-import-test ()
    (py-test-with-temp-buffer
    "import pdb
"
    (should (eq 0 (py-compute-indentation)))))

(ert-deftest py-compute-indentation-bob-test ()
    (py-test-with-temp-buffer-point-min
    " def foo():
    if True:
        pass
    else:
        pass
"

    (should (eq 0 (py-compute-indentation)))))

(ert-deftest py-indentation-lp-1375122-test ()
  (py-test-with-temp-buffer
      "def foo():
    if True:
pass
"
    (forward-line -1)
    (call-interactively 'py-indent-or-complete)
    (sit-for 0.1 t)
    (should (eq 8 (current-column)))
    (beginning-of-line)
    (delete-horizontal-space)
    (indent-to 4)
    (call-interactively 'py-indent-or-complete)
    (sit-for 0.1 t)
    (should (eq 8 (current-column)))
    ;;
    ;; (call-interactively 'py-indent-or-complete)
    ;; (call-interactively 'py-indent-or-complete)
    ;; (sit-for 0.1 t)
    ;; (should (eq 4 (current-column)))
    ;; (py-indent-or-complete)
    ;; (sit-for 0.1 t)
    ;; (should (eq 8 (current-column)))
    ))

(ert-deftest py-shell-python-lp-1398530-test ()
  (when (buffer-live-p (get-buffer "*Python*"))(py-kill-buffer-unconditional "*Python*"))
  (py-test-with-temp-buffer
      ""
    (when py-debug-p (switch-to-buffer (current-buffer)))
    (let ((py-shell-name "python"))
      (py-shell)
      (sit-for 0.1 t)
      (should (buffer-live-p (get-buffer "*Python*"))))))

(ert-deftest py-shell-python3-lp-1398530-test ()
  (when (buffer-live-p (get-buffer "*Python3*"))(py-kill-buffer-unconditional "*Python3*"))
  (py-test-with-temp-buffer
      ""

    (let ((py-shell-name "python3"))
      (py-shell)
      (sit-for 0.1 t)
      (should (buffer-live-p (get-buffer "*Python3*"))))))

(ert-deftest py-shell-python2-lp-1398530-test ()
  (when (buffer-live-p (get-buffer "*Python2*"))(py-kill-buffer-unconditional "*Python2*"))
  (py-test-with-temp-buffer
      ""
    (when py-debug-p (switch-to-buffer (current-buffer)))
    (let ((py-shell-name "python2"))
      (py-shell)
      (sit-for 0.1 t)
      (should (buffer-live-p (get-buffer "*Python2*"))))))

(ert-deftest py-backward-statement-test-1 ()
  (py-test-with-temp-buffer
      (let ((py-return-result-p t)
	    py-result py-store-result-p)
	"# -*- coding: utf-8 -*-
print dir()
c = Cat()
c.hello() #causes error, but emacs tracking fails
import sys, os; os.remove('do/something/nasty') # lp:1025000

def foo(*args):2
    \"\"\"
    ASDF
    \"\"\"
    # ABD
    args = \"asdf\"
")
    (py-backward-statement)
    (should (eq (char-after) ?a))
    (py-backward-statement)
    (should (eq (char-after) ?d))
    (py-backward-statement)
    (should (eq (char-after) ?o))
    (py-backward-statement)
    (should (eq (char-after) ?i))
    (py-backward-statement)
    (should (eq (char-after) ?c))
    (py-backward-statement)
    (should (eq (char-after) ?c))
    (py-backward-statement)
    (should (eq (char-after) ?p))
    (py-backward-statement)
    (should (bobp))))

(ert-deftest py-ert-backward-except-block-test ()
  (py-test-with-temp-buffer
      "
# -*- coding: utf-8 -*-
class bar:
    def foo ():
        try:
            if True:
                for a in range(anzahl):
                    pass
        except:
            block2
        "
    (py-backward-except-block)
    (should (eq (char-after) ?e))))

(ert-deftest py-ert-backward-except-block-bol-test ()
  (py-test-with-temp-buffer
      "
# -*- coding: utf-8 -*-
class bar:
    def foo ():
        try:
            if True:
                for a in range(anzahl):
                    pass
        except:
            block2
        "
    (py-backward-except-block-bol)
    (should (eq (char-after) ?\ ))))

  ;; (and (bufferp (get-buffer "*Python*"))(buffer-live-p (get-buffer "*Python*"))(py-kill-buffer-unconditional "*Python*"))
  ;; (and (bufferp (get-buffer "*IPython*"))(buffer-live-p (get-buffer "*IPython*"))(py-kill-buffer-unconditional "*IPython*")))

(defun nested-dictionaries-indent-lp:328791-test (&optional arg)
  "With ARG greater 1 keep test buffer open.

If no `load-branch-function' is specified, make sure the appropriate branch is loaded. Otherwise default python-mode will be checked. "
  (interactive "p")
  (let ((teststring "

# hanging
asdf = {
    'a':{
         'b':3,
         'c':4
        }
    }

# closing
asdf = {
    'a':{
        'b':3,
        'c':4
    }
}

data = {
    'key':
    {
        'objlist': [
            {
                'pk': 1,
                'name': 'first',
            },
            {
                'pk': 2,
                'name': 'second',
            }
        ]
    }
}

"))
    (py-bug-tests-intern 'nested-dictionaries-indent-lp:328791-base arg teststring)))

(ert-deftest py-ert-nested-dictionaries-indent-lp:328791-test ()
  (py-test-with-temp-buffer-point-min
      "

# hanging
asdf = {
    'a':{
         'b':3,
         'c':4
        }
    }

# closing
asdf = {
    'a':{
        'b':3,
        'c':4
    }
}

data = {
    'key':
    {
        'objlist': [
            {
                'pk': 1,
                'name': 'first',
            },
            {
                'pk': 2,
                'name': 'second',
            }
        ]
    }
}

"
    (let ((py-indent-honors-multiline-listing t)
	  py-closing-list-dedents-bos)
      (search-forward "'a':{")
      (should (eq 4 (py-compute-indentation)))
      (search-forward "}")
      (should (eq 8 (py-compute-indentation)))
      (search-forward "}")
      (should (eq 4 (py-compute-indentation)))
      ;; py-closing-list-dedents-bos
      (setq py-closing-list-dedents-bos t)
      (search-forward "'a':{")
      (should (eq 4 (py-compute-indentation)))
      (search-forward "}")
      (should (eq 4 (py-compute-indentation)))
      (search-forward "}")
      (should (eq 0 (py-compute-indentation)))
      (search-forward "}" nil nil 2)
      (should (eq 12 (py-compute-indentation)))
      (search-forward "]")
      (should (eq 8 (py-compute-indentation)))
      (search-forward "}")
      (should (eq 4 (py-compute-indentation)))
      (search-forward "}")
      (should (eq 0 (py-compute-indentation))))))

(ert-deftest py-ert-flexible-indentation-lp-328842-test-1 ()
  (py-test-with-temp-buffer-point-min
      "\(long, sequence, of_items,
 that, needs, to_be, wrapped) = input_list

packed_entry = (long, sequence, of_items,
that, needs, to_be, wrapped)

\( whitespaced, long, sequence, of_items,
    that, needs, to_be, wrapped) = input_list
"
    (let ((py-indent-honors-multiline-listing t))
        (search-forward "(long")
      (forward-char -1)
      ;; (goto-char 6)
      (should (eq nil (get-char-property (point) 'face))))))

(ert-deftest py-ert-flexible-indentation-lp-328842-test-2 ()
  (py-test-with-temp-buffer-point-min
      "\(long, sequence, of_items,
 that, needs, to_be, wrapped) = input_list

packed_entry = (long, sequence, of_items,
that, needs, to_be, wrapped)

\( whitespaced, long, sequence, of_items,
    that, needs, to_be, wrapped) = input_list
"
    (let ((py-indent-honors-multiline-listing t)
	  py-indent-paren-spanned-multilines-p)
      (goto-char 33)
      (assert (eq 1 (py-compute-indentation)) nil "flexible-indentation-lp-328842-test failed")
      (goto-char 115)
      (assert (eq 16 (py-compute-indentation)) nil "flexible-indentation-lp-328842-test failed")
      (goto-char 202)
      (assert (eq 2 (py-compute-indentation)) nil "flexible-indentation-lp-328842-test failed"))))

(ert-deftest py-ert-flexible-indentation-lp-328842-test-3 ()
  (py-test-with-temp-buffer-point-min
      "\(long, sequence, of_items,
 that, needs, to_be, wrapped) = input_list

packed_entry = (long, sequence, of_items,
that, needs, to_be, wrapped)

\( whitespaced, long, sequence, of_items,
    that, needs, to_be, wrapped) = input_list
"
    (let ((py-indent-honors-multiline-listing t)
	  (py-indent-paren-spanned-multilines-p t))
      (goto-char 33)
      (assert (eq 5 (py-compute-indentation)) nil "flexible-indentation-lp-328842-test failed")
      (goto-char 115)
      (assert (eq 20 (py-compute-indentation)) nil "flexible-indentation-lp-328842-test failed")
      (goto-char 202)
      (assert (eq 6 (py-compute-indentation)) nil "flexible-indentation-lp-328842-test failed"))))

(ert-deftest py-ert-indent-in-arglist-test ()
  (py-test-with-temp-buffer
      "def foo (a,

):"
    (let (py-indent-paren-spanned-multilines-p)
      (should (eq 9 (py-compute-indentation))))
    (let ((py-indent-paren-spanned-multilines-p t))
      (should (eq 13 (py-compute-indentation))))))

(ert-deftest py-complete-in-python-shell-test ()
  (let ((py-shell-name "python")
	(py-switch-buffers-on-execute-p t))
    (py-kill-buffer-unconditional "*Python*")
    (python)
    (goto-char (point-max))
    (insert "pri")
    (py-indent-or-complete)
    (forward-word -1)
    (should (eq ?p (char-after)))))

(ert-deftest py-complete-in-python3-shell-test ()
  (let ((py-shell-name "python3")
	(py-switch-buffers-on-execute-p t))
    (py-kill-buffer-unconditional "*Python3*")
    (python3)
    (should (eq (current-buffer) (get-buffer "*Python3*")))
    (goto-char (point-max))
    (insert "pri")
    (py-indent-or-complete)
    (forward-word -1)
    (should (eq ?p (char-after)))))

(ert-deftest py-complete-empty-string-result-test ()
  (let ((py-shell-name "python3")
	(py-switch-buffers-on-execute-p t))
    (py-kill-buffer-unconditional "*Python3*")
    (python3)
    (goto-char (point-max))
    (insert "foo")
    (py-indent-or-complete)
    (should (looking-back "foo"))))

(ert-deftest py-ert-close-block-test ()
  (py-test-with-temp-buffer-point-min
      "# -*- coding: utf-8 -*-

def main():
    if len(sys.argv)==1:
        usage()
        sys.exit()
if __name__==\"__main__\":
    main()
"
    (search-forward "exit()")
    (should (eq 4 (py-close-block)))))

(ert-deftest py-ert-close-def-or-class-test ()
  (py-test-with-temp-buffer-point-min
      "# -*- coding: utf-8 -*-

def main():
    if len(sys.argv)==1:
        usage()
        sys.exit()
if __name__==\"__main__\":
    main()
"
    (search-forward "exit()")
    (should (eq 0 (py-close-def-or-class)))))

(ert-deftest py-ert-close-def-test ()
  (py-test-with-temp-buffer-point-min
      "# -*- coding: utf-8 -*-

def main():
    if len(sys.argv)==1:
        usage()
        sys.exit()
if __name__==\"__main__\":
    main()
"
    (search-forward "exit()")
    (should (eq 0 (py-close-def)))))

(ert-deftest py-ert-close-class-test ()
  (py-test-with-temp-buffer-point-min
      "# -*- coding: utf-8 -*-
class asdf:
    def main():
        if len(sys.argv)==1:
            usage()
            sys.exit()
    if __name__==\"__main__\":
        main()
"
    (search-forward "exit()")
    (should (eq 0 (py-close-class)))))

(ert-deftest py-ert-dedent-forward-test ()
  (py-test-with-temp-buffer
   "with file(\"roulette-\" + zeit + \".csv\", 'w') as datei:
    for i in range(anzahl):
        klauf.pylauf()
        datei.write(str(spiel[i]) + \"\\n\")"
   (skip-chars-backward " \t\r\n\f")
   (py-dedent-forward-line)
   (should (empty-line-p))
   (forward-line -1)
   (should (eq 4 (current-indentation)))))


(ert-deftest py-face-lp-1454858-python2-1-test ()
  (let ((py-python-edit-version ""))
    (py-test-with-temp-buffer
	"#! /usr/bin/env python2
file.close()"
      (beginning-of-line)
      (font-lock-fontify-buffer)
      (sit-for 0.1)
      (should (eq (face-at-point) 'py-builtins-face)))))

;; Setting of py-python-edit-version should precede
(ert-deftest py-face-lp-1454858-python2-2-test ()
  (let ((py-python-edit-version "python2"))
    (py-test-with-temp-buffer
	"#! /usr/bin/env python3
file.close()"
      (beginning-of-line)
      (font-lock-fontify-buffer)
      (sit-for 0.1)
      (should (eq (face-at-point) 'py-builtins-face)))))

(ert-deftest py-face-lp-1454858-python2-3-test ()
  (let ((py-python-edit-version ""))
    (with-temp-buffer
      (insert "#! /usr/bin/env python2
print()")
      (switch-to-buffer (current-buffer))
      (beginning-of-line)
      (python-mode)
      (font-lock-fontify-buffer)
      (sit-for 0.1)
      (should (eq (face-at-point) 'font-lock-keyword-face)))))

(ert-deftest py-ert-in-comment-p-test ()
  (py-test-with-temp-buffer
      "# "
    (should (py--in-comment-p))))

(ert-deftest py-ert-in-sq-string-p-test ()
  (py-test-with-temp-buffer
      "' "
    (should (py-in-string-p))))

(ert-deftest py-ert-in-dq-string-p-test ()
  (py-test-with-temp-buffer
      "\" "
    (should (py-in-string-p))))

(ert-deftest py-ert-in-sq-tqs-string-p-test ()
  (py-test-with-temp-buffer
      "''' "
    (should (py-in-string-p))))

(ert-deftest py-ert-in-dq-tqs-string-p-test ()
  (py-test-with-temp-buffer
      "\"\"\" "
    (should (py-in-string-p))))

(ert-deftest py-ert-electric-delete-test ()
  (py-test-with-temp-buffer-point-min
      "  {}"
    (py-electric-delete)
    (should (eq (char-after) ?{))))

(ert-deftest py-ert-end-of-def-or-class-test-1 ()
  (py-test-with-temp-buffer-point-min
      "class MyTest(unittest.TestCase):
    def test(self):
        self.assertEqual(fun(3), 4)"
    (skip-chars-forward "^(")
    (py-end-of-def-or-class)
    (should (eobp))))

(ert-deftest py-ert-end-of-def-or-class-test-2 ()
  (py-test-with-temp-buffer-point-min
      "class MyTest(unittest.TestCase):
    def test(self):
        pass
    def test(self):
        pass"
    (search-forward "pass")
    (py-end-of-def-or-class)
    (should (eobp))))

(ert-deftest py-ert-narrow-to-block-test ()
  (py-test-with-temp-buffer
      "with file(\"roulette-\" + zeit + \".csv\", 'w') as datei:
    for i in range(anzahl):
        klauf.pylauf()
        "
      (py-narrow-to-block)
      (should (eq 50 (length (buffer-substring-no-properties (point-min)(point-max)))))))

(ert-deftest py-ert-narrow-to-block-or-clause-test ()
  (py-test-with-temp-buffer
      "if treffer in gruen:
    # print \"0, Gruen\"
    ausgabe[1] = treffer
    ausgabe[2] = treffer

elif treffer in schwarz:
    # print \"%i, Schwarz\" % (treffer)
    ausgabe[1] = treffer
"
    (py-narrow-to-block-or-clause)
    (should (eq 87 (length (buffer-substring-no-properties (point-min)(point-max)))))))

(ert-deftest py-ert-narrow-to-clause-test ()
  (py-test-with-temp-buffer
      "if treffer in gruen:
    # print \"0, Gruen\"
    ausgabe[1] = treffer
    ausgabe[2] = treffer

elif treffer in schwarz:
    # print \"%i, Schwarz\" % (treffer)
    ausgabe[1] = treffer
"
    (py-narrow-to-clause)
    (should (eq 87 (length (buffer-substring-no-properties (point-min)(point-max)))))))

(ert-deftest py-ert-narrow-to-class-test ()
  (py-test-with-temp-buffer
      py-def-and-class-test-string
    (search-backward "treffer")
    (py-narrow-to-class)
    (should (eq 710 (length (buffer-substring-no-properties (point-min)(point-max)))))))

(ert-deftest py-ert-narrow-to-def-test ()
  (py-test-with-temp-buffer
      py-def-and-class-test-string
    (search-backward "treffer")
    (py-narrow-to-def)
    (should (< 480 (length (buffer-substring-no-properties (point-min)(point-max)))))))

(ert-deftest py-ert-narrow-to-def-or-class-test ()
  (py-test-with-temp-buffer
      py-def-and-class-test-string
    (search-backward "treffer")
    (py-narrow-to-def-or-class)
    (should (< 480 (length (buffer-substring-no-properties (point-min)(point-max)))))
    (should (> 490 (length (buffer-substring-no-properties (point-min)(point-max)))))))

(ert-deftest py-ert-narrow-to-statement-test ()
  (py-test-with-temp-buffer
      py-def-and-class-test-string
    (search-backward "treffer")
    (py-narrow-to-statement)
    (should (eq 32 (length (buffer-substring-no-properties (point-min)(point-max)))))))

(ert-deftest py-ert-section-backward-test ()
  (py-test-with-temp-buffer
      "# {{
print('%(language)s has %(number)03d quote types.' %
       {'language': \"Python\", \"number\": 2})
# }}
# {{
print(\"%(language)s has %(number)03d quote types.\" %
       {'language': \"Python\", \"number\": 2})
# }}
"
    (py-backward-section)
    (should (eq (char-after) ?#))
    (py-backward-section)
    (should (eq (char-after) ?#))))

(ert-deftest py-ert-section-forward-test ()
  (py-test-with-temp-buffer-point-min
      "# {{
print('%(language)s has %(number)03d quote types.' %
       {'language': \"Python\", \"number\": 2})
# }}
# {{
print(\"%(language)s has %(number)03d quote types.\" %
       {'language': \"Python\", \"number\": 2})
# }}
"
    (py-forward-section)
    (should (eq (char-before) ?}))
    (py-forward-section)
    (should (eq (char-before) ?}))))

(ert-deftest py-ert-sectionize-test ()
  (py-test-with-temp-buffer-point-min
      "print('%(language)s has %(number)03d quote types.' %
       {'language': \"Python\", \"number\": 2})
"
    (end-of-line)
    (py-sectionize-region (point-min) (point-max))
    (goto-char (point-min))
    (should (eq (char-after) ?#))
    (py-forward-section)
    (should (eq (char-before) ?}))))

(ert-deftest py-ert-jump-matching-indent-test ()
  (py-test-with-temp-buffer
      py-def-and-class-test-string
    (search-backward "if ")
    (forward-line -1)
    (indent-to 12)
    (py-backward-block)
    (should (eq (current-column) 8))))

(ert-deftest py-ert-fill-plain-string-test ()
  (py-test-with-temp-buffer-point-min
      "'''asdf' asdf asdf asdf asdf asdfasdf asdfasdf a asdf asdf asdf asdfasdfa asdf asdf asdf asdf asdf' asdf asdf asdf asdf asdfasdf asdfasdf a asdf asdf asdf asdfasdfa asdf asdf asdf asdfasdf' asdf asdf asdf asdf asdfasdf asdfasdf a asdf asdf asdf asdfasdfa asdf asdf asdf asdf
'''"
      (forward-char 4)
      (fill-paragraph)
      (forward-line 1)
      (should (not (empty-line-p)))))

(ert-deftest py-ert-nil-docstring-style-lp-1477422-test ()
  (py-test-with-temp-buffer-point-min
      "def foo():
    '''asdf' asdf asdf asdf asdf asdfasdf asdfasdf a asdf asdf asdf asdfasdfa asdf asdf asdf asdf asdf' asdf asdf asdf asdf asdfasdf asdfasdf a asdf asdf asdf asdfasdfa asdf asdf asdf asdfasdf' asdf asdf asdf asdf asdfasdf asdfasdf a asdf asdf asdf asdfasdfa asdf asdf asdf asdf'''"
    (let (py-docstring-style)
      (search-forward "'''")
      (save-excursion
	(fill-paragraph))
      (forward-line 1)
      (should (not (empty-line-p))))))

(ert-deftest py-markup-region-as-section-test ()
  (py-test-with-temp-buffer-point-min
      py-def-and-class-test-string
      (search-forward "fertig")
      (py-sectionize-region (match-beginning 0) (line-end-position))
      (py-mark-section)
      (should (eq 371 (region-beginning)))
      (should (eq 408 (region-end)))))


(ert-deftest py-indent-in-docstring-gh6 ()
  (py-test-with-temp-buffer-point-min
      "def f():
    \"\"\"
    Return nothing.

    .. NOTE::

        First note line
    second note line\"\"\"
    pass"
    (search-forward "second")
    (back-to-indentation)
    (should (eq 8 (py-compute-indentation)))))

(provide 'py-ert-tests-2)
;;; py-ert-tests-2.el ends here
