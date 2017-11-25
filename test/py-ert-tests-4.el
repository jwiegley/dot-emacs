;;; py-interactive-tests.el --- Tests expected to succeed interactively -*- lexical-binding: t; -*-

;; Copyright (C) 2015  Andreas Röhler

;; Author: Andreas Röhler <andreas.roehler@online.de>
;; Keywords: lisp

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

;;

;;; Code:

(defun py-shell-complete-test (&optional arg load-branch-function)
  (interactive "p")
  (let ((teststring (concat py-test-shebang "
# -*- coding: utf-8 -*-
impo")))
    (py-bug-tests-intern 'py-shell-complete-base arg teststring)))

(defun py-shell-complete-base ()
  (when (and (interactive-p) py-debug-p) (switch-to-buffer (current-buffer))
	(font-lock-fontify-buffer))
  ;; (sit-for 0.1 t)
  (py-shell-complete)
  ;; (sit-for 0.1)
  (assert (looking-back "import") nil "py-shell-complete-test failed"))

(ert-deftest py-ert-fast-complete-1 ()
  (py-test-with-temp-buffer
      "obj"
    (let ((py-return-result-p t)
	  py-result py-store-result-p)
      (when py-debug-p (switch-to-buffer (current-buffer)))
      (py-fast-complete)
      (should (eq (char-before) 40)))))

(ert-deftest py-ert-shift-right-test-1 ()
  (py-test-with-temp-buffer
      "def foo():
    if path == '/tmp':
    raise ValueError"
    (back-to-indentation)
    (py-shift-right 1)
    (should (eq 8 (current-indentation)))))

(ert-deftest py-ert-shift-right-test-2 ()
  (py-test-with-temp-buffer
      "def foo():
    if path == '/tmp':
    raise ValueError"
    (back-to-indentation)
    (py-shift-right 1)
    (forward-line -1)
    (should (eq 4 (current-indentation)))))

(ert-deftest py-ert-shift-right-test-3 ()
  (py-test-with-temp-buffer
      "def foo():
    if path == '/tmp':
    raise ValueError"
    (beginning-of-line)
    (py-shift-right 1)
    (forward-line -1)
    (should (eq 4 (current-indentation)))))

(ert-deftest py-ert-shift-right-test-4 ()
  (py-test-with-temp-buffer
      "def foo():
    if path == '/tmp':
    raise ValueError"
    (back-to-indentation)
    (forward-word 1)
    (py-shift-right 1)
    (should (eq 8 (current-indentation)))
    (beginning-of-buffer)
    (should (eq 0 (current-indentation)))))

(ert-deftest py-ert-shift-right-test-5 ()
  (py-test-with-temp-buffer
      "def foo():
    if path == '/tmp':
    raise ValueError"
    (forward-char -2)
    (deactivate-mark)
    (py-shift-right 1)
    (should (eq 8 (current-indentation)))
    (beginning-of-buffer)
    (should (eq 0 (current-indentation)))))

(ert-deftest py-ert-shift-right-test-6 ()
  (py-test-with-temp-buffer
      "def foo():
    if path == '/tmp':
    raise ValueError"
    (forward-char -2)
    (py-shift-right 1)
    (should (eq 8 (current-indentation)))
    (beginning-of-buffer)
    (should (eq 0 (current-indentation)))))

(ert-deftest py-execute-region-test-1 ()
  (py-test-with-temp-buffer
      "def foo(x):
    if x == 1:
        return 0"
    (push-mark)
    (goto-char (point-min))
    (py-execute-region (point) (mark))
    (set-buffer (get-buffer py-buffer-name))
    (should-not (search-backward "FileNotFoundError" nil t 1))))

(ert-deftest py-end-of-def-or-class-test-1 ()
  (py-test-with-temp-buffer
      "class foo:
    \"\"\"asdf\"\"\"
    def bar():
        \"\"\"\"\"\"
        return True

    @asdf
    def baz():
        \"\"\"\"\"\"
        pass"
    (search-backward "@asdf")
    (end-of-line)
    (py-end-of-def-or-class)
    (should (looking-back "pass"))))

(ert-deftest py-down-statement-test-1 ()
  (py-test-with-temp-buffer
      "class OrderedDict1(dict):
    \"\"\"
    This implementation of a dictionary keeps track of the order
    in which keys were inserted.
    \"\"\"

    def __init__(self, d={}):
        self._keys = d.keys()
        dict.__init__(self, d)"
    (search-backward "\"")
    (forward-char 1) 
    (py-down-statement)
    (should (eq (char-after) ?d))))

(ert-deftest py-backward-minor-block-test-1 ()
  (py-test-with-temp-buffer
      "class OrderedDict1(dict):
    \"\"\"
    This implementation of a dictionary keeps track of the order
    in which keys were inserted.
    \"\"\"

    def f():
        \"\"\"
        class for in 'for in while with blah'
        \"\"\"
        if c:
             pass
        if a:"
    (py-backward-minor-block)
    (should (eq (char-after) ?i))))

(ert-deftest py-forward-block-or-clause-test-1 ()
  (py-test-with-temp-buffer
      "def main():
    if len(sys.argv) == 1:
        usage()
        sys.exit()

    class asdf(object):
        zeit = time.strftime('%Y%m%d--%H-%M-%S')

        def Utf8_Exists(filename):
            return os.path.exists(filename.encode('utf-8'))"
    (search-backward "()")
    (end-of-line)
    (py-forward-block-or-clause)
    (should (eq (char-before) ?\)))))

(ert-deftest py-forward-statement-38-test ()
  (py-test-with-temp-buffer
      "def gen_segments(x, y):
    for i in range(0, len(x)-1):
        yield (x[i], x[i+1]), (y[i], y[i+1])"
    (back-to-indentation) 
    (py-forward-statement)
    (should (eobp))))

(ert-deftest py-wrong-on-quotes-31-test ()
  (py-test-with-temp-buffer
      "print(\"don't\")"
    (py-execute-statement)))

(ert-deftest support-PEP-553-built-in-breakpoint-42-test ()
  (py-test-with-temp-buffer
  "# point is at the end, now hit return
# point ends up here when it should line up under the 'b'
def foo(x):
    if x == 7:
        breakpoint()"
  (should (eq 8 (py-compute-indentation))))) 



(provide 'py-interactive-tests)
;;; py-interactive-tests.el ends here
