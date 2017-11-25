;;; py-bug-numbered-tests.el --- run single tests according to bug number

;; Author: Andreas Roehler <andreas.roehler@online.de>
;; Keywords: languages
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

(defmacro py-bug-tests-intern (testname arg teststring)
  "Just interally. "
  (declare (debug (edebug-form-spec t)))
  `(let ((debug-on-error t)
         (enable-local-variables :all)
         py-load-pymacs-p
         ;; py-split-window-on-execute
         ;; py-switch-buffers-on-execute-p
         py-start-run-py-shell
         proc
         py-fontify-shell-buffer-p
  	 (test-buffer (get-buffer-create (replace-regexp-in-string "\\\\" "" (replace-regexp-in-string "-base$" "-test" (prin1-to-string ,testname))))))
     (with-current-buffer test-buffer
       (delete-other-windows)
       (erase-buffer)
       (fundamental-mode)
       (python-mode)
       (insert ,teststring)
       (when py-debug-p (switch-to-buffer test-buffer))
       (local-unset-key (kbd "RET"))
       (sit-for 0.1)
       (when (and (boundp 'company-mode) company-mode) (company-abort))
       (funcall ,testname ,arg)
       (message "%s" (replace-regexp-in-string "\\\\" "" (concat (replace-regexp-in-string "-base$" "-test" (prin1-to-string ,testname)) " passed")))
       ;; (unless (< 1 arg)
       (unless (eq 2 arg)
  	 (set-buffer-modified-p 'nil)
  	 (and (get-buffer-process test-buffer)
  	      (set-process-query-on-exit-flag (get-buffer-process test-buffer) nil)
  	      (kill-process (get-buffer-process test-buffer)))
  	 (kill-buffer test-buffer)))))

(defvar py-test-shebang-list (list "#! /usr/bin/env python" "#! /usr/bin/env ipython" "#! /usr/bin/python" "#! /usr/bin/ipython")
  "Values to test as `py-test-shebang', resp. `py-shell-name'. ")

(setq py-test-shebang-list (list "#! /usr/bin/env python" "#! /usr/bin/ipython"))

(defvar py-test-shebang "#! /usr/bin/env python"
  "Default value used for tests. ")

(defvar py-ipython-test-shebang "#! /usr/bin/env ipython"
  "Default value used for testing IPython. ")

(defvar bug-numbered-tests nil
  "Tests following reports at https://bugs.launchpad.net/python-mode")

(defun py-run-bug-numbered-tests (&optional arg)
  "With ARG greater 1 keep test buffers open. "
  (interactive "p")
  (dolist (ele bug-numbered-tests)
    (funcall ele arg)))

(setq bug-numbered-tests
      (list
       'py-shell-invoking-python-lp-835151-test
       'py-shell-invoking-ipython-lp-835151-test
       'py-shell-invoking-python3-lp-835151-test
       'py-shell-invoking-python2-lp-835151-test
       'py-shell-invoking-jython-lp-835151-test
       'auto-indent-lp-134258-test
       'py-execute-buffer-ipython-lp-1252643-test
       'py-empty-line-closes-p-lp-1235324-test
       'C-c-C-c-lp-1221310-and-store-result-test
       'Bogus-whitespace-left-in-docstring-after-wrapping-lp-1178455-test
       'Bogus-dedent-when-typing-colon-in-dictionary-literal-lp-1197171-test
       'python-mode-very-slow-lp-1107037-test
       'cascading-indent-lp-1101962-test
       'line-after-colon-with-inline-comment-lp-1109946-test
       'more-docstring-filling-woes-lp-1102296-pep-257-nn-test
       'more-docstring-filling-woes-lp-1102296-pep-257-test
       'more-docstring-filling-woes-lp-1102296-nil-test
       'more-docstring-filling-woes-lp-1102296-onetwo-test
       'more-docstring-filling-woes-lp-1102296-django-test
       'more-docstring-filling-woes-lp-1102296-symmetric-test
       'module-docstring-when-following-comment-lp-1102011-test
       'py-newline-and-indent-leaves-eol-whitespace-lp-1100892-test
       'py-underscore-word-syntax-p-customization-has-no-effect-lp-1100947-test
       'py-up-test-python-el-111-test
       'py-down-python-el-112-test
       'enter-key-does-not-indent-properly-after-return-statement-lp-1098793-test
       'filename-completion-fails-in-ipython-lp-1027265-n1-test
       'filename-completion-fails-in-ipython-lp-1027265-n2-test
       'comments-start-a-new-line-lp-1092847-n1-test
       'comments-start-a-new-line-lp-1092847-n2-test
       'temporary-files-remain-when-python-raises-exception-lp-1083973-n1-test
       'temporary-files-remain-when-python-raises-exception-lp-1083973-n2-test
       'temporary-files-remain-when-python-raises-exception-lp-1083973-n3-test
       'temporary-files-remain-when-python-raises-exception-lp-1083973-n4-test
       'wrong-indentation-after-return-or-pass-keyword-lp-1087499-test
       'wrong-indent-after-asignment-lp-1087404-test
       'py-execute-buffer-python3-looks-broken-lp-1085386-test
       'fill-paragraph-in-comments-results-in-mess-lp-1084769-test
       'imenu-add-menubar-index-fails-lp-1084503-test
       'spuriously-indents-whole-line-while-making-some-portion-inline-comment-lp-1080973-test
       'fill-paragraph-in-a-comment-does-not-stop-at-empty-comment-lines-lp-1077139-test
       'incorrect-indentation-of-comments-in-a-multiline-list-lp-1077063-test
       'fails-to-indent-abs-wrong-type-argument-lp-1075673-test
       'incorrect-indentation-of-one-line-functions-lp-1067633-test
       'several-new-bugs-with-paragraph-filling-lp-1066489-test
       'impossible-to-execute-a-buffer-with-from-future-imports-lp-1063884-test
       'exception-in-except-clause-highlighted-as-keyword-lp-909205-test
       'pyindex-mishandles-class-definitions-lp-1018164-test
       'stalls-emacs-probably-due-to-syntax-highlighting-lp-1058261-test
       'py-find-imports-lp-1023236-test
       'pycomplete-imports-not-found-error-when-no-symbol-lp-1019791-test
       'return-statement-indented-incorrectly-lp-1019601-test
       'converts-tabs-to-spaces-in-indent-tabs-mode-t-lp-1019128-test
       'empty-triple-quote-lp-1009318-test
       'spurious-trailing-whitespace-lp-1008679-test
       'completion-fails-in-python-script-r989-lp-1004613-test
       'no-completion-at-all-lp-1001328-test
       'py-narrow-to-defun-lp-1020531-test
       'not-that-useful-completion-lp-1003580-test
       'pycomplete-same-folder-class-lp-889052-test
       'pycomplete-same-folder-def-lp-889052-test
       'indent-region-lp-997958-test
       'py-describe-symbol-fails-on-modules-lp-919719-test
       'mark-block-region-lp-328806-test
       'mark-decorators-lp-328851-test
       'nested-dictionaries-indent-lp-328791-test
       'tqs-lp-302834-lp-1018994-test
       'fore-00007F-breaks-indentation-lp-328788-test
       'dq-in-tqs-string-lp-328813-test
       'flexible-indentation-lp-328842-test
       'py-current-defun-lp-328846-test
       'cls-pseudo-keyword-lp-328849-test
       'hungry-delete-backwards-lp-328853-test
       'hungry-delete-forward-lp-328853-test
       'beg-end-of-defun-lp-303622-test
       'bullet-lists-in-comments-lp-328782-test
       'imenu-newline-arglist-lp-328783-test
       'imenu-matches-in-docstring-lp-436285-test
       'exceptions-not-highlighted-lp-473525-test
       'fill-paragraph-problems-lp-710373-test
       'nested-indents-lp-328775-test
       'previous-statement-lp-637955-test
       'inbound-indentation-multiline-assignment-lp-629916-test
       'indentation-of-continuation-lines-lp-691185-test
       ;; test passes only when run from edebug
       ;; assistance appreciated
       ;; 'syntaxerror-on-py-execute-region-lp-691542-test
       'goto-beginning-of-tqs-lp-735328-test
       'class-treated-as-keyword-lp-709478-test
       'py-decorators-face-lp-744335-test
       'indent-after-return-lp-745208-test
       'keep-assignments-column-lp-748198-test
       'indent-triplequoted-to-itself-lp-752252-test
       'multiline-listings-indent-lp-761946-test
       'new-page-char-causes-loop-lp-762498-test
       'nested-dicts-indent-lp-763756-test
       'bad-indent-after-except-lp-771289-test
       'indent-open-paren-not-last-lp-771291-test
       'wrong-indent-after-else-lp-772610-test
       'except-indents-wrong-lp-784432-test
       'indent-explicitly-set-in-multiline-tqs-lp-784225-test
       'unbalanced-parentheses-lp-784645-test
       'explicitly-indent-in-list-lp-785018-test
       'explicit-backslashed-continuation-line-indent-lp-785091-test
       'indentation-error-lp-795773-test
       'indent-function-arglist-lp-800088-test
       'python-mode-hangs-lp-801780-test
       'stops-backslashed-line-lp-802504-test
       'stops-backslashed-line-lp-802504-test2
       'python-mode-slow-lp-803275-test
       'master-file-not-honored-lp-794850-test
       'py-variable-name-face-lp-798538-test
       'colon-causes-error-lp-818665-test
       'if-indentation-lp-818720-test
       'closing-parenthesis-indent-lp-821820-test
       'py-indent-line-lp-822532-test
       'indent-honor-arglist-whitespaces-lp-822540-test
       'comments-indent-honor-setting-lp-824427-test
       'infinite-loop-after-tqs-lp-826044-test
       'closing-list-lp-826144-test
       'py-electric-comment-add-space-lp-828398-test
       'py-electric-comment-add-space-t-lp-828398-test
       'execute-indented-code-lp-828314-test
       'py-hungry-delete-backwards-needs-cc-lp-850595-test
       'wrong-guess-for-py-indent-offset-lp-852052-test
       'indent-match-import-pkg-lp-852500-test
       'py-shift-line-when-no-region-lp-855565-test
       'indentation-of-from-import-continuation-lines-lp-858041-test
       'indentation-after-one-line-suites-lp-858044-test
       'py-compute-indentation-wrong-at-eol-lp-858043-test
       'comment-indentation-level-lp-869854-test
       'indentation-wrong-after-multi-line-parameter-list-lp-871698-test
       'no-indent-after-continue-lp-872676-test
       'indent-after-inline-comment-lp-873372-test
       'else-clause-indentation-lp-874470-test
       'py-complete-lp-858621-test
       'incorrect-use-of-region-in-py-shift-left-lp-875951-test
       'indent-after-multiple-except-statements-lp-883815-test
       'wrongly-highlighted-as-keywords-lp-885144-test
       'glitch-when-indenting-lists-lp-886473-test
       'indentation-keyword-lp-885143-test
       'indentation-bug-inside-docstrings-lp-899455-test
       'another-indentation-bug-inside-docstrings-lp-900684-test
       'py-shebang-consider-ipython-lp-849293-test
       'py-shebang-ipython-env-lp-849293-test
       'indent-offset-not-guessed-when-loading-lp-902890-test
       'from-__future__-import-absolute_import-mishighlighted-lp-907084-test
       ;; 'automatic-indentation-is-broken-lp-889643-test
       'chars-uU-preceding-triple-quoted-get-string-face-lp-909517-test
       'problem-with-py-separator-char-under-windows-lp-975539-test
       'tuple-unpacking-highlighted-incorrectly-lp-961496-test
       'new-problem-with-py-temp-directory-lp-965762-test

       'wrong-type-argument-lp-901541-test
       'py-pychecker-run-missing-lp-910783-test
       'py-forward-into-nomenclature-lp-916818-test
       'py-forward-into-nomenclature-jumps-over-CamelCased-words-lp-919540-test
       'py-backward-into-nomenclature-caps-names-lp-919541-test
       'execute-buffer-ipython-fails-lp-928087-test
       'py-indent-comments-nil-ignored-lp-958721-test
       'broken-font-locking-lp-961231-test
       'regression-in-py-execute-region-lp-962227-test
       'py-mark-block-clause-misbehave-lp-949310-test
       'py-mark-clause-misbehave-lp-949310-test
       'py-mark-block-misbehave-lp-949310-test

       'script-buffer-appears-instead-of-python-shell-buffer-lp-957561-test
       'UnicodeEncodeError-lp-550661-test
       'py-shell-complete-lp-328836-test))



;; py-if-name-main-permission-p
(defun py-if-name-main-permission-lp-326620-test (&optional arg)
  (interactive "p")
  (let ((teststring "#! /usr/bin/env python
# -*- coding: utf-8 -*-
def py_if_name_main_permission_test():
    if __name__ == \"__main__\" :
        print(\"__name__ == '__main__' run\")
        return True

    else:
        print(\"__name__ == '__main__' supressed\")
        return False

py_if_name_main_permission_test()
"))
  (py-bug-tests-intern 'py-if-name-main-permission-lp-326620-base arg teststring)))

(defun py-if-name-main-permission-lp-326620-base (arg)
  (when py-debug-p (switch-to-buffer (current-buffer))
	(font-lock-fontify-buffer))
  (goto-char (point-min))
  (let ((py-if-name-main-permission-p t))
    (py-execute-buffer)
    (set-buffer "*Python*")
    (when py-debug-p (switch-to-buffer (current-buffer)))
    (goto-char (point-max))
    (forward-line -1)
    (end-of-line)
    (sit-for 0.2)
    (assert (looking-back "run") nil "py-if-name-main-permission-lp-326620-test #1 failed")))

;; (let (py-if-name-main-permission-p)
;;   (py-execute-buffer)
;;   (set-buffer "*Python*")
;;   ;; (switch-to-buffer (current-buffer))
;;   (goto-char (point-max))
;;   (forward-line -1)
;;   (end-of-line)
;;   (sit-for 0.2)
;;   (or
;;    (assert (looking-back "supressed") nil "py-if-name-main-permission-lp-326620-test #2 failed")
;;    (message "%s" "py-if-name-main-permission-lp-326620-test #2 passed"))))

(defun sexp-commands-lp-328778-test (&optional arg)
  "With ARG greater 1 keep test buffer open.
If no `load-branch-function' is specified, make sure the appropriate branch is loaded. Otherwise default python-mode will be checked.

Reported by Montanaro on 2003-08-05
\[ ... ]
 You can kill balanced expressions on a
 particular line but it's not possible to remove the
 whole of an 'if' or 'while' block."
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
    (py-bug-tests-intern 'sexp-commands-lp-328778 arg teststring)))

(defun sexp-commands-lp-328778 ()
  (let ((size (buffer-size)))
    (goto-char (point-min))
    (forward-line 15)
    (py-kill-clause)
    (or
	(assert (< (buffer-size) size) nil "sexp-commands-lp-328778-test #1 failed")
      (message "%s" "sexp-commands-lp-328778-test #1 passed"))
    (kill-line 1)
    (indent-according-to-mode)
    (or
	(assert (eq (buffer-size) 404) nil "sexp-commands-lp-328778-test #2 failed")
      (message "%s" "sexp-commands-lp-328778-test #2 passed"))
    (forward-line -4)
    (py-kill-block)
    (or
	(assert (eq (buffer-size) 233) nil "sexp-commands-lp-328778-test #3 failed")
      (message "%s" "sexp-commands-lp-328778-test #3 passed"))))


(defun mark-block-region-lp-328806-test (&optional arg)
  "With ARG greater 1 keep test buffer open.
If no `load-branch-function' is specified, make sure the appropriate branch is loaded. Otherwise default python-mode will be checked."
  (interactive "p")
  (let ((teststring "def f():
    \"\"\"
    class blah blah
    \"\"\"
    if a:
        ar_atpt_python_list_roh = ([
                'python-expression',

    #     def ar_thingatpt_write_lists (&optional datei):
                'python-partial-expression',
                'python-statement',
                ])
"))
    (py-bug-tests-intern 'mark-block-region-lp-328806-base arg teststring)))

(defun mark-block-region-lp-328806-base (arg)
  (forward-line -2)
  (py-mark-block)
  (assert (< (region-beginning) (region-end)) nil "mark-block-region-lp-328806-test failed!"))

(defun py-current-defun-lp-328846-test (&optional arg)
  "With ARG greater 1 keep test buffer open.
If no `load-branch-function' is specified, make sure the appropriate branch is loaded. Otherwise default python-mode will be checked."
  (interactive "p")
  (let ((teststring python-mode-teststring))
    (py-bug-tests-intern 'py-current-defun-lp-328846-base arg teststring)))

(defun py-current-defun-lp-328846-base (arg)
  (goto-char 331)
  (assert (string= "f" (py-current-defun)) nil "py-current-defun-lp-328846-test failed"))

(defun cls-pseudo-keyword-lp-328849-test (&optional arg)
  "consider also lp-1340455"
  (interactive "p")
  (let ((teststring "class Foo(object):
    def summat(cls, x):
          .....
    summat = classmethod(summat)
"))
    (py-bug-tests-intern 'cls-pseudo-keyword-lp-328849-base arg teststring)))

(defun cls-pseudo-keyword-lp-328849-base (arg)
  (when py-debug-p (switch-to-buffer (current-buffer)))
  (let (font-lock-verbose)
    (font-lock-mode 1)
    (font-lock-fontify-buffer)
    (goto-char 36)
    (sit-for 0.1)
    (assert (eq (get-char-property (point) 'face) 'py-object-reference-face) nil "cls-pseudo-keyword-lp-328849-test #1 failed ")

    (assert (or
	     (eq 'unspecified (face-attribute 'py-object-reference-face ':inherit))
  	     (eq 'py-pseudo-keyword-face (face-attribute 'py-object-reference-face ':inherit))) nil "cls-pseudo-keyword-lp-328849-test #1 failed ")))

(defun mark-decorators-lp-328851-test (&optional arg)
  "With ARG greater 1 keep test buffer open.
If no `load-branch-function' is specified, make sure the appropriate branch is loaded. Otherwise default python-mode will be checked."
  (interactive "p")
  (let ((teststring "@foo.bar
def baz():
    pass
"))
    (py-bug-tests-intern 'mark-decorators-lp-328851-base arg teststring)))

(defun mark-decorators-lp-328851-base (arg)
  (goto-char 10)
  (py-mark-def t)
  (assert (eq 28 (- (region-end)(region-beginning))) nil "mark-decorators-lp-328851-test failed"))

(defun beg-end-of-defun-lp-303622-test (&optional arg)
  "With ARG greater 1 keep test buffer open.
If no `load-branch-function' is specified, make sure the appropriate branch is loaded. Otherwise default python-mode will be checked."
  (interactive "p")
  (let ((teststring "
class f():
    \"\"\"
    class blah blah
    \"\"\"
    if a:
        ar_atpt_python_list_roh = ([
            'python-expression',

            # def ar_thingatpt_write_lists (&optional datei):
            'python-partial-expression',
            'python-statement',
        ])
"))
    (py-bug-tests-intern 'beg-end-of-defun-lp-303622 arg teststring)))

(defun beg-end-of-defun-lp-303622 ()
  (goto-char 13)
  (py-end-of-def-or-class)
  (sit-for 0.1)
  (assert (eq 275 (point)) nil "beg-end-of-defun-lp-303622-test #1 failed!")
  (beginning-of-defun)
  (sit-for 0.1)
  (assert (eq 2 (point)) nil "beg-end-of-defun-lp-303622-test #2 failed!"))

(defun dq-in-tqs-string-lp-328813-test (&optional arg)
  "With ARG greater 1 keep test buffer open.
If no `load-branch-function' is specified, make sure the appropriate branch is loaded. Otherwise default python-mode will be checked."
  (interactive "p")
  (let ((teststring "
# Bug #328813 (sf1775975)
print(\"\"\" \"Hi!\" I'm a doc string\"\"\")
print(''' 'Hi!' I'm a doc string''')
print(\"\"\" ''' \"Hi!\" I'm a doc string ''' \"\"\")
print(''' \"\"\" \"Hi!\" I'm a doc string \"\"\" ''')
"))
    (py-bug-tests-intern 'dq-in-tqs-string-lp-328813 arg teststring)))

(defun dq-in-tqs-string-lp-328813 ()
  (let ((font-lock-verbose nil))
    (font-lock-mode 1)
    (font-lock-fontify-buffer)
    (goto-char 78)
    (let ((erg (get-char-property (point) 'face)))
      (insert "\"")
      (font-lock-fontify-buffer)
      (assert (eq erg (get-char-property (point) 'face)) nil "dq-in-tqs-string-lp-328813-test failed ")
      (goto-char 122))))

(defun imenu-matches-in-docstring-lp-436285-test (&optional arg)
  "With ARG greater 1 keep test buffer open.
If no `load-branch-function' is specified, make sure the appropriate branch is loaded. Otherwise default python-mode will be checked."
  (interactive "p")
  (let ((teststring "
class foo():
    \"\"\"
    class hello(object):
        def __init__(self):
        ...
    \"\"\"
    pass
"))
    (py-bug-tests-intern 'imenu-matches-in-docstring-lp-436285-base arg teststring)))

(defun imenu-matches-in-docstring-lp-436285-base (arg)
  (goto-char 40)
  (assert (eq (py-beginning-of-def-or-class) 2) nil "imenu-matches-in-docstring-lp-436285-test failed"))

(defun fill-paragraph-problems-lp-710373-test (&optional arg)
  "With ARG greater 1 keep test buffer open.
If no `load-branch-function' is specified, make sure the appropriate branch is loaded. Otherwise default python-mode will be checked."
  (interactive "p")
  (let ((teststring "
    \"\"\"
    triple-quoted string containing \"quotation\" marks.
    triple-quoted string containing \"quotation\" marks.
    triple-quoted string containing \"quotation\" marks.
    triple-quoted string containing \"quotation\" marks.
    triple-quoted string containing \"quotation\" marks.
    \"\"\"
"))
    (fill-paragraph-problems-lp-710373-test-intern arg teststring)))

(defun fill-paragraph-problems-lp-710373-test-intern (arg teststring)
  (let ((tmp-dir "/tmp/")
        (fpp-exec-buffer "fill-paragraph-problems-lp-710373")
        (diff-buffer "fpp-lp-710373-old"))
    (set-buffer (get-buffer-create diff-buffer))
    (erase-buffer)
    (fundamental-mode)
    (insert teststring)
    (write-file (concat tmp-dir diff-buffer))
    (if arg
        (progn
          (set-buffer (get-buffer-create fpp-exec-buffer))
          (switch-to-buffer (current-buffer))
          (erase-buffer)
          (insert teststring)
          (fundamental-mode)
          (fill-paragraph-problems-lp-710373-test-base arg tmp-dir fpp-exec-buffer diff-buffer))
      (with-temp-buffer
        (insert teststring)
        (fill-paragraph-problems-lp-710373-test-base arg tmp-dir fpp-exec-buffer diff-buffer)))))

(defun fill-paragraph-problems-lp-710373-test-base (arg tmp-dir fpp-exec-buffer diff-buffer)
  (goto-char 48)
  (py-fill-paragraph)
  (write-file (concat tmp-dir fpp-exec-buffer))
  (diff (concat tmp-dir fpp-exec-buffer) (concat tmp-dir diff-buffer) "-u")
  (if (featurep 'xemacs)
      (progn
        (set-buffer "*Diff Output*")
        (switch-to-buffer (current-buffer)))
    (set-buffer "*Diff*")
    (sit-for 1)
    (assert (numberp (progn (goto-char (point-min))(search-forward "no differences" nil t 1))) t)
    (message "%s" "fill-paragraph-problems-lp-710373 passed"))
  (set-buffer "fill-paragraph-problems-lp-710373")
  (unless (< 1 arg)
    (set-buffer-modified-p 'nil)
    (kill-buffer (current-buffer))))

(defun tqs-lp-302834-lp-1018994-test (&optional arg)
  "With ARG greater 1 keep test buffer open.
If no `load-branch-function' is specified, make sure the appropriate branch is loaded. Otherwise default python-mode will be checked."
  (interactive "p")
  (let ((teststring "class OrderedDict1(dict):
    \"\"\"
    This implementation of a dictionary keeps track of the order
    in which keys were inserted.

    \"\"\"

    '''I'asdfa'''
"))

    (py-bug-tests-intern 'triple-quoted-string-dq-lp-302834 arg teststring)))

(defun triple-quoted-string-dq-lp-302834 ()
  (let ((font-lock-verbose nil))
    (font-lock-mode 1)
    (font-lock-fontify-buffer)
    (goto-char 78)
    (let ((erg (get-char-property (point) 'face)))
      (insert "\"")
      (font-lock-fontify-buffer)
      (sit-for 0.2)
      (assert (eq erg (get-char-property (point) 'face)) "tqs-lp-302834-lp-1018994-test #1 failed.")
      (goto-char 153)
      (assert (eq erg (get-char-property (point) 'face)) "tqs-lp-302834-lp-1018994-test #2 failed.")
      )))

(defun inbound-indentation-multiline-assignment-lp-629916-test (&optional arg)
  "With ARG greater 1 keep test buffer open.
If no `load-branch-function' is specified, make sure the appropriate branch is loaded. Otherwise default python-mode will be checked."
  (interactive "p")
  (let ((teststring "foo_long_long_long_long = (
    bar_long_long_long_long[
        (x_long_long_long_long == X) &
        (y_long_long_long_long == Y)])
"))
    (py-bug-tests-intern 'inbound-indentation-multiline-assignment-lp-629916 arg teststring)))

(defun inbound-indentation-multiline-assignment-lp-629916 ()
  (when py-debug-p (switch-to-buffer (current-buffer))
	  (font-lock-fontify-buffer)) 
  (let ((py-indent-honors-multiline-listing t))
    (goto-char 33)
    (assert (eq 4 (py-compute-indentation)) nil "inbound-indentation-multiline-assignment-lp-629916-test #1 failed")
    (goto-char 62)
    (assert (eq 8 (current-indentation)) nil "inbound-indentation-multiline-assignment-lp-629916-test #2 failed")))

(defun previous-statement-lp-637955-test (&optional arg)
  "With ARG greater 1 keep test buffer open.
If no `load-branch-function' is specified, make sure the appropriate branch is loaded. Otherwise default python-mode will be checked."
  (interactive "p")
  (let ((teststring "class OrderedDict1(dict):
    \"\"\"
    This implementation of a dictionary keeps track of the order
    in which keys were inserted.
    \"\"\""))
    (py-bug-tests-intern 'previous-statement-lp-637955 arg teststring)))

(defun previous-statement-lp-637955 ()
  (beginning-of-line)
  (py-beginning-of-statement)
  (sit-for 0.1)
  (assert (eq 31 (point)) nil "previous-statement-lp-637955-test failed."))

(defun nested-indents-lp-328775-test (&optional arg)
  "With ARG greater 1 keep test buffer open.
If no `load-branch-function' is specified, make sure the appropriate branch is loaded. Otherwise default python-mode will be checked."
  (interactive "p")
  (let ((teststring "
if x > 0:
    for i in range(100):
        print(i)
    else:
    print(\"All done\")
elif x < 0:
    print(\"x is negative\")
"))
    (py-bug-tests-intern 'nested-indents-lp-328775 arg teststring)))

(defun nested-indents-lp-328775 ()
  (assert (eq 4 (py-compute-indentation)) nil "nested-indents-lp-328775-test #1 failed!")
  (goto-char 41)
  (assert (eq 8 (py-compute-indentation)) nil "nested-indents-lp-328775-test #2 failed!")
  (goto-char 54)
  (assert (eq 4 (py-compute-indentation)) nil "nested-indents-lp-328775-test #3 failed!"))

(defun bullet-lists-in-comments-lp-328782-test (&optional arg)
  "With ARG greater 1 keep test buffer open.
If no `load-branch-function' is specified, make sure the appropriate branch is loaded. Otherwise default python-mode will be checked."
  (interactive "p")
  (let ((teststring))
    (bullet-lists-in-comments-lp-328782-test-intern arg teststring)))

(defun bullet-lists-in-comments-lp-328782-test-intern (&optional arg teststring)
  (let ((font-lock-verbose nil))
    (set-buffer (get-buffer-create "bullet-lists-in-comments-lp-328782-test"))
    (erase-buffer)
    (insert "
## * If the filename is a directory and not a Maildir nor
##   an MH Mailbox, it will be processed as a Mailbox --this bug named here: bullet-lists-in-comments-lp-328782.htm--
##   directory consisting of just .txt and .lorien files.
")
    (when arg (switch-to-buffer (current-buffer)))
    (python-mode)
    (font-lock-mode 1)
    (font-lock-fontify-buffer)
    (goto-char 100)
    (py-fill-paragraph)
    (set-buffer "bullet-lists-in-comments-lp-328782-test")
    (unless (< 1 arg)
      (set-buffer-modified-p 'nil)
      (kill-buffer (current-buffer)))))

(defun imenu-newline-arglist-lp-328783-test (&optional arg)
  "With ARG greater 1 keep test buffer open.
If no `load-branch-function' is specified, make sure the appropriate branch is loaded. Otherwise default python-mode will be checked."
  (interactive "p")
  (let ((teststring "def editor(db, db_name, table_name,
    #api
    dbapi,dbapi_exceptions):
        pass"))
    (py-bug-tests-intern 'imenu-newline-arglist-lp-328783-base arg teststring)))

(defun imenu-newline-arglist-lp-328783-base (arg)
  (goto-char 60)
  (py-beginning-of-def-or-class)
  (assert (eq (point) 1) nil "imenu-newline-arglist-lp-328783-test failed"))

(defun hungry-delete-backwards-lp-328853-test (&optional arg)
  "With ARG greater 1 keep test buffer open.
If no `load-branch-function' is specified, make sure the appropriate branch is loaded. Otherwise default python-mode will be checked."
  (interactive "p")
  (let ((teststring python-mode-teststring))
    (py-bug-tests-intern 'hungry-delete-backwards-lp-328853 arg teststring)))

(defun hungry-delete-backwards-lp-328853 ()
  (goto-char 421)
  (py-hungry-delete-backwards)
  (assert (eq 409 (point)) nil "hungry-delete-backwards-lp-328853-test failed"))

(defun hungry-delete-forward-lp-328853-test (&optional arg)
  "With ARG greater 1 keep test buffer open.
If no `load-branch-function' is specified, make sure the appropriate branch is loaded. Otherwise default python-mode will be checked."
  (interactive "p")
  (let ((teststring python-mode-teststring))
    (py-bug-tests-intern 'hungry-delete-forward-lp-328853 arg teststring)))

(defun hungry-delete-forward-lp-328853 ()
  (goto-char 409)
  (py-hungry-delete-forward)
  (assert (looking-at "#") nil "hungry-delete-backwards test failed"))

(defun UnicodeEncodeError-lp-550661-test (&optional arg)
  (interactive "p")
  (let ((teststring (concat py-test-shebang "
# -\*- coding: utf-8 -\*-
print(u'\\xA9')
"))
	py-smart-indentation)
    (py-bug-tests-intern 'UnicodeEncodeError-lp-550661-base 2 teststring)))

(defun UnicodeEncodeError-lp-550661-base (arg)
  ;; (py-execute-buffer-switch)
  (message "py-smart-indentation: %s" py-smart-indentation)
  (goto-char 48)
  (end-of-line)
  (py-execute-region-switch (line-beginning-position) (point))
  (set-buffer "*Python*")
  (sit-for 0.1 t)
  ;; (switch-to-buffer (current-buffer))
  (assert (or (eq (char-after) 169)(search-backward "©" nil t)(search-forward "©" nil t)) nil "UnicodeEncodeError-lp-550661-test failed"))

(defun indentation-of-continuation-lines-lp-691185-test (&optional arg)
  "With ARG greater 1 keep test buffer open.
If no `load-branch-function' is specified, make sure the appropriate branch is loaded. Otherwise default python-mode will be checked."
  (interactive "p")
  (let ((teststring "    def f(val):
        # current behavior - indent to just after the first space
        a_verry_loonng_variable_nammmee = \\
                                        val
"))
    (py-bug-tests-intern 'indentation-of-continuation-lines-lp-691185 arg teststring)))

(defun indentation-of-continuation-lines-lp-691185 ()
  (let ((py-continuation-offset 2))
    (goto-char 127)
    (delete-horizontal-space)
    (indent-to (py-compute-indentation))
    (assert (eq 10 (current-indentation)) nil "indentation-of-continuation-lines-lp-691185-test failed!")))

(defun goto-beginning-of-tqs-lp-735328-test (&optional arg)
  "With ARG greater 1 keep test buffer open.
If no `load-branch-function' is specified, make sure the appropriate branch is loaded. Otherwise default python-mode will be checked."
  (interactive "p")
  (let ((teststring "class Foo(object):
\"\"\"
This docstring isn't indented, test should pass anyway.
\"\"\"

"))
    (py-bug-tests-intern 'goto-beginning-of-tqs-lp-735328 arg teststring)))

(defun goto-beginning-of-tqs-lp-735328 ()
  (goto-char 84)
  (sit-for 0.2)
  (assert (eq 4 (py-compute-indentation)) nil "goto-beginning-of-tqs-lp-735328-test failed")
  )

(defun class-treated-as-keyword-lp-709478-test (&optional arg)
  "With ARG greater 1 keep test buffer open.
If no `load-branch-function' is specified, make sure the appropriate branch is loaded. Otherwise default python-mode will be checked."
  (interactive "p")
  (let ((teststring "foo = [
    T.div(
        T.tabl(*trows),

        CLASS='blok',)
]
"))
    (py-bug-tests-intern 'class-treated-as-keyword-lp-709478 arg teststring)))

(defun class-treated-as-keyword-lp-709478 ()
  (let ((font-lock-verbose nil))
    (font-lock-fontify-buffer)
    (goto-char 63)
    (sit-for 0.1)
    (assert (eq (get-char-property (point) 'face) 'font-lock-string-face) nil "class-treated-as-keyword-lp-709478d 1th test failed")
    (goto-char 57)
    ;; (assert (if (get-char-property (point) 'face)(eq (get-char-property (point) 'face) 'py-variable-name-face)t) nil "class-treated-as-keyword-lp-709478-test 2th failed")))
    (assert (eq (get-char-property (point) 'face) 'py-variable-name-face) nil "class-treated-as-keyword-lp-709478-test 2th failed")))

(defun fore-00007F-breaks-indentation-lp-328788-test (&optional arg)
  "With ARG greater 1 keep test buffer open.
If no `load-branch-function' is specified, make sure the appropriate branch is loaded. Otherwise default python-mode will be checked."
  (interactive "p")
  (let ((teststring "class a:
    def __init__(self):
        self.StyleSetSpec(self.STYLE_FIELD, \"fore:#00007F\" )
            self.StyleSetSpec(self.STYLE_FIELD, \"fore:#00007F\" )
"))
    (py-bug-tests-intern 'fore-00007F-breaks-indentation-lp-328788 arg teststring)))

(defun fore-00007F-breaks-indentation-lp-328788 ()
  (switch-to-buffer (current-buffer))
  (goto-char 34)
  (sit-for 0.1)
  ;; (debug-on-entry 'py-compute-indentation)
  (assert (eq 8 (py-compute-indentation)) nil "fore-00007F-breaks-indentation-lp-328788-test #1 failed")
  (goto-char 121)
  (assert (eq 8 (py-compute-indentation)) nil "fore-00007F-breaks-indentation-lp-328788-test #2 failed"))

(defun exceptions-not-highlighted-lp-473525-test (&optional arg)
  "With ARG greater 1 keep test buffer open.
If no `load-branch-function' is specified, make sure the appropriate branch is loaded. Otherwise default python-mode will be checked."
  (interactive "p")
  (let ((teststring "excs = (SystemExit, Exception, KeyboardInterrupt)"))
    (py-bug-tests-intern 'exceptions-not-highlighted-lp-473525 arg teststring)))

(defun exceptions-not-highlighted-lp-473525 ()
  (let ((font-lock-verbose nil))
    (goto-char 39)
    (font-lock-fontify-buffer)
    (sit-for 0.1)
    (assert (eq (get-char-property (point) 'face) 'py-exception-name-face) nil "exceptions-not-highlighted-lp-473525-test failed")))

(defun syntaxerror-on-py-execute-region-lp-691542-test (&optional arg)
  (interactive "p")
  (let ((teststring "# -*- coding: utf-8 -*-
print(\"Poet Friedrich Hölderlin\""))
    (py-bug-tests-intern 'syntaxerror-on-py-execute-region-lp-691542-base arg teststring)))

(defun syntaxerror-on-py-execute-region-lp-691542-base (arg)
  (let ((oldbuf (current-buffer))
        erg kill-buffer-query-functions py-switch-to-python)
    (when (buffer-live-p (get-buffer (concat "*" py-which-bufname "*")))
      (when
          (processp (get-process py-which-bufname))

        (set-process-query-on-exit-flag (get-process py-which-bufname) nil))
      (kill-buffer (concat "*" py-which-bufname "*")))
    (py-execute-region (line-beginning-position) (line-end-position))
    (when (interactive-p) (switch-to-buffer (current-buffer)))
    (set-buffer (get-buffer (concat "*" py-which-bufname "*")))
    (assert (or (search-forward "Hölderlin" nil t 1)
                (search-backward "Hölderlin" nil t 1)) nil "syntaxerror-on-py-execute-region-lp-691542-test failed")))

(defun backslashed-continuation-line-indent-lp-742993-test (&optional arg)
  "With ARG greater 1 keep test buffer open.
If no `load-branch-function' is specified, make sure the appropriate branch is loaded. Otherwise default python-mode will be checked."
  (interactive "p")
  (let ((teststring "
# py-continuation-offset: 2
self.last_abc_attr = \\
self.last_xyz_attr = \\
self.last_abc_other = \\
self.last_xyz_other = None

# py-continuation-offset: 4
self.last_abc_attr = \\
self.last_xyz_attr = \\
self.last_abc_other = \\
self.last_xyz_other = None

# py-continuation-offset: 6
self.last_abc_attr = \\
self.last_xyz_attr = \\
self.last_abc_other = \\
self.last_xyz_other = None
"))
    (py-bug-tests-intern 'backslashed-continuation-line-indent-lp-742993 arg teststring)))

(defun backslashed-continuation-line-indent-lp-742993 ()
  (let ((py-continuation-offset 2))
    (goto-char 54)
    (assert (eq 2 (py-compute-indentation)) nil "backslashed-continuation-line-indent-lp-742993-test #1a failed")
    (assert (eq (py-compute-indentation) py-continuation-offset) nil "backslashed-continuation-line-indent-lp-742993-test #1b failed")

    (setq py-continuation-offset 4)
    (goto-char 180)
    (assert (eq 4 (py-compute-indentation)) nil "backslashed-continuation-line-indent-lp-742993-test #2a failed")
    (assert (eq (py-compute-indentation) py-continuation-offset) nil "backslashed-continuation-line-indent-lp-742993-test #2b failed")

    (setq py-continuation-offset 6)
    (goto-char 306)
    (assert (eq 6 (py-compute-indentation)) nil "backslashed-continuation-line-indent-lp-742993-test #3a failed")
    (assert (eq (py-compute-indentation) py-continuation-offset) nil "backslashed-continuation-line-indent-lp-742993-test #3b failed")
    ))

(defun py-decorators-face-lp-744335-test (&optional arg)
  "With ARG greater 1 keep test buffer open.
If no `load-branch-function' is specified, make sure the appropriate branch is loaded. Otherwise default python-mode will be checked."
  (interactive "p")
  (let ((teststring "@foo.bar
def baz():
    pass
"))
    (py-bug-tests-intern 'py-decorators-face-lp-744335 arg teststring)))

(defun py-decorators-face-lp-744335 ()
  (let ((font-lock-verbose nil))
    (goto-char 7)
    (font-lock-fontify-buffer)
    (sit-for 0.1)
    (assert (eq (get-char-property (point) 'face) 'py-decorators-face) nil "py-decorators-face-lp-744335-test failed")))

(defun indent-after-return-lp-745208-test (&optional arg)
  "With ARG greater 1 keep test buffer open.
If no `load-branch-function' is specified, make sure the appropriate branch is loaded. Otherwise default python-mode will be checked."
  (interactive "p")
  (let ((teststring "class FOO\():
    if len(sys.argv)==1:
        usage\()
        sys.exit\()

    def build_extension\(self, ext):

        if ext.name == '_ctypes':
            if not self.configure_ctypes\(ext):
                return

        try:
            build_ext.build_extension\(self, ext)
        except \(CCompilerError, DistutilsError) as why:
            self.announce\('WARNING: building of extension \"%s\"
failed: %s' %
                          \(ext.name, sys.exc_info()\[1]))
            self.failed.append(ext.name)
            return
        # Workaround for Mac OS X: The Carbon-based modules cannot be
        # reliably imported into a command-line Python
        if 'Carbon' in ext.extra_link_args:
            self.announce\(
                'WARNING: skipping import check for Carbon-based
\"%s\"' %
                ext.name)
            return
"))
    (py-bug-tests-intern 'indent-after-return-lp-745208 arg teststring)))

(defun indent-after-return-lp-745208 ()
  (assert (eq 8 (py-compute-indentation)) nil "indent-after-return-lp-745208-test failed"))

(defun keep-assignments-column-lp-748198-test (&optional arg)
  "With ARG greater 1 keep test buffer open.
If no `load-branch-function' is specified, make sure the appropriate branch is loaded. Otherwise default python-mode will be checked."
  (interactive "p")
  (let ((teststring "bar = foo(a=1,
          b=2,
          c=3)
"))
    (py-bug-tests-intern 'keep-assignments-column-lp-748198 arg teststring)))

(defun keep-assignments-column-lp-748198 ()
  (goto-char 45)
  (py-newline-and-indent)
  (assert (eq 0 (current-column)) nil "py-vor test failed"))

(defun indent-triplequoted-to-itself-lp-752252-test (&optional arg)
  "With ARG greater 1 keep test buffer open.
If no `load-branch-function' is specified, make sure the appropriate branch is loaded. Otherwise default python-mode will be checked."
  (interactive "p")
  (let ((teststring "def foo():
    \"\"\"The real foo thing.\n"))
    (py-bug-tests-intern 'indent-triplequoted-to-itself-lp-752252-base arg teststring)))

(defun indent-triplequoted-to-itself-lp-752252-base (arg)
  (sit-for 0.1)
  (when py-debug-p (switch-to-buffer (current-buffer))
	(font-lock-fontify-buffer))
  ;; (message "(py-compute-indentation): %s" (py-compute-indentation))
  (assert (eq 4 (py-compute-indentation)) nil "indent-triplequoted-to-itself-lp-752252-test failed"))

(defun multiline-listings-indent-lp-761946-test (&optional arg)
  (interactive "p")
  (let ((teststring "def foo():
    do_something_first(
        a=1,
                       b=2,
"))
    (py-bug-tests-intern 'multiline-listings-indent-lp-761946-base arg teststring)))

(defun multiline-listings-indent-lp-761946-base (arg)
  (goto-char 49)
  (assert (eq 8 (py-compute-indentation)) nil "multiline-listings-indent-lp-761946-test failed"))

(defun new-page-char-causes-loop-lp-762498-test (&optional arg)
  (interactive "p")
  (let ((teststring "class Foo:
    def baz(self):


"))
    (py-bug-tests-intern 'new-page-char-causes-loop-lp-762498-base arg teststring)))

(defun new-page-char-causes-loop-lp-762498-base (arg)
  (goto-char 31)
  (assert (eq 8 (py-compute-indentation)) "new-page-char-causes-loop-lp-762498-test failed"))

(defun nested-dicts-indent-lp-763756-test (&optional arg)
  (interactive "p")
  (let ((teststring "feature_operation_matrix = {
    \"character\": {
        \"kill\": \"{ctrl-k}\",{
            }
        }
    }
))
"))
    (py-bug-tests-intern 'nested-dicts-indent-lp-763756-base arg teststring)))

(defun nested-dicts-indent-lp-763756-base (arg)
  (let ((py-indent-honors-multiline-listing nil))
    (goto-char 30)
    (assert (eq 4 (py-compute-indentation)) nil "nested-dicts-indent-lp-763756-test failed")
    (goto-char 49)
    (assert (eq 8 (py-compute-indentation)) nil "nested-dicts-indent-lp-763756-test failed")
    (forward-line 1)
    (assert (eq 12 (py-compute-indentation)) nil "nested-dicts-indent-lp-763756-test failed")))

(defun bad-indent-after-except-lp-771289-test (&optional arg)
  (interactive "p")
  (let ((teststring "def foo():
    try:
        baz()
    except ValueError:
"))
    (py-bug-tests-intern 'bad-indent-after-except-lp-771289-base arg teststring)))

(defun bad-indent-after-except-lp-771289-base (arg)
  (assert (eq 8 (py-compute-indentation)) nil "bad-indent-after-except-lp-771289-test failed"))

(defun indent-open-paren-not-last-lp-771291-test (&optional arg)
  (interactive "p")
  (let ((teststring "

# Put point after the comma on the last line and hit return. You
# end up in column 8 (i.e. under the 'g' in 'thing') when you
# should end up in column 20 (under the 'w' in 'with_something').
# Note that this is a different case than previously reported,
# where the open paren was the last thing on the line. When the
# open paren is *not* the last thing on the line, the next line's
# indentation should line up under the first non-whitespace
# character following the open paren.

def foo():
    thing = call_it(with_something,
"))
    (py-bug-tests-intern 'indent-open-paren-not-last-lp-771291-base arg teststring)))

(defun indent-open-paren-not-last-lp-771291-base (arg)
  (assert (eq 20 (py-compute-indentation)) nil "indent-open-paren-not-last-lp-771291-test failed"))

(defun wrong-indent-after-else-lp-772610-test (&optional arg)
  (interactive "p")
  (let ((teststring "if True:
    pass
else:
"))
    (py-bug-tests-intern 'wrong-indent-after-else-lp-772610-base arg teststring)))

(defun wrong-indent-after-else-lp-772610-base (arg)
  (assert (eq 4 (py-compute-indentation)) nil "wrong-indent-after-else-lp-772610-test failed"))

(defun except-indents-wrong-lp-784432-test (&optional arg)
  (interactive "p")
  (let ((teststring "try:
    block1
except:
    block2"))
    (py-bug-tests-intern 'except-indents-wrong-lp-784432-base arg teststring)))

(defun except-indents-wrong-lp-784432-base (arg)
  (goto-char 17)
  (assert (eq 0 (py-compute-indentation)) nil "except-indents-wrong-lp-784432-test #1 failed")
  (goto-char 25)
  (assert (eq 4 (py-compute-indentation)) nil "except-indents-wrong-lp-784432-test #2 failed"))

(defun indent-explicitly-set-in-multiline-tqs-lp-784225-test (&optional arg)
  (interactive "p")
  (let ((teststring "def foo():
    with bar('x', \"\"\"
        [hello]
"
                    ))
    (py-bug-tests-intern 'indent-explicitly-set-in-multiline-tqs-lp-784225-base arg teststring)))

(defun indent-explicitly-set-in-multiline-tqs-lp-784225-base (arg)
  (assert (eq 8 (py-compute-indentation)) nil "indent-explicitly-set-in-multiline-tqs-lp-784225-test failed"))

(defun unbalanced-parentheses-lp-784645-test (&optional arg)
  (interactive "p")
  (let ((teststring "def foo():
    something()

    another(
"))
    (py-bug-tests-intern 'unbalanced-parentheses-lp-784645-base arg teststring)))

(defun unbalanced-parentheses-lp-784645-base (arg)
  (goto-char 28)
  (assert (eq 4 (py-compute-indentation)) nil "unbalanced-parentheses-lp-784645-test failed"))

(defun explicitly-indent-in-list-lp-785018-test (&optional arg)
  (interactive "p")
  (let ((teststring "def foo():
    with bar('x',
        [hello]
"
                    ))
    (py-bug-tests-intern 'explicitly-indent-in-list-lp-785018-base arg teststring)))

(defun explicitly-indent-in-list-lp-785018-base (arg)
  (assert (eq 8 (py-compute-indentation)) nil "explicitly-dedented-in-list-lp-784225-test failed"))

(defun explicit-backslashed-continuation-line-indent-lp-785091-test (&optional arg)
  (interactive "p")
  (let ((teststring "        a_verry_loonng_variable_nammmee = \\
                                        val \\
"))
    (py-bug-tests-intern 'explicit-backslashed-continuation-line-indent-lp-785091-base arg teststring)))

(defun explicit-backslashed-continuation-line-indent-lp-785091-base (arg)
  (assert (eq 40 (py-compute-indentation)) nil "explicit-backslashed-continuation-line-indent-lp-785091  test failed"))

(defun indentation-error-lp-795773-test (&optional arg)
  (interactive "p")
  (let ((teststring "class MailTransportAgentAliases:
    \"\"\"Utility for generating all the aliases of a mailing
list.\"\"\"

    implements(IMailTransportAgentAliases)

    def aliases(self, mlist):
        \"\"\"See `IMailTransportAgentAliases`.\"\"\"
        # Always return
        yield mlist.posting_address
        for destination in SUBDESTINATIONS:
            yield '{0}-{1}@{2}'.format(mlist.list_name,
                                             destination,
                                             mlist.host_name)
"))
    (py-bug-tests-intern 'indentation-error-lp-795773-base arg teststring)))

(defun indentation-error-lp-795773-base (arg)
  (goto-char 385)
  (assert (eq 39 (py-compute-indentation)) nil "indentation-error-lp-795773-test failed"))

(defun class-highlighted-as-keywords-lp-798287-test (&optional arg)
  (interactive "p")
  (let ((teststring "class X:
    pass

# Everything is highlighted as a keyword.
"))
    (py-bug-tests-intern 'class-highlighted-as-keywords-lp-798287-base arg teststring)))

(defun class-highlighted-as-keywords-lp-798287-base (arg)
  (let ((font-lock-verbose nil))
    (goto-char 7)
    (font-lock-fontify-buffer)
    ;; (sit-for 0.1)
    (assert (eq (get-char-property (point) 'face) 'py-class-name-face) nil "class-highlighted-as-keywords-lp-798287-test failed")))

(defun indent-function-arglist-lp-800088-test (&optional arg)
  (interactive "p")
  (let ((teststring "def long_function_name(
        var_one, var_two, var_three,
        var_four):
     print(var_one)
"))
    (py-bug-tests-intern 'indent-function-arglist-lp-800088-base arg teststring)))

(defun indent-function-arglist-lp-800088-base (arg)
  (goto-char 25)
  (let ((py-indent-offset 4))
    (assert (eq 8 (py-compute-indentation)) nil "indent-function-arglist-lp-800088-test failed")))

(defun python-mode-hangs-lp-801780-test (&optional arg)
  (interactive "p")
  (let ((teststring "@jit.unroll_safe
def pushrevvalues(self, n, values_w): # n should be len(values_w)
    make_sure_not_resized(values_w)
    while True:
        n -= 1
        if n < 0:
            break
        self.pushvalue(values_w[n])
"))
    (py-bug-tests-intern 'python-mode-hangs-lp-801780-base arg teststring)))

(defun python-mode-hangs-lp-801780-base (arg)
  (assert (eq 18 (py-beginning-of-def-or-class)) nil "python-mode-hangs-lp-801780-test failed"))

(defun stops-backslashed-line-lp-802504-test (&optional arg)
  (interactive "p")
  (let ((teststring (concat py-test-shebang "
# -*- coding: utf-8 -*-

if bar == 1 or bar == 2 or bar == 3 or bar == 4 or bar == 5 or bar == 6 or bar == 7 \\
  or bar == 8 or bar == 9 or bar == 10 or bar == 11 or bar == 12 or bar == 13 \\
  or bar == 14 or bar == 15 or bar == 16 or bar == 17 or bar == 18:
")))
    (py-bug-tests-intern 'stops-backslashed-line-lp-802504-base arg teststring)))

(defun stops-backslashed-line-lp-802504-base (arg)
  (goto-char 49)
  (assert (eq 282 (py-end-of-statement)) nil "stops-backslashed-line-lp-802504-test failed"))

(defun stops-backslashed-line-lp-802504-test2 (&optional arg)
  (interactive "p")
  (let ((teststring (concat py-test-shebang "
# -*- coding: utf-8 -*-

if x>1 and x<100 and y>1 and y<200:
  if bar == 1 or bar == 2 or bar == 3 or bar == 4 or bar == 5 or bar == 6 or bar == 7 \\
  or bar == 8 or bar == 9 or bar == 10 or bar == 11 or bar == 12 or bar == 13 or \\
")))
    (py-bug-tests-intern 'stops-backslashed-line2-lp-802504-base arg teststring)))

(defun stops-backslashed-line2-lp-802504-base (arg)
  (assert (eq 87 (py-beginning-of-statement)) nil "stops-backslashed-line-lp-802504-test failed"))

(defun python-mode-slow-lp-803275-test (&optional arg)
  (interactive "p")
  (let ((teststring "# commands.py - command processing for mercurial
#
# Copyright 2005-2007 Matt Mackall <mpm@selenic.com>
#
# This software may be used and distributed according to the terms of the
# GNU General Public License version 2 or any later version.

from node import hex, bin, nullid, nullrev, short
from lock import release
from i18n import _, gettext
import os, re, difflib, time, tempfile, errno
import hg, scmutil, util, revlog, extensions, copies, error, bookmarks
import patch, help, url, encoding, templatekw, discovery
import archival, changegroup, cmdutil, hbisect
import sshserver, hgweb, hgweb.server, commandserver
import merge as mergemod
import minirst, revset, fileset
import dagparser, context, simplemerge
import random, setdiscovery, treediscovery, dagutil

table = {}

command = cmdutil.command(table)

# common command options

globalopts = [
    ('R', 'repository', '',
     _('repository root directory or name of overlay bundle file'),
     _('REPO')),
    ('', 'cwd', '',
     _('change working directory'), _('DIR')),
    ('y', 'noninteractive', None,
     _('do not prompt, assume \\'yes\\' for any required answers')),
    ('q', 'quiet', None, _('suppress output')),
    ('v', 'verbose', None, _('enable additional output')),
    ('', 'config', [],
     _('set/override config option (use \\'section.name=value\\')'),
     _('CONFIG')),
    ('', 'debug', None, _('enable debugging output')),
    ('', 'debugger', None, _('start debugger')),
    ('', 'encoding', encoding.encoding, _('set the charset encoding'),
     _('ENCODE')),
    ('', 'encodingmode', encoding.encodingmode,
     _('set the charset encoding mode'), _('MODE')),
    ('', 'traceback', None, _('always print a traceback on exception')),
    ('', 'time', None, _('time how long the command takes')),
    ('', 'profile', None, _('print command execution profile')),
    ('', 'version', None, _('output version information and exit')),
    ('h', 'help', None, _('display help and exit')),
]

dryrunopts = [('n', 'dry-run', None,
               _('do not perform actions, just print output'))]

remoteopts = [
    ('e', 'ssh', '',
     _('specify ssh command to use'), _('CMD')),
    ('', 'remotecmd', '',
     _('specify hg command to run on the remote side'), _('CMD')),
    ('', 'insecure', None,
     _('do not verify server certificate (ignoring web.cacerts config)')),
]

walkopts = [
    ('I', 'include', [],
     _('include names matching the given patterns'), _('PATTERN')),
    ('X', 'exclude', [],
     _('exclude names matching the given patterns'), _('PATTERN')),
]

commitopts = [
    ('m', 'message', '',
     _('use text as commit message'), _('TEXT')),
    ('l', 'logfile', '',
     _('read commit message from file'), _('FILE')),
]

commitopts2 = [
    ('d', 'date', '',
     _('record the specified date as commit date'), _('DATE')),
    ('u', 'user', '',
     _('record the specified user as committer'), _('USER')),
]

templateopts = [
    ('', 'style', '',
     _('display using template map file'), _('STYLE')),
    ('', 'template', '',
     _('display with template'), _('TEMPLATE')),
]

logopts = [
    ('p', 'patch', None, _('show patch')),
    ('g', 'git', None, _('use git extended diff format')),
    ('l', 'limit', '',
     _('limit number of changes displayed'), _('NUM')),
    ('M', 'no-merges', None, _('do not show merges')),
    ('', 'stat', None, _('output diffstat-style summary of changes')),
] + templateopts

diffopts = [
    ('a', 'text', None, _('treat all files as text')),
    ('g', 'git', None, _('use git extended diff format')),
    ('', 'nodates', None, _('omit dates from diff headers'))
]

diffopts2 = [
    ('p', 'show-function', None, _('show which function each change is in')),
    ('', 'reverse', None, _('produce a diff that undoes the changes')),
    ('w', 'ignore-all-space', None,
     _('ignore white space when comparing lines')),
    ('b', 'ignore-space-change', None,
     _('ignore changes in the amount of white space')),
    ('B', 'ignore-blank-lines', None,
     _('ignore changes whose lines are all blank')),
    ('U', 'unified', '',
     _('number of lines of context to show'), _('NUM')),
    ('', 'stat', None, _('output diffstat-style summary of changes')),
]

similarityopts = [
    ('s', 'similarity', '',
     _('guess renamed files by similarity (0<=s<=100)'), _('SIMILARITY'))
]

subrepoopts = [
    ('S', 'subrepos', None,
     _('recurse into subrepositories'))
]

# Commands start here, listed alphabetically

@command('^add',
    walkopts + subrepoopts + dryrunopts,
    _('[OPTION]... [FILE]...'))
def add(ui, repo, \*pats, \*\*opts):
    \"\"\"add the specified files on the next commit

    Schedule files to be version controlled and added to the
    repository.

    The files will be added to the repository at the next commit. To
    undo an add before that, see :hg:`forget`.

    If no names are given, add all files to the repository.

    .. container:: verbose

       An example showing how new (unknown) files are added
       automatically by :hg:`add`::

         \$ ls
         foo.c
         \$ hg status
         ? foo.c
         \$ hg add
         adding foo.c
         \$ hg status
         A foo.c

    Returns 0 if all files are successfully added.
    \"\"\"

    m = scmutil.match(repo[None], pats, opts)
    rejected = cmdutil.add(ui, repo, m, opts.get('dry_run'),
                           opts.get('subrepos'), prefix=\"\")
    return rejected and 1 or 0
"))
    (py-bug-tests-intern 'python-mode-slow-lp-803275-base arg teststring)))

(defun python-mode-slow-lp-803275-base (arg)
  (goto-char 1)
  (sit-for 0.1)
  (assert (eq 5430 (py-end-of-def-or-class)) nil "python-mode-slow-lp-803275-test failed"))

(defun master-file-not-honored-lp-794850-test (&optional arg)
  (interactive "p")
  (let ((teststring (concat py-test-shebang "
 # -*- coding: utf-8 -*-

# Local Variables:
# py-master-file: \"/usr/tmp/my-master.py\"
# End:

print(\"master-file is executed\")
")))
    (py-bug-tests-intern 'master-file-not-honored-lp-794850-base arg teststring)))

(defun master-file-not-honored-lp-794850-base (arg)
  (let ((oldbuf (current-buffer)))
    (save-excursion
      (set-buffer (get-buffer-create "test-master.py"))
      (erase-buffer)
      (insert "#! /usr/bin/env python
 # -*- coding: utf-8 -*-

print(\"Hello, I'm your master!\")
")
      (write-file "/var/tmp/my-master.py"))
    (set-buffer oldbuf)
    (unwind-protect
        (py-execute-buffer)
      (when (file-readable-p "/var/tmp/my-master.py") (delete-file "/var/tmp/my-master.py")))))

(defun py-variable-name-face-lp-798538-test (&optional arg)
  (interactive "p")
  (let ((teststring "class Foo(object):
    def summat(cls, x):
          .....
    summat = classmethod(summat)
"))
    (py-bug-tests-intern 'py-variable-name-face-lp-798538-base arg teststring)))

(defun py-variable-name-face-lp-798538-base (arg)
  (let ((font-lock-verbose nil))
    (font-lock-mode 1)
    (font-lock-fontify-buffer)
    (goto-char 64)
    (sit-for 0.1)
    (assert (eq (get-char-property (point) 'face) 'py-variable-name-face) nil "py-variable-name-face-lp-798538-test failed ")))

(defun colon-causes-error-lp-818665-test (&optional arg)
  (interactive "p")
  (let ((teststring (concat py-test-shebang "
 # -*- coding: utf-8 -*-

print(\"Hello!\")
")))
    (py-bug-tests-intern 'colon-causes-error-lp-818665-base arg teststring)))

(defun colon-causes-error-lp-818665-base (arg)
  (insert ":")
  (forward-char -1)
  (assert (looking-at ":") nil "colon-causes-error-lp-818665-test failed"))

(defun if-indentation-lp-818720-test (&optional arg)
  (interactive "p")
  (let ((teststring (concat py-test-shebang "
 # -*- coding: utf-8 -*-

class X():
    def __init__( self ):
        self.lookup = {}

    def y( self, p ):
        p = p.foo()
        if p in self.lookup:
            return self.lookup[ foo ]
        else:
            return None
")))
    (py-bug-tests-intern 'if-indentation-lp-818720-base arg teststring)))

(defun if-indentation-lp-818720-base (arg)
  (goto-char 196)
  (assert (eq 12 (py-compute-indentation)) nil "if-indentation-lp-818720-test failed"))

(defun closing-parenthesis-indent-lp-821820-test (&optional arg)
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
    (py-bug-tests-intern 'closing-parenthesis-indent-lp-821820-base arg teststring)))

(defun closing-parenthesis-indent-lp-821820-base (arg)
  (let ((py-closing-list-dedents-bos t))
    (forward-line -1)
    (assert (eq 4 (py-compute-indentation)) nil "closing-parenthesis-indent-lp-821820-test failed")))

(defun py-indent-line-lp-822532-test (&optional arg)
  (interactive "p")
  (let ((teststring "
if x > 0:
    for i in range(100):
        print(i)
    else:
    print(\"All done\")
elif x < 0:
    print(\"x is negative\")
"))
    (py-bug-tests-intern 'py-indent-line-lp-822532-base arg teststring)))

(defun py-indent-line-lp-822532-base (arg)
  (goto-char 54)
  (assert (eq 4 (py-compute-indentation)) nil "py-indent-line-lp-822532-test failed"))

(defun indent-honor-arglist-whitespaces-lp-822540-test (&optional arg)
  (interactive "p")
  (let ((teststring (concat py-test-shebang "
# -*- coding: utf-8 -*-

abc( ghi,
    jkl
")))
    (py-bug-tests-intern 'indent-honor-arglist-whitespaces-lp-822540-base arg teststring)))

(defun indent-honor-arglist-whitespaces-lp-822540-base (arg)
  (forward-line -1)
  (assert (eq 5 (py-compute-indentation)) nil "indent-honor-arglist-whitespaces-lp-822540-test failed"))

(defun comments-indent-honor-setting-lp-824427-test (&optional arg)
  (interactive "p")
  (let ((teststring (concat py-test-shebang "
# -\*- coding: utf-8 -\*-

if __name__ == '__main__':
    from foo import \*
    foo([\"baz\"]) # list of foo's development directories

# limitations:
#
#   Some comments on limitations:
# asdf
")))
    (py-bug-tests-intern 'comments-indent-honor-setting-lp-824427-base arg teststring)))

(defun comments-indent-honor-setting-lp-824427-base (arg)
  (goto-char 206)
  (assert (eq 0 (py-compute-indentation)) nil "comments-indent-honor-setting-lp-824427-test failed"))

(defun infinite-loop-after-tqs-lp-826044-test (&optional arg)
  (interactive "p")
  (let ((teststring "\"\"\"
hey
\"\"\"
"))
    (py-bug-tests-intern 'infinite-loop-after-tqs-lp-826044-base arg teststring)))

(defun infinite-loop-after-tqs-lp-826044-base (arg)
  (assert (eq 0 (py-newline-and-indent)) nil "infinite-loop-after-tqs-lp-826044-test failed"))

(defun closing-list-lp-826144-test (&optional arg)
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
    (py-bug-tests-intern 'closing-list-lp-826144-base arg teststring)))

(defun closing-list-lp-826144-base (arg)
  (let (py-closing-list-dedents-bos)
    (goto-char (point-min))
    (re-search-forward ") *$" nil t 1)
    (assert (eq 12 (py-compute-indentation)) nil "closing-list-lp-826144-test #1 failed")
    (re-search-forward ") *$" nil t 1)
    (assert (eq 8 (py-compute-indentation)) nil "closing-list-lp-826144-test #2 failed")
    (setq py-closing-list-dedents-bos t)
    (goto-char (point-min))
    (re-search-forward ") *$" nil t 1)
    (assert (eq 8 (py-compute-indentation)) nil "closing-list-lp-826144-test #1 failed")
    (re-search-forward ") *$" nil t 1)
    (assert (eq 4 (py-compute-indentation)) nil "closing-list-lp-826144-test #2 failed")))

(defun py-electric-comment-add-space-lp-828398-test (&optional arg)
  (interactive "p")
  (let ((teststring ""))
    (py-bug-tests-intern 'py-electric-comment-add-space-lp-828398-base arg teststring)))

(defun py-electric-comment-add-space-lp-828398-base (arg)
  (let ((py-electric-comment-add-space-p nil))
    (when py-debug-p (switch-to-buffer (current-buffer)))
    (py-electric-comment 1)
    (assert (looking-back "#") nil "py-electric-comment-add-space-lp-828398-test failed")))

(defun py-electric-comment-add-space-t-lp-828398-test (&optional arg)
  (interactive "p")
  (let ((teststring ""))
    (py-bug-tests-intern 'py-electric-comment-add-space-t-lp-828398-base arg teststring)))

(defun py-electric-comment-add-space-t-lp-828398-base (arg)
  (let ((py-electric-comment-add-space-p t))
    (py-electric-comment 1)
    (assert (looking-back " ") nil "py-electric-comment-add-space-lp-828398-test failed")))

(defun execute-indented-code-lp-828314-test (&optional arg)
  (interactive "p")
  (let ((teststring "if __name__ == \"__main__\":
    print(\"hello, I'm the execute-indented-code-lp-828314-test\")
"))
    (py-bug-tests-intern 'execute-indented-code-lp-828314-base 2 teststring)))

(defun execute-indented-code-lp-828314-base (arg)
  (let ((debug-on-error t)
	(py-shell-name "python"))
    (goto-char 28)
    (py-execute-line-python)
    (set-buffer "*Python*")
    (goto-char (point-max))
    (assert (search-backward "execute-indented-code-lp-828314-test") nil "execute-indented-code-lp-828314-test failed")))

(defun wrong-indentation-of-function-arguments-lp-840891-test (&optional arg)
  (interactive "p")
  (let ((teststring "abdc = foo(a=1,
           b=2,
    c=3)
"))
    (py-bug-tests-intern 'wrong-indentation-of-function-arguments-lp-840891-base arg teststring)))

(defun wrong-indentation-of-function-arguments-lp-840891-base (arg)
  (goto-char 38)
  (assert (eq 11 (py-compute-indentation)) nil "wrong-indentation-of-function-arguments-lp-840891-test failed"))

(defun py-hungry-delete-backwards-needs-cc-lp-850595-test (&optional arg)
  (interactive "p")
  (let ((teststring ""))
    (py-bug-tests-intern 'py-hungry-delete-backwards-needs-cc-lp-850595-base arg teststring)))

(defun py-hungry-delete-backwards-needs-cc-lp-850595-base (arg)
  (assert (functionp 'c-hungry-delete-backwards) nil "py-hungry-delete-backwards-needs-cc-lp-850595-test failed"))

(defun wrong-guess-for-py-indent-offset-lp-852052-test (&optional arg)
  (interactive "p")
  (let ((teststring "# The indent offset shouldn't be guessed from backslash
# continuations. I have

from long.pkg.name import long, list, of, \\
     class_and_function, and, function, names

# (note there are five spaces before \"class\", to match with the
# start of the pkg name.)

# Since the indent of backlash-continued lines has no meaning for
# code, it should not be considered.
"))
    (py-bug-tests-intern 'wrong-guess-for-py-indent-offset-lp-852052-base arg teststring)))

(defun wrong-guess-for-py-indent-offset-lp-852052-base (arg)
  (goto-char 126)
  (assert (eq 4 (py-guess-indent-offset)) nil "wrong-guess-for-py-indent-offset-lp-852052-test failed"))

(defun indent-match-import-pkg-lp-852500-test (&optional arg)
  (interactive "p")
  (let (py-smart-indentation
        (teststring "from long.pkg.name import long, list, of, \\
     class_and_function, names

# (note there are five spaces before \"class\", to match with the
# start of the pkg name.)
"))
    (py-bug-tests-intern 'indent-match-import-pkg-lp-852500-base arg teststring)))

(defun indent-match-import-pkg-lp-852500-base (arg)
  (goto-char 45)
  (assert (eq 5 (py-compute-indentation)) nil "indent-match-import-pkg-lp-852500-test failed"))

(defun py-shift-line-when-no-region-lp-855565-test (&optional arg)
  (interactive "p")
  (let ((teststring (concat py-test-shebang "
# -*- coding: utf-8 -*-

if foo:
    print")))
    (py-bug-tests-intern 'py-shift-line-when-no-region-lp-855565-base arg teststring)))

(defun py-shift-line-when-no-region-lp-855565-base (arg)
  (goto-char 58)
  (assert (eq 8 (py-shift-right 1)) nil "py-shift-line-when-no-region-lp-855565-test failed"))

(defun highlighting-in-multiline-function-call-arguments-lp-856833-test (&optional arg)
  (interactive "p")
  (let ((teststring (concat py-test-shebang "
# -\*- coding: utf-8 -\*-

newObj = SomeClassWithManyManyArgs (param0 = val0,
    param1 = val1,
    param2 = val2, param3 = val3)
")))
    (py-bug-tests-intern 'highlighting-in-multiline-function-call-arguments-lp-856833-base arg teststring)))

(defun highlighting-in-multiline-function-call-arguments-lp-856833-base (arg)
  (font-lock-fontify-buffer)
  (goto-char 80)
  ;; (goto-char 106)
  (assert (eq (get-char-property (point) 'face) nil) nil "highlighting-in-multiline-function-call-arguments-lp-856833 test failed "))

(defun py-shift-preserve-active-region-lp-857837-test (&optional arg)
  (interactive "p")
  (let ((teststring (concat py-test-shebang "
# -\*- coding: utf-8 -\*-

print('hello')
print('world')
")))
    (py-bug-tests-intern 'py-shift-preserve-active-region-lp-857837-base arg teststring)))

(defun py-shift-preserve-active-region-lp-857837-base (arg)
  (goto-char 49)
  (assert nil "py-shift-preserve-active-region-lp-857837-test failed"))

(defun variable-highlighted-on-LHS-of-eq-lp-858304-test (&optional arg)
  (interactive "p")
  (let ((teststring (concat py-test-shebang "
# -*- coding: utf-8 -*-

if someVar == 5:
    doSomething()
")))
    (py-bug-tests-intern 'variable-highlighted-on-LHS-of-eq-lp-858304-base arg teststring)))

(defun variable-highlighted-on-LHS-of-eq-lp-858304-base (arg)
  (goto-char 55)
  (assert (eq (get-char-property (point) 'face) nil) nil "variable-highlighted-on-LHS-of-eq-lp-858304-test failed"))

(defun indent-guessing-lp-858040-test (&optional arg)
  (interactive "p")
  (let ((teststring (concat py-test-shebang "
# -*- coding: utf-8 -*-

some_longer_call(arguments,
         arguments)
")))
    (py-bug-tests-intern 'indent-guessing-lp-858040-base arg teststring)))

(defun indent-guessing-lp-858040-base (arg)
  (goto-char 40)
  (assert (eq 4 py-indent-offset) nil "indent-guessing-lp-858040-test failed"))

(defun indentation-of-from-import-continuation-lines-lp-858041-test (&optional arg)
  (interactive "p")
  (let ((teststring (concat py-test-shebang "
# -*- coding: utf-8 -*-

from nicos import session
from nicos import status, loggers
from nicos.utils import DeviceMeta, Param, Override, Value, getVersions, \\
usermethod, tupleof, floatrange, any, none_or

")))
    (py-bug-tests-intern 'indentation-of-from-import-continuation-lines-lp-858041-base arg teststring)))

(defun indentation-of-from-import-continuation-lines-lp-858041-base (arg)
  (goto-char 184)
  (assert (eq 5 (py-compute-indentation)) nil "indentation-of-from-import-continuation-lines-lp-858041-test failed"))

(defun indentation-after-one-line-suites-lp-858044-test (&optional arg)
  (interactive "p")
  (let ((teststring (concat py-test-shebang "
# -*- coding: utf-8 -*-

if foo: return

")))
    (py-bug-tests-intern 'indentation-after-one-line-suites-lp-858044-base arg teststring)))

(defun indentation-after-one-line-suites-lp-858044-base (arg)
  (goto-char 64)
  (assert (eq 0 (py-compute-indentation)) nil "indentation-after-one-line-suites-lp-858044-test failed"))

(defun py-compute-indentation-wrong-at-eol-lp-858043-test (&optional arg)
  (interactive "p")
  (let ((teststring (concat py-test-shebang "
# -*- coding: utf-8 -*-

if maxdepth == 0 or depth < maxdepth:
      item += build_toc(sectionnode, depth+1)
")))
    (py-bug-tests-intern 'py-compute-indentation-wrong-at-eol-lp-858043-base arg teststring)))

(defun py-compute-indentation-wrong-at-eol-lp-858043-base (arg)
  (setq py-smart-indentation nil)
  (setq py-indent-offset 4)
  (goto-char 132)
  (assert (eq 4 (py-compute-indentation)) nil "py-compute-indentation-wrong-at-eol-lp-858043-test failed"))

(defun comment-indentation-level-lp-869854-test (&optional arg)
  (interactive "p")
  (let ((teststring (concat py-test-shebang "
# -*- coding: utf-8 -*-

def foo():
    def bar():
        x = 1
# asdf

")))
    (py-bug-tests-intern 'comment-indentation-level-lp-869854-base arg teststring)))

(defun comment-indentation-level-lp-869854-base (arg)
  (goto-char 104)
  (assert (eq 0 (py-compute-indentation))  nil "comment-indentation-level-lp-869854-test failed"))

(defun indentation-wrong-after-multi-line-parameter-list-lp-871698-test (&optional arg)
  (interactive "p")
  (let ((teststring (concat py-test-shebang "
# -*- coding: utf-8 -*-

def foo(bar, baz):
    # indenation as it should be

def foo(bar,
        baz):
# this is the next indentation line (none)

class Foo:
    def bar(biz,
            baz):
    # indentation here after newline

")))
    (py-bug-tests-intern 'indentation-wrong-after-multi-line-parameter-list-lp-871698-base arg teststring)))

(defun indentation-wrong-after-multi-line-parameter-list-lp-871698-base (arg)
  (goto-char 68)
  (assert (eq 4 (py-compute-indentation)) nil "indentation-wrong-after-multi-line-parameter-list-lp-871698-test #1 failed")
  (goto-char 115)
  (assert (eq 8 (py-compute-indentation)) nil "indentation-wrong-after-multi-line-parameter-list-lp-871698-test #2 failed")
  (goto-char 201)
  (assert (eq 12 (py-compute-indentation)) nil "indentation-wrong-after-multi-line-parameter-list-lp-871698-test #3 failed")
  (goto-char 223)
  (assert (eq 8 (py-compute-indentation)) nil "indentation-wrong-after-multi-line-parameter-list-lp-871698-test #4 failed")
  )

(defun no-indent-after-continue-lp-872676-test (&optional arg)
  (interactive "p")
  (let ((teststring (concat py-test-shebang "
# -*- coding: utf-8 -*-

def foo():
    for i in range(10):
        if i == 7:
            continue
        if i == 9

")))
    (py-bug-tests-intern 'no-indent-after-continue-lp-872676-base arg teststring)))

(defun no-indent-after-continue-lp-872676-base (arg)
  (goto-char 141)
  (assert (eq 8 (py-compute-indentation)) nil "no-indent-after-continue-lp-872676-test failed"))

(defun indent-after-inline-comment-lp-873372-test (&optional arg)
  (interactive "p")
  (let ((teststring (concat py-test-shebang "
# -*- coding: utf-8 -*-

foo = True # the next line is indented incorrectly
           # to here
")))
    (py-bug-tests-intern 'indent-after-inline-comment-lp-873372.txt-base arg teststring)))

(defun indent-after-inline-comment-lp-873372.txt-base (arg)
  (let ((py-indent-honors-inline-comment t))
    (goto-char 111)
    (assert (eq 11 (py-compute-indentation)) nil "indent-after-inline-comment-lp-873372-test #1 failed"))
  (let (py-indent-honors-inline-comment)
    (goto-char 111)
    (assert (eq 0 (py-compute-indentation)) nil "indent-after-inline-comment-lp-873372-test #2 failed")))

(defun else-clause-indentation-lp-874470-test (&optional arg)
  (interactive "p")
  (let ((teststring (concat py-test-shebang "
# -*- coding: utf-8 -*-

def foo():
    for i in range(10):
        if i == 7:
            continue
        do_something(i)
    else
")))
    (py-bug-tests-intern 'else-clause-indentation-lp-874470-base arg teststring)))

(defun else-clause-indentation-lp-874470-base (arg)
  (goto-char 156)
  (assert (eq 4 (py-compute-indentation)) nil "else-clause-indentation-lp-874470-test failed"))

(defun incorrect-use-of-region-in-py-shift-left-lp-875951-test (&optional arg)
  (interactive "p")
  (let ((teststring (concat py-test-shebang "
# -*- coding: utf-8 -*-

def foo():
    for i in range(10):
        for j in range(10):
            print(i, j)
        print('next')

")))
    (py-bug-tests-intern 'incorrect-use-of-region-in-py-shift-left-lp-875951-base arg teststring)))

(defun incorrect-use-of-region-in-py-shift-left-lp-875951-base (arg)
  (push-mark 84)
  (goto-char 135)
  (py-shift-left 1 84 135)
  (assert (eq  8 (current-indentation)) nil "incorrect-use-of-region-in-py-shift-left-lp-875951-test failed"))

(defun py-complete-lp-858621-test (&optional arg)
  (interactive "p")
  (let ((teststring (concat py-test-shebang "
# -*- coding: utf-8 -*-

pri
")))
    (py-bug-tests-intern 'py-complete-lp-858621-base 2 teststring)))

(defun py-complete-lp-858621-base (arg)
  (goto-char 52)
  (ignore-errors (py-shell-complete))
  (sit-for 0.1)
  (assert (eq 54 (point)) nil "py-complete-lp-858621-test failed"))

(defun indentation-after-line-with-keyword-lp-883073-test (&optional arg)
  (interactive "p")
  (let ((teststring (concat py-test-shebang "
# -*- coding: utf-8 -*-

with_foo = False
    # indents here
")))
    (py-bug-tests-intern 'indentation-after-line-with-keyword-lp-883073-base arg teststring)))

(defun indentation-after-line-with-keyword-lp-883073-base (arg)
  (goto-char 66)
  (assert (eq 0 (py-compute-indentation)) nil "indentation-after-line-with-keyword-lp-883073-test failed"))

(defun indent-after-multiple-except-statements-lp-883815-test (&optional arg)
  (interactive "p")
  (let ((teststring (concat py-test-shebang "
# -*- coding: utf-8 -*-

def foo():
    try:
        x = 1
    except SystemError:
        f = 1
except KeyError:
        p = 1
")))
    (py-bug-tests-intern 'indent-after-multiple-except-statements-lp-883815-base arg teststring)))

(defun indent-after-multiple-except-statements-lp-883815-base (arg)
  (goto-char 121)
  (assert (eq 4 (py-compute-indentation)) nil "indent-after-multiple-except-statements-lp-883815-test failed"))

(defun wrongly-highlighted-as-keywords-lp-885144-test (&optional arg)
  (interactive "p")
  (let ((teststring (concat py-test-shebang "
# -*- coding: utf-8 -*-

date_range = 4
date_range_max = 3
latest_sum = 5
")))
    (py-bug-tests-intern 'wrongly-highlighted-as-keywords-lp-885144-base arg teststring)))

(defun wrongly-highlighted-as-keywords-lp-885144-base (arg)
  (font-lock-fontify-buffer)
  (goto-char 55)
  (sit-for 0.1)
  (assert (eq (get-char-property (point) 'face) 'py-variable-name-face) nil "wrongly-highlighted-as-keywords-lp-885144-test failed"))

(defun glitch-when-indenting-lists-lp-886473-test (&optional arg)
  (interactive "p")
  (let ((teststring (concat py-test-shebang "
# -*- coding: utf-8 -*-
def foo(bar,
        baz):
    pass
")))
    (py-bug-tests-intern 'glitch-when-indenting-lists-lp-886473-base arg teststring)))

(defun glitch-when-indenting-lists-lp-886473-base (arg)
  (goto-char 61)
  (assert (eq 8 (py-compute-indentation))  nil "glitch-when-indenting-lists-lp-886473-test failed"))

(defun keywords-in-identifiers-highlighted-incorrectly-lp-888338-test (&optional arg)
  (interactive "p")
  (let ((teststring (concat py-test-shebang "
# -*- coding: utf-8 -*-
def possibly_break():
    pass
")))
    (py-bug-tests-intern 'keywords-in-identifiers-highlighted-incorrectly-lp-888338-base arg teststring)))

(defun keywords-in-identifiers-highlighted-incorrectly-lp-888338-base (arg)
  (font-lock-fontify-buffer)
  (sit-for 0.1)
  (goto-char 55)
  (assert (eq (get-char-property (point) 'face) 'font-lock-function-name-face) nil "keywords-in-identifiers-highlighted-incorrectly-lp-888338-test failed"))

(defun indentation-keyword-lp-885143-test (&optional arg)
  (interactive "p")
  (let ((teststring (concat py-test-shebang "
# -*- coding: utf-8 -*-
import sys
")))
    (py-bug-tests-intern 'indentation-keyword-lp-885143-base arg teststring)))

(defun indentation-keyword-lp-885143-base (arg)
  (goto-char 48)
  (assert (eq 0 (py-compute-indentation))  nil "indentation-keyword-lp-885143-test failed"))

(defun py-shell-complete-lp-328836-test (&optional arg)
  (interactive "p")
  (let ((teststring (concat py-test-shebang "
# -*- coding: utf-8 -*-

")))
    (py-bug-tests-intern 'py-shell-complete-lp-328836-base 2 teststring)))

(defun py-shell-complete-lp-328836-base (arg)
  (python-dedicated)
  (goto-char (point-max))
  (insert "pri")
  (py-shell-complete)
  (assert (looking-back "print") nil "py-shell-complete-lp-328836-test failed"))

(defun indentation-bug-inside-docstrings-lp-899455-test (&optional arg)
  (interactive "p")
  (let ((teststring (concat py-test-shebang "
# -*- coding: utf-8 -*-

def foo():
    \"\"\"This is my docstring.

    There are many others like it, but this one is mine. My docstring is my
    best friend. It is my life. I must master it as I must master my life.
    Without me, my docstring is useless. Without my docstring, I am useless.
    I must write my docstring true. I must write clearer than my enemy, who
    is trying to confuse me. I must enlighten him before he enlightens me. I
    will. Before Guido I swear this creed: my docstring and myself are
    defenders of my codebase, we are the masters of our enemy, we are the
    saviors of my life. So be it, until there is no enemy, but peace. Amen.

    foo: str or None
        If None then baz.

    \"\"\"

")))
    (py-bug-tests-intern 'indentation-bug-inside-docstrings-lp-899455-base arg teststring)))

(defun indentation-bug-inside-docstrings-lp-899455-base (arg)
  (goto-char 742)
  (sit-for 0.2)
  (assert (eq 8 (py-compute-indentation)) nil "indentation-bug-inside-docstrings-lp-899455-test failed"))

(defun another-indentation-bug-inside-docstrings-lp-900684-test (&optional arg)
  (interactive "p")
  (let ((teststring (concat py-test-shebang "
# -*- coding: utf-8 -*-
def is_x_day(date):
    \"\"\"Return True if given date is the X-day.

    \"\"\"
")))
    (py-bug-tests-intern 'another-indentation-bug-inside-docstrings-lp-900684-base arg teststring)))

(defun another-indentation-bug-inside-docstrings-lp-900684-base (arg)
  (goto-char 116)
  (sit-for 0.1)
  (assert (eq 4 (py-compute-indentation)) nil "another-indentation-bug-inside-docstrings-lp-900684-test failed"))

(defun indent-offset-not-guessed-when-loading-lp-902890-test (&optional arg)
  (interactive "p")
  (let ((teststring (concat py-test-shebang "
# -*- coding: utf-8 -*-
#! /usr/bin/python
# -*- coding: utf-8 -*-
def main():
  if len(sys.argv)==1:
    usage()
    sys.exit()
")))
    (py-bug-tests-intern 'indent-offset-not-guessed-when-loading-lp-902890-base arg teststring)))

(defun indent-offset-not-guessed-when-loading-lp-902890-base (arg)
  "This doesn't check precisely the feature requested. "
  (assert (eq 2 (py-guess-indent-offset)) nil "indent-offset-not-guessed-when-loading-lp-902890-test failed"))

(defun from-__future__-import-absolute_import-mishighlighted-lp-907084-test (&optional arg)
  (interactive "p")
  (let ((teststring (concat py-test-shebang "
# -*- coding: utf-8 -*-
from __future__ import absolute_import
")))
    (py-bug-tests-intern 'from-__future__-import-absolute_import-mishighlighted-lp-907084-base arg teststring)))

(defun from-__future__-import-absolute_import-mishighlighted-lp-907084-base (arg)
  (font-lock-fontify-buffer)
  (goto-char 82)
  (assert (not (eq (get-char-property (point) 'face) 'font-lock-keyword-face)) nil "from-__future__-import-absolute_import-mishighlighted-lp-907084-test failed"))

(defun automatic-indentation-is-broken-lp-889643-test (&optional arg)
  (interactive "p")
  (let ((teststring (concat py-test-shebang "
# -*- coding: utf-8 -*-

")))
    (py-bug-tests-intern 'automatic-indentation-is-broken-lp-889643-base arg teststring)))

(defun automatic-indentation-is-broken-lp-889643-base (arg)
  (assert (eq (key-binding (kbd "RET")) 'py-newline-and-indent) nil "automatic-indentation-is-broken-lp-889643-test failed")
  )

(defun chars-uU-preceding-triple-quoted-get-string-face-lp-909517-test (&optional arg)
  (interactive "p")
  (let ((teststring (concat py-test-shebang "
# -*- coding: utf-8 -*-
u\"hi\" and u\"\"\"d\"\"\"
")))
    (py-bug-tests-intern 'chars-uU-preceding-triple-quoted-get-string-face-lp-909517-base arg teststring)))

(defun chars-uU-preceding-triple-quoted-get-string-face-lp-909517-base (arg)
  (goto-char 58)
  (assert (eq nil (get-char-property (point) 'face)) nil "chars-uU-preceding-triple-quoted-get-string-face-lp-909517-test failed"))

(defun wrong-type-argument-lp-901541-test (&optional arg)
  (interactive "p")
  (let ((teststring (concat py-test-shebang "
# -*- coding: utf-8 -*-
# source: argparse.py
# Author: Steven J. Bethard <steven.bethard@gmail.com>.

\"\"\"Command-line parsing library

This module is an optparse-inspired command-line parsing library that:

    - handles both optional and positional arguments
    - produces highly informative usage messages
    - supports parsers that dispatch to sub-parsers
\"\"\"
")))
    (py-bug-tests-intern 'wrong-type-argument-lp-901541-base arg teststring)))

(defun wrong-type-argument-lp-901541-base (arg)
  (goto-char 385)
  (sit-for 0.1)
  ;; (message "%s" "wrong-type-argument-lp-901541-test")
  ;; (message "(py-compute-indentation): should 4: %s" (py-compute-indentation))
  (assert (eq 4 (py-compute-indentation)) nil "wrong-type-argument-lp-901541-test failed"))

(defun py-pychecker-run-missing-lp-910783-test (&optional arg)
  (interactive "p")
  (let ((teststring (concat py-test-shebang "
# -*- coding: utf-8 -*-

")))
    (py-bug-tests-intern 'py-pychecker-run-missing-lp-910783-base arg teststring)))

(defun py-pychecker-run-missing-lp-910783-base (arg)
  (assert (commandp 'py-pychecker-run) nil "py-pychecker-run-missing-lp-910783-test failed"))

(defun py-forward-into-nomenclature-lp-916818-test (&optional arg)
  (interactive "p")
  (let ((teststring (concat py-test-shebang "
# -*- coding: utf-8 -*-
def doSomething(blah)
print(\"\"\"Es müsste \"müßte\" heißen.\"\"\")
")))
    (py-bug-tests-intern 'py-forward-into-nomenclature-lp-916818-base arg teststring)))

(defun py-forward-into-nomenclature-lp-916818-base (arg)
  (goto-char 48)
  (assert (eq 51 (py-forward-into-nomenclature)) nil "py-forward-into-nomenclature-lp-916818-test #1 failed")
  (assert (eq 54 (py-forward-into-nomenclature)) nil "py-forward-into-nomenclature-lp-916818-test #2 failed")
  (assert (eq 63 (py-forward-into-nomenclature)) nil "py-forward-into-nomenclature-lp-916818-test #3 failed")
  (assert (eq 68 (py-forward-into-nomenclature)) nil "py-forward-into-nomenclature-lp-916818-test #4 failed")
  (goto-char 88)
  (assert (eq 95 (py-forward-into-nomenclature)) nil "py-forward-into-nomenclature-lp-916818-test #5 failed"))

(defun tab-completion-in-Ipython-buffers-lp-916869-test (&optional arg)
  (interactive "p")
  (let ((teststring (concat py-test-shebang "
# -*- coding: utf-8 -*-

")))
    (py-bug-tests-intern 'tab-completion-in-Ipython-buffers-lp-916869-base arg teststring)))

(defun tab-completion-in-Ipython-buffers-lp-916869-base (arg)
  (ipython-dedicated)
  (switch-to-buffer (current-buffer))
  (goto-char (point-max))
  (sit-for 0.1)
  (insert "pri")
  (ipython-complete)
  (sit-for 0.1)
  (assert (looking-back "print") nil "tab-completion-in-Ipython-buffers-lp-916869-test failed"))

(defun py-forward-into-nomenclature-jumps-over-CamelCased-words-lp-919540-test (&optional arg)
  (interactive "p")
  (let ((teststring (concat py-test-shebang "
# -*- coding: utf-8 -*-
def SomeFunction(arg):
    pass
")))
    (py-bug-tests-intern 'py-forward-into-nomenclature-jumps-over-CamelCased-words-lp-919540-base arg teststring)))

(defun py-forward-into-nomenclature-jumps-over-CamelCased-words-lp-919540-base (arg)
  (goto-char 52)
  (assert (eq 56 (py-forward-into-nomenclature)) nil "py-forward-into-nomenclature-jumps-over-CamelCased-words-lp-919540-test failed"))

(defun py-backward-into-nomenclature-caps-names-lp-919541-test (&optional arg)
  (interactive "p")
  (let ((teststring (concat py-test-shebang "
# -*- coding: utf-8 -*-
return SOME_Constant + blah
")))
    (py-bug-tests-intern 'py-backward-into-nomenclature-caps-names-lp-919541-base arg teststring)))

(defun py-backward-into-nomenclature-caps-names-lp-919541-base (arg)
  (goto-char 64)
  (assert (eq 60 (py-backward-into-nomenclature)) nil "py-backward-into-nomenclature-caps-names-lp-919541-test failed"))

(defun py-ipython-complete-lp-927136-test (&optional arg)
  (interactive "p")
  ;; (py-shell nil nil "ipython" 'noswitch)
  (let ((teststring (concat py-ipython-test-shebang "
# -*- coding: utf-8 -*-
execf
")))
    (py-bug-tests-intern 'py-ipython-complete-lp-927136-base arg teststring)))

(defun py-ipython-complete-lp-927136-base (arg)
  (goto-char (point-min))
  (search-forward "execf")
  (py-shell-complete)
  (sit-for 0.1)
  (assert (looking-back "execfile")  nil "py-ipython-complete-lp-927136-test #2 lp-1026705 failed"))

(defun execute-buffer-ipython-fails-lp-928087-test (&optional arg)
  (interactive "p")
  (let ((teststring (concat py-ipython-test-shebang "
# -*- coding: utf-8 -*-
print(4 + 5)
print(u'\\xA9')
")))
    (py-bug-tests-intern 'execute-buffer-ipython-fails-lp-928087-base arg teststring)))

(defun execute-buffer-ipython-fails-lp-928087-base (arg)
  (let (py-split-window-on-execute
        py-switch-buffers-on-execute-p)
    (assert (py-execute-buffer) nil "execute-buffer-ipython-fails-lp-928087-test failed")))

(defun fourth-level-blocks-indent-incorrectly-lp-939577-test (&optional arg)
  (interactive "p")
  (let ((teststring (concat py-test-shebang "
# -*- coding: utf-8 -*-
for x in y:
    for z in l:
        for r in t:
            pass # <--- indents here. Pressing <backspace> dedents eight spaces (i.e. you can go to column 0 in two presess)
")))
    (py-bug-tests-intern 'fourth-level-blocks-indent-incorrectly-lp-939577-base arg teststring)))

(defun fourth-level-blocks-indent-incorrectly-lp-939577-base (arg)
  (goto-char 88)
  (assert (eq 4 (py-guess-indent-offset)) nil "fourth-level-blocks-indent-incorrectly-lp-939577-test failed")
  (goto-char 225)
  (assert (eq 4 (py-guess-indent-offset)) nil "fourth-level-blocks-indent-incorrectly-lp-939577-test failed")
  )

(defun py-mark-expression-marks-too-much-lp-941140-test (&optional arg)
  (interactive "p")
  (let ((teststring (concat py-test-shebang "
# -*- coding: utf-8 -\*-
  somevar = \"some string\"
  # some code

# when point is on the first quote, calling py-mark-expression marks the next several lines, no matter what they are.

# This only seems to happen when point is in the first quote of a string literal which is the last thing on a line.

  somevar = some_string.some_property()
  # point at first quote works

  somevar = \"a\" + \"b\"
  # works at quote before a, fails at quote before b

I am using version 6.0.4

")))
    (py-bug-tests-intern 'py-mark-expression-marks-too-much-lp-941140-base arg teststring)))

(defun py-mark-expression-marks-too-much-lp-941140-base (arg)
  (goto-char 60)

  (assert (string-match "some" (py-expression)) nil "py-mark-expression-marks-too-much-lp-941140-test failed")
  (goto-char 417)
  (assert (string-match "a" (py-expression)) nil "py-mark-expression-marks-too-much-lp-941140-test failed"))

;;; Py-shell tests
(defun py-shell-invoking-python-lp-835151-test (&optional arg)
  (interactive "p")
  (let ((teststring "print(\"py-shell-name: python\")"))
    (py-bug-tests-intern 'py-shell-invoking-python-lp-835151-base arg teststring)))

(defun py-shell-invoking-python-lp-835151-base (arg)
  (setq py-shell-name "python")
  (py-execute-buffer)
  (set-buffer "*Python*")
  (sit-for 0.1)
  (and
   (assert (or (search-forward "py-shell-name: python" nil t 1)
	       (search-backward "py-shell-name: python" nil t 1))
	   nil "py-shell-invoking-python-lp-835151-test failed")
   (message "%s" "py-shell-invoking-python-lp-835151-test passed")))

(defun py-shell-invoking-ipython-lp-835151-test (&optional arg)
  (interactive "p")
  (let ((teststring "print(\"py-shell-name: ipython\")"))
    (py-bug-tests-intern 'py-shell-invoking-ipython-lp-835151-base arg teststring)))

(defun py-shell-invoking-ipython-lp-835151-base (arg)
  (setq py-shell-name "ipython")
  (py-execute-buffer)
  (set-buffer py-buffer-name)
  (goto-char (point-max))
  (assert (search-backward "py-shell-name: ipython")  nil "py-shell-invoking-ipython-lp-835151-test failed"))

(defun py-shell-invoking-jython-lp-835151-test (&optional arg)
  (interactive "p")
  (let ((teststring "print(\"py-shell-name: jython\")"))
    (py-bug-tests-intern 'py-shell-invoking-jython-lp-835151-base arg teststring)))

(defun py-shell-invoking-jython-lp-835151-base (arg)
  (setq py-shell-name "jython")
  (py-execute-buffer)
  (set-buffer py-buffer-name)
  (goto-char (point-max))
  (assert (search-backward "py-shell-name: jython")  nil "py-shell-invoking-jython-lp-835151-test failed"))

(defun py-shell-invoking-python3-lp-835151-test (&optional arg)
  (interactive "p")
  (let ((teststring "print(\"py-shell-name: python3\")"))
    (py-bug-tests-intern 'py-shell-invoking-python3-lp-835151-base arg teststring)))

(defun py-shell-invoking-python3-lp-835151-base (arg)
  (let ((py-force-py-shell-name-p t)
	(py-shell-name "python3"))
    (py-execute-buffer)
    (assert (buffer-live-p (get-buffer "*Python3*")) nil "py-shell-invoking-python3-lp-835151-test failed")))

(defun py-shell-invoking-python2-lp-835151-test (&optional arg)
  (interactive "p")
  (let ((teststring "print(\"py-shell-name: python2\")"))
    (py-bug-tests-intern 'py-shell-invoking-python2-lp-835151-base arg teststring)))

(defun py-shell-invoking-python2-lp-835151-base (arg)
  (let ((py-force-py-shell-name-p t)
	(py-shell-name "python2"))
    (py-execute-buffer)
    (assert (buffer-live-p (get-buffer "*Python2*")) nil "py-shell-invoking-python2-lp-835151-test failed")))

(defun py-mark-block-clause-misbehave-lp-949310-test (&optional arg)
  (interactive "p")
  (let ((teststring " if foo:
    try:
        pass
"))
    (py-bug-tests-intern 'py-mark-block-clause-misbehave-lp-949310-base arg teststring)))

(defun py-mark-block-clause-misbehave-lp-949310-base (arg)
  (goto-char 15)
  (assert (eq 14 (car (py-mark-block-or-clause))) nil "py-mark-block-clause-misbehave-lp-949310-test failed"))

(defun py-mark-clause-misbehave-lp-949310-test (&optional arg)
  (interactive "p")
  (let ((teststring " if foo:
    try:
        pass
"))
    (py-bug-tests-intern 'py-mark-clause-misbehave-lp-949310-base arg teststring)))

(defun py-mark-clause-misbehave-lp-949310-base (arg)
  (goto-char 15)
  (assert (eq 14 (car (py-mark-block-or-clause))) nil "py-mark-clause-misbehave-lp-949310-test failed"))

(defun py-mark-block-misbehave-lp-949310-test (&optional arg)
  (interactive "p")
  (let ((teststring " if foo:
    try:
        pass
"))
    (py-bug-tests-intern 'py-mark-block-misbehave-lp-949310-base arg teststring)))

(defun py-mark-block-misbehave-lp-949310-base (arg)
  (goto-char 15)
  (assert (eq 14 (car (py-mark-block-or-clause))) nil "py-mark-block-misbehave-lp-949310-test failed"))

(defun py-indent-comments-nil-ignored-lp-958721-test (&optional arg)
  (interactive "p")
  (let (py-indent-comments
        (teststring (concat py-test-shebang "
# -*- coding: utf-8 -*-
if x > 0:
    for i in range(100):
        # print(i)
")))
    (py-bug-tests-intern 'py-indent-comments-nil-ignored-lp-958721-base arg teststring)))

(defun py-indent-comments-nil-ignored-lp-958721-base (arg)
  (goto-char 83)
  (assert (eq 0 (py-compute-indentation)) nil "py-indent-comments-nil-ignored-lp-958721-test failed"))

(defun broken-font-locking-lp-961231-test (&optional arg)
  (interactive "p")
  (let ((teststring (concat py-test-shebang "
# -*- coding: utf-8 -*-
def baz():
    foo = None
    bar = False
    baz = True
    foo, bar, baz = baz()
    return foo, bar, baz

# None, False, and True get colored with font-lock-constant-face instead of py-pseudo-keyword-face

# On the second to last line, \"foo\" \"bar\" and \"baz\" all get colored with font-lock-variable-name-face whereas
# I think they should get default face, just as they would if no comma or equal sign appeared on the line.

def baz(mydict):
    mydict['hello'] = 'baz'

    # 'mydict' gets colored with font-lock-variable-name-face but it should be default face.

def baz(self):
    self.baz = 'hello'

    # 'self' gets colored with font-lock-keyword-face instead of py-pseudo-keyword-face

def baz(self):
    return set(range(100))

# 'set' and 'range' get rendered in font-lock-builtin-face when they should get rendered in py-builtins-face

print myobj.range()

# the latter range should get default face

")))
    (py-bug-tests-intern 'broken-font-locking-lp-961231-base arg teststring)))

(defun broken-font-locking-lp-961231-base (arg)
  (font-lock-fontify-buffer)
  (sit-for 0.1)
  (goto-char 87)
  (assert (eq (get-char-property (point) 'face) 'py-pseudo-keyword-face) nil "broken-font-locking-lp-961231-test #1 failed")
  (goto-char 488)
  (assert (eq (get-char-property (point) 'face) 'nil) nil "broken-font-locking-lp-961231-test #2 failed")
  (goto-char 637)
  (assert (eq (get-char-property (point) 'face) 'py-object-reference-face) nil "broken-font-locking-lp-961231-test #3 failed")
  (goto-char 775)
  ;; also covers lp-1354872 bad-syntax-highlight-for-py-builtin-face
  (assert (eq (get-char-property (point) 'face) 'nil) nil "broken-font-locking-lp-961231-test #4 failed")
  )

(defun regression-in-py-execute-region-lp-962227-test (&optional arg)
  (interactive "p")
  (let ((teststring (concat py-test-shebang "
# -*- coding: utf-8 -*-
def foo():
    def bar():
        return True
    return bar

# In the past it was possible to highlight the middle two lines and run py-execute-region. This would have
# the effect of defining bar() at global scope, but that's okay since it was explicitly asked for. Now
# however you get this error in the Python buffer:

# >>> Traceback (most recent call last):
# File \"<stdin>\", line 1, in <module>
# File \"/tmp/Python4249aED.py\", line 8
# return True
# ^
# IndentationError: expected an indented block

# which perhaps makes sense, but isn't helpful. What python-mode used to do was, if the block to be executed
# was indented, it would still a \"if True:\" line indented to column zero in front of the region to be
# executed. This is essentially a no-op that just makes the indented region valid syntactically.

")))
    (py-bug-tests-intern 'regression-in-py-execute-region-lp-962227-base arg teststring)))

(defun regression-in-py-execute-region-lp-962227-base (arg)
  (goto-char 59)
  (push-mark)
  (goto-char 93)
  (assert (py-execute-region 59 93) nil "regression-in-py-execute-region-lp-962227-test failed"))

(defun auto-indent-behaves-strangely-with-slices-lp-961684.txt-test (&optional arg)
  (interactive "p")
  (let ((teststring (concat py-test-shebang "
# -*- coding: utf-8 -*-

# In the final line of the following, I want the line not to be indented at
# all (the loop in the preceding lines is complete). But if you type a :
# after the 1 to form potential.difference(set(S[1]:)), this activates the
# automatic indentation and incorrectly indents the line under the
# preceding line in the for loop.
potential = set([])
for j in X:
    potential = potential.union(visible[j])
potential = potential.difference(set(S[1]))

# py-electric-colon-active-p is t.

")))
    (py-bug-tests-intern 'auto-indent-behaves-strangely-with-slices-lp-961684-base arg teststring)))

(defun auto-indent-behaves-strangely-with-slices-lp-961684-base (arg)
  (goto-char 40)
  (assert (eq 0 (py-compute-indentation)) nil "auto-indent-behaves-strangely-with-slices-lp-961684.txt-test failed"))

(defun tuple-unpacking-highlighted-incorrectly-lp-961496-test (&optional arg)
  (interactive "p")
  (let ((teststring (concat py-test-shebang "
# -*- coding: utf-8 -*-
foo, bar = toothpick
")))
    (py-bug-tests-intern 'tuple-unpacking-highlighted-incorrectly-lp-961496-base arg teststring)))

(defun tuple-unpacking-highlighted-incorrectly-lp-961496-base (arg)
  (font-lock-fontify-buffer)
  (sit-for 0.1)
  (goto-char 50)
  (assert (eq (get-char-property (point) 'face) 'py-variable-name-face) nil "tuple-unpacking-highlighted-incorrectly-lp-961496-test failed"))

(defun new-problem-with-py-temp-directory-lp-965762-test (&optional arg)
  (interactive "p")
  (let ((teststring (concat py-test-shebang "
# -*- coding: utf-8 -*-

")))
    (py-bug-tests-intern 'new-problem-with-py-temp-directory-lp-965762-base arg teststring)))

(defun new-problem-with-py-temp-directory-lp-965762-base (arg)
  (assert (stringp py-temp-directory) nil "new-problem-with-py-temp-directory-lp-965762-test failed"))

(defun problem-with-py-separator-char-under-windows-lp-975539-test (&optional arg)
  (interactive "p")
  (let ((teststring ""))
    (py-bug-tests-intern 'problem-with-py-separator-char-under-windows-lp-975539-base arg teststring)))

(defun problem-with-py-separator-char-under-windows-lp-975539-base (arg)
  (assert (string= (char-to-string  py-separator-char) (py-separator-char)) nil "problem-with-py-separator-char-under-windows-lp-975539-test failed"))

(defun another-broken-font-locking-lp-961231-test (&optional arg)
  (interactive "p")
  (let ((teststring (concat py-test-shebang "
# -*- coding: utf-8 -*-
# So while in this case, range() refers to the built-in function:

print(range(10))

# in this case, it's just a method on some object:

print(myobj.range(10))

# The two 'range's have no relationship at all.
# That's why I suggest that the former be colored with py-builtins-face but the latter by default face.

")))
    (py-bug-tests-intern 'another-broken-font-locking-lp-961231-base arg teststring)))

(defun another-broken-font-locking-lp-961231-base (arg)
  (goto-char 120)
  (sit-for 0.1)
  (assert (not (get-char-property (point) 'face)) nil "another-broken-font-locking-lp-961231-test #2 failed")
  (goto-char 124)
  (sit-for 0.1)
  (assert (eq (get-char-property (point) 'face) 'py-builtins-face) nil "another-broken-font-locking-lp-961231-test #2 failed")
  (goto-char 197)
  (sit-for 0.2)
  (assert (eq (get-char-property (point) 'face) nil) nil "another-broken-font-locking-lp-961231-test #3 failed"))

(defun temp-file-stored-in-python-script-directory-lp-958987-test (&optional arg)
  (interactive "p")
  (let ((teststring "
# -*- coding: utf-8 -*-
Richard Stanton (a-stanton) wrote on 2012-03-20:  #5

> > 1) The directory is not being applied correctly.
> >
>
> need a recipe for it, a new report would help, as it's related only

Actually, I think this is the original problem I was reporting. Any python script will do in my experience,
but the problem only occurs if the script file does \*not\* contain a shebang line. For example, the
following file works fine:

--------

#!/usr/bin/python
print \"Hi, Richard\"

---------

In this case, the temp file is created in the appropriate temp directory.

However, if I use the same file without the shebang line,

--------

print \"Hi, Richard\"

---------

now the problem occurs.

print \"Hi, Richard\"

Richard Stanton (a-stanton) wrote 1 hour ago:  #10

The problem is still there in certain situations, I'm afraid, with r918 on my Mac. Here are three
experiments. In numbers 1 and 2, things work as they're supposed to. In number 3, they don't:

1) Script file =

#!/usr/bin/ipython
print \"Hi, Richard\"

In this case, the temp file is correctly stored in the temp directory as (for example)
/var/folders/zf/bgjm4tvs3wv_6q7_6z3b2nx00000gn/T/ipython61090CmR.py. The ipython buffer is called
\*IPython\*.

2) Script file =

print \"Hi, Richard\"

py-shell-name = \"ipython\"

In this case, the temp file is again correctly stored in the temp directory as (for example)
/var/folders/zf/bgjm4tvs3wv_6q7_6z3b2nx00000gn/T/ipython61090CmR.py. The ipython buffer is again named
\*IPython\*

3) Script file =

print \"Hi, Richard\"

py-shell-name = \"/Library/Frameworks/EPD64.framework/Versions/7.2/bin/ipython\"

In this case, the temp file is saved in the \*wrong\* location as
/Library/Frameworks/EPD64.framework/Versions/7.2/bin/ipython61090PwX.py.

In this case, the ipython buffer is called \*ND 0.12\*

"))
    (py-bug-tests-intern 'temp-file-stored-in-python-script-directory-lp-958987-base arg teststring)))

(defun temp-file-stored-in-python-script-directory-lp-958987-base (arg)
  (goto-char 40)
  (assert nil "temp-file-stored-in-python-script-directory-lp-958987-test failed"))

(defun temp-buffer-affected-by-py-shell-name-lp-958987-test (&optional arg)
  (interactive "p")
  (let* ((py-shell-name (concat (expand-file-name py-shell-name-testpath) "/ipython"))
         (teststring (concat "#! " py-shell-name "
# -*- coding: utf-8 -*-
print(\"I'm the temp-buffer-affected-by-py-shell-name-lp-958987-test\")
")))
    (py-bug-tests-intern 'temp-buffer-affected-by-py-shell-name-lp-958987-base arg teststring)))

(defun temp-buffer-affected-by-py-shell-name-lp-958987-base (arg)
  (message "%s" py-shell-name)
  (assert (not (py-execute-buffer)) nil "temp-buffer-affected-by-py-shell-name-lp-958987-test failed"))

(defun toggle-force-local-shell-lp-988091-test (&optional arg)
  (interactive "p")
  (let ((teststring (concat py-epd-shebang "
# -\*- coding: utf-8 -\*-
pri
impo
\"\"\" Am 25.04.2012 01:32, schrieb Yaroslav Halchenko:

\[ ... ]

another convenience might be to have an option 'follow' the desired shell -- i.e. if someone explicitly
asks for a buffer to execute it in ipython, that sets py-shell-name to ipython.
\"\"\"

")))
    (if (and (boundp 'py-epd-shebang)
             (stringp py-epd-shebang))
        (py-bug-tests-intern 'toggle-force-local-shell-lp-988091-base arg teststring)
      (error "Please edit `py-epd-shebang' with your local EPD before running this test."))))

(defun toggle-force-local-shell-lp-988091-base (arg)
  (let ((old py-shell-name))
    (py-force-local-shell-on)
    (goto-char 92)
    (save-excursion (py-shell-complete))
    (message "%s" completion-at-point-functions)
    (assert (looking-at "print") nil "toggle-force-local-shell-lp-988091-test #1 failed")
    (force-py-shell-name-p-off)
    (goto-char 99)
    (save-excursion (py-shell-complete))
    (message "%s" completion-at-point-functions)
    (assert (looking-at "import") nil "toggle-force-local-shell-lp-988091-test #1 failed")
    ))

(defun py-describe-symbol-fails-on-modules-lp-919719-test (&optional arg)
  (interactive "p")
  (let ((teststring "#! /usr/bin/env python
# -*- coding: utf-8 -*-
import os
os.chmod
"))
    (py-bug-tests-intern 'py-describe-symbol-fails-on-modules-lp-919719-base arg teststring)))

(defun py-describe-symbol-fails-on-modules-lp-919719-base (arg)
  (when py-debug-p (switch-to-buffer (current-buffer)) (font-lock-fontify-buffer))
  (goto-char 61)
  (py-help-at-point)
  (sit-for 0.1)
  (set-buffer "*Python-Help*")
  (goto-char (point-min))
  (switch-to-buffer (current-buffer))
  (assert (looking-at "Help on built-in function chmod in os:") nil "py-describe-symbol-fails-on-modules-lp-919719-test failed"))

(defun pycomplete-same-folder-def-lp-889052-test (&optional arg)
  (interactive "p")
  (save-excursion
    (set-buffer (get-buffer-create "somedef.py"))
    (switch-to-buffer (current-buffer))
    (erase-buffer)
    (insert "#! /usr/bin/env python
# -*- coding: utf-8 -*-

def someDef():
    print(\"I'm someDef\")
")
    (write-file (concat (py--normalize-directory py-temp-directory) "somedef.py")))

  (let ((teststring "#! /usr/bin/env python
# -*- coding: utf-8 -*-
from somedef import *
someDe
"))
    (py-bug-tests-intern 'pycomplete-same-folder-def-lp-889052-base arg teststring)))

(defun pycomplete-same-folder-def-lp-889052-base (arg)
  (write-file (concat (py--normalize-directory py-temp-directory) "samefolder.py"))
  (goto-char 76)
  (py-complete)
  (beginning-of-line)
  (assert (looking-at "someDef") nil "pycomplete-same-folder-def-lp-889052-test failed"))

(defun pycomplete-same-folder-class-lp-889052-test (&optional arg)
  (interactive "p")
  (save-excursion
    (set-buffer (get-buffer-create "somedef.py"))
    (switch-to-buffer (current-buffer))
    (erase-buffer)
    (insert "#! /usr/bin/env python
# -*- coding: utf-8 -*-
class Blah():
    def someDef():
        print(\"I'm someDef\")
")
    ;; (write-file (concat (py--normalize-directory py-temp-directory) "classblah.py")))
    ;; as completion is  already in $PYTHONPATH
   (write-file (concat (expand-file-name (py--normalize-directory py-install-directory)) "completion" "/" "classblah.py"))
     (set-buffer-modified-p 'nil)
  (kill-buffer (current-buffer)))
  (let ((teststring "#! /usr/bin/env python
# -*- coding: utf-8 -*-
from classblah import *
CLASS_INS = Blah()
CLASS_INS.someDe
"))
    (py-bug-tests-intern 'pycomplete-same-folder-class-lp-889052-base arg teststring)))

(defun pycomplete-same-folder-class-lp-889052-base (arg)
  (let ((testfile1 (concat (expand-file-name (py--normalize-directory py-install-directory)) "completion" "/" "classblah.py"))
        (testfile2 (concat (expand-file-name (py--normalize-directory py-install-directory)) "completion" "/" "somedef.py"))
        py-indent-no-completion-p)
    (write-file testfile2)
    (goto-char 107)
    (unwind-protect
        (py-shell-complete)
      (beginning-of-line))
    (when (file-readable-p testfile1) (delete-file testfile1))
    (when (file-readable-p testfile2) (delete-file testfile2)))
  (assert (looking-at "CLASS_INS.someDef") "pycomplete-same-folder-class-lp-889052-test failed"))

(defun shebang-interpreter-not-detected-lp-1001327-test (&optional arg)
  (interactive "p")
  (let ((teststring "#!/usr/bin/python
"))
    (py-bug-tests-intern 'shebang-interpreter-not-detected-lp-1001327-base arg teststring)))

(defun shebang-interpreter-not-detected-lp-1001327-base (arg)
  (assert (string= "/usr/bin/python" (py-choose-shell)) nil "shebang-interpreter-not-detected-lp-1001327-test failed"))

(defun no-completion-at-all-lp-1001328-test (&optional arg)
  (interactive "p")
  (let ((teststring "#!/usr/bin/python
basdklfjasdf = 3
basd
"))
    (py-bug-tests-intern 'no-completion-at-all-lp-1001328-base arg teststring)))

(defun no-completion-at-all-lp-1001328-base (arg)
  (goto-char 40)
  (py-shell-complete)
  (beginning-of-line)
  (sit-for 0.1)
  (when
      (assert (looking-at "basdklfjasdf") nil "no-completion-at-all-lp-1001328-test failed")
    (message "%s" "no-completion-at-all-lp-1001328-test passed")))

(defun not-that-useful-completion-lp-1003580-test (&optional arg)
  (interactive "p")
  (let ((teststring "#! /usr/bin/env python
# -*- coding: utf-8 -*-
import numpy
def test_bu():
    numpy.CL
"))
    (py-bug-tests-intern 'not-that-useful-completion-lp-1003580-base arg teststring)))

(defun not-that-useful-completion-lp-1003580-base (arg)
  (switch-to-buffer (current-buffer))
  (goto-char 88)
  (py-shell-complete nil t)
  (sit-for 0.3)
  (when
      (assert (looking-back "numpy.CLIP") nil "not-that-useful-completion-lp-1003580-test failed")
    (message "%s" "not-that-useful-completion-lp-1003580-test passed")))

(defun completion-fails-in-python-script-r989-lp-1004613-test (&optional arg)
  (interactive "p")
  (let ((teststring "#! /usr/bin/env ipython
# -*- coding: utf-8 -*-
ex
"))
    (py-bug-tests-intern 'completion-fails-in-python-script-r989-lp-1004613-base arg teststring)))

(defun completion-fails-in-python-script-r989-lp-1004613-base (arg)
  (when (buffer-live-p (get-buffer py-python-completions))
    (kill-buffer py-python-completions))
  (goto-char 51)
  ;; (ipython-complete)
  (py-indent-or-complete)
  (set-buffer "*Python Completions*")
  (sit-for 0.1 t)
  (assert (search-forward "except") nil "completion-fails-in-python-script-r989-lp-1004613-test failed"))


(defun spurious-trailing-whitespace-lp-1008679-test (&optional arg)
  (interactive "p")
  (let ((teststring "#! /usr/bin/env python
# -*- coding: utf-8 -*-
def foo():        X
"))
    (py-bug-tests-intern 'spurious-trailing-whitespace-lp-1008679-base arg teststring)))

(defun spurious-trailing-whitespace-lp-1008679-base (arg)
  (let ((py-trailing-whitespace-smart-delete-p t))
    (goto-char 66)
    (py-newline-and-indent)
    (forward-line -1)
    (end-of-line)
    (or
	(assert (eq (point) 58) nil "spurious-trailing-whitespace-lp-1008679-test failed")
      (message "%s" "spurious-trailing-whitespace-lp-1008679-test passed"))))

(defun empty-triple-quote-lp-1009318-test (&optional arg)
  (interactive "p")
  (let ((teststring "#! /usr/bin/env python
# -*- coding: utf-8 -*-
\"\"\"\"\"\"
''''''
"))
    (py-bug-tests-intern 'empty-triple-quote-lp-1009318-base arg teststring)))

(defun empty-triple-quote-lp-1009318-base (arg)
  (goto-char 54)
  (when
      (assert (not (nth 4 (syntax-ppss))) nil "empty-triple-quote-lp-1009318-test #1 failed")
    (message "%s" "empty-triple-quote-lp-1009318-test #1 passed")
    (goto-char 61))
  (when
      (assert (not (nth 4 (syntax-ppss))) nil "empty-triple-quote-lp-1009318-test #2 failed")
    (message "%s" "empty-triple-quote-lp-1009318-test #2 passed")))

(defun completion-at-gentoo-lp-1008842-test (&optional arg)
  (interactive "p")
  (let ((teststring "#! /usr/bin/env python
# -*- coding: utf-8 -*-
import re
re.s
"))
    (py-bug-tests-intern 'completion-at-gentoo-lp-1008842-base arg teststring)))

(defun completion-at-gentoo-lp-1008842-base (arg)
  (goto-char 62)
  (py-shell-complete)
  (sit-for 0.1)
  (when
      (assert (buffer-live-p (get-buffer py-python-completions)) nil "completion-at-gentoo-lp-1008842-test failed")

    (message "%s" "completion-at-gentoo-lp-1008842-test passed")))

(defun converts-tabs-to-spaces-in-indent-tabs-mode-t-lp-1019128-test (&optional arg)
  (interactive "p")
  (let ((teststring "#! /usr/bin/env python
# -*- coding: utf-8 -*-
setup(
	name = \"fail2ban\",
"))
    (py-bug-tests-intern 'converts-tabs-to-spaces-in-indent-tabs-mode-t-lp-1019128-base arg teststring)))

(defun converts-tabs-to-spaces-in-indent-tabs-mode-t-lp-1019128-base (arg)
  (let ((indent-tabs-mode t))
    (goto-char 74)
    (py-newline-and-indent)
    (beginning-of-line))
  (when
      (assert (looking-at "\t") nil "converts-tabs-to-spaces-in-indent-tabs-mode-t-lp-1019128-test failed"
	      (message "%s" "converts-tabs-to-spaces-in-indent-tabs-mode-t-lp-1019128-test passed"))))

(defun return-statement-indented-incorrectly-lp-1019601-test (&optional arg)
  (interactive "p")
  (let ((teststring "#! /usr/bin/env python
# -*- coding: utf-8 -*-
def foo():
    while True:
        bar()
    baz()
        return 1
"))
    (py-bug-tests-intern 'return-statement-indented-incorrectly-lp-1019601-base arg teststring)))

(defun return-statement-indented-incorrectly-lp-1019601-base (arg)
  (goto-char 99)
  (assert (eq 4 (py-compute-indentation)) nil "return-statement-indented-incorrectly-lp-1019601-test failed"))

(defun pycomplete-imports-not-found-error-when-no-symbol-lp-1019791-test (&optional arg)
  (interactive "p")
  (let ((teststring "#! /usr/bin/env python
# -*- coding: utf-8 -*-
from PyQt4.QtGui import QMainWindow
"))
    (py-bug-tests-intern 'pycomplete-imports-not-found-error-when-no-symbol-lp-1019791-base arg teststring)))

(defun pycomplete-imports-not-found-error-when-no-symbol-lp-1019791-base (arg)
  (assert (py-find-imports) nil "pycomplete-imports-not-found-error-when-no-symbol-lp-1019791-test failed"))

(defun py-narrow-to-defun-lp-1020531-test (&optional arg)
  (interactive "p")
  (let ((teststring "#! /usr/bin/env python
# -*- coding: utf-8 -*-
def usage():
    print \"\"\"Fehler: %s
Es muß die aufzurufende Ziehungszahl als Argument angegeben werden:
'python roulette.py 1, 'python roulette.py 2', ... 'python roulette.py n'.
\"\"\" % (
          os.path.basename(sys.argv[0]))

def main():
    if len(sys.argv) == 1:
        usage()
        sys.exit()

    class asdf(object):
        zeit = time.strftime('%Y%m%d--%H-%M-%S')

        def utf8_exists(filename):
            return os.path.exists(filename.encode('utf-8'))

if __name__ == \"__main__\":
    main()

"))
    (py-bug-tests-intern 'py-narrow-to-defun-lp-1020531-base arg teststring)))

(defun py-narrow-to-defun-lp-1020531-base (arg)
  (goto-char 334)
  (py-narrow-to-defun)
  (assert (eq 521 (point-max)) nil "py-narrow-to-defun-lp-1020531-test failed"))

(defun py-find-imports-lp-1023236-test (&optional arg)
  (interactive "p")
  (let ((teststring "#! /usr/bin/env python
# -*- coding: utf-8 -*-
#############################################################################
#
# Import test
#
#############################################################################

import urllib
import os, sys
from hashlib import md5

from construct import Container
from twisted.internet import reactor, defer
from twisted.internet.protocol import ClientFactory
from twisted.python import log, failure, filepath

from mock import mock1, mock2, \\
     mock3, mock4
print \"ignored\"

print \"ignored\"

def something():
    pass

"))
    (py-bug-tests-intern 'py-find-imports-lp-1023236-base arg teststring)))

(defun py-find-imports-lp-1023236-base (arg)
  (goto-char 334)
  (assert (equal (py-find-imports) "import urllib;import os, sys;from hashlib import md5;from construct import Container;from twisted.internet import reactor, defer;from twisted.internet.protocol import ClientFactory;from twisted.python import log, failure, filepath;from mock import mock1, mock2, mock3, mock4;") nil "py-find-imports-lp-1023236-test failed"))

(defun py-guess-indent-offset-dont-detect-indent-of-2-lp-1027389-test (&optional arg)
  (interactive "p")
  (let ((teststring "#! /usr/bin/env python
# -*- coding: utf-8 -*-
for something:
  for other:
    if hello:
      while x:
    statement1
"))
  (py-bug-tests-intern 'py-guess-indent-offset-dont-detect-indent-of-2-lp-1027389-base arg teststring)))

(defun py-guess-indent-offset-dont-detect-indent-of-2-lp-1027389-base (arg)
    (goto-char 109)
    (assert (eq 2 (py-guess-indent-offset)) nil "py-guess-indent-offset-dont-detect-indent-of-2-lp-1027389-test failed"))

(defun complaint-about-non-ASCII-character-lp-1042949-test (&optional arg)
  (interactive "p")
  (let ((teststring "# -*- coding: utf-8 -*-

# 11–14 ä
"))
  (py-bug-tests-intern 'complaint-about-non-ASCII-character-lp-1042949-base arg teststring)))

(defun complaint-about-non-ASCII-character-lp-1042949-base (arg)
  (assert (not (ignore (py-execute-buffer))) nil "complaint-about-non-ASCII-character-lp-1042949-test failed"))

(defun dont-indent-code-unnecessarily-lp-1048778-test (&optional arg)
  (interactive "p")
  (let ((teststring "#! /usr/bin/env python
# -*- coding: utf-8 -*-
def foo(a):
    if a == 1:
        return 1
    elif a == 2:
        if a < 7:
            return 3
    elif a == 3
"))
  (py-bug-tests-intern 'dont-indent-code-unnecessarily-lp-1048778-base arg teststring)))

(defun dont-indent-code-unnecessarily-lp-1048778-base (arg)
    (goto-char 163)
    (py-electric-colon 1)
    (assert (eq 4 (current-indentation)) nil "dont-indent-code-unnecessarily-lp-1048778-test failed"))

(defun IndentationError-expected-an-indented-block-when-execute-lp-1055569-test (&optional arg)
  (interactive "p")
  (let ((teststring "#! /usr/bin/env python3

if __name__ == '__main__':
    print('IndentationError-expected-an-indented-block-when-execute-lp-1055569-test')
"))
  (py-bug-tests-intern 'IndentationError-expected-an-indented-block-when-execute-lp-1055569-base 1 teststring)))

(defun IndentationError-expected-an-indented-block-when-execute-lp-1055569-base (arg)
  (when py-debug-p (switch-to-buffer (current-buffer))
	(font-lock-fontify-buffer))
  (py-execute-buffer)
  (with-current-buffer py-buffer-name
    ;; (message "%s" py-buffer-name)
    (goto-char (point-min))
    ;; (sit-for 1 t)
    (assert (search-forward "IndentationError-expected-an-indented-block-when-execute-lp-1055569-test" nil t 1) nil "IndentationError-expected-an-indented-block-when-execute-lp-1055569-test failed")))

(defun stalls-emacs-probably-due-to-syntax-highlighting-lp-1058261-test (&optional arg)
  (interactive "p")
  (let ((teststring "#! /usr/bin/env python
# -*- coding: utf-8 -*-
class Parallel(Logger):
    ''' Helper class for readable parallel mapping.

        Parameters
        -----------
        n_jobs: int
            The number of jobs to use for the computation. If -1 all CPUs
            are used. If 1 is given, no parallel computing code is used
            at all, which is useful for debuging. For n_jobs below -1,
            (n_cpus + 1 - n_jobs) are used. Thus for n_jobs = -2, all
            CPUs but one are used.
        verbose: int, optional
            The verbosity level: if non zero, progress messages are
            printed. Above 50, the output is sent to stdout.
            The frequency of the messages increases with the verbosity level.
            If it more than 10, all iterations are reported.
        pre_dispatch: {'all', integer, or expression, as in '3\*n_jobs'}
            The amount of jobs to be pre-dispatched. Default is 'all',
            but it may be memory consuming, for instance if each job
            involves a lot of a data.

        Notes
        -----

        This object uses the multiprocessing module to compute in
        parallel the application of a function to many different
        arguments. The main functionality it brings in addition to
        using the raw multiprocessing API are (see examples for details):

            \* More readable code, in particular since it avoids
              constructing list of arguments.

            \* Easier debuging:
                - informative tracebacks even when the error happens on
                  the client side
                - using 'n_jobs=1' enables to turn off parallel computing
                  for debuging without changing the codepath
                - early capture of pickling errors

            \* An optional progress meter.

            \* Interruption of multiprocesses jobs with 'Ctrl-C'

        Examples
        --------

        A simple example:

        >>> from math import sqrt
        >>> from joblib import Parallel, delayed
        >>> Parallel(n_jobs=1)(delayed(sqrt)(i\*\*2) for i in range(10))
        [0.0, 1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0, 9.0]

        Reshaping the output when the function has several return
        values:

        >>> from math import modf
        >>> from joblib import Parallel, delayed
        >>> r = Parallel(n_jobs=1)(delayed(modf)(i/2.) for i in range(10))
        >>> res, i = zip(\*r)
        >>> res
        (0.0, 0.5, 0.0, 0.5, 0.0, 0.5, 0.0, 0.5, 0.0, 0.5)
        >>> i
        (0.0, 0.0, 1.0, 1.0, 2.0, 2.0, 3.0, 3.0, 4.0, 4.0)

        The progress meter: the higher the value of `verbose`, the more
        messages::

            >>> from time import sleep
            >>> from joblib import Parallel, delayed
            >>> r = Parallel(n_jobs=2, verbose=5)(delayed(sleep)(.1) for _ in range(10)) #doctest: +SKIP
            [Parallel(n_jobs=2)]: Done   1 out of  10 | elapsed:    0.1s remaining:    0.9s
            [Parallel(n_jobs=2)]: Done   3 out of  10 | elapsed:    0.2s remaining:    0.5s
            [Parallel(n_jobs=2)]: Done   6 out of  10 | elapsed:    0.3s remaining:    0.2s
            [Parallel(n_jobs=2)]: Done   9 out of  10 | elapsed:    0.5s remaining:    0.1s
            [Parallel(n_jobs=2)]: Done  10 out of  10 | elapsed:    0.5s finished

        Traceback example, note how the line of the error is indicated
        as well as the values of the parameter passed to the function that
        triggered the exception, even though the traceback happens in the
        child process::

         >>> from string import atoi
         >>> from joblib import Parallel, delayed
         >>> Parallel(n_jobs=2)(delayed(atoi)(n) for n in ('1', '300', 30)) #doctest: +SKIP
         #...
         ---------------------------------------------------------------------------
         Sub-process traceback:
         ---------------------------------------------------------------------------
         TypeError                                          Fri Jul  2 20:32:05 2010
         PID: 4151                                     Python 2.6.5: /usr/bin/python
         ...........................................................................
         /usr/lib/python2.6/string.pyc in atoi(s=30, base=10)
             398     is chosen from the leading characters of s, 0 for octal, 0x or
             399     0X for hexadecimal.  If base is 16, a preceding 0x or 0X is
             400     accepted.
             401
             402     \"\"\"
         --> 403     return _int(s, base)
             404
             405
             406 # Convert string to long integer
             407 def atol(s, base=10):

         TypeError: int() can't convert non-string with explicit base
         ___________________________________________________________________________

        Using pre_dispatch in a producer/consumer situation, where the
        data is generated on the fly. Note how the producer is first
        called a 3 times before the parallel loop is initiated, and then
        called to generate new data on the fly. In this case the total
        number of iterations cannot be reported in the progress messages::

         >>> from math import sqrt
         >>> from joblib import Parallel, delayed

         >>> def producer():
         ...     for i in range(6):
         ...         print 'Produced %s' % i
         ...         yield i

         >>> out = Parallel(n_jobs=2, verbose=100, pre_dispatch='1.5\*n_jobs')(
         ...                         delayed(sqrt)(i) for i in producer()) #doctest: +SKIP
         Produced 0
         Produced 1
         Produced 2
         [Parallel(n_jobs=2)]: Done   1 jobs       | elapsed:    0.0s
         Produced 3
         [Parallel(n_jobs=2)]: Done   2 jobs       | elapsed:    0.0s
         Produced 4
         [Parallel(n_jobs=2)]: Done   3 jobs       | elapsed:    0.0s
         Produced 5
         [Parallel(n_jobs=2)]: Done   4 jobs       | elapsed:    0.0s
         [Parallel(n_jobs=2)]: Done   5 out of   6 | elapsed:    0.0s remaining:    0.0s
         [Parallel(n_jobs=2)]: Done   6 out of   6 | elapsed:    0.0s finished
    '''
    def __init__(self, n_jobs=1, verbose=0, pre_dispatch='all'):
        self.verbose = verbose
        self.n_jobs = n_jobs
        self.pre_dispatch = pre_dispatch
        self._pool = None
        # Not starting the pool in the __init__ is a design decision, to be
        # able to close it ASAP, and not burden the user with closing it.
        self._output = None
        self._jobs = list()

    def dispatch(self, func, args, kwargs):
        \"\"\" Queue the function for computing, with or without multiprocessing
        \"\"\"
        if self._pool is None:
            job = ImmediateApply(func, args, kwargs)
            index = len(self._jobs)
            if not _verbosity_filter(index, self.verbose):
                self._print('Done %3i jobs       | elapsed: %s',
                        (index + 1,
                            short_format_time(time.time() - self._start_time)
                        ))
            self._jobs.append(job)
            self.n_dispatched += 1
        else:
            self._lock.acquire()
            # If job.get() catches an exception, it closes the queue:
            try:
                job = self._pool.apply_async(SafeFunction(func), args,
                            kwargs, callback=CallBack(self.n_dispatched, self))
                self._jobs.append(job)
                self.n_dispatched += 1
            except AssertionError:
                print '[Parallel] Pool seems closed'
            finally:
                self._lock.release()

    def dispatch_next(self):
        \"\"\" Dispatch more data for parallel processing
        \"\"\"
        self._dispatch_amount += 1
        while self._dispatch_amount:
            try:
                # XXX: possible race condition shuffling the order of
                # dispatchs in the next two lines.
                func, args, kwargs = self._iterable.next()
                self.dispatch(func, args, kwargs)
                self._dispatch_amount -= 1
            except ValueError:
                \"\"\" Race condition in accessing a generator, we skip,
                    the dispatch will be done later.
                \"\"\"
            except StopIteration:
                self._iterable = None
                return

    def _print(self, msg, msg_args):
        \"\"\" Display the message on stout or stderr depending on verbosity
        \"\"\"
        # XXX: Not using the logger framework: need to
        # learn to use logger better.
        if not self.verbose:
            return
        if self.verbose < 50:
            writer = sys.stderr.write
        else:
            writer = sys.stdout.write
        msg = msg % msg_args
        writer('[%s]: %s\\n' % (self, msg))

    def print_progress(self, index):
        \"\"\"Display the process of the parallel execution only a fraction
           of time, controled by self.verbose.
        \"\"\"
        if not self.verbose:
            return
        elapsed_time = time.time() - self._start_time

        # This is heuristic code to print only 'verbose' times a messages
        # The challenge is that we may not know the queue length
        if self._iterable:
            if _verbosity_filter(index, self.verbose):
                return
            self._print('Done %3i jobs       | elapsed: %s',
                        (index + 1,
                         short_format_time(elapsed_time),
                        ))
        else:
            # We are finished dispatching
            queue_length = self.n_dispatched
            # We always display the first loop
            if not index == 0:
                # Display depending on the number of remaining items
                # A message as soon as we finish dispatching, cursor is 0
                cursor = (queue_length - index + 1
                          - self._pre_dispatch_amount)
                frequency = (queue_length // self.verbose) + 1
                is_last_item = (index + 1 == queue_length)
                if (is_last_item or cursor % frequency):
                    return
            remaining_time = (elapsed_time / (index + 1) \*
                        (self.n_dispatched - index - 1.))
            self._print('Done %3i out of %3i | elapsed: %s remaining: %s',
                        (index + 1,
                         queue_length,
                         short_format_time(elapsed_time),
                         short_format_time(remaining_time),
                        ))

    def retrieve(self):
        self._output = list()
        while self._jobs:
            # We need to be careful: the job queue can be filling up as
            # we empty it
            if hasattr(self, '_lock'):
                self._lock.acquire()
            job = self._jobs.pop(0)
            if hasattr(self, '_lock'):
                self._lock.release()
            try:
                self._output.append(job.get())
            except tuple(self.exceptions), exception:
                if isinstance(exception,
                        (KeyboardInterrupt, WorkerInterrupt)):
                    # We have captured a user interruption, clean up
                    # everything
                    if hasattr(self, '_pool'):
                        self._pool.close()
                        self._pool.terminate()
                    raise exception
                elif isinstance(exception, TransportableException):
                    # Capture exception to add information on the local stack
                    # in addition to the distant stack
                    this_report = format_outer_frames(context=10,
                                                      stack_start=1)
                    report = \"\"\"Multiprocessing exception:
%s
---------------------------------------------------------------------------
Sub-process traceback:
---------------------------------------------------------------------------
%s\"\"\" % (
                            this_report,
                            exception.message,
                        )
                    # Convert this to a JoblibException
                    exception_type = _mk_exception(exception.etype)[0]
                    raise exception_type(report)
                raise exception

    def __call__(self, iterable):
        if self._jobs:
            raise ValueError('This Parallel instance is already running')
        n_jobs = self.n_jobs
        if n_jobs < 0 and multiprocessing is not None:
            n_jobs = max(multiprocessing.cpu_count() + 1 + n_jobs, 1)

        # The list of exceptions that we will capture
        self.exceptions = [TransportableException]
        if n_jobs is None or multiprocessing is None or n_jobs == 1:
            n_jobs = 1
            self._pool = None
        else:
            if multiprocessing.current_process()._daemonic:
                # Daemonic processes cannot have children
                n_jobs = 1
                self._pool = None
                warnings.warn(
                    'Parallel loops cannot be nested, setting n_jobs=1',
                    stacklevel=2)
            else:
                self._pool = multiprocessing.Pool(n_jobs)
                self._lock = threading.Lock()
                # We are using multiprocessing, we also want to capture
                # KeyboardInterrupts
                self.exceptions.extend([KeyboardInterrupt, WorkerInterrupt])

        if self.pre_dispatch == 'all' or n_jobs == 1:
            self._iterable = None
            self._pre_dispatch_amount = 0
        else:
            self._iterable = iterable
            self._dispatch_amount = 0
            pre_dispatch = self.pre_dispatch
            if hasattr(pre_dispatch, 'endswith'):
                pre_dispatch = eval(pre_dispatch)
            self._pre_dispatch_amount = pre_dispatch = int(pre_dispatch)
            iterable = itertools.islice(iterable, pre_dispatch)

        self._start_time = time.time()
        self.n_dispatched = 0
        try:
            for function, args, kwargs in iterable:
                self.dispatch(function, args, kwargs)

            self.retrieve()
            # Make sure that we get a last message telling us we are done
            elapsed_time = time.time() - self._start_time
            self._print('Done %3i out of %3i | elapsed: %s finished',
                        (len(self._output),
                         len(self._output),
                            short_format_time(elapsed_time)
                        ))

        finally:
            if n_jobs > 1:
                self._pool.close()
                self._pool.join()
            self._jobs = list()
        output = self._output
        self._output = None
        return output

    def __repr__(self):
        return '%s(n_jobs=%s)' % (self.__class__.__name__, self.n_jobs)

"))
  (py-bug-tests-intern 'stalls-emacs-probably-due-to-syntax-highlighting-lp-1058261-base arg teststring)))

(defun stalls-emacs-probably-due-to-syntax-highlighting-lp-1058261-base (arg)
  (switch-to-buffer (current-buffer))
  (goto-char 6184)
    (while (not (bobp))
      (forward-line -1)
      (end-of-line)
      ;; (when (interactive-p) (sit-for 0.1))
      (beginning-of-line))
    (assert (bobp) nil "stalls-emacs-probably-due-to-syntax-highlighting-lp-1058261-test failed"))

(defun pyindex-mishandles-class-definitions-lp-1018164-test (&optional arg)
  (interactive "p")
  (let ((teststring "#! /usr/bin/env python
# -*- coding: utf-8 -*-
import sys
import io
import subprocess
import re
import copy
import pickle
import textwrap
import datetime
import util
import cldef
import datatypes
from themes.thutil import lisp, fontNames, Color, emacsPosition

###############################################################################
version = 3

###############################################################################
# used to raise a type error if a call is made with incorrect arguments
def _emptyParametersCheck(): pass

###############################################################################
class Font(object, metaclass=cldef.metaClass):
    __cldef = cldef.metaClass.wrapclass()
    __cldef.slots(\"__fontStr\")
    __cldef.fields(\"weight slant width height pointSize size face\")
    __cldef.field(\"mapKey\", initfunc=lambda f:(f.size,f.weight,f.slant))
    __cldef.field(\"sortKey\", initfunc=lambda f:(f.width,f.height))

    ###########################################################################
    __parseFontStrRE = __cldef.constant(re.compile(
        r'-outline-Courier New-(?P<weight>bold|normal)'\\
        r'-(?P<slant>i|r)-normal-normal' \\
        r'-(?P<height>\\d+)-(?P<size>\\d+)-\\d+-\\d+-c-(?P<width>\\d+)-iso10646-1'))

    ###########################################################################
    def __init__(self, fontStr):
        self.__fontStr = fontStr
        match = self.__parseFontStrRE.match(fontStr)
        self.weight = match.group('weight')
        self.slant = 'italic' if match.group('slant') == 'i' else 'regular'
        self.width = int(match.group('width'))//10
        self.height = int(match.group('height'))
        self.pointSize = (int(match.group('size')) + 5)//10
        self.size = \"%sx%s\" % (self.__width, self.__height)
        self.face = \"Courier New\"

    ###########################################################################
    def __str__(self): return self.__fontStr

    ###########################################################################
    def qt(self):
        if 'QtGui' not in globals():
            global QtGui
            from PyQt4 import QtGui
        font = QtGui.QFont(self.face, self.pointSize)
        font.setItalic(self.slant == 'italic')
        font.setBold(self.weight == 'bold')
        return font

###############################################################################
class FontAttrs(object, metaclass=cldef.metaClass):
    __cldef = cldef.metaClass.wrapclass()
    mapKey = property(lambda self: (self.size, self.weight, self.slant))

    ###########################################################################
    class FontAttrs(__cldef.FieldClass):
        access, fields = 'rw', \"fontSize fontWeight fontSlant\"
        def sethook(obj, fieldName, value):
            value = str(value)
            if value in obj.fontOptions(fieldName):
                return value
            raise ValueError(\"%s invalid value for %s\"%(value, fieldName))

    ###########################################################################
    attrNames = __cldef.constant(frozenset(FontAttrs.fields.split()))

    ###########################################################################
    class FontAttrAbbrevs(__cldef.FieldClass):
        access, fields = 'rw', tuple(\"size weight slant\".split())
        def fget(obj): pass
        def gethook(obj,name,\*p):
            return getattr(obj, 'font'+name.capitalize())
        def fset(obj,val): pass
        def sethook(obj,name,val,\*p):
            setattr(obj, 'font'+name.capitalize(), val)

    ###########################################################################
    def __init__(self, size='8x13', weight='bold', slant='regular'):
        self.__initAttrs(\*\*locals())

    ###########################################################################
    def font():
        # font options contain the valid values for each font attr
        _fontOptions = {'weight':('normal','bold'),
                        'slant':('regular','italic')}

        # Get the list of font names from thutil and create the font lookup
        # dict. It is assumed that the weight and slant are not specified,
        # so will fill in the \"typical\" options here.
        _fontMap = dict()
        for fontStr in fontNames():
            for weight in ('normal', 'bold'):
                for slant in ('r', 'i'):
                    font = Font(fontStr.replace(\"\*-\*\", weight+'-'+slant))
                    _fontMap[font.mapKey] = font

        # getFont: use the fontAttrSize, fontWeight and fontSize attrs
        # to lookup the font in _fontMap
        def getFont(self): return _fontMap[self.mapKey]

        # scan all the values of _fontMap an garther all fontSize options
        _fontSizes = set(f.size for f in _fontMap.values())
        def fontSizeSortKey(size):
            return tuple(int(i) for i in size.split('x'))
        _fontOptions['size'] = tuple(sorted(_fontSizes, key=fontSizeSortKey))

        #provide a function to query the fontoptions
        def fontOptions(attrName):
            attrName = attrName.lower()
            if attrName.startswith('font'):
                attrName = attrName[len('font'):]
            return _fontOptions[attrName]

        return property(fget=getFont), staticmethod(fontOptions)
    font, fontOptions = font()

###############################################################################
class ColorAttrs(object, metaclass=cldef.metaClass):
    __cldef = cldef.metaClass.wrapclass()
    attrNames = \"foregroundColor backgroundColor cursorColor\".split()
    attrNames = __cldef.constant(tuple(attrNames))
    __cldef.fields(attrNames.val, 'rw', sethook=Color)

    ###########################################################################
    def __init__(self, backgroundColor=\"grey13\", foregroundColor='navajowhite',
                 cursorColor=None):
        self.backgroundColor = backgroundColor
        self.foregroundColor = foregroundColor
        self.cursorColor = self.getColor_i(cursorColor,\"light green\", \"black\")

    ###########################################################################
    def getColor_i(self, val, forDark, forLight):
        if val is None:
            val = forDark if self.backgroundColor.isDark() else forLight
        return Color(val)

###############################################################################
class Face(object, metaclass=cldef.metaClass):
    ###########################################################################
    __cldef = cldef.metaClass.wrapclass(privAttrAccess=True)
    unspecified = __cldef.constant(None)
    __cldef.fields('name theme')
    __cldef.fields('inherit', access='rw',
                   sethook=lambda obj,val: obj.setInheritHook_i(val))

    ###########################################################################
    class FontAttrs(__cldef.FieldClass):
        access, fields = 'rw', (\"bold\",\"italic\",\"underline\",\"raised\")
        sethook = lambda val: val if val is None else bool(val)
        gethook = lambda obj,attr,val: obj.getAttrHook_i(attr, val)

    ###########################################################################
    class ColorAttrs(__cldef.FieldClass):
        access, fields = 'rw', (\"foreground\", \"background\")
        sethook = lambda val: val if val is None else Color(val)
        gethook = lambda obj,attr,val: obj.getAttrHook_i(attr, val)

    ###########################################################################
    fontAttrs, colorAttrs, faceAttrs = __cldef.constants(
        frozenset(FontAttrs.fields),
        frozenset(ColorAttrs.fields),
        frozenset(FontAttrs.fields + ColorAttrs.fields + ('inherit',)))

    ###########################################################################
    def __init__(self, name, theme, \*\*opts):
        self.name, self.theme = name, theme
        for attr in self.faceAttrs:
            self.__setPrivAttr(attr,None)
        for attr,val in opts.items():
            setattr(self, attr, val)

    ###########################################################################
    def __str__(self):
        return self.setFaceSexpr()

    ###########################################################################
    def copy(self):
        copy = self.__class__(self.name, self.theme)
        for attr in self.faceAttrs:
            copy.__setPrivAttr(attr, self.__getPrivAttr(attr))
        return copy

    ###########################################################################
    def __eq__(self, peer):
        if not isinstance(peer, Face):
            return NotImplemented
        getSelf, getPeer = self.__getPrivAttr, peer.__getPrivAttr
        return (self.name == peer.name and
                self.faceAttrs == peer.faceAttrs and
                all(getSelf(a) == getPeer(a) for a in self.faceAttrs))

    ###########################################################################
    def __neq__(self, peer):
        return not(self == peer)

    ###########################################################################
    def reset(self, peer):
        for attr in self.faceAttrs:
            self.__setPrivAttr(attr, peer.__getPrivAttr(attr))

    ###########################################################################
    def isSet(self, attr):
        return self.__getPrivAttr(attr) is not None

    ###########################################################################
    def getPeer(self, peerName):
        if peerName in (None, 'default'):
            return self.theme.defaultFace
        return self.theme.facesAttrs[peerName]

    ###########################################################################
    def inheritOrder(self):
        return (self.name, ) + self.getPeer(self.inherit).inheritOrder()

    ###########################################################################
    def derivesFrom(self, peer):
        return self.theme == peer.theme and peer.name in self.inheritOrder()

    ###########################################################################
    def getSource(self, attr):
        return self if self.isSet(attr) else \\
               self.getPeer(self.inherit).getSource(attr)

    ###########################################################################
    def getAttrHook_i(self, attr, val):
        return val if val is not None \\
               else getattr(self.getPeer(self.inherit), attr)

    ###########################################################################
    def setInheritHook_i(self, val):
        if val in (None, 'default'):
            return None
        if isinstance(val, str):
            theme = self.theme
            if not(hasattr(theme, 'faceAttrs')) or val in theme.faceAttrs:
                return val
        raise ValueError(\"Invalid inherit value=%s\" % val)

    ###########################################################################
    def getLispValue(self, attr, mapBool=('nil','t')):
        val = self.__getPrivAttr(attr)
        if val is None:
            return \"'unspecified\"
        if isinstance(val, bool):
            return mapBool[int(val)]
        if isinstance(val, str):
            return \"'%s\" % val
        if isinstance(val, Color):
            return '\"%s\"' % (val,)
        raise ValueError(\"getLispValue(%s): Invalid attr val=%s\" % (attr,val))

    ###########################################################################
    def setFaceSexpr(self, parms=\"\"):
        isSet, lispVal = self.isSet, self.getLispValue
        # add inhert attr
        if isSet('inherit'):
            parms += ' :inherit %s' % lispVal('inherit')

        # add foreground, background color attrs if attr is set
        for attr in filter(isSet, self.colorAttrs):
            parms += ' :%s %s' % (attr, lispVal(attr))

        # add bold attr
        if isSet('bold'):
            parms += ' :weight %s' % lispVal('bold', (\"'normal\", \"'bold\"))

        # add italic attr
        if isSet('italic'):
            parms += ' :slant %s' % lispVal('italic', (\"'normal\", \"'italic\"))

        # add underline attr
        if isSet('underline'):
            parms += ' :underline %s' % lispVal('underline')

        # add raised attr
        if isSet('raised'):
            val = lispVal('raised')
            if val == 't':
                val = '(:line-width 2 :color \"%s\" :style released-button)' % \\
                      self.foreground.blend(self.background)
            parms += ' :box %s' % val

        # make func call to set face in emacs
        return \"(themes-set-face '%s %s)\" % (self.name, parms)

###############################################################################
class DefaultFace(Face, metaclass=cldef.metaClass):
    __cldef = cldef.metaClass.wrapclass()
    inherit, underline, raised = __cldef.constants(None, False, False)
    ###########################################################################
    def __init__(self, theme):
        self.__super.__init__(\"default\", theme)

    ###########################################################################
    bold = property(lambda self: self.theme.font.weight == 'bold')
    italic = property(lambda self: self.theme.font.slant == 'italic')
    foreground = property(lambda self: self.theme.foregroundColor)
    background = property(lambda self: self.theme.backgroundColor)

    ###########################################################################
    def setFaceSexpr(self):
        return '(themes-set-defaults \"%s\" \"%s\" \"%s\")' % \\
               (self.foreground, self.background, self.theme.font)

    ###########################################################################
    def isSet(self, attr):
        return True

    ###########################################################################
    def inheritOrder(self):
        return (self.name,)

###############################################################################
class FacesAttrs(object, metaclass=cldef.metaClass):
    __cldef = cldef.metaClass.wrapclass()
    __cldef.slots(\"__faceMap __faces\")
    __cldef.field(\"theme\")

    ###########################################################################
    def __init__(self, theme, facesAttrs=None):
        self.theme,  self.__faceMap, self.__faces = theme, {}, []
        if facesAttrs is None:
            facesAttrs = self.loadFacesFromEmacs_i()
        for faceAttrs in facesAttrs:
            face = Face(theme=theme, \*\*faceAttrs)
            if self.__faceMap.setdefault(face.name, face) is not face:
                raise KeyError(\"Face name %r is not unique\" % face.name)
            self.__faces.append(face)
        for face in self.__faces:
            if face.inherit is not None:
                assert face.inherit in self.__faceMap

    ###########################################################################
    def copy(self):
        copy = self.__class__.__new__(self.__class__)
        copy.theme = self.theme
        copy.__faces = [f.copy() for f in self.__faces]
        copy.__faceMap = dict((f.name,f) for f in copy.__faces)
        return copy

    ###########################################################################
    def reset(self, peer):
        self.__faces = [f.copy() for f in peer.__faces]
        self.__faceMap = dict((f.name,f) for f in self.__faces)

    ###########################################################################
    def __len__(self):
        return len(self.__faceMap)

    ###########################################################################
    def __iter__(self):
        return iter(self.__faces)

    ###########################################################################
    def __eq__(self, peer):
        if not isinstance(peer, FacesAttrs):
            return NotImplemented
        return self.__faceMap == peer.__faceMap

    ###########################################################################
    def __neq__(self, peer):
        return not(self == peer)

    ###########################################################################
    def get(self, name, default=None):
        return self.__faceMap.get(name,default)

    ###########################################################################
    def __getitem__(self, name):
        return self.__faceMap[name]

    ###########################################################################
    def __contains__(self, name):
        return name in self.__faceMap

    ###########################################################################
    def loadFacesFromEmacs_i(self):
        facesSexpr = textwrap.dedent(\"\"\"\\
        (progn (add-to-list 'load-path \"%(elDir)s\")
               (add-to-list 'load-path \"%(elDir)s/python\")
               (add-to-list 'load-path \"%(elDir)s/imported\")
               (require 'themes)
               (write-region (themes-python-faces-attrs %(thColors)s)
                             nil \"%(outFile)s\")
               (kill-emacs))\"\"\")
        facesSexpr = ' '.join(facesSexpr.split())
        thColors = self.theme.foregroundColor, self.theme.backgroundColor
        outFile = (util.dirPath('\$TEMP')/'themeFaces.py').uniquify()
        facesSexpr %= {'elDir': util.Path('~/emacs').emacsName,
                       'thColors': '\"%s\" \"%s\"' % thColors,
                       'outFile': outFile.emacsName}
        try:
            subprocess.check_call(['emacs.exe', '--no-init-file',
                                   '--iconic', '--eval', facesSexpr],
                                   shell=True)
            return eval(outFile.text().replace('\\r\\n', '\\n'))
        finally:
            if outFile.isfile():
                outFile.remove()

###############################################################################
class ThemeChoice(object, metaclass=cldef.metaClass):
    __cldef = cldef.metaClass.wrapclass()
    __cldef.slots(\"__args\")

    ##########################################################################
    def __namedTests():
        _darkThreshold = 3 \* 255 \* 0.6
        def isThemeBackgroundDark(theme):
            return sum(theme.colorAttrs.backgroundColor) < _darkThreshold
        def isThemeBold(theme):
            return theme.fontAttrs.weight == 'bold'
        return dict(isThemeBackgroundDark = isThemeBackgroundDark,
                    isThemeFontBold = isThemeBold)
    __namedTests = __cldef.constant(__namedTests())

    ###########################################################################
    def __init__(self, theme, themeTest, onTrueValue, onFalseValue):
        self.__args= (theme, themeTest, onTrueValue, onFalseValue)

    ###########################################################################
    def __call__(self):
        theme, themeTest, onTrueValue, onFalseValue = self.__args
        if isinstance(themeTest, str):
            themeTest = self.__namedTests[themeTest]
        if themeTest(theme):
            return onTrueValue
        return onFalseValue

###############################################################################
class ThemeAccessor(object, metaclass=cldef.metaClass):
    __cldef = cldef.metaClass.wrapclass()
    __cldef.slots(\"__args\")

    ###########################################################################
    def __init__(self, theme, path):
        self.__args = (theme, path.split(\".\"))

    ###########################################################################
    def __call__(self):
        obj, path = self.__args
        for attr in path:
            obj = getattr(obj, attr)
        return obj

###############################################################################
class EmacsFrameTheme(object, metaclass=cldef.metaClass):
    __cldef = cldef.metaClass.wrapclass()
    __cldef.fields(\"name colorAttrs fontAttrs defaultFace facesAttrs \"
                   \"canDelete\")
    foregroundColor = property(lambda self: self.colorAttrs.foregroundColor)
    backgroundColor = property(lambda self: self.colorAttrs.backgroundColor)
    font = property(lambda self: self.fontAttrs.font)

    ###########################################################################
    def __str__(self):
        return util.nomen(self, \"%s:%s\" % (self.name, hex(id(self))))

    ###########################################################################
    def __init__(self, name, \*\*themeOpts):
        self.name = name
        self.colorAttrs = ColorAttrs()
        self.fontAttrs = FontAttrs()
        self.defaultFace = DefaultFace(self)
        facesAttrs = themeOpts.pop('facesAttrs', None)
        self.facesAttrs = FacesAttrs(self, facesAttrs=facesAttrs)
        self.canDelete = themeOpts.pop('canDelete', True)
        self.update(themeOpts)

    ###########################################################################
    def update(self, \*args, \*\*opts):
        if len(args) > 1:
            raise TypeError(\"Can be at most one positional argument\")
        opts = dict((args[0] if args else ()), \*\*opts)
        for attrs in (self.colorAttrs, self.fontAttrs):
            for attrName in attrs.attrNames:
                val = opts.pop(attrName, None)
                if val is not None:
                    setattr(attrs, attrName, val)
        _emptyParametersCheck(\*\*opts)

    ###########################################################################
    @classmethod
    def loadTheme(cls, themeFile, canDelete=True):
        themeFile = util.Path(themeFile, lambda f: f.isfile() and f.ext=='.el')
        themeSexpr = textwrap.dedent(\"\"\"\\
        (progn (add-to-list 'load-path \"%(elDir)s\")
               (add-to-list 'load-path \"%(elDir)s/python\")
               (add-to-list 'load-path \"%(elDir)s/imported\")
               (require 'themes)
               (load \"%(themeFile)s\")
               (write-region (themes-python-theme-attrs) nil \"%(outFile)s\")
               (kill-emacs))\"\"\")
        themeSexpr = ' '.join(themeSexpr.split())
        outFile = (util.dirPath('\$TEMP')/'themeAttrs.py').uniquify()
        themeSexpr %= {'elDir': util.Path('~/emacs').emacsName,
                       'themeFile': themeFile.stripext().emacsName,
                       'outFile': outFile.emacsName}
        try:
            subprocess.check_call(['emacs.exe', '--no-init-file',
                                   '--iconic', '--eval', themeSexpr],
                                   shell=True)
            themeOpts, facesAttrs = eval(outFile.text().replace('\\r\\n','\\n'))
            # convert the font string spec returned by emacs to fontAttrs
            # argumets expected by __init__
            font = Font(themeOpts.pop('font'))
            themeOpts.update(fontSize=font.size, fontWeight=font.weight,
                             fontSlant=font.slant, canDelete=canDelete)
            themeName = themeFile.namebase
            return cls(themeName, facesAttrs=facesAttrs, \*\*themeOpts)
        finally:
            if outFile.isfile():
                outFile.remove()

    ###########################################################################
    def copy(self, newThemeName, \*\*newThemeOpts):
        newTheme = copy.deepcopy(self)
        newTheme.__name = newThemeName
        newTheme.update(newThemeOpts)
        return newTheme

    ###########################################################################
    def __eq__(self, peer):
        if not isinstance(peer, EmacsFrameTheme):
            return NotImplemented
        return (self.name == peer.name and
                self.foregroundColor == peer.foregroundColor and
                self.backgroundColor == peer.backgroundColor and
                self.font == peer.font and
                self.facesAttrs == peer.facesAttrs)

    ###########################################################################
    def __neq__(self, peer):
        return not(self == peer)

    ###########################################################################
    @property
    def sexpr(self):
        cursor = Face('cursor', self, background=self.colorAttrs.cursorColor)
        faces = [self.defaultFace, cursor] + list(self.facesAttrs)
        return \"(progn\\n  %s)\" % \"\\n  \".join(f.setFaceSexpr() for f in faces)

    ###########################################################################
    __applyFormat = \"%(sexpr)s\\n(themes-save-cache-file (quote %(sexpr)s))\"

    ###########################################################################
    def applyTheme(self):
        lisp(self.__applyFormat % dict(sexpr=self.sexpr))

    ###########################################################################
    def accessor(self, \*p, \*\*kw):
        return ThemeAccessor(self, \*p, \*\*kw)

    ###########################################################################
    def choice(self, \*p, \*\*kw):
        return ThemeChoice(self, \*p, \*\*kw)

###############################################################################
def cacheFilePath(path):
    return util.Path(path, lambda f: not(f.isdir()))

###############################################################################
class EmacsFrameThemes(object, metaclass=cldef.metaClass):
    __cldef = cldef.metaClass.wrapclass()
    __cldef.slots(\"__themes\")
    __cldef.field('cacheFile', 'ri', sethook=cacheFilePath)
    __cldef.field(\"saveEnabled\", 'rw', initval=True, sethook=bool)
    __cldef.field(\"current\", 'rw',
                  fset=lambda obj,theme: obj.setCurrentTheme(theme))

    ###########################################################################
    def __new__(cls, themeMgr=None):
        if themeMgr is None:
            # pickle internals called __new__ SURPRISE!
            return object.__new__(cls)
        if themeMgr.cacheFile.isfile():
            # load themes from cache file
            return cls.loadCache_i(themeMgr.cacheFile)
        themes = object.__new__(cls)
        elispFiles = themeMgr.archive.files('\*.el')
        if elispFiles:
            # load themes from a collection (archive) of elisp files created
            # this module and emacs can use to initialize themes
            themes.loadArchive_i(elispFiles, themeMgr.cacheFile)
        else:
            # create themes using a few 'canned' themes
            themes.bootstrap_i(themeMgr.cacheFile)
        return themes

    ###########################################################################
    @classmethod
    def loadCache_i(cls, cacheFile):
        try:
            with cacheFile.open('rb') as cacheFP:
                themes = pickle.load(cacheFP)
        except:
            # If file has windows newlines '\\r\\n', read it as text which
            # converting newlines, encode to bytes and retry loading
            themes = pickle.loads(cacheFile.text().encode())
        assert isinstance(themes, cls)
        themes.__cacheFile = cacheFilePath(cacheFile)
        return themes

    ###########################################################################
    def loadArchive_i(self, elispFiles, cacheFile):
        self.__themes = []
        self.cacheFile, self.saveEnabled = cacheFile, False
        elispFiles = dict((f.namebase, f) for f in elispFiles)
        # load archive files in (standard themes) order. if no arcive file
        # is named after a standard theme, create it using provided args
        for thName,thOpts in ((d['name'],d) for d in self.standardThemes()):
            elispFile = elispFiles.pop(thName, None)
            if elispFile is not None:
                self.addTheme(EmacsFrameTheme.loadTheme(
                    elispFile, thOpts['canDelete']))
            else:
                self.addTheme(EmacsFrameTheme(\*\*thOpts))
        # load any remaining archive files
        for elispFile in sorted(elispFiles.values()):
            self.addTheme(EmacsFrameTheme.loadTheme(elispFile))
        self.current = self.__themes[0]
        self.saveEnabled = True
        self.save()

    ###########################################################################
    @staticmethod
    def standardThemes():
        return [dict(name='dark_frames', canDelete=False),
                dict(name='red_frames', canDelete=False,
                     backgroundColor=\"RGB:55/0/0\"),
                dict(name=\"green_frames\", canDelete=False,
                     backgroundColor=\"RGB:16/25/25\"),
                dict(name=\"blue_frames\", canDelete=False,
                     backgroundColor=\"RGB:0B/0B/2D\"),
                dict(name=\"light_frames\", canDelete=False,
                     foregroundColor='black',
                     backgroundColor='white')]

    ###########################################################################
    def bootstrap_i(self, cacheFile):
        self.__themes = []
        self.cacheFile, self.saveEnabled = cacheFile, False
        # create dark theme as current theme
        self.current = EmacsFrameTheme(\"dark_frames\", canDelete=False)
        # create red theme
        self.addTheme(EmacsFrameTheme(\"red_frames\", canDelete=False,
                                      backgroundColor=\"RGB:55/0/0\"))
        # create green theme
        self.addTheme(EmacsFrameTheme(\"green_frames\", canDelete=False,
                                      backgroundColor=\"RGB:16/25/25\"))
        # create blue theme
        self.addTheme(EmacsFrameTheme(\"blue_frames\", canDelete=False,
                                      backgroundColor=\"RGB:0B/0B/2D\"))
        # create light theme from default
        self.addTheme(EmacsFrameTheme(\"light_frames\", canDelete=False,
                                      foregroundColor='black',
                                      backgroundColor='white'))
        self.saveEnabled = True
        self.save()

    ###########################################################################
    def reset(self, prototype, copy=True):
        assert type(self) is type(prototype)
        if copy:
            prototype = copy.deepcopy(prototype)
        for attr in self.__slots__:
            setattr(self, attr, getattr(prototype, attr))
        self.save()

    ###########################################################################
    def save(self):
        if self.saveEnabled:
            with self.cacheFile.open('wb') as cacheFile:
                pickle.dump(self, cacheFile)

    ###########################################################################
    def addTheme(self, theme):
        if theme.name in self:
            raise KeyError(\"theme.name(%s) is not unique\" % theme.name)
        self.__themes.append(theme)
        self.save()

    ###########################################################################
    def getTheme(self, name, exact=True, default=None):
        if exact:
            for theme in self.__themes:
                if theme.name == name:
                    return theme
        else:
            name = name.strip().lower()
            for theme in self.__themes:
                if name in theme.name.lower():
                    return theme
        return default

    ###########################################################################
    def setCurrentTheme(self, theme):
        if isinstance(theme,str):
            theme = self.getTheme(theme)
        if isinstance(theme, EmacsFrameTheme):
            self.__current = theme
            if theme not in self:
                self.addTheme(theme)
        else:
            raise ValueError(\"%s invalid theme\" % theme)

    ###########################################################################
    def removeTheme(self, theme, force=False):
        # arg can be either a theme instance or a str naming the theme
        if isinstance(theme,str):
            theme = self.getTheme(theme)
        if not force:
            if len(self.__themes) == 1:
                raise ValueError(\"Can't remove last theme\")
            if not theme.canDelete:
                raise ValueError(\"Theme %s can't be removed\" % theme.name)
        # remove the theme from both the themes list
        self.__themes.remove(theme)
        # adjust current attr if theme deleted was current one
        if theme == self.__current:
            try:
                self.__current = self.__themes[0]
            except IndexError:
                del self.__current
        self.save()

    ###########################################################################
    def swapThemes(self, theme1, theme2):
        if isinstance(theme1, str):
            theme1 = self.getTheme(theme1)
        if isinstance(theme2, str):
            theme2 = self.getTheme(theme2)
        index1 = self.__themes.index(theme1)
        index2 = self.__themes.index(theme2)
        self.__themes[index2] = theme1
        self.__themes[index1] = theme2

    ###########################################################################
    def __iter__(self):
        return iter(self.__themes)

    ###########################################################################
    def __len__(self):
        return len(self.__themes)

    ###########################################################################
    def __contains__(self, item):
        if isinstance(item, str):
            return item in (theme.name for theme in self.__themes)
        return item in self.__themes

###############################################################################
class EmacsFrameThemeManager(datatypes.Singleton, metaclass=cldef.metaClass):
    __cldef = cldef.metaClass.wrapclass()
    __cldef.fields('themesDir cacheFile archive')
    __cldef.field('themes', 'r', initfunc=lambda obj: EmacsFrameThemes(obj))
    currentTheme = property(lambda self: self.themes.current)

    ###########################################################################
    def newSingleton_i(self, themesDir=None):
        self.__super.newSingleton_i()
        if themesDir is None:
            themesDir = '\$APPDATA/_emacsthemes_v%d' % version
        self.themesDir = util.dirPath(themesDir)
        archive = self.themesDir/'archive'
        if not archive.exists():
            archive.mkdir()
        self.archive = util.dirPath(archive)
        self.cacheFile = self.themesDir/'cache.pkl'

    ###########################################################################
    def applyNamedTheme(self, themeName, exact=True):
        themeName = themeName.replace(\"-\",\"_\")
        self.__themes.current = self.__themes.getTheme(themeName, exact)
        self.currentTheme.applyTheme()

    ###########################################################################
    def setFrameTheme(self, themeName, \*\*themeOpts):
        self.__themes.current = themeName
        self.currentTheme.update(themeOpts)
        self.currentTheme.applyTheme()

    ###########################################################################
    def gui(self):
        global EmacsFrameThemesApp
        try:
            guiRun = EmacsFrameThemesApp.run
        except NameError:
            from themes.thgui import EmacsFrameThemesApp
            guiRun = EmacsFrameThemesApp.run
        guiRun(self, tuple(i+50 for i in emacsPosition()))

    ###########################################################################
    def archiveThemes(self):
        textFormat = textwrap.dedent(\"\"\"\\
        ;;; %s :: %s -\*-Emacs-Lisp-\*-
        ;;; -- Used by themes.el for persistance of current frame theme
        ;;;    settings across emacs invocations
        %s
        \"\"\")
        for theme in self.themes:
            archiveFile = self.archive/(theme.name + '.el')
            timeStr = datetime.datetime.now().strftime(\"%a %b %d %H:%M:%S %Y\")
            archiveFile.write_text(
                textFormat % (archiveFile.name, timeStr, theme.sexpr))
"))
  (py-bug-tests-intern 'pyindex-mishandles-class-definitions-lp-1018164-base arg teststring)))

(defun pyindex-mishandles-class-definitions-lp-1018164-base (arg)
    (goto-char 25548)
    (assert (eq 26242 (py-end-of-def-or-class)) nil "pyindex-mishandles-class-definitions-lp-1018164-test failed"))

(defun exception-in-except-clause-highlighted-as-keyword-lp-909205-test (&optional arg)
  (interactive "p")
  (let ((teststring "#! /usr/bin/env python
# -*- coding: utf-8 -*-
try:
    blah
except ormexc.NoResultFound:
    pass
"))
  (py-bug-tests-intern 'exception-in-except-clause-highlighted-as-keyword-lp-909205-base arg teststring)))

(defun exception-in-except-clause-highlighted-as-keyword-lp-909205-base (arg)
  (font-lock-fontify-buffer)
  (goto-char 65)
  (sit-for 0.1)
  (assert (eq (get-char-property (point) 'face) 'font-lock-keyword-face) nil "exception-in-except-clause-highlighted-as-keyword-lp-909205-test #1 failed")
  (goto-char 77)
  (assert (eq (get-char-property (point) 'face) 'py-exception-name-face) nil "exception-in-except-clause-highlighted-as-keyword-lp-909205-test #2 failed"))

(defun inconvenient-window-splitting-behavior-python-lp-1018996-test (&optional arg)
  (interactive "p")
  (let ((teststring "#! /usr/bin/env python
# -*- coding: utf-8 -*-
import re
import sys
import os
re.DE
os.EX_CONF
"))
  (py-bug-tests-intern 'inconvenient-window-splitting-behavior-python-lp-1018996-base arg teststring)))

(defun inconvenient-window-splitting-behavior-python-lp-1018996-base (arg)
  (goto-char 84)
  (py-shell-complete nil t)
  (sit-for 0.1)
  (assert (looking-back "^re.DEBUG") nil "inconvenient-window-splitting-behavior-python-lp-1018996-test #1 failed")
  (goto-char 98)
  (py-shell-complete nil t)
  (sit-for 0.1)
  (assert (looking-back "^os.EX_CONFIG") nil "inconvenient-window-splitting-behavior-python-lp-1018996-test #2 failed"))

(defun inconvenient-window-splitting-behavior-ipython-lp-1018996-test (&optional arg)
  (interactive "p")
  (let ((teststring "#! /usr/bin/env ipython
# -*- coding: utf-8 -*-
import re
import sys
import os
re.
os.
"))
  (py-bug-tests-intern 'inconvenient-window-splitting-behavior-ipython-lp-1018996-base arg teststring)))

(defun inconvenient-window-splitting-behavior-ipython-lp-1018996-base (arg)
  (goto-char 83)
  (py-shell-complete nil t)
  (sit-for 0.1 t)
  (set-buffer "*Python Completions*")
  (goto-char (point-min))
  (assert (search-forward  "re." nil t 1) nil "inconvenient-window-splitting-behavior-ipython-lp-1018996-test #1 failed")
  (goto-char 87)
  (py-shell-complete nil t)
  (assert (search-forward  "re." nil t 1) nil "inconvenient-window-splitting-behavior-ipython-lp-1018996-test #2 failed"))


(defun impossible-to-execute-a-buffer-with-from-future-imports-lp-1063884-test (&optional arg)
  (interactive "p")
  (let ((teststring "#! /usr/bin/env python
# -*- coding: utf-8 -*-
from __future__ import with_statement
print(\"I'm the \\\"impossible-to-execute-a-buffer-with-from-future-imports-lp-1063884-test\\\"\")
"))
  (py-bug-tests-intern 'impossible-to-execute-a-buffer-with-from-future-imports-lp-1063884-base arg teststring)))

(defun impossible-to-execute-a-buffer-with-from-future-imports-lp-1063884-base (arg)
  (when
      (assert (not (ignore (py-execute-buffer))) nil "impossible-to-execute-a-buffer-with-from-future-imports-lp-1063884-test failed")
    (message "%s" "impossible-to-execute-a-buffer-with-from-future-imports-lp-1063884-test passed")))

(defun several-new-bugs-with-paragraph-filling-lp-1066489-test (&optional arg)
  (interactive "p")
  (let ((teststring "#! /usr/bin/env python
# -*- coding: utf-8 -*-
class IBanManager(Interface):
    \"\"\"The global manager of email address bans.\"\"\"

    def ban(email):
        \"\"\"Ban an email address from subscribing to a mailing list.

        The `IBanManager` is created by adapting an `IMailingList` or ``None``.
        For global bans, use ``None``.

        When an email address is banned, it will not be allowed to subscribe
        to a the named mailing list. This does not affect any email address
        already subscribed to the mailing list.

        It is also possible to add a 'ban pattern' whereby all email addresses
        matching a Python regular expression can be banned. This is
        accomplished by using a `^` as the first character in `email`.

        When an email address is already banned for the given mailing list (or
        globally), then this method does nothing. However, it is possible to
        extend a ban for a specific mailing list into a global ban; both bans
        would be in place and they can be removed individually.

        :param email: The text email address being banned or, if the string
            starts with a caret (^), the email address pattern to ban.
        :type email: str
        :param mailing_list: The fqdn name of the mailing list to which the
            ban applies. If None, then the ban is global.
        :type mailing_list: string
        \"\"\"
"))
  (py-bug-tests-intern 'several-new-bugs-with-paragraph-filling-lp-1066489-base arg teststring)))

(defun several-new-bugs-with-paragraph-filling-lp-1066489-base (arg)
  (goto-char 932)
  (py-fill-paragraph)
  (sit-for 0.1)
  (when
      (assert (re-search-forward "^ +:type email") nil "several-new-bugs-with-paragraph-filling-lp-1066489-test failed")
    (message "%s" "several-new-bugs-with-paragraph-filling-lp-1066489-test passed")))

(defun incorrect-indentation-of-one-line-functions-lp-1067633-test (&optional arg)
  (interactive "p")
  (let ((teststring "#! /usr/bin/env python
# -*- coding: utf-8 -*-
def foo():
    pass
"))
  (py-bug-tests-intern 'incorrect-indentation-of-one-line-functions-lp-1067633-base arg teststring)))

(defun incorrect-indentation-of-one-line-functions-lp-1067633-base (arg)
  (goto-char 67)
  (when
      (assert (eq 4 (py-compute-indentation)) nil "incorrect-indentation-of-one-line-functions-lp-1067633-test failed")
    (message "%s" "incorrect-indentation-of-one-line-functions-lp-1067633-test passed")))

(defun does-not-dedent-regions-lp-1072869-test (&optional arg)
  (interactive "p")
  (let ((teststring "        print(\"HELLO\")"))
  (py-bug-tests-intern 'does-not-dedent-regions-lp-1072869-base arg teststring)))

(defun does-not-dedent-regions-lp-1072869-base (arg)
  (let ((oldbuf (current-buffer)))
    (or
	(assert (progn (py-execute-buffer-python)(set-buffer "*Python*")(goto-char (point-max))(search-backward "HELLO")) nil "does-not-dedent-regions-lp-1072869-test #2 failed")
      (message "%s" "does-not-dedent-regions-lp-1072869-test #2 passed"))
    (py-kill-buffer-unconditional "*Python*")
    (set-buffer oldbuf)
    (or
	(assert (progn (py-execute-buffer-ipython)(set-buffer "*IPython*")(goto-char (point-max))(search-backward "HELLO")) nil "does-not-dedent-regions-lp-1072869-test #1 failed")
      (message "%s" "does-not-dedent-regions-lp-1072869-test #1 passed"))))

(defun inconvenient-py-switch-buffers-on-execute-lp-1073-test (&optional arg)
  (interactive "p")
  (let ((teststring "#! /usr/bin/env python
# -*- coding: utf-8 -*-
print \"HELLO!\"
"))
  (py-bug-tests-intern 'inconvenient-py-switch-buffers-on-execute-lp-1073-base arg teststring)))

;; doesn't word, patches welcome
(defun inconvenient-py-switch-buffers-on-execute-lp-1073-base (arg)
  (let ((py-switch-buffers-on-execute-p t)
        erg)
    (py-execute-buffer-python)
    (message "current: %s" (buffer-name (current-buffer)))
    (setq erg (string-match "Python" (buffer-name (current-buffer))))
    ;; (assert erg nil "inconvenient-py-switch-buffers-on-execute-lp-1073-test failed")
    (switch-to-buffer (current-buffer))
    ))

(defun fails-to-indent-abs-wrong-type-argument-lp-1075673-test (&optional arg)
  (interactive "p")
  (let ((teststring "#!/usr/bin/env python
# emacs: -\*- mode: python; py-indent-offset: 4; indent-tabs-mode: nil -\*-
# vi: set ft=python sts=4 ts=4 sw=4 et:
### ### ### ### ### ### ### ### ### ### ### ### ### ### ### ### ### ### ### ##
#
#   See COPYING file distributed along with the PyMVPA package for the
#   copyright and license terms.
#
### ### ### ### ### ### ### ### ### ### ### ### ### ### ### ### ### ### ### ##
\"\"\"Python distutils setup for PyMVPA\"\"\"

from numpy.distutils.core import setup, Extension
import os
import sys
from glob import glob

if sys.version_info[:2] < (2, 5):
"))
  (py-bug-tests-intern 'fails-to-indent-abs-wrong-type-argument-lp-1075673-base arg teststring)))

(defun fails-to-indent-abs-wrong-type-argument-lp-1075673-base (arg)
    (assert (eq 4 (py-compute-indentation)) nil "fails-to-indent-abs-wrong-type-argument-lp-1075673-test failed"))

(defun incorrect-indentation-of-comments-in-a-multiline-list-lp-1077063-test (&optional arg)
  (interactive "p")
  (let ((teststring "#!/usr/bin/python
#emacs: -\*- mode: python; py-indent-offset: 4; tab-width: 4; indent-tabs-mode: nil -\*-
#ex: set sts=4 ts=4 sw=4 noet:

class X:
    XX = [
        \"asdfasdF\",
        \"asdfasdf\",
    # lakjsdflkjasdf
    \"lkajsdlkfj\"
    ]

# There is no way to indent #comment line with TAB, nor subsequent list entry to the level of previous
# entries

"))
  (py-bug-tests-intern 'incorrect-indentation-of-comments-in-a-multiline-list-lp-1077063-base arg teststring)))

(defun incorrect-indentation-of-comments-in-a-multiline-list-lp-1077063-base (arg)
    (goto-char 202)
    (assert (eq 8 (py-compute-indentation)) nil "incorrect-indentation-of-comments-in-a-multiline-list-lp-1077063-test failed"))

(defun fill-paragraph-in-a-comment-does-not-stop-at-empty-comment-lines-lp-1077139-test (&optional arg)
  (interactive "p")
  (let ((teststring "#! /usr/bin/env python
# -*- coding: utf-8 -*-
# in older version of python-mode (5.1.0) fill-paragraph (Alt-q) e.g. on first line of

# line1: alskdjfl aksdjlfkas dklfj aslkdjf aklsdj flkasjd fklasjd lfkasj dlkfj asdklfj aslkdfj
#
# line2

# would fill only portion of line1:

# line1: alskdjfl aksdjlfkas dklfj aslkdjf aklsdj flkasjd fklasjd
# lfkasj dlkfj asdklfj aslkdfj
#
# line2

# while current version disregards such stop paragraph separation... unless it is at the beginning of the
# buffer!! ;), so adding an empty line before the first comment line of this test example, results in:

# line1: alskdjfl aksdjlfkas dklfj aslkdjf aklsdj flkasjd fklasjd
# lfkasj dlkfj asdklfj aslkdfj line2

"))
  (py-bug-tests-intern 'fill-paragraph-in-a-comment-does-not-stop-at-empty-comment-lines-lp-1077139-base arg teststring)))

(defun fill-paragraph-in-a-comment-does-not-stop-at-empty-comment-lines-lp-1077139-base (arg)
  (let ((empty-comment-line-separates-paragraph-p t))
    (goto-char 152)
    (fill-paragraph)
    (goto-char 233)
    (beginning-of-line)
    (assert (looking-at paragraph-separate) nil "fill-paragraph-in-a-comment-does-not-stop-at-empty-comment-lines-lp-1077139-test failed")))

(defun spuriously-indents-whole-line-while-making-some-portion-inline-comment-lp-1080973-test (&optional arg)
  (interactive "p")
  (let ((teststring "#! /usr/bin/env python
# -*- coding: utf-8 -*-

# originally it actually added indentation level in my case so code became

#     @sweepargs(clf=[kNN(5)]) #clfswh['multiclass'])
# def test_auc(self, clf):
#     pass

# but on example to reproduce
class A(object):
    def prev():
        pass

    @decorator(1) lkajsd
    def buga():
        pass

# attempt to insert # before lkajsd actually dedented it and made it

class A(object):
    def prev():
        pass

@decorator(1) #lkajsd
    def buga():
        pass

# imho making inline comment should not alter whole line indentation

"))
  (py-bug-tests-intern 'spuriously-indents-whole-line-while-making-some-portion-inline-comment-lp-1080973-base arg teststring)))

(defun spuriously-indents-whole-line-while-making-some-portion-inline-comment-lp-1080973-base (arg)
    (goto-char 312)
    (assert (eq 4 (py-compute-indentation)) nil "spuriously-indents-whole-line-while-making-some-portion-inline-comment-lp-1080973-test #1 failed")
    (goto-char 349)
    (assert (eq 4 (py-compute-indentation)) nil "spuriously-indents-whole-line-while-making-some-portion-inline-comment-lp-1080973-test #2 failed")
    )

(defun imenu-add-menubar-index-fails-lp-1084503-test (&optional arg)
  (interactive "p")
  (let ((teststring "#! /usr/bin/env python
# -*- coding: utf-8 -*-
"))
  (py-bug-tests-intern 'imenu-add-menubar-index-fails-lp-1084503-base arg teststring)))

(defun imenu-add-menubar-index-fails-lp-1084503-base (arg)
  (assert (imenu-add-menubar-index) nil "imenu-add-menubar-index-fails-lp-1084503-test failed"))

(defun fill-paragraph-in-comments-results-in-mess-lp-1084769-test (&optional arg)
  (interactive "p")
  (let ((teststring "#! /usr/bin/env python
# -*- coding: utf-8 -*-
def update():
    # We need to get a reliable checksum for the dictionary in
    # newpkg_list. Dictionary order is unpredictable, so to get a
    # reproducible checksum, we get the items of the dict, sort on the
    # keys, then get the json representation of this sorted list, encode
    # this to bytes assuming utf-8, and hash
    # the resulting bytes.
"))
  (py-bug-tests-intern 'fill-paragraph-in-comments-results-in-mess-lp-1084769-base arg teststring)))

(defun fill-paragraph-in-comments-results-in-mess-lp-1084769-base (arg)
    (goto-char 266)
    (fill-paragraph)
    (beginning-of-line)
    (assert (looking-at "    ") nil "fill-paragraph-in-comments-results-in-mess-lp-1084769-test failed"))

(defun py-execute-buffer-python3-looks-broken-lp-1085386-test (&optional arg)
  (interactive "p")
  (let ((teststring "i = 0
i+=1
print(i)
"))
  (py-bug-tests-intern 'py-execute-buffer-python3-looks-broken-lp-1085386-base arg teststring)))

(defun py-execute-buffer-python3-looks-broken-lp-1085386-base (arg)
  (let ((py-use-current-dir-when-execute-p t))
    (assert (progn (py-execute-buffer-python3) (set-buffer (py--fetch-first-python-buffer))(goto-char (point-min)) (search-forward "1"))  nil "py-execute-buffer-python3-looks-broken-lp-1085386-test failed")))

(defun wrong-indent-after-asignment-lp-1087404-test (&optional arg)
  (interactive "p")
  (let ((teststring "#! /usr/bin/env python
# -*- coding: utf-8 -*-
a = 1
# After pressing enter column 1 as expected
b = [1]

# Now after pressing enter indents to column 4

"))
  (py-bug-tests-intern 'wrong-indent-after-asignment-lp-1087404-base arg teststring)))

(defun wrong-indent-after-asignment-lp-1087404-base (arg)
    (goto-char 106)
    (assert (eq 0 (py-compute-indentation)) nil "wrong-indent-after-asignment-lp-1087404-test failed"))

(defun wrong-indentation-after-return-or-pass-keyword-lp-1087499-test (&optional arg)
  (interactive "p")
  (let ((teststring "#! /usr/bin/env python
# -*- coding: utf-8 -*-
class Foo(self):
    def bar(self):
        return self.baz

class Baz(self):
    def bar(self):
        pass

"))
  (py-bug-tests-intern 'wrong-indentation-after-return-or-pass-keyword-lp-1087499-base arg teststring)))

(defun wrong-indentation-after-return-or-pass-keyword-lp-1087499-base (arg)
  (goto-char 108)
  (assert (eq 4 (py-compute-indentation)) nil "wrong-indentation-after-return-or-pass-keyword-lp-1087499-test failed")
  (goto-char 158)
  (assert (py-compute-indentation) nil "wrong-indentation-after-return-or-pass-keyword-lp-1087499-test failed"))

(defun temporary-files-remain-when-python-raises-exception-lp-1083973-n1-test (&optional arg)
  (interactive "p")
  (let ((teststring "#! /usr/bin/env python
# -*- coding: utf-8 -*-
import os
import urllib
os.chdir(\"NOT-EXISTING\")
f = urllib.urlopen(\"NOT-EXISTING.html\")
for lines in f:
    print(lines)
"))
  (py-bug-tests-intern 'temporary-files-remain-when-python-raises-exception-lp-1083973-n1-base arg teststring)))

(defun temporary-files-remain-when-python-raises-exception-lp-1083973-n1-base (arg)
  "Doesn't test for remaining files yet. "
  (when py-debug-p (switch-to-buffer (current-buffer)))
  (let ((python-mode-v5-behavior-p t))
    (assert (py-execute-buffer) nil "temporary-files-remain-when-python-raises-exception-lp-1083973-n1-test failed")))

(defun temporary-files-remain-when-python-raises-exception-lp-1083973-n2-test (&optional arg)
  "Doesn't test for remaining files yet. "
  (interactive "p")
  (let ((teststring "#! /usr/bin/env python
# -*- coding: utf-8 -*-
import os
import urllib
f = urllib.urlopen(\"NOT-EXISTING.html\")
for lines in f:
    print(lines)
"))
  (py-bug-tests-intern 'temporary-files-remain-when-python-raises-exception-lp-1083973-n2-base arg teststring)))

(defun temporary-files-remain-when-python-raises-exception-lp-1083973-n2-base (arg)
  "Doesn't test for remaining files yet. "
  (let ((python-mode-v5-behavior-p t))
    (assert (py-execute-buffer) nil "temporary-files-remain-when-python-raises-exception-lp-1083973-n2-test failed")))

;; TBD
(defun temporary-files-remain-when-python-raises-exception-lp-1083973-n3-test (&optional arg)
  "Doesn't test for remaining files yet. "
  (interactive "p")
  (let ((teststring "#! /usr/bin/env python
# -*- coding: utf-8 -*-
import os
import urllib
f = urllib.urlopen(\"NOT-EXISTING.html\")
for lines in f:
    print(lines)
"))
    (py-bug-tests-intern 'temporary-files-remain-when-python-raises-exception-lp-1083973-n3-base arg teststring)))

(defun temporary-files-remain-when-python-raises-exception-lp-1083973-n3-base (arg)
  (assert (py-execute-buffer) nil "temporary-files-remain-when-python-raises-exception-lp-1083973-n3-test failed"))

(defun temporary-files-remain-when-python-raises-exception-lp-1083973-n4-test (&optional arg)
  (interactive "p")
  (let ((teststring "#! /usr/bin/env python
# -*- coding: utf-8 -*-
import os
import urllib
f = urllib.urlopen(\"NOT-EXISTING.html\")
for lines in f:
    print(lines)
"))
  (py-bug-tests-intern 'temporary-files-remain-when-python-raises-exception-lp-1083973-n4-base arg teststring)))

(defun temporary-files-remain-when-python-raises-exception-lp-1083973-n4-base (arg)
  (when py-debug-p (switch-to-buffer (current-buffer))
	  (font-lock-fontify-buffer)) 
  (py-execute-buffer)
  (assert (py-execute-buffer) nil "temporary-files-remain-when-python-raises-exception-lp-1083973-n4-test failed"))

(defun comments-start-a-new-line-lp-1092847-n1-test (&optional arg)
  (interactive "p")
  (let ((teststring "#! /usr/bin/env python
# -*- coding: utf-8 -*-
# I am using python-mode.el in Emacs to edit some Python code and it has the most annoying feature where it
# auto-indents a comment and then starts a new line. For example, if I have this:

def x():
    y = 1
<cursor is here, at root indentation level>

And then add in one # at the root indentation level:

def x():
    y = 1

    #
<cursor is now here>

# It automatically indents, inserts the #, and inserts a carriage return after the #. It's driving me crazy.
# I want my comments to stay exactly where I put them! Any suggestions?

# I've looked through the elisp code for the mode and can't find anything yet nor can I find anything
# elsewhere online. All I can find is that comments won't be used for future indentation (py-honor-comment-
# indentation) but nothing related to the comment itself. Nor the strange carriage return.

"))
  (py-bug-tests-intern 'comments-start-a-new-line-lp-1092847-n1-base arg teststring)))

(defun comments-start-a-new-line-lp-1092847-n1-base (arg)
  (let ((py-electric-comment-p t))
    (goto-char 258)
    (py-electric-comment 1)
    (back-to-indentation)
    (assert (eq 4 (current-column)) nil "comments-start-a-new-line-lp-1092847-n1-test failed")))

(defun comments-start-a-new-line-lp-1092847-n2-test (&optional arg)
  (interactive "p")
  (let ((teststring "#! /usr/bin/env python
# -*- coding: utf-8 -*-
# I am using python-mode.el in Emacs to edit some Python code and it has the most annoying feature where it
# auto-indents a comment and then starts a new line. For example, if I have this:

def x():
    y = 1
<cursor is here, at root indentation level>

And then add in one # at the root indentation level:

def x():
    y = 1

    #
<cursor is now here>

# It automatically indents, inserts the #, and inserts a carriage return after the #. It's driving me crazy.
# I want my comments to stay exactly where I put them! Any suggestions?

# I've looked through the elisp code for the mode and can't find anything yet nor can I find anything
# elsewhere online. All I can find is that comments won't be used for future indentation (py-honor-comment-
# indentation) but nothing related to the comment itself. Nor the strange carriage return.

"))
  (py-bug-tests-intern 'comments-start-a-new-line-lp-1092847-n2-base arg teststring)))

(defun comments-start-a-new-line-lp-1092847-n2-base (arg)
  (let ((py-electric-comment-p nil))
    (goto-char 258)
    (py-electric-comment 1)
    (back-to-indentation)
    (assert (eq 0 (current-column)) nil "comments-start-a-new-line-lp-1092847-n2-test failed")))

(defun filename-completion-fails-in-ipython-lp-1027265-n1-test (&optional arg)
  (interactive "p")
  (let ((teststring "#! /usr/bin/env python
# -*- coding: utf-8 -*-
a = open('/ho
"))
    (py-bug-tests-intern 'filename-completion-fails-in-ipython-lp-1027265-n1-base arg teststring)))

(defun filename-completion-fails-in-ipython-lp-1027265-n1-base (arg)
  (goto-char 61)
  (py-shell-complete)
  (assert (looking-back "home") nil "filename-completion-fails-in-ipython-lp-1027265-n1-test failed"))

(defun filename-completion-fails-in-ipython-lp-1027265-n2-test (&optional arg)
  (interactive "p")
  (let ((teststring "#! /usr/bin/env ipython
# -*- coding: utf-8 -*-
a = open('/ho
"))
    (py-bug-tests-intern 'filename-completion-fails-in-ipython-lp-1027265-n2-base arg teststring)))

(defun filename-completion-fails-in-ipython-lp-1027265-n2-base (arg)
  (goto-char 62)
  (py-shell-complete)
  (assert (looking-back "home") nil "filename-completion-fails-in-ipython-lp-1027265-n2-test failed"))

(defun enter-key-does-not-indent-properly-after-return-statement-lp-1098793-test (&optional arg)
  (interactive "p")
  (let ((teststring "#! /usr/bin/env python
# -*- coding: utf-8 -*-
def foo():
    while something():
        bar()
    baz()
    return 1

# Once the cursor is placed after \"return 1\" and I hit enter, on the next line, the cursor is placed under
# the \"r\" in return statement, instead of moving indentation to the outer block.
#
# \"ENTER\" key is bound to (py-newline-and-indent)
#
# Some version information:
#
# emacs-version
# \"GNU Emacs 24.2.1 (i686-pc-cygwin) of 2012-08-27 on fiona\"
# py-version
# \"6.1.0\"

"))
  (py-bug-tests-intern 'enter-key-does-not-indent-properly-after-return-statement-lp-1098793-base arg teststring)))

(defun enter-key-does-not-indent-properly-after-return-statement-lp-1098793-base (arg)
    (goto-char 119)
    (assert (eq 0 (py-compute-indentation)) nil "enter-key-does-not-indent-properly-after-return-statement-lp-1098793-test failed"))

(defun py-up-test-python-el-111-test (&optional arg)
  (interactive "p")
  (let ((teststring "#! /usr/bin/env python
# -\*- coding: utf-8 -\*-
# up-list: Scan error: \"Unbalanced parentheses\"
# Hi, when I press C-M-u in python buffer I get:
#
# up-list: Scan error: \"Unbalanced parentheses\"

# My expected behavior is something like this:
#
# Scenario: Going higher level by C-M-u
#     When I insert:

# def f():
#    if True:
#        [i for i in range(3)]

#     And I am looking at \"3)]\"
#     And I press C-M-u
#     Then I should looking at \"(3)]\"
#     And I press C-M-u
#     Then I should looking at \"[i for i\"
#     And I press C-M-u
#     Then I should looking at \"if True\"
#     And I press C-M-u
#     Then I should looking at \"def f\"
#
# related: #106

def f():
    if True:
        print(\"[i for i in range(3)]: %s \" % ([i for i in range(3)]))

"))
  (py-bug-tests-intern 'py-up-test-python-el-111-base arg teststring)))

(defun py-up-test-python-el-111-base (arg)
    (goto-char 757)
    (assert (eq 756 (py-up)) nil "py-up-test-python-el-111-test #1 failed")
    (assert (eq 739 (py-up)) nil "py-up-test-python-el-111-test #2 failed")
    (assert (eq 738 (py-up)) nil "py-up-test-python-el-111-test #3 failed")
    (assert (eq 706 (py-up)) nil "py-up-test-python-el-111-test #4 failed")
    (assert (eq 701 (py-up)) nil "py-up-test-python-el-111-test #5 failed")
    (assert (eq 684 (py-up)) nil "py-up-test-python-el-111-test #6 failed")
    (assert (eq 671 (py-up)) nil "py-up-test-python-el-111-test #7 failed")
    (goto-char 726)
    (assert (eq 707 (py-up)) nil "py-up-test-python-el-111-test #8 failed")
    (assert (eq 706 (py-up)) nil "py-up-test-python-el-111-test #9 failed")
    )

(defun py-down-python-el-112-test (&optional arg)
  (interactive "p")
  (let ((teststring "#! /usr/bin/env python
# -*- coding: utf-8 -*-
# Scenario: Going lover level by C-M-d
#     When I insert:

class C(object):
    def m(self):
        if True:
            return [i for i in range(3)]
        else:
            return []

    # And I am looking at \"class C\"
    # And I press C-M-d
    # Then I should looking at \"def m\"
    # And I press C-M-d
    # Then I should looking at \"if True\"
    # And I press C-M-d
    # Then I should looking at \"i for i\"
    # And I press C-M-d
    # Then I should looking at \"3\"

# Current version of C-M-d jumps to inside of (object)
# because it is just a plain down-list. I think it's
# better to have python-specific one for symmetry.

"))
  (py-bug-tests-intern 'py-down-python-el-112-base arg teststring)))

(defun py-down-python-el-112-base (arg)
    (goto-char 109)
    (assert (eq 130 (py-down)) nil "py-down-test-python-el-112-test #1 failed")
    (assert (eq 151 (py-down)) nil "py-down-test-python-el-112-test #2 failed")
    (assert (eq 172 (py-down)) nil "py-down-test-python-el-112-test #3 failed")
    (assert (eq 179 (py-down)) nil "py-down-test-python-el-112-test #4 failed")
    (assert (eq 196 (py-down)) nil "py-down-test-python-el-112-test #5 failed")
)

(defun py-underscore-word-syntax-p-customization-has-no-effect-lp-1100947-test (&optional arg)
  (interactive "p")
  (let ((teststring "#! /usr/bin/env python
# -*- coding: utf-8 -*-
_
"))
  (py-bug-tests-intern 'py-underscore-word-syntax-p-customization-has-no-effect-lp-1100947-base arg teststring)))

(defun py-underscore-word-syntax-p-customization-has-no-effect-lp-1100947-base (arg)
  (goto-char 48)
  (py-underscore-word-syntax-p-on)
  (assert (eq 119 (char-syntax (char-after))) nil "py-underscore-word-syntax-p-customization-has-no-effect-lp-1100947-test #1 failed")
  (py-underscore-word-syntax-p-off)
  (assert (eq 95 (char-syntax (char-after))) nil "py-underscore-word-syntax-p-customization-has-no-effect-lp-1100947-test #2 failed")
  (py-underscore-word-syntax-p-on)
  (assert (eq 119 (char-syntax (char-after))) nil "py-underscore-word-syntax-p-customization-has-no-effect-lp-1100947-test #3 failed")
)

(defun py-newline-and-indent-leaves-eol-whitespace-lp-1100892-test (&optional arg)
  (interactive "p")
  (let ((teststring "#! /usr/bin/env python
# -\*- coding: utf-8 -\*-
# py-newline-and-indent leaves extra whitespace at eol if used inside an existing construct. It should
# instead clean up all trailing whitespace. I believe this is a regression.

def foo():
    x = some_long_call(supercalifragilistic=6, expialidocious=7)

# Now, put point on the 'e' of expialidocious and hit RET

# You will see that there's an extra space left after the \"6, \". All trailing whitespace should instead be
# removed.

"))
  (py-bug-tests-intern 'py-newline-and-indent-leaves-eol-whitespace-lp-1100892-base arg teststring)))

(defun py-newline-and-indent-leaves-eol-whitespace-lp-1100892-base (arg)
  (let ((py-newline-delete-trailing-whitespace-p t))
    (goto-char 286)
    (py-newline-and-indent)
    (sit-for 0.1)
    (skip-chars-backward " \t\r\n\f")
    (assert (eq (char-after) 10) nil "py-newline-and-indent-leaves-eol-whitespace-lp-1100892-test failed")))

(defun module-docstring-when-following-comment-lp-1102011-test (&optional arg)
  (interactive "p")
  (let ((teststring "# -*- coding: utf-8 -*-
# *****************************************************************************
# <Name of software>
# Copyright (c) 2009-2012 by the contributors (see AUTHORS)
#
# This program is free software; you can redistribute it and/or modify it under
# the terms of the GNU General Public License as published by the Free Software
# Foundation; either version 2 of the License, or (at your option) any later
# version.
#
# This program is distributed in the hope that it will be useful, but WITHOUT
# ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
# FOR A PARTICULAR PURPOSE. See the GNU General Public License for more
# details.
#
# You should have received a copy of the GNU General Public License along with
# this program; if not, write to the Free Software Foundation, Inc.,
# 59 Temple Place, Suite 330, Boston, MA 02111-1307 USA
#
# Module authors:
# Georg Brandl <email address>
#
# *****************************************************************************
\"\"\"Some docstring.\"\"\"

__version__ = \"\$Revision\$\"

"))
  (py-bug-tests-intern 'module-docstring-when-following-comment-lp-1102011-base arg teststring)))

(defun module-docstring-when-following-comment-lp-1102011-base (arg)
  (let ((py-use-font-lock-doc-face-p t))
    (goto-char 1024)
    (python-mode)
    (font-lock-fontify-buffer)
    (sit-for 1)
    (assert (eq (face-at-point) 'font-lock-doc-face) nil "module-docstring-when-following-comment-lp-1102011-test failed")))

(defun ipython-complete-lp-1102226-test (&optional arg)
  (interactive "p")
  (let ((teststring "#! /usr/bin/env ipython
# -*- coding: utf-8 -*-
import re
re.
"))
  (py-bug-tests-intern 'ipython-complete-lp-1102226-base arg teststring)))

(defun ipython-complete-lp-1102226-base (arg)
  (and (featurep 'company)(company-mode -1))
  (when py-debug-p (switch-to-buffer (current-buffer))
	(font-lock-fontify-buffer))
  (goto-char 62)
  (py-shell-complete)
  ;; (set-buffer "*IPython Completions*")
  ;; (switch-to-buffer (current-buffer))
  (assert (bufferp (get-buffer "*Python Completions*")) nil "ipython-complete-lp-1102226-test failed"))

(defun more-docstring-filling-woes-lp-1102296-pep-257-test (&optional arg)
  (interactive "p")
  (let ((teststring "#! /usr/bin/env python
# -*- coding: utf-8 -*-
# (I selected \"PEP-257-NN\" as the docstring fill style.)
# Given the following code:

class Test(object):
    \"\"\"
    Builds target formats from the reST sources.
    \"\"\"

    def method1(self):
        \"\"\"Return the template bridge configured.\"\"\"
        pass

    def method2(self):
        \"\"\"Load necessary templates and perform initialization. The default implementation does nothing.
        \"\"\"
        pass

# There are three misbehaviors here:
# \* should have removed the whitespace at the beginning and end of the class docstring
# \* in method1, the \"pass\" should remain on its own line
# \* in method2, the closing triple-quote should get its own line, and the \"pass\" too

"))
  (py-bug-tests-intern 'more-docstring-filling-woes-lp-1102296-pep-257-base arg teststring)))

(defun more-docstring-filling-woes-lp-1102296-pep-257-base (arg)
  (let ((py-docstring-style 'pep-257))
    ;; (when py-debug-p (switch-to-buffer (current-buffer))
    ;; (font-lock-fontify-buffer))
    (goto-char (point-min))
    (search-forward "Builds")
    (sit-for 0.1 t)
    (fill-paragraph)
    (sit-for 0.1 t)
    (end-of-line)
    (assert (looking-back "\"\"\"") nil "more-docstring-filling-woes-lp-1102296-pep-257-test #1 failed")
    (message "%s" "more-docstring-filling-woes-lp-1102296-pep-257-test #1 done")
    (search-forward "Return")
    (fill-paragraph)
    (forward-line 1)
    (assert (looking-at "        pass") nil "more-docstring-filling-woes-lp-1102296-pep-257-test #2 failed")
    (message "%s" "more-docstring-filling-woes-lp-1102296-pep-257-test #2 done")
    (search-forward "Load")
    (fill-paragraph)
    (forward-line 1)
    ;; (sit-for 0.1 t)
    (assert (empty-line-p) nil "more-docstring-filling-woes-lp-1102296-pep-257-test #3a failed")
    (message "%s" "more-docstring-filling-woes-lp-1102296-pep-257-test #3a done")
    (forward-line 4)
    (assert (looking-at "        pass") nil "more-docstring-filling-woes-lp-1102296-pep-257-test #3c failed")
    (message "%s" "more-docstring-filling-woes-lp-1102296-pep-257-test #3c done")))

(defun more-docstring-filling-woes-lp-1102296-onetwo-test (&optional arg)
  (interactive "p")
  (let ((teststring "#! /usr/bin/env python
# -*- coding: utf-8 -*-
# (I selected \"PEP-257-NN\" as the docstring fill style.)
# Given the following code:

class Test(object):
    \"\"\"
    Builds target formats from the reST sources.
    \"\"\"

    def method1(self):
        \"\"\"Return the template bridge configured.\"\"\"
        pass

    def method2(self):
        \"\"\"Load necessary templates and perform initialization. The default implementation does nothing.
        \"\"\"
        pass

# There are three misbehaviors here:
# \* should have removed the whitespace at the beginning and end of the class docstring
# \* in method1, the \"pass\" should remain on its own line
# \* in method2, the closing triple-quote should get its own line, and the \"pass\" too

"))
  (py-bug-tests-intern 'more-docstring-filling-woes-lp-1102296-onetwo-base arg teststring)))

(defun more-docstring-filling-woes-lp-1102296-onetwo-base (arg)
  (when py-debug-p (switch-to-buffer (current-buffer))
	(font-lock-fontify-buffer))
  (let ((py-docstring-style 'onetwo))
    (goto-char 178)
    (fill-paragraph)
    (end-of-line)
    (assert (looking-back "\"\"\"")  nil "more-docstring-filling-woes-lp-1102296-onetwo-test #1 failed")
    (message "%s" "more-docstring-filling-woes-lp-1102296-onetwo-test #1 done")
    (goto-char 259)
    (fill-paragraph)
    (forward-line 1)
    (assert (looking-at "        pass") nil "more-docstring-filling-woes-lp-1102296-onetwo-test #2 failed")
    (message "%s" "more-docstring-filling-woes-lp-1102296-onetwo-test #2 done")
    (goto-char 357)
    (fill-paragraph)
    (beginning-of-line)
    (sit-for 0.1 t)
    ;; (message "%d" (skip-chars-forward " "))
    (assert (eq (skip-chars-forward " ") 8) nil "more-docstring-filling-woes-lp-1102296-onetwo-test #3 failed")
    (message "%s" "more-docstring-filling-woes-lp-1102296-onetwo-test #3 done")
    (goto-char 357)
    (forward-line 1)
    (assert (empty-line-p) nil "more-docstring-filling-woes-lp-1102296-onetwo-test #4 failed")
    (message "%s" "more-docstring-filling-woes-lp-1102296-onetwo-test #4 done")
    (forward-line 2)
    (assert (empty-line-p) nil "more-docstring-filling-woes-lp-1102296-onetwo-test #5 failed")
    (message "%s" "more-docstring-filling-woes-lp-1102295-onetwo-test #5 done")
    (forward-line 2)
    (assert (looking-at "        pass") nil "more-docstring-filling-woes-lp-1102296-onetwo-test #5 failed")
    (message "%s" "more-docstring-filling-woes-lp-1102296-onetwo-test #5 done")))

(defun more-docstring-filling-woes-lp-1102296-django-test (&optional arg)
  (interactive "p")
  (let ((teststring "#! /usr/bin/env python
# -*- coding: utf-8 -*-
# (I selected \"PEP-257-NN\" as the docstring fill style.)
# Given the following code:

class Test(object):
    \"\"\"
    Builds target formats from the reST sources.
    \"\"\"

    def method1(self):
        \"\"\"Return the template bridge configured.\"\"\"
        pass

    def method2(self):
        \"\"\"Load necessary templates and perform initialization. The default implementation does nothing.
        \"\"\"
        pass

# There are three misbehaviors here:
# \* should have removed the whitespace at the beginning and end of the class docstring
# \* in method1, the \"pass\" should remain on its own line
# \* in method2, the closing triple-quote should get its own line, and the \"pass\" too

"))
  (py-bug-tests-intern 'more-docstring-filling-woes-lp-1102296-django-base arg teststring)))

(defun more-docstring-filling-woes-lp-1102296-django-base (arg)
  (when py-debug-p (switch-to-buffer (current-buffer))
	(font-lock-fontify-buffer))
  (let ((py-docstring-style 'django))
    (goto-char 178)
    (assert (fill-paragraph) nil "more-docstring-filling-woes-lp-1102296-django-test #1 failed")
    (message "%s" "more-docstring-filling-woes-lp-1102296-django-test #1 done")
    (goto-char 259)
    (fill-paragraph)
    (forward-line 2)
    (assert (looking-at "        pass") nil "more-docstring-filling-woes-lp-1102296-django-test #2 failed")
    (message "%s" "more-docstring-filling-woes-lp-1102296-django-test #2 done")
    (goto-char 380)
    (fill-paragraph)
    (beginning-of-line)
    (sit-for 0.1 t)
    (assert (looking-at "        L") nil "more-docstring-filling-woes-lp-1102296-django-test #3 failed")
    (message "%s" "more-docstring-filling-woes-lp-1102296-django-test #3 done")
    (goto-char 357)
    (forward-line 2)
    (assert (empty-line-p) nil "more-docstring-filling-woes-lp-1102296-django-test #4 failed")
    (message "%s" "more-docstring-filling-woes-lp-1102296-django-test #4 done")
    (forward-line 3)
    (assert (looking-at "        pass") nil "more-docstring-filling-woes-lp-1102296-django-test #5 failed")
    (message "%s" "more-docstring-filling-woes-lp-1102296-django-test #5 done")))

(defun more-docstring-filling-woes-lp-1102296-symmetric-test (&optional arg)
  (interactive "p")
  (let ((teststring "#! /usr/bin/env python
# -*- coding: utf-8 -*-
# (I selected \"PEP-257-NN\" as the docstring fill style.)
# Given the following code:

class Test(object):
    \"\"\"
    Builds target formats from the reST sources.
    \"\"\"

    def method1(self):
        \"\"\"Return the template bridge configured.\"\"\"
        pass

    def method2(self):
        \"\"\"Load necessary templates and perform initialization. The default implementation does nothing.
        \"\"\"
        pass

# There are three misbehaviors here:
# \* should have removed the whitespace at the beginning and end of the class docstring
# \* in method1, the \"pass\" should remain on its own line
# \* in method2, the closing triple-quote should get its own line, and the \"pass\" too

"))
  (py-bug-tests-intern 'more-docstring-filling-woes-lp-1102296-symmetric-base arg teststring)))

(defun more-docstring-filling-woes-lp-1102296-symmetric-base (arg)
  (when py-debug-p (switch-to-buffer (current-buffer))
	(font-lock-fontify-buffer))
  (let ((py-docstring-style 'symmetric))
    (goto-char 178)
    (assert (fill-paragraph) nil "more-docstring-filling-woes-lp-1102296-symmetric-test #1 failed")
    (message "%s" "more-docstring-filling-woes-lp-1102296-symmetric-test #1 done")
    (goto-char 259)
    (fill-paragraph)
    (forward-line 1)
    (assert (looking-at "        pass") nil "more-docstring-filling-woes-lp-1102296-symmetric-test #2 failed")
    (message "%s" "more-docstring-filling-woes-lp-1102296-symmetric-test #2 done")
    (goto-char 380)
    (fill-paragraph)
    (forward-line -1)
    (beginning-of-line)
    (sit-for 0.1 t)
    (assert (looking-at "        \"\"\"") nil "more-docstring-filling-woes-lp-1102296-symmetric-test #3 failed")
    (message "%s" "more-docstring-filling-woes-lp-1102296-symmetric-test #3 done")
    (forward-line 5)
    (assert (looking-at "        pass") nil "more-docstring-filling-woes-lp-1102296-symmetric-test #4 failed")
    (message "%s" "more-docstring-filling-woes-lp-1102296-symmetric-test #4 done")))

(defun line-after-colon-with-inline-comment-lp-1109946-test (&optional arg)
  (interactive "p")
  (let ((teststring "#! /usr/bin/env python
# -*- coding: utf-8 -*-
def f():
    if a:
        b
    if c: # inline comment

        # |<---- cursor will not indent properly with <TAB>>
"))
  (py-bug-tests-intern 'line-after-colon-with-inline-comment-lp-1109946-base arg teststring)))

(defun line-after-colon-with-inline-comment-lp-1109946-base (arg)
  (let ((py-indent-honors-inline-comment t))
    (goto-char 104)
    (assert (eq 10 (py-compute-indentation)) nil "line-after-colon-with-inline-comment-lp-1109946-test failed")))

(defun cascading-indent-lp-1101962-test (&optional arg)
  (interactive "p")
  (let ((teststring "#! /usr/bin/env python
# -*- coding: utf-8 -*-
def foo():
    pgdt = []
    pdwd = []
        cItemLik = [ ht(\"Item\", T.hr(), T.span(\"Like\", style=
                            \"background-color: rgb( 229, 200, 136 )\")),
                     lambda item: ht( item['!'], T.br(), like( item ))
                     ]
"))
  (py-bug-tests-intern 'cascading-indent-lp-1101962-base arg teststring)))

(defun cascading-indent-lp-1101962-base (arg)
    (goto-char 87)
    (assert (eq 4 (py-compute-indentation)) nil "cascading-indent-lp-1101962-test failed"))

(defun python-mode-very-slow-lp-1107037-test (&optional arg)
  (interactive "p")
  (let ((teststring "# Since the last few commits, python-mode is unbearably slow on nontrivial files. Even
# just moving around in the file makes Emacs use 100% CPU for a few seconds.
#
# If this is due to the fix for lp-1102011, I would rather live with the highlight bug :)
# Georg Brandl (gbrandl) wrote 11 hours ago: #2
#
# Try the file below. I have narrowed the problem to the fix for lp-1102011 -- the regex
# \*must\* have pathological behavior (which wouldn't surprise me, such backtracking
# problems are very hard to fix). In general, for that many lines between module start
# and docstring, I think it is quite fine for python-mode not to color the docstring as
# such. I think the number of permitted comment lines should be restricted to 2, in order
# to accomodate a shebang line and a coding declaration.
# -\*- coding: utf-8 -\*-
# \*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*
# <Name of software>
# Copyright (c) 2009-2012 by the contributors (see AUTHORS)
#
# This program is free software; you can redistribute it and/or modify it under
# the terms of the GNU General Public License as published by the Free Software
# Foundation; either version 2 of the License, or (at your option) any later
# version.
#
# This program is distributed in the hope that it will be useful, but WITHOUT
# ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
# FOR A PARTICULAR PURPOSE. See the GNU General Public License for more
# details.
#
# You should have received a copy of the GNU General Public License along with
# this program; if not, write to the Free Software Foundation, Inc.,
# 59 Temple Place, Suite 330, Boston, MA 02111-1307 USA
#
# Module authors:
# Georg Brandl <email address>
#
# \*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*

\"\"\"Some docstring.\"\"\"

__version__ = \"$Revision: 1.1 $\"

"))
  (py-bug-tests-intern 'python-mode-very-slow-lp-1107037-base arg teststring)))

(defun python-mode-very-slow-lp-1107037-base (arg)
  (let ((py-use-font-lock-doc-face-p t))
    (goto-char 1825)
    (python-mode)
    (font-lock-fontify-buffer)
    (sit-for 1)
    (assert (eq (face-at-point) 'font-lock-doc-face) nil "python-mode-very-slow-lp-1107037-test failed")))

(defun add-custom-switch-for-ffap-hooks-lp-1117119-test (&optional arg)
  (interactive "p")
  (let ((teststring "#! /usr/bin/env python
# -*- coding: utf-8 -*-
/usr/lib/pyt
"))
  (py-bug-tests-intern 'add-custom-switch-for-ffap-hooks-lp-1117119-base arg teststring)))

(defun add-custom-switch-for-ffap-hooks-lp-1117119-base (arg)
  (let ((py-ffap-p t)
        (python-ffap t))
    (goto-char 60)
    (assert (member 'py--set-ffap-form python-mode-hook) nil "add-custom-switch-for-ffap-hooks-lp-1117119-test #1 failed")
    ))

(defun more-docstring-filling-woes-lp-1102296-nil-test (&optional arg)
  (interactive "p")
  (let ((teststring "#! /usr/bin/env python
# -*- coding: utf-8 -*-
# (I selected \"PEP-257-NN\" as the docstring fill style.)
# Given the following code:

class Test(object):
    \"\"\"
    Builds target formats from the reST sources.
    \"\"\"

    def method1(self):
        \"\"\"Return the template bridge configured.\"\"\"
        pass

    def method2(self):
        \"\"\"Load necessary templates and perform initialization. The default implementation does nothing.
        \"\"\"
        pass

# There are three misbehaviors here:
# \* should have removed the whitespace at the beginning and end of the class docstring
# \* in method1, the \"pass\" should remain on its own line
# \* in method2, the closing triple-quote should get its own line, and the \"pass\" too

"))
  (py-bug-tests-intern 'more-docstring-filling-woes-lp-1102296-nil-base arg teststring)))

(defun more-docstring-filling-woes-lp-1102296-nil-base (arg)
  (when py-debug-p (switch-to-buffer (current-buffer))
	(font-lock-fontify-buffer))
  (let ((py-docstring-style nil))
    (goto-char 178)
    (fill-paragraph)
    (end-of-line)
    (message "(current-column): %s" (current-column))
    (assert (eq 54 (current-column)) nil "more-docstring-filling-woes-lp-1102296-nil-test #1 failed")
    (message "%s" "more-docstring-filling-woes-lp-1102296-nil-test #1 done")
    (goto-char 259)
    (fill-paragraph)
    (forward-line 1)
    (sit-for 0.2)
    (assert (looking-at "        pass") nil "more-docstring-filling-woes-lp-1102296-nil-test #2 failed")
    (message "%s" "more-docstring-filling-woes-lp-1102296-nil-test #2 done")
    (goto-char 380)
    (fill-paragraph)
    (back-to-indentation)
    (sit-for 0.1 t)
    (assert (eq (char-after) 34) nil "more-docstring-filling-woes-lp-1102296-nil-test #3a failed")
    (message "%s" "more-docstring-filling-woes-lp-1102296-nil-test #3a done")
    (search-forward "pass" nil t 1)
    (beginning-of-line)
    (assert (looking-at "        pass") nil "more-docstring-filling-woes-lp-1102296-nil-test #3c failed")
    (message "%s" "more-docstring-filling-woes-lp-1102296-nil-test #3c done")))

(defun more-docstring-filling-woes-lp-1102296-pep-257-nn-test (&optional arg)
  (interactive "p")
  (let ((teststring "#! /usr/bin/env python
# -*- coding: utf-8 -*-
# (I selected \"PEP-257-NN\" as the docstring fill style.)
# Given the following code:

class Test(object):
    \"\"\"
    Builds target formats from the reST sources.
    \"\"\"

    def method1(self):
        \"\"\"Return the template bridge configured.\"\"\"
        pass

    def method2(self):
        \"\"\"Load necessary templates and perform initialization. The default implementation does nothing.
        \"\"\"
        pass

# There are three misbehaviors here:
# \* should have removed the whitespace at the beginning and end of the class docstring
# \* in method1, the \"pass\" should remain on its own line
# \* in method2, the closing triple-quote should get its own line, and the \"pass\" too

"))
  (py-bug-tests-intern 'more-docstring-filling-woes-lp-1102296-pep-257-nn-base arg teststring)))

(defun more-docstring-filling-woes-lp-1102296-pep-257-nn-base (arg)
  (let ((py-docstring-style 'pep-257-nn))
    (when py-debug-p (switch-to-buffer (current-buffer))
	  (font-lock-fontify-buffer))
    (sit-for 0.1 t)
    (goto-char 178)
    (assert (fill-paragraph) nil "more-docstring-filling-woes-lp-1102296-pep-257-nn-test #1 failed")
    (message "%s" "more-docstring-filling-woes-lp-1102296-pep-257-nn-test #1 done")
    (goto-char 259)
    (fill-paragraph)
    (forward-line 1)
    (assert (looking-at "        pass") nil "more-docstring-filling-woes-lp-1102296-pep-257-nn-test #2 failed")
    (message "%s" "more-docstring-filling-woes-lp-1102296-pep-257-nn-test #2 done")
    (goto-char 357)
    (fill-paragraph)
    (beginning-of-line)
    (sit-for 0.1 t)
    (assert (eq (current-indentation) 8) nil "more-docstring-filling-woes-lp-1102296-pep-257-nn-test #3a failed")
    (message "%s" "more-docstring-filling-woes-lp-1102296-pep-257-nn-test #3a done")
    (search-forward "pass")
    (beginning-of-line)
    (sit-for 0.1 t)
    (assert (looking-at "        pass") nil "more-docstring-filling-woes-lp-1102296-pep-257-nn-test #3b failed")
    (message "%s" "more-docstring-filling-woes-lp-1102296-pep-257-nn-test #3b done")))

(defun infinite-loop-on-lp-1156426-test (&optional arg)
  (interactive "p")
  (let ((teststring "#! /usr/bin/env python
# -*- coding: utf-8 -*-
while mvi.t2 <= T:

# calculate a spline for the kinematic inputs
#fname = 'data/monte_1000hz.mat'
"))
  (py-bug-tests-intern 'infinite-loop-on-lp-1156426-base arg teststring)))

(defun infinite-loop-on-lp-1156426-base (arg)
  (let ((py-indent-comments t))
    (goto-char 68)
    (assert (eq 4 (py-compute-indentation)) nil "infinite-loop-on-lp-1156426-test #1 failed"))
  (goto-char (point-max))
  (assert (eq 0 (py-compute-indentation)) nil "infinite-loop-on-lp-1156426-test #2 failed"))

(defun fill-paragraph-in-docstring-lp-1161232-test (&optional arg)
  (interactive "p")
  (let ((teststring "def foo ():
    \"\"\"Returns a rewritten path.

Assuming that ``cr`` is a :class:`ContextRewriter` instance, that the rewriter maps the path ``views/<filename>`` to asdf asdf asdf asdf asdf asdf asdf asdf asdfasdf asdfasdf asdf asdf \"\"\"
    pass
"))
  (py-bug-tests-intern 'fill-paragraph-in-docstring-lp-1161232-base arg teststring)))

(defun fill-paragraph-in-docstring-lp-1161232-base (arg)
    (goto-char 94)
    (fill-paragraph t)
    (sit-for 0.1 t)
    (assert (eq (point) 51) nil "fill-paragraph-in-docstring-lp-1161232-test #1 failed")
    (goto-char 249)
    (sit-for 1)
    (message "%s" (buffer-substring-no-properties (line-beginning-position) (line-end-position) ))
    (assert (looking-at "    pass") nil "fill-paragraph-in-docstring-lp-1161232-test #2 failed")
    )

(defun wfmc-lp-1160022-test (&optional arg)
  (interactive "p")
  (let ((teststring "#! /usr/bin/env python
# -*- coding: utf-8 -*-
# which-func-misses-class-lp-1160022
class kugel(object):
    zeit = time.strftime('%Y%m%d--%H-%M-%S')
    # zeit = time.strftime('%Y-%m-%d--%H-%M-%S')
    spiel = []

    def pylauf(self):
        \"\"\"Eine Doku fuer pylauf\"\"\"
        pass

a = \"asdf\"
"))
  (py-bug-tests-intern 'wfmc-lp-1160022-base arg teststring)))

(defun wfmc-lp-1160022-base (arg)
  (imenu-add-menubar-index)
  (goto-char 251)
  (which-func-mode)
  (company-mode -1)
  (yas/minor-mode -1)
  (hs-minor-mode -1)
  (undo-tree-mode -1)
  (abbrev-mode -1)
  ;; (car (nth 2 (car '((#1="class kugel" (#1# . 85) ("kugel.pylauf" . 224))))))
  (assert (string= "kugel.pylauf" (car (nth 2 (eval '(car imenu--index-alist))))) nil "wfmc-lp-1160022-test failed"))

(defun tab-results-in-never-ending-process-lp-1163423-test (&optional arg)
  (interactive "p")
  (let ((teststring "#! /usr/bin/env python
# -\*- coding: utf-8 -\*-
    class asdf(object):
        zeit = time.strftime('%Y%m%d--%H-%M-%S')

        def utf8_exists(filename):
            return os.path.exists(filename.encode('utf-8'))
"))
  (py-bug-tests-intern 'tab-results-in-never-ending-process-lp-1163423-base arg teststring)))

(defun tab-results-in-never-ending-process-lp-1163423-base (arg)
  (let ((py-tab-indents-region-p t)
        (py-tab-indent t))
    (goto-char 216)
    (push-mark)
    (goto-char 122)
    (call-interactively 'py-indent-line)
    (sit-for 0.1 t)
    ;; (message "point: %s" (point))
    (assert (bolp)  nil "tab-results-in-never-ending-process-lp-1163423-test failed")))

(defun loops-on-if-else-lp-328777-test (&optional arg)
  (interactive "p")
  (let ((teststring "x = (if 1: 2
     else: 3)
"))
  (py-bug-tests-intern 'loops-on-if-else-lp-328777-base arg teststring)))

(defun loops-on-if-else-lp-328777-base (arg)
    (goto-char 14)
    (assert (eq 5 (py-compute-indentation)) nil "loops-on-if-else-lp-328777-test failed"))

(defun nested-dictionaries-indent-again-lp-1174174-test (&optional arg)
  "With ARG greater 1 keep test buffer open.

If no `load-branch-function' is specified, make sure the appropriate branch is loaded. Otherwise default python-mode will be checked. "
  (interactive "p")
  (let ((teststring "
d = {'a':{'b':3,
          'c':4
          }
     }

d = {'a':{
          'b':3,
          'c':4
         }
     }
"))
    1174174
    (py-bug-tests-intern 'nested-dictionaries-indent-again-lp-1174174 arg teststring)))

(defun nested-dictionaries-indent-again-lp-1174174 ()
  (let ((py-indent-honors-multiline-listing t))
    (goto-char 19)
    (assert (eq 10 (py-compute-indentation)) nil "nested-dictionaries-indent-again-lp-1174174-test #1 failed")
    (goto-char 35)
    (assert (eq 10 (py-compute-indentation)) nil "nested-dictionaries-indent-again-lp-1174174-test #2 failed")
    (goto-char 47)
    (assert (eq 5 (py-compute-indentation)) nil "nested-dictionaries-indent-again-lp-1174174-test #3 failed")
    ;; (goto-char 57)
    ;; (assert (eq 4 (py-compute-indentation)) nil "nested-dictionaries-indent-again-lp-1174174-test #4 failed")
    ;; (goto-char 63)
    ;; (assert (eq 0 (py-compute-indentation)) nil "nested-dictionaries-indent-again-lp-1174174-test #5 failed")

    ))

(defun TAB-leaves-point-in-the-wrong-lp-1178453-test (&optional arg)
  (interactive "p")
  (let ((teststring "#! /usr/bin/env python
# -*- coding: utf-8 -*-
# r1225

import tarfile

src = tarfile.open('src.tgz', 'r:gz')
dst = tarfile.open('dst.tgz', 'w:gz')

for name in src.getnames():
    print('name:', name)
    info = src.getmember(name)
    fp = src.extractfile(name)
    dst.addfile(info, fp)

src.close()
dst.close()

# Put point at the end of the `dst.addfile` line and hit return. Point is
# properly left on the next line right under the first 'd'. Now hit TAB. Point is
# correctly left at the beginning of the line. Hit TAB one more time.
#
# Now, while 4 spaces have been added to the beginning of the line, point is left
# at the beginning of the line instead of at the end of the just inserted
# whitespace. Point should be at column 4.
"))
  (py-bug-tests-intern 'TAB-leaves-point-in-the-wrong-lp-1178453-base arg teststring)))

(defun TAB-leaves-point-in-the-wrong-lp-1178453-base (arg)
    (goto-char 292)
    (py-indent-line)
    (assert (eq 4 (current-column)) nil "TAB-leaves-point-in-the-wrong-lp-1178453-test failed"))

(defun Bogus-whitespace-left-in-docstring-after-wrapping-lp-1178455-test (&optional arg)
  (interactive "p")
  (let ((teststring "#! /usr/bin/env python
# -*- coding: utf-8 -*-
# r1225

def foo():
    \"\"\"Line one of a comment.

    A paragraph of comments. These should get wrapped correctly. These should get wrapped correctly.
    These should get wrapped correctly.
    They do, but whooboy!

    Last line of comment.
    \"\"\"

# Put point somewhere in the middle paragraph and hit M-q (fill-paragraph).
#
# The paragraph gets properly wrapped, but the blank line before it and after it
# get additional 4 bogus spaces at the beginning of their lines.
"))
  (py-bug-tests-intern 'Bogus-whitespace-left-in-docstring-after-wrapping-lp-1178455-base arg teststring)))

(defun Bogus-whitespace-left-in-docstring-after-wrapping-lp-1178455-base (arg)
  (when py-debug-p (switch-to-buffer (current-buffer))
	(font-lock-fontify-buffer))
  (goto-char 97)
  ;; (message "paragraph-start: %s" paragraph-start)
  ;; (message "Fehler? %s" (buffer-substring-no-properties (line-beginning-position) (line-end-position)))
  (fill-paragraph t)
  ;; (sit-for 0.1 t)
  ;; (message "Fehler? %s" (buffer-substring-no-properties (line-beginning-position) (line-end-position)))
  (forward-line 1)
  ;;  (sit-for 1)
  (assert (and (bolp) (eolp)) nil "Bogus-whitespace-left-in-docstring-after-wrapping-lp-1178455-test #1 failed")
  (goto-char 140)
  (fill-paragraph t)
  (end-of-line)
  (assert (eq 70 (current-column)) nil "Bogus-whitespace-left-in-docstring-after-wrapping-lp-1178455-test #2 failed")
  (forward-line 3)
  (assert (and (bolp) (eolp)) nil "Bogus-whitespace-left-in-docstring-after-wrapping-lp-1178455-test #3 failed")
  (goto-char 273)
  (sit-for 0.1 t)
  (fill-paragraph t)
  (end-of-line)
  (assert (eq 25 (current-column)) nil "Bogus-whitespace-left-in-docstring-after-wrapping-lp-1178455-test #4 failed"))

(defun trouble-with-py-fill-paragraph-lp-1180653-test (&optional arg)
  (interactive "p")
  (let ((teststring "#! /usr/bin/env python
# -\*- coding: utf-8 -\*-
# I'm trying to refill the following docstring:

class BlockCache(object):

    def remove(self, inode, start_no, end_no=None):
        \"\"\"Remove blocks for `inode`

        If `end_no` is not specified, remove just the `start_no`
        block.
        Otherwise removes all blocks from `start_no` to, but not
        including, `end_no`.

        Note: if `get` and `remove` are called concurrently, then
it is
        possible that a block that has been requested with `get`
and
        passed to `remove` for deletion will not be deleted.
        \"\"\"

        log.debug('remove(inode=%d, start=%d, end=%s): start',
inode, start_no, end_no)

        if end_no is None:
            end_no = start_no + 1

# When I place the cursor on e.g. the first line (\"If `end_no`...)
# and execute M-x py-fill-paragraph, the buffer is scrolled such that
# this becomes the first visible line, and the indentation is
# removed. No filling occurs at all.
#
# Am I doing something wrong? py-docstring-style is set to
# pep-256-nn.
"))
  (py-bug-tests-intern 'trouble-with-py-fill-paragraph-lp-1180653-base arg teststring)))

(defun trouble-with-py-fill-paragraph-lp-1180653-base (arg)
    (goto-char 214)
    (assert nil "trouble-with-py-fill-paragraph-lp-1180653-test failed"))

(defun py-shell-in-a-shell-buffer-doesnt-work-lp-1182696-test (&optional arg)
  (interactive "p")
  (let ((teststring ""))
  (py-bug-tests-intern 'py-shell-in-a-shell-buffer-doesnt-work-lp-1182696-base arg teststring)))

(defun py-shell-in-a-shell-buffer-doesnt-work-lp-1182696-base (arg)
  (let (py-switch-buffers-on-execute-p
        py-split-window-on-execute)
    (shell)
    (delete-other-windows)
    (py-shell 1)
    (assert (string= "*shell*" (buffer-name)) nil "py-shell-in-a-shell-buffer-doesnt-work-lp-1182696-test #1 failed")
    (let ((py-switch-buffers-on-execute-p t))
      (py-shell 1))
    (sit-for 0.1 t)
    (assert (string-match "*Python" (buffer-name)) nil "py-shell-in-a-shell-buffer-doesnt-work-lp-1182696-test #2 failed")))

(defun from-within-py-shell-call-another-instance-lp-1169687-test (&optional arg)
  (interactive "p")
  (let ((teststring ""))
  (py-bug-tests-intern 'from-within-py-shell-call-another-instance-lp-1169687-base arg teststring)))

(defun from-within-py-shell-call-another-instance-lp-1169687-base (arg)
    (let ((py-shell-name "python")
	  (py-split-window-on-execute t)
          (py-switch-buffers-on-execute-p t))
    (py-shell)
    (sit-for 0.1 t)
    (py-shell '(4))
    (assert (string-match "\\*Python" (buffer-name)) nil "from-within-py-shell-call-another-instance-lp-1169687-test failed")))

(defun multibuffer-mayhem-lp-1162q272-test (&optional arg)
  (interactive "p")
  (let ((teststring "#! /usr/bin/env python
# -*- coding: utf-8 -*-
def do_something():
wrong_indent
"))
  (py-bug-tests-intern 'multibuffer-mayhem-lp-1162272-base arg teststring)))

(defun multibuffer-mayhem-lp-1162272-base (arg)
    (assert (not (py-execute-buffer)) nil "multibuffer-mayhem-lp-1162272-test failed"))

(defun incorrect-indentation-with-tertiary-lp-1189604-test (&optional arg)
  (interactive "p")
  (let ((teststring "#! /usr/bin/env python
# -*- coding: utf-8 -*-

# Put point right after the 'c' on the last line and hit return. You
# will be indented to column 8 when you should be indented to column
# 13.

def foo(c):
    a = 1
    other = ('yes'
             if a == c
"))
  (py-bug-tests-intern 'incorrect-indentation-with-tertiary-lp-1189604-base arg teststring)))

(defun incorrect-indentation-with-tertiary-lp-1189604-base (arg)
  (assert (eq 13 (py-compute-indentation)) nil "incorrect-indentation-with-tertiary-lp-1189604-test failed"))

(defun indentation-doesnt-honor-comment-on-preceding-lp-1190288-test (&optional arg)
  (interactive "p")
  (let ((teststring "#! /usr/bin/env python
# -*- coding: utf-8 -*-
# Put point at the end of the comment line and hit return. The next
# line indents to column 8 when it should indent to column 4.

def foo():
    with bar() as baz:
        baz.frobnicate()
    # This is a comment
"))
  (py-bug-tests-intern 'indentation-doesnt-honor-comment-on-preceding-lp-1190288-base arg teststring)))

(defun indentation-doesnt-honor-comment-on-preceding-lp-1190288-base (arg)
    (assert (eq 4 (py-compute-indentation)) nil "indentation-doesnt-honor-comment-on-preceding-lp-1190288-test failed"))

(defun fill-paragraph-corrupts-the-lp-1162912-test (&optional arg)
  (interactive "p")
  (let ((teststring "#! /usr/bin/env python
# -*- coding: utf-8 -*-

# Put point on the whitespace at the beginning of the line that
# starts with 'The' inside the docstring and hit M-q. You end up with
# the following:
#
# -----snip snip-----
# def foo():
#     \"\"\"This is a function.
# The function does some stuff that is very interesting. It's hard to
#     describe, but you will certainly love it when you try it. It's
# one
#     of the best functions ever written, not just by me, but by all
# of
#     mankind. Well, that may be overstating it, but it is a wondeful
#     function. \"\"\"

def foo():
    \"\"\"This is a function.

    The function does some stuff that is very interesting. It's
hard to
    describe, but you will certainly love it when you try it. It's
one of the
    best functions ever written, not just by me, but by all of
mankind.
    Well, that may be overstating it, but it is a wondeful
function.
    \"\"\"

"))
  (py-bug-tests-intern 'fill-paragraph-corrupts-the-lp-1162912-base arg teststring)))

(defun fill-paragraph-corrupts-the-lp-1162912-base (arg)
    (goto-char 616)
    (fill-paragraph)
    (forward-line 1)
    (assert (eq 4 (current-indentation))  nil "fill-paragraph-corrupts-the-lp-1162912-test failed"))

(defun return-key-is-broken-lp-1191158-test (&optional arg)
  (interactive "p")
  (let ((teststring "#! /usr/bin/env python
# -*- coding: utf-8 -*-
# A recent change broke the return key.
#
# Put point at the end of the last line and hit return. You correctly end
# up on a new line at column 8. But hit return again and point doesn't
# move! It should insert a blank line and leave you at column 8 on a new
# line.

def foo():
    with open('foo') as fp:
        do_something()"))
  (py-bug-tests-intern 'return-key-is-broken-lp-1191158-base arg teststring)))

(defun return-key-is-broken-lp-1191158-base (arg)
  (goto-char 378)
  (py-newline-and-indent)
  (py-newline-and-indent)
  (message "%s" (point) )
  ;; (sit-for 0.1 t)
  (assert (and (eq 14 (count-lines  (point-min) (point))) (eq 8 (current-column)))  nil "return-key-is-broken-lp-1191158-test failed"))

(defun indent-refused-lp-1191133-test (&optional arg)
  (interactive "p")
  (let ((teststring "#! /usr/bin/env python
# -*- coding: utf-8 -*-
def(foo):
"))
  (py-bug-tests-intern 'indent-refused-lp-1191133-base arg teststring)))

(defun indent-refused-lp-1191133-base (arg)
  (message "%s" (current-buffer))
  ;; (switch-to-buffer (current-buffer))
  (assert (eq 4 (py-compute-indentation)) nil "indent-refused-lp-1191133-test failed"))

(defun Parens-span-multiple-lines-lp-1191225-test (&optional arg)
  (interactive "p")
  (let ((teststring "#! /usr/bin/env python
# -*- coding: utf-8 -*-
# On Jun 14, 2013, at 05:04 PM, Felipe Reyes wrote:
def foo():
    if (foo &&
        baz):
        bar()
# >> This example raises a pep8 warning[0],
# >> I've been dealing with it and manually
# >> adding another indentation level to not leave 'baz' aligned with 'baz
# ()'
# >>
def foo():
    if (foo &&
            baz):
        bar()
"))
  (py-bug-tests-intern 'Parens-span-multiple-lines-lp-1191225-base arg teststring)))

(defun Parens-span-multiple-lines-lp-1191225-base (arg)
  (let (py-indent-paren-spanned-multilines-p)
    (goto-char 126)
    (assert (eq 8 (py-compute-indentation)) nil "Parens-span-multiple-lines-lp-1191225-test #1 failed")
    (goto-char 354)
    (setq py-indent-paren-spanned-multilines-p t)
    (assert (eq 12 (py-compute-indentation)) nil "Parens-span-multiple-lines-lp-1191225-test #2 failed")))

(defun Bogus-dedent-when-typing-colon-in-dictionary-literal-lp-1197171-test (&optional arg)
  (interactive "p")
  (let
      ((teststring "#! /usr/bin/env python
# -*- coding: utf-8 -*-
def foo():
    bar('thing',
        {'another'

# Put point at the end of the last line and hit colon, as you would to
# separate the key from the value. The last line will incorrectly dedent
# to column 4. Indentation should not change.

"))
    (py-bug-tests-intern 'Bogus-dedent-when-typing-colon-in-dictionary-literal-lp-1197171-base arg teststring)))

(defun Bogus-dedent-when-typing-colon-in-dictionary-literal-lp-1197171-base (arg)
    (goto-char 94)
    (assert (eq 8 (py-compute-indentation)) nil "Bogus-dedent-when-typing-colon-in-dictionary-literal-lp-1197171-test failed"))

(defun Non-indenting-colon-lp-1207405-test (&optional arg)
  (interactive "p")
  (let ((teststring "#! /usr/bin/env python
# -\*- coding: utf-8 -\*-
def foo(bar):
 for i in range(10)
        print(i)
    tied = bar[

# Put point on the last line, after the open bracket. Hit colon (as if you
# were going to type bar[:]). The line gets incorrectly indented to under
# the `print`.
#
# There may be other situations where colons should not re-indent the
# line.

"))
  (py-bug-tests-intern 'Non-indenting-colon-lp-1207405-base arg teststring)))

(defun Non-indenting-colon-lp-1207405-base (arg)
  (goto-char 81)
  (py-electric-colon t)
  (message "(current-indentation): %s" (current-indentation))
  (assert (eq 4 (current-indentation)) nil "Non-indenting-colon-lp-1207405-test #1 failed")
  (goto-char 118)
  (ignore-errors (py-electric-colon 1))
  (assert (eq 4 (current-indentation)) nil "Non-indenting-colon-lp-1207405-test #2 failed"))

;; (defun missing-py-variable-name-face-lp-1215791-test (&optional arg)
;;   (interactive "p")
;;    (let ((teststring "a = b = c = 5
;; a, b, c = (1, 2, 3)
;; # http://lists.gnu.org/archive/html/bug-gnu-emacs/2013-08/msg00740.
;; # html
;; #
;; # The symptom is that in the code:
;;
;;     # no s'ha trobat cap oferta, l'alumne queda sense assignar
;;     # (alumne.assignacio == None)
;;     self._logger.info(
;;          u\"no assigna '%s'\",
;;          alumne.id
;;          )
;;     alumne.assignacio = None
;;
;; # 'alumne.assignacio' isn't properly colorized after visiting the
;; # file.
;; #
;; # In order to reproduce this behaviour:
;; #
;; # emacs -Q /tmp/bugtest.py
;; #
;; # type:
;;
;; # a =
;; variable = \"value\"
;; a = b = c = 5
;; a, b, c = (1, 2, 3)
;; "))
;;   (py-bug-tests-intern 'missing-py-variable-name-face-lp-1215791-base arg teststring)))

(defun missing-py-variable-name-face-lp-1215791-test (&optional arg)
  (interactive "p")
   (let ((teststring "# a ==
variable = \"value\"
a = b = c = 5
a, b, c = (1, 2, 3)
# http://lists.gnu.org/archive/html/bug-gnu-emacs/2013-08/msg00740.
# html
#
# The symptom is that in the code:

    # no s'ha trobat cap oferta, l'alumne queda sense assignar
    # (alumne.assignacio == None)
    self._logger.info(
         u\"no assigna '%s'\",
         alumne.id
         )
    alumne.assignacio = None

# 'alumne.assignacio' isn't properly colorized after visiting the
# file.
#
# In order to reproduce this behaviour:

"))
  (py-bug-tests-intern 'missing-py-variable-name-face-lp-1215791-base arg teststring)))

(defun missing-py-variable-name-face-lp-1215791-base (arg)
  (font-lock-fontify-buffer)
  ;; (when py-debug-p (switch-to-buffer (current-buffer)))
  ;; (goto-char 6)
  (goto-char 27)
  (sit-for 0.1 t)
  (assert (eq (get-char-property (point) 'face) 'py-variable-name-face) nil "missing-py-variable-name-face-lp-1215791-test #1 failed")
  (goto-char 44)
  (assert (eq (get-char-property (point) 'face) 'py-variable-name-face) nil "missing-py-variable-name-face-lp-1215791-test #2 failed")
  (goto-char 360)
  (assert (eq (get-char-property (point) 'face) 'py-variable-name-face) nil "missing-py-variable-name-face-lp-1215791-test #3 failed")

  )

(defun C-c-C-c-lp-1221310-and-store-result-test (&optional arg)
  (interactive "p")
   (let ((teststring "print(\"C-c-C-c-lp-1221310-and-store-result-test\")
"))
  (py-bug-tests-intern 'C-c-C-c-lp-1221310-and-store-result-base arg teststring)))

(defun C-c-C-c-lp-1221310-and-store-result-base (arg)
  (when py-debug-p (switch-to-buffer (current-buffer)))
  (write-file (concat py-temp-directory "/lp-1221310.py"))
  (assert (let ((py-store-result-p t))
	    (py-execute-buffer)
            (sit-for 0.1 t)
            (string= "C-c-C-c-lp-1221310-and-store-result-test" (car kill-ring))) nil "C-c-C-c-lp-1221310-and-store-result-test failed"))

(defun py-empty-line-closes-p-lp-1235324-test (&optional arg)
  (interactive "p")
   (let ((teststring "#! /usr/bin/env python
if True:
    if True:
        print(\"This line is part of the inner statement\")

    print(\"This line is NOT part of the inner statement\")
\")
"))
  (py-bug-tests-intern 'py-empty-line-closes-p-lp-1235324-base arg teststring)))

(defun py-empty-line-closes-p-lp-1235324-base (arg)
  (goto-char (point-min))
  (let (py-empty-line-closes-p)
    (search-forward "print" nil t 2)
    (assert (eq 8 (py-compute-indentation)) nil "py-empty-line-closes-p-lp-1235324-test #1 failed"))
  (let ((py-empty-line-closes-p t))
    (assert (eq 4 (py-compute-indentation)) nil "py-empty-line-closes-p-lp-1235324-test #2 failed")))

(defun py-docstring-style-pep-257-nn-closing-quotes-lp-1241147-test (&optional arg)
  (interactive "p")
  (let ((teststring "#! /usr/bin/env python
# -*- coding: utf-8 -*-
class Class(object):
    \"\"\"A long long long long long long long long long long long
long long long long long long long line.\"\"\"
"))
    (py-bug-tests-intern 'py-docstring-style-pep-257-nn-closing-quotes-lp-1241147-base arg teststring)))

(defun py-docstring-style-pep-257-nn-closing-quotes-lp-1241147-base (arg)
  (let ((py-docstring-style 'pep-257-nn))
    (forward-line -1)
    (fill-paragraph)
    (sit-for 0.1 t)
    (assert (search-forward "    \"\"\"" nil t 1) nil "py-docstring-style-pep-257-nn-closing-quotes-lp-1241147-test failed")))

(defun indentation-after-parentized-assignment-lp-1243012-test (&optional arg)
  (interactive "p")
   (let ((teststring "#! /usr/bin/env python
def main():
    (a, b) = (1, 2)
"))
  (py-bug-tests-intern 'indentation-after-parentized-assignment-lp-1243012-base arg teststring)))

(defun indentation-after-parentized-assignment-lp-1243012-base (arg)
    (goto-char 40)
    (assert nil "indentation-after-parentized-assignment-lp-1243012-test failed"))

(defun py-execute-buffer-ipython-lp-1252643-test (&optional arg)
  (interactive "p")
   (let ((teststring "#! /usr/bin/env python
print(1234)
"))
  (py-bug-tests-intern 'py-execute-buffer-ipython-lp-1252643-base arg teststring)))

(defun py-execute-buffer-ipython-lp-1252643-base (arg)
  (ignore-errors (py-kill-buffer-unconditional "*IPython*"))
  (let ((py-switch-buffers-on-execute-p t))
    (py-execute-buffer-ipython)
    (buffer-live-p (get-buffer  "*IPython*"))
    (sit-for 0.2 t)
    (assert (progn (set-buffer "*IPython*")(goto-char (point-max)) (search-backward "1234")) nil "py-execute-buffer-ipython-lp-1252643-test failed")))

(defun Execute-region_statement-runs-full-file-lp-1269855-test (&optional arg)
  (interactive "p")
   (let ((teststring "#! /usr/bin/env python
# -*- coding: utf-8 -*-
def s (n):
    sum=0
    for i in range(1,n+1):
         sum += i
         #print i
    return sum

print s(10)
print s(100)
print s(500)
"))
  (py-bug-tests-intern 'Execute-region_statement-runs-full-file-lp-1269855-base arg teststring)))

(defun Execute-region_statement-runs-full-file-lp-1269855-base (arg)
  (py-execute-buffer)
  (goto-char 149)
  (py-execute-statement)
  (assert nil "Execute-region_statement-runs-full-file-lp-1269855-test failed"))

(defun abbrevs-changed-t-when-starting-lp-1270631-test (&optional arg)
  (interactive "p")
   (let ((teststring "#! /usr/bin/env python
# -*- coding: utf-8 -*-

"))
  (py-bug-tests-intern 'abbrevs-changed-t-when-starting-lp-1270631-base arg teststring)))

(defun abbrevs-changed-t-when-starting-lp-1270631-base (arg)
  (assert (eq nil abbrevs-changed) nil "abbrevs-changed-t-when-starting-lp-1270631-test failed"))

(defun wrong-type-argument-inserted-chars-lp-1293172-test (&optional arg)
  (interactive "p")
   (let ((teststring ""))
  (py-bug-tests-intern 'wrong-type-argument-inserted-chars-lp-1293172-base arg teststring)))

(defun wrong-type-argument-inserted-chars-lp-1293172-base (arg)
      (assert (insert-file-contents (concat py-install-directory "/test/tn_clippy.txt")) nil "wrong-type-argument-inserted-chars-lp-1293172-test failed"))

(defun py-mark-def-hangs-lp-1294478.py-test (&optional arg)
  (interactive "p")
   (let ((teststring "#! /usr/bin/env python
# -*- coding: utf-8 -*-
def expand(self, leading=0, subs={}):
    for tracking_ln in self.template_list:
	# count leading blanks
	# find \$x and \${x} form
	# expand each sub string before replacement
	# replace \$x and \${x} form
	tLinePreCnt = len(tLine)-len(fullstr.lstrip())
	tracking_ndx = tLinePreCnt

	# breakdown line
	# don't process a line starting with a hash
	# first look for the \$. Then it should be followed by
	# either a \$,{ or a-zA-Z add spaces iff sub is multi-line

	character position = template line.find(\"#\")
	if character position == trailing index:
	    # skip this line
	    expansion_list.append (template line)
	    break

	working_line = template line [0: trailing index]
	while(True):
	    #scan for all \$ combos
	    character position = template line.find (\"\$\", trailing index)
	    if character position == -1:
		# copy the rest of the line
		working_line.append (template line [trailing index: -1])
		break

	    elif template line[character position + 1] is \"\$\":
		# this is a quoted \$?  de-quote
		working_line.append (template line [trailing index: character position]
		trailing index = character position+2

	    elif template line[character position + 1] is \"{\":
		# extract alphanum + _
		working_line.append (template line [trailing index: character position -1])
		start bracket = character position+1
		end bracket = template line.find (\"}\", start bracket)
		if end bracket == -1:
		    #no closing bracket. time to raise exception.
		    raise
		# substitution key is between start bracket and end bracket
		substitution key = template line [start bracket+1:end bracket-1]
		sub_string = sub[substitution key]
		expanded lines = self.recursive_expand(sub_string)
		# append the first line to working line, then append the
		# rest of the lines after adding preamble

	    elif template line [character position + 1].isalnum():
		# \$a-z form
		print \"not implemented yet\"
	    else:
		print \"why am I here\"

     return expansion_list
"))
  (py-bug-tests-intern 'py-mark-def-hangs-lp-1294478.py-base arg teststring)))

(defun py-mark-def-hangs-lp-1294478.py-base (arg)
    (goto-char 40)
    (assert nil "py-mark-def-hangs-lp-1294478.py-test failed"))

(defun execute-region-lp-1294796-test (&optional arg)
  (interactive "p")
   (let ((teststring "print(1)
"))
  (py-bug-tests-intern 'execute-region-lp-1294796-base arg teststring)))

(defun execute-region-lp-1294796-base (arg)
  (let ((py-shell-name "ipython"))
    (py-execute-buffer)
    (set-buffer "*IPython*")
    (when py-debug-p (switch-to-buffer (current-buffer)))
    (goto-char comint-last-output-start)
    (sit-for 0.1 t)
    (and (eq (char-before) ?\n) (forward-char -1))
    (assert (or (eq 49 (char-after))(eq 49 (char-before))) nil "execute-region-lp-1294796-test failed")))

(defun wrong-coloring-lp-1315186-test (&optional arg)
  (interactive "p")
   (let ((teststring "if show_search_box and jquery_path:
    search_box= '<form id=\"pubSearchBox\" name=\"pubSearchBox\"><input id=\"pubSearchInputBox\" type=\"text\" name=\"keyword\" />&nbsp;<input id=\"pubSearchButton\" type=\"button\" value=\"Search\" onClick=\"searchFunction()\" /></form><script type=\"text/javascript\" src=\"'+jquery_path+\"\"\"\"></script><script type=\"text/javascript\">
  function getURLParameter(name) {
    return decodeURIComponent((new RegExp('[?|&]' + name + '=' + '([^&;]+?)(&|#|;|\$)').exec(location.search)||[,\"\"])[1].replace(/\\+/g, '%20'))||null;
  }
  jQuery( document ).ready(function() {
    jQuery('#pubSearchInputBox').val(getURLParameter(\"keyword\"));
    searchFunction();
  });
function searchFunction() {
  var searchTerms = document.pubSearchBox.keyword.value.split(\" \");
  jQuery( \".bib-item\").css( \"display\", \"none\" );
  var q = \".bib-item\";
  jQuery.each(searchTerms, function(i,x) {q = q + \":contains('\"+x+\"')\";});
  jQuery(q).css( \"display\", \"block\" );
}
  jQuery(function() {    // <== Doc ready
  // stackoverflow q 3971524
    var inputVal = jQuery(\"#pubSearchInputBox\").val(),
        timer,
        checkForChange = function() {
            var self = this; // or just use .bind(this)
            if (timer) { clearTimeout(timer); }
            // check for change of the text field after each key up
            timer = setTimeout(function() {
                if(self.value != inputVal) {
                    searchFunction();
                    inputVal = self.value
                }
            }, 250);
        };
    jQuery(\"#pubSearchInputBox\").bind('keyup paste cut', checkForChange);
});</script>
\"\"\"
"))
  (py-bug-tests-intern 'wrong-coloring-lp-1315186-base arg teststring)))

(defun wrong-coloring-lp-1315186-base (arg)
    (goto-char (point-min))
    (search-forward "getURLParameter")
    (assert (eq (face-at-point) 'font-lock-string-face) nil "wrong-coloring-lp-1315186-test failed"))

(defun shell-not-advanced-lp-1294809-test (&optional arg)
  (interactive "p")
   (let ((py-split-window-on-execute t)
	 (teststring "#! /usr/bin/env python
# -*- coding: utf-8 -*-
print(123)
print(123w)
print(123)
print(123)
print(123)
")
	 py-prompt-on-changed-p)
  (py-bug-tests-intern 'shell-not-advanced-lp-1294809-base arg teststring)))

(defun shell-not-advanced-lp-1294809-base (arg)
  (py-execute-buffer)
  (assert nil "shell-not-advanced-lp-1294809-test failed"))

(defun show-source-code-lp-1318991-test (&optional arg)
  (interactive "p")
   (let ((teststring "#! /usr/bin/env python
# -*- coding: utf-8 -*-
1/0
"))
  (py-bug-tests-intern 'show-source-code-lp-1318991-base arg teststring)))

(defun show-source-code-lp-1318991-base (arg)
  (py-execute-buffer-python2-switch)
  (assert nil "show-source-code-lp-1318991-test failed"))

(defun specify-default-interpreter-lp-1332652-test ()
  (interactive)
  (with-current-buffer
      (set-buffer (get-buffer-create (get-buffer-create "default.py")))
    (set (make-local-variable 'py-shell-name) "python3.4")
    (switch-to-buffer (current-buffer))
    (or
	(assert (string= "python3.4" py-shell-name) nil "specify-default-interpreter-lp-1332652-test failed")
      (message "%s" "specify-default-interpreter-lp-1332652-test passed"))))

(defun vertical-alignment-lp-1332245-test (&optional arg)
  (interactive "p")
   (let ((teststring "#! /usr/bin/env python
# -\*- coding: utf-8 -\*-
# According to PEP-8, \"[c]ontinuation lines should align wrapped
# elements either vertically using Python's implicit line joining
# inside parentheses, brackets and braces, or using a hanging
# indent\". py-newline-and-indent does the job of aligning the next
# line with the opening parenthesis fine. However, when TAB is then
# pressed, this position is lost and multiples of py-python-offset
# are used instead. At the same, running M-x indent-for-tab-command
# or indent-according-to-mode fixes the problem.
#
# This is with python-mode 6.1.3 and Emacs 24.3.1.
# Marcin (antyfilidor) on 2014-06-19

# For instance in the PEP 8 example

foo = long_function_name(var_one, var_two,
                        var_three,
                        var_four)
"))
  (py-bug-tests-intern 'vertical-alignment-lp-1332245-base arg teststring)))

(defun vertical-alignment-lp-1332245-base (arg)
  (goto-char 755)
  (let ((need (py-compute-indentation)))
    (call-interactively 'py-indent-line)
    (or
	(assert (eq (current-indentation) need) nil "Vertical-alignment-with-opening-lp-1332245-test failed")
      (message "%s" "Vertical-alignment-with-opening-lp-1332245-test passed"))))

(defun stop-before-prompt-lp-1331953-test  ()
  (interactive)
  (let ((erg (py-shell nil t)))
    (unwind-protect
	(set-buffer erg)
      (goto-char (point-max))
      (insert "print(123)")
      (py-beginning-of-statement)
      (or
	  (assert (eq 4 (current-column)) nil "stop-before-prompt-lp-1331953-test failed")
	(message "%s" "stop-before-prompt-lp-1331953-test passed")))
    (py-kill-buffer-unconditional erg)))

(defun execute-buffer-lp-1338134-test (&optional arg)
  (interactive)
  (when py-verbose-p (message "run: %s" "execute-buffer-lp-1338134-test"))
   (let ((teststring "#! /usr/bin/env python
# -*- coding: utf-8 -*-
print(123)
"))
  (py-bug-tests-intern 'execute-buffer-lp-1338134-base arg teststring)))

(defun execute-buffer-lp-1338134-base (arg)
  (when py-verbose-p (message "run: %s" "execute-buffer-lp-1338134-base"))
  (assert (py-execute-buffer) nil "execute-buffer-lp-1338134-test failed"))

(defun dont-complete-empty-line-lp-1340824-test (&optional arg)
  (interactive "p")
   (let ((teststring "#! /usr/bin/env python
# -*- coding: utf-8 -*-
class Foo:a
"))
  (py-bug-tests-intern 'dont-complete-empty-line-lp-1340824-base arg teststring)))

(defun dont-complete-empty-line-lp-1340824-base (arg)
  (py-indent-or-complete)
  (sit-for 0.1 t)
  (assert (eq 4 (current-indentation)) nil "dont-complete-empty-line-lp-1340824-test failed"))

(defun auto-indent-lp-134258-test (&optional arg)
  (interactive "p")
   (let ((teststring "#! /usr/bin/env python
# -*- coding: utf-8 -*-
for d in os.listdir('console'):
    if('Scripts' != d):
"))
  (py-bug-tests-intern 'auto-indent-lp-134258-base arg teststring)))

(defun auto-indent-lp-134258-base (arg)
    (goto-char 80)
    (py-newline-and-indent)
    (assert (eq 4 (current-indentation)) nil "auto-indent-lp-134258-test failed"))

(defun py-object-reference-face-should-inherit-from-lp-1340455-test (&optional arg)
  (interactive "p")
   (let ((teststring "#! /usr/bin/env python
# -*- coding: utf-8 -*-
def foo(self):
"))
  (py-bug-tests-intern 'py-object-reference-face-should-inherit-from-lp-1340455-base arg teststring)))

(defun py-object-reference-face-should-inherit-from-lp-1340455-base (arg)
  (font-lock-fontify-buffer)
  (goto-char 57)
  (sit-for 0.1)
  (message "py-object-reference-face-should-inherit-from-lp-1340455-test: %s" (prin1-to-string (get-char-property (point) 'face)))
  (assert (eq (get-char-property (point) 'face) py-object-reference-face) nil " py-object-reference-face-should-inherit-from-lp-1340455-test failed"))

(defun tab-complete-dict-keys-lp-1251690-test (&optional arg)
  (interactive "p")
   (let ((teststring "#! /usr/bin/env python
# -*- coding: utf-8 -*-
d = {\"apple\": 1, \"banana\": 2}
d[\"a\""))
  (py-bug-tests-intern 'tab-complete-dict-keys-lp-1251690-base arg teststring)))

(defun tab-complete-dict-keys-lp-1251690-base (arg)
    (goto-char 40)
    (assert nil "tab-complete-dict-keys-lp-1251690-test failed"))

(defun py-shell-name-no-op-lp-1349549-test (&optional arg)
  (interactive "p")
   (let ((teststring "#! /usr/bin/env python
# -*- coding: utf-8 -*-
"))
  (py-bug-tests-intern 'py-shell-name-no-op-lp-1349549-base arg teststring)))

(defun py-shell-name-no-op-lp-1349549-base (arg)
  (let ((py-switch-buffers-on-execute-p t)
	(py-force-py-shell-name-p t)
	(py-shell-name "ipython"))
    (py-shell)
    (sit-for 1 t)
    (assert (string-match "\*IP" (buffer-name (current-buffer))) nil "py-shell-name-no-op-lp-1349549-test failed")))

(defun interpreter-mode-alist-lp-1355458-test-1 (&optional arg)
  (interactive "p")
   (let ((teststring "#! /usr/bin/env python
# -*- coding: utf-8 -*-
"))
  (py-bug-tests-intern 'interpreter-mode-alist-lp-1355458-base-1 arg teststring)))

(defun interpreter-mode-alist-lp-1355458-base-1 ()
  (assert (eq 'python-mode major-mode) nil "interpreter-mode-alist-lp-1355458-test-1 failed")
  (py-kill-buffer-unconditional (current-buffer)))

(defun interpreter-mode-alist-lp-1355458-test-2 (&optional arg)
  (interactive "p")
   (let ((teststring "#! /usr/bin/env python2
# -*- coding: utf-8 -*-
"))
  (py-bug-tests-intern 'interpreter-mode-alist-lp-1355458-base-2 arg teststring)))

(defun interpreter-mode-alist-lp-1355458-base-2 ()
  (assert (eq 'python-mode major-mode) nil "interpreter-mode-alist-lp-1355458-test-2 failed")
  (py-kill-buffer-unconditional (current-buffer)))

(defun interpreter-mode-alist-lp-1355458-test-3 (&optional arg)
  (interactive "p")
   (let ((teststring "#! /usr/bin/env python3
# -*- coding: utf-8 -*-
"))
  (py-bug-tests-intern 'interpreter-mode-alist-lp-1355458-base-3 arg teststring)))

(defun interpreter-mode-alist-lp-1355458-base-3 ()
  (assert (eq 'python-mode major-mode) nil "interpreter-mode-alist-lp-1355458-test-3 failed")
  (py-kill-buffer-unconditional (current-buffer)))

(defun interpreter-mode-alist-lp-1355458-test-4 (&optional arg)
  (interactive "p")
   (let ((teststring "#! /usr/bin/env ipython
# -*- coding: utf-8 -*-
"))
  (py-bug-tests-intern 'interpreter-mode-alist-lp-1355458-base-4 arg teststring)))

(defun interpreter-mode-alist-lp-1355458-base-4 ()
  (assert (eq 'python-mode major-mode) nil "interpreter-mode-alist-lp-1355458-test-4 failed")
  (py-kill-buffer-unconditional (current-buffer)))

(defun interpreter-mode-alist-lp-1355458-base-5 ()
  (assert (eq 'python-mode major-mode) nil "interpreter-mode-alist-lp-1355458-test-5 failed")
  (py-kill-buffer-unconditional (current-buffer)))

(defun interpreter-mode-alist-lp-1355458-test-6 (&optional arg)
  (interactive "p")
  (let ((teststring "#! /usr/bin/env jython
# -*- coding: utf-8 -*-
"))
    (py-bug-tests-intern 'interpreter-mode-alist-lp-1355458-base-6 arg teststring)))

(defun interpreter-mode-alist-lp-1355458-base-6 ()
  (assert (eq 'jython-mode major-mode) nil "interpreter-mode-alist-lp-1355458-test-6 failed")
  (py-kill-buffer-unconditional (current-buffer)))

(defun py-indent-line-lp-1382799-test (&optional arg)
  (interactive "p")
   (let ((teststring "#! /usr/bin/env python
# -*- coding: utf-8 -*-
import pdb; pdb.set_trace()
    Lattice.__setstate__(self, picdict)
"))
  (py-bug-tests-intern 'py-indent-line-lp-1382799-base arg teststring)))

(defun py-indent-line-lp-1382799-base (arg)
  (when py-debug-p (switch-to-buffer (current-buffer)))
  (font-lock-fontify-buffer)
  (goto-char 40)
  (py-forward-statement)
  (assert (eq (point) 59) nil "py-indent-line-lp-1382799-test #1 failed")
  (py-forward-statement)
  (assert (eq (point) 75) nil "py-indent-line-lp-1382799-test #2 failed")
  (py-forward-statement)
  (assert (eq (point) 115) nil "py-indent-line-lp-1382799-test #3 failed")
  (py-backward-statement)
  (assert (eq (point) 80) nil "py-indent-line-lp-1382799-test #4 failed")
  (py-backward-statement)
  (assert (eq (point) 60) nil "py-indent-line-lp-1382799-test #5 failed")
  (py-backward-statement)
  (assert (eq (point) 48) nil "py-indent-line-lp-1382799-test #6 failed")
  (goto-char 76)
  (assert (eq 0 (py-compute-indentation)) nil "py-indent-line-lp-1382799-test #7 failed")

  )

(defun indent-after-expect-lp-1387329-test (&optional arg)
  (interactive "p")
   (let ((teststring "#! /usr/bin/env python
# -*- coding: utf-8 -*-
try:
    something
except: pass

"))
  (py-bug-tests-intern 'indent-after-expect-lp-1387329-base arg teststring)))

(defun indent-after-expect-lp-1387329-base (arg)
  (when py-debug-p (switch-to-buffer (current-buffer)))
  (assert (eq 0 (py-compute-indentation)) nil "indent-after-expect-lp-1387329-test failed"))


(defun comment-inside-curly-braces-lp-1395076-test (&optional arg)
  (interactive "p")
  (let ((teststring "#! /usr/bin/env python
# -*- coding: utf-8 -*-

def foo():
    foo.bar = {
        'foo': 'bar',
    # foobar comment
    }

"))
    (py-bug-tests-intern 'comment-inside-curly-braces-lp-1395076-base arg teststring)))

(defun comment-inside-curly-braces-lp-1395076-base (arg)
  (goto-char 102)
  (assert (eq 8 (py-compute-indentation)) nil "comment-inside-curly-braces-lp-1395076-test failed"))


(defun opening-brace-on-builtins-lp-1400951-test (&optional arg)
  (interactive "p")
   (let ((teststring "#! /usr/bin/env python
# -*- coding: utf-8 -*-
print(sorted(range()))
"))
  (py-bug-tests-intern 'opening-brace-on-builtins-lp-1400951-base arg teststring)))

(defun opening-brace-on-builtins-lp-1400951-base (arg)
  (goto-char 53)
  (assert (not (get-char-property (point) 'face)) nil "opening-brace-on-builtins-lp-1400951-test #1 failed")
  (goto-char 60)
  (assert (not (get-char-property (point) 'face)) nil "opening-brace-on-builtins-lp-1400951-test #2 failed"))


(provide 'py-bug-numbered-tests)
;;; py-bug-numbered-tests.el ends here
