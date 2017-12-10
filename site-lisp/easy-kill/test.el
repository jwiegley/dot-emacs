;;; test.el --- tests for easy-kill                  -*- lexical-binding: t; -*-

;; Copyright (C) 2014  Free Software Foundation, Inc.

;; Author: Leo Liu <sdl.web@gmail.com>
;; Keywords: maint

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

;;; Code:

(require 'easy-kill)
(require 'ert)

;; (defmacro with-named-temp-buffer (name &rest body)
;;   (declare (indent with-current-buffer))
;;   `(unwind-protect
;;        (with-current-buffer (get-buffer-create ,name)
;;          ,@body)
;;      (and (get-buffer ,name) (kill-buffer ,name))))

;; (ert-deftest test-compilation ()
;;   (should (zerop (call-process "emacs" nil nil nil
;;                                "-batch" "-Q" "-f" "batch-byte-compile"
;;                                "easy-kill.el"))))

(ert-deftest test-easy-kill-trim ()
  (should (string= "" (easy-kill-trim "  \f\t\n\n\n")))
  (should (string= "abc" (easy-kill-trim " \t\fabc")))
  (should (string= "abc" (easy-kill-trim "abc")))
  (should (string= " \t\fabc" (easy-kill-trim " \t\fabc" 'right)))
  (should (string= "abc" (easy-kill-trim " \t\fabc" 'left))))

(ert-deftest test-easy-kill-get ()
  (with-temp-buffer
    (insert "two words")
    (easy-kill)
    (setf (easy-kill-get bounds) '(1 . 4))
    (should (string= (easy-kill-candidate) "two"))
    (should-error (setf (easy-kill-get bounds) nil))
    (setf (easy-kill-get end) (point-max))
    (should (= (easy-kill-get end) (point-max)))))

(ert-deftest test-easy-kill-candidate ()
  (let ((w "yes"))
    (with-temp-buffer
      (insert w)
      (should-error (easy-kill-candidate))
      (easy-kill)
      (easy-kill-thing 'word)
      (should (string= w (easy-kill-candidate)))
      (easy-kill-thing 'buffer-file-name)
      (should (string= (directory-file-name default-directory)
                       (easy-kill-candidate))))))

(ert-deftest test-easy-kill-describe-candidate ()
  (with-temp-buffer
    (insert "(list 1 2 3)")
    (forward-word -1)
    (easy-kill)
    (easy-kill-thing 'sexp)
    (easy-kill-thing 'list)
    (should (string-match-p "^\\s-*thing:\\s-*list"
                            (easy-kill-describe-candidate)))))

(ert-deftest test-easy-kill-append ()
  (with-temp-buffer
    (insert "abc")
    (easy-kill)
    (easy-kill-thing 'word)
    (call-interactively #'easy-kill-append)
    (should (string= (car kill-ring) "abc"))))

(ert-deftest test-easy-kill-delete-region ()
  (with-temp-buffer
    (insert "abc def ghi")
    (backward-word 2)
    (kill-new "test")
    (easy-kill)
    (easy-kill-thing 'word)
    (call-interactively #'easy-kill-delete-region)
    (should (string= (car kill-ring) "test"))
    (should (string= (buffer-substring-no-properties (point-min) (point)) "abc "))
    (should (string= (buffer-substring-no-properties (point) (point-max)) " ghi"))))

;;; Make sure the old format of easy-kill-alist is still supported.
(ert-deftest test-old-easy-kill-alist ()
  (let ((easy-kill-alist '((?w . word)
                           (?s . sexp)
                           (?l . list)
                           (?f . filename)
                           (?d . defun)
                           (?e . line)
                           (?b . buffer-file-name)))
        (text "(first line\nsecond line\nthird line)"))
    (with-temp-buffer
      (insert text)
      (goto-char (point-min))
      (easy-kill)
      (let ((last-command-event ?d))
        (call-interactively #'easy-kill-thing))
      (should (string= text (easy-kill-candidate))))))

(ert-deftest test-easy-kill-help ()
  (let ((easy-kill-alist '((?w . word)
                           (?s . sexp)
                           (?l . list)
                           (?f filename)
                           (?d defun "\n\n")
                           (?e . line)
                           (?b . buffer-file-name)
                           (?x buffer-file-name-buffer-file-name "\t"))))
    (easy-kill-help)
    (with-current-buffer (help-buffer)
      (goto-char (point-min))
      (should (save-excursion
                (re-search-forward "^w\\s-*word$" nil t)))
      (should (save-excursion
                (re-search-forward "^d\\s-*defun\\s-*\"\\\\n\\\\n\"$" nil t)))
      (should (save-excursion
                (re-search-forward "^f\\s-*filename$" nil t)))
      (should (save-excursion
                (re-search-forward "^b\\s-*buffer-file-name$" nil t))))))

(ert-deftest test-easy-kill-thing-handler ()
  (should (eq (easy-kill-thing-handler "easy-kill-on-list" 'nxml-mode)
              'easy-kill-on-list:nxml))
  (should (eq (easy-kill-thing-handler "easy-kill-on-list" 'js2-mode)
              'easy-kill-on-list:js2))
  (should (eq (easy-kill-thing-handler "easy-kill-on-sexp" 'nxml-mode)
              'easy-kill-on-sexp))
  ;; XXX: side-effect
  (fset 'js2:easy-kill-on-list #'ignore)
  (eq (easy-kill-thing-handler "easy-kill-on-sexp" 'js2-mode)
      'js2:easy-kill-on-list))

(ert-deftest test-easy-kill-bounds-of-list-at-point ()
  (let ((text "\"abc (1 2 3) xyz\" ; dummy comment")
        (text2 "(progn
                 \"[compile\"
                 (should (string= \"display editor.\\nsome of the ways to customize it;\"
                                  (easy-kill-candidate))))"))
    (cl-labels ((getb (bounds)
                      (if bounds
                          (buffer-substring (car bounds) (cdr bounds))
                        "")))
      (with-temp-buffer
        (emacs-lisp-mode)
        (insert text)
        (search-backward "2")
        (should (string= (getb (easy-kill-bounds-of-list-at-point)) "(1 2 3)"))
        (up-list -1)
        (forward-word -1)
        (should (string= (getb (easy-kill-bounds-of-list-at-point))
                         "\"abc (1 2 3) xyz\""))
        (search-forward "dummy")
        (forward-word -1)
        (should (string= (getb (easy-kill-bounds-of-list-at-point))
                         "dummy"))
        ;; text2
        (erase-buffer)
        (insert text2)
        (goto-char (point-min))
        (re-search-forward "customize")
        (call-interactively 'easy-kill)
        (easy-kill-thing 'list)
        (should (string= "\"display editor.\\nsome of the ways to customize it;\""
                         (easy-kill-candidate)))))))

(ert-deftest test-easy-kill-on-list ()
  (let ((text "(defun first-error (&optional n)
                \"This operates on the output from the \\\\[compile] command, for instance.\"
                (interactive \"p\")
                (next-error n t)) ;some dummy comment here"))
    (with-temp-buffer
      (emacs-lisp-mode)
      (insert text)
      (goto-char (point-min))
      (search-forward "[compile")
      (call-interactively 'easy-kill)
      (easy-kill-thing 'list)
      (should (string= "[compile]" (easy-kill-candidate)))
      (up-list -1)
      (call-interactively 'easy-kill)
      (let ((clipboard))
        (cl-letf (((symbol-function 'easy-kill-interprogram-cut)
                   (lambda (text) (setq clipboard text))))
          (easy-kill-thing 'list))
        (should (string= (easy-kill-candidate) clipboard)))
      (should (string= "\"This operates on the output from the \\\\[compile] command, for instance.\""
                       (easy-kill-candidate)))
      (easy-kill-thing 'list)
      (should (string-match-p "(interactive \"p\")" (easy-kill-candidate)))
      (should (string-prefix-p "\"This operates on" (easy-kill-candidate)))
      (forward-sexp 1)                  ; where bounds of list is nil
      (call-interactively 'easy-kill)
      (easy-kill-thing 'list)
      (should (string= "\"This operates on the output from the \\\\[compile] command, for instance.\""
                       (easy-kill-candidate)))
      (search-forward "dummy")
      (forward-word -1)
      (call-interactively 'easy-kill)
      (easy-kill-thing 'list)
      (should (string= "dummy" (easy-kill-candidate))))))

(ert-deftest test-js2-mode ()
  :expected-result :failed
  (let ((js "function View(name, options) {
  options = options || {};
  this.name = name;
  this.root = options.root;
  var engines = options.engines;
  this.defaultEngine = options.defaultEngine;
  var ext = this.ext = extname(name);
  if (!ext && !this.defaultEngine) throw new Error('No default engine was specified and no extension was provided.');
  if (!ext) name += (ext = this.ext = ('.' != this.defaultEngine[0] ? '.' : '') + this.defaultEngine);
  this.engine = engines[ext] || (engines[ext] = require(ext.slice(1)).__express);
  this.path = this.lookup(name);
}")
        (buff (get-buffer-create "*js2*")))
    (eval-and-compile (require 'js2-mode nil t))
    (setq js2-idle-timer-delay 0)
    (global-font-lock-mode 1)
    (unwind-protect
        (with-current-buffer buff
          (js2-mode)
          (insert js)
          (goto-char (point-min))
          (js2-reparse t)
          ;; (js2-do-parse)
          (while js2-mode-buffer-dirty-p
            (sit-for 0.1))
          (search-forward "this.defaultEngine =")
          (forward-char -1)
          (easy-kill)
          (easy-kill-thing 'char)
          (easy-kill-thing 'list)
          (should (string= "this.defaultEngine = options.defaultEngine"
                           (easy-kill-candidate)))
          ;; XXX: should also test (easy-kill-digit-argument 0)
          )
      (kill-buffer buff))))

(ert-deftest test-nxml-mode ()
  (let ((xml "<?xml version=\"1.0\"?>
<catalog>
  <book id=\"bk101\">
    <author>Gambardella, Matthew</author>
    <title>XML Developer's Guide</title>
    <genre>Computer</genre>
    <price>44.95</price>
    <publish_date>2000-10-01</publish_date>
    <description>An in-depth look at creating applications
    with XML.</description>
  </book>
</catalog>"))
    (with-temp-buffer
      (nxml-mode)
      (insert xml)
      (goto-char (point-min))
      (search-forward "Gambardella")
      (easy-kill)
      (easy-kill-thing 'sexp)
      (easy-kill-expand)
      (easy-kill-expand)
      (easy-kill-shrink)
      (should (eq (easy-kill-get thing) 'sexp))
      (should (string= "<author>Gambardella, Matthew</author>"
                       (easy-kill-candidate)))
      (call-interactively 'easy-kill)
      (easy-kill-thing 'list)
      (should (string= "<author>Gambardella, Matthew</author>"
                       (easy-kill-candidate)))
      (easy-kill-thing nil 1)
      (easy-kill-digit-argument 0)
      (should (string= "<author>Gambardella, Matthew</author>"
                       (easy-kill-candidate))))))

(ert-deftest test-org-mode ()
  (let ((org "#+title: This is a title
#+author: Leo Liu

This is an example of org document.

* Life
  One two three ....
*** Fruits
    1. apple
    2. orange
    3. mango

* Sports cars
  + Lamborghini
  + Ferrari
  + Porsche
"))
    (with-temp-buffer
      ;; http://debbugs.gnu.org/17724
      (ignore-errors (org-mode))
      (insert org)
      (goto-char (point-min))
      (search-forward "This is")
      (call-interactively 'easy-kill)
      (easy-kill-thing 'sexp)
      (easy-kill-expand)
      (should (string= "#+title: This is a title\n" (easy-kill-candidate)))
      (search-forward "Fruits")
      (call-interactively 'easy-kill)
      (easy-kill-thing 'sexp)
      (easy-kill-expand)
      (should (string-prefix-p "*** Fruits" (easy-kill-candidate)))
      (search-forward "Ferrari")
      (call-interactively 'easy-kill)
      (easy-kill-thing 'list)
      (should (string= "Ferrari\n" (easy-kill-candidate)))
      (easy-kill-expand)
      (should (string= "  + Ferrari\n" (easy-kill-candidate)))
      ;; org quirks
      (search-backward "Lamborghini")
      (call-interactively 'easy-kill)
      (easy-kill-thing 'list)
      ;; You get the whole plainlist here; see `org-element-at-point'.
      (easy-kill-expand)
      (should (string= "  + Lamborghini\n  + Ferrari\n  + Porsche\n"
                       (easy-kill-candidate)))
      (easy-kill-expand)
      (should (string= "* Sports cars\n  + Lamborghini\n  + Ferrari\n  + Porsche\n"
                       (easy-kill-candidate))))))

(ert-deftest test-elisp-mode ()
  (let ((el "(defun set-hard-newline-properties (from to)
           (let ((sticky (get-text-property from 'rear-nonsticky)))
             ;; XXX: (put-text-property from to 'hard 't)
             ;; If rear-nonsticky is not \"t\", add 'hard to rear-nonsticky list
             (if (and (listp sticky) (not (memq 'hard sticky)))
                 (put-text-property from (point) 'rear-nonsticky
                                    (cons 'hard sticky)))))"))
    (with-temp-buffer
      (insert el)
      (goto-char (point-min))
      (search-forward "put-text-property")
      (easy-kill)
      (easy-kill-thing 'sexp)
      (easy-kill-expand)
      (should (eq (easy-kill-get thing) 'sexp))
      (should (string= "(put-text-property from to 'hard 't)"
                       (easy-kill-candidate)))
      (easy-kill-expand)
      (easy-kill-expand)
      (should (string= el (easy-kill-candidate)))
      (easy-kill-shrink)
      (easy-kill-shrink)
      (should (string= "(put-text-property from to 'hard 't)"
                       (easy-kill-candidate)))
      (easy-kill-digit-argument 0)
      (should (string= (thing-at-point 'sexp) (easy-kill-candidate))))))

(ert-deftest test-easy-kill-thing-forward ()
  (let ((txt "Emacs is the extensible
   display editor.
some of the ways to customize it;
24.3."))
    (with-temp-buffer
      (insert txt)
      (forward-line -1)
      (easy-kill)
      (easy-kill-thing 'line)
      (should (string= "some of the ways to customize it;\n24.3."
                       (easy-kill-candidate)))
      (easy-kill-shrink)
      (should (string= "some of the ways to customize it;\n"
                       (easy-kill-candidate)))
      (easy-kill-shrink)
      (should (string= "   display editor.\nsome of the ways to customize it;\n"
                       (easy-kill-candidate)))
      (easy-kill-thing 'word)
      (easy-kill-shrink)
      (should (string= "editor.\nsome" (easy-kill-candidate)))
      (easy-kill-shrink)
      (should (string= "display editor.\nsome" (easy-kill-candidate)))
      (easy-kill-expand)
      (should (string= " editor.\nsome" (easy-kill-candidate)))
      (easy-kill-destroy-candidate)
      (goto-char (point-min))
      (forward-line 1)
      (call-interactively 'easy-mark)
      (should (string= "   display" (easy-kill-candidate)))
      (goto-char (easy-kill-get origin))
      (deactivate-mark 1)
      ;; Test the case where there is no thing at point
      (call-interactively 'easy-kill)
      (setf (easy-kill-get thing) 'word)
      (setf (easy-kill-get bounds) (cons (point) (point)))
      (easy-kill-expand)
      (should (string= "   display" (easy-kill-candidate)))
      (easy-kill-shrink)
      (easy-kill-shrink)
      (easy-kill-shrink)
      (should (string= "the extensible\n" (easy-kill-candidate))))))

(ert-deftest test-workaround-defun-bug ()
  ;; http://debbugs.gnu.org/17247
  (let ((txt "(tan 2)\n\n(sin 2)\n(cos 2)\n"))
    (with-temp-buffer
      (insert txt)
      (easy-kill)
      (easy-kill-thing 'defun)
      (easy-kill-shrink)
      (should (string= "(sin 2)\n(cos 2)\n" (easy-kill-candidate)))
      (easy-kill-shrink)
      (should (string= txt (easy-kill-candidate))))))

(ert-deftest test-easy-kill-exchange-point-and-mark ()
  (let ((txt "(delete-region (point)
                            (if (re-search-forward \"[^ \\t\\n]\" nil t)
                                (progn (beginning-of-line) (point))
                              (point-max)))"))
    (with-temp-buffer
      (emacs-lisp-mode)
      (insert txt)
      (goto-char (point-min))
      (search-forward "re-search-forward")
      (call-interactively 'easy-mark)
      (should (string= "re-search-forward" (easy-kill-candidate)))
      (should (= (point) (easy-kill-get end)))
      (call-interactively 'easy-kill-exchange-point-and-mark)
      (easy-kill-expand)
      (should (= (point) (easy-kill-get start)))
      (should (= (mark t) (easy-kill-get end)))
      (call-interactively 'easy-kill-exchange-point-and-mark)
      (easy-kill-shrink)
      (should (= (mark t) (easy-kill-get start)))
      (should (= (point) (easy-kill-get end))))))

;;; test.el ends here
