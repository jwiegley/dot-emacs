;;; string-inflection.el --- underscore -> UPCASE -> CamelCase -> lowerCamelCase conversion of names

;; Copyright (C) 2004,2014,2016,2017 Free Software Foundation, Inc.

;; Author: akicho8 <akicho8@gmail.com>
;; Keywords: elisp
;; Version: 1.0.6

;; This file is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 2, or (at your option)
;; any later version.

;; This file is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with GNU Emacs; see the file COPYING.  If not, write to
;; the Free Software Foundation, Inc., 59 Temple Place - Suite 330,
;; Boston, MA 02111-1307, USA.

;;; Commentary:

;; Main functions are three
;;
;;   1. For Ruby -> string-inflection-ruby-style-cycle  (foo_bar => FOO_BAR => FooBar => foo_bar)
;;   2. For Java -> string-inflection-java-style-cycle  (fooBar  => FOO_BAR => FooBar => fooBar)
;;   3. For All  -> string-inflection-all-cycle         (foo_bar => FOO_BAR => FooBar => fooBar => foo-bar => foo_bar)
;;
;;
;; Setting Example 1
;;
;;   (require 'string-inflection)
;;   (global-unset-key (kbd "C-q"))
;;   ;; C-q C-u is the key bindings similar to Vz Editor.
;;   (global-set-key (kbd "C-q C-u") 'my-string-inflection-cycle-auto)
;;
;;   (defun my-string-inflection-cycle-auto ()
;;     "switching by major-mode"
;;     (interactive)
;;     (cond
;;      ;; for emacs-lisp-mode
;;      ((eq major-mode 'emacs-lisp-mode)
;;       (string-inflection-all-cycle))
;;      ;; for java
;;      ((eq major-mode 'java-mode)
;;       (string-inflection-java-style-cycle))
;;      (t
;;       ;; default
;;       (string-inflection-ruby-style-cycle))))
;;
;;
;; Setting Example 2
;;
;;   (require 'string-inflection)
;;
;;   ;; default
;;   (global-set-key (kbd "C-c C-u") 'string-inflection-all-cycle)
;;
;;   ;; for ruby
;;   (add-hook 'ruby-mode-hook
;;             '(lambda ()
;;                (local-set-key (kbd "C-c C-u") 'string-inflection-ruby-style-cycle)))
;;
;;   ;; for java
;;   (add-hook 'java-mode-hook
;;             '(lambda ()
;;                (local-set-key (kbd "C-c C-u") 'string-inflection-java-style-cycle)))
;;
;; You may also consider setting `string-inflection-skip-backward-when-done' to
;; `t' if you don't like `string-inflect' moving your point to the end of the
;; word

;;; Code:

(defconst string-inflection-word-chars "a-zA-Z0-9_-")

(defvar string-inflection-skip-backward-when-done nil
  "Whether point just move backward to the beginning of the word after inflecting.")

;; --------------------------------------------------------------------------------

;;;###autoload
(defun string-inflection-ruby-style-cycle ()
  "foo_bar => FOO_BAR => FooBar => foo_bar"
  (interactive)
  (string-inflection-insert
   (string-inflection-ruby-style-cycle-function (string-inflection-get-current-word))))

(fset 'string-inflection-cycle 'string-inflection-ruby-style-cycle)

;;;###autoload
(defun string-inflection-java-style-cycle ()
  "fooBar => FOO_BAR => FooBar => fooBar"
  (interactive)
  (string-inflection-insert
   (string-inflection-java-style-cycle-function (string-inflection-get-current-word))))

;;;###autoload
(defun string-inflection-all-cycle ()
  "foo_bar => FOO_BAR => FooBar => fooBar => foo-bar => foo_bar"
  (interactive)
  (string-inflection-insert
   (string-inflection-all-cycle-function (string-inflection-get-current-word))))

;;;###autoload
(defun string-inflection-toggle ()
  "toggle foo_bar <=> FooBar"
  (interactive)
  (string-inflection-insert
   (string-inflection-toggle-function (string-inflection-get-current-word))))

;;;###autoload
(defun string-inflection-camelcase ()
  "FooBar format"
  (interactive)
  (string-inflection-insert
   (string-inflection-camelcase-function (string-inflection-get-current-word t))))

;;;###autoload
(defun string-inflection-lower-camelcase ()
  "fooBar format"
  (interactive)
  (string-inflection-insert
   (string-inflection-lower-camelcase-function (string-inflection-get-current-word t))))

;;;###autoload
(defun string-inflection-underscore ()
  "foo_bar format"
  (interactive)
  (string-inflection-insert
   (string-inflection-underscore-function (string-inflection-get-current-word t))))

;;;###autoload
(defun string-inflection-upcase ()
  "FOO_BAR format"
  (interactive)
  (string-inflection-insert
   (string-inflection-upcase-function (string-inflection-get-current-word t))))

;;;###autoload
(defun string-inflection-kebab-case ()
  "foo-bar format"
  (interactive)
  (string-inflection-insert
   (string-inflection-kebab-case-function (string-inflection-get-current-word t))))

(fset 'string-inflection-lisp 'string-inflection-kebab-case)

;; --------------------------------------------------------------------------------

(defun string-inflection-insert (s)
  (insert s)
  (when string-inflection-skip-backward-when-done (skip-chars-backward string-inflection-word-chars)))

(defun string-inflection-non-word-chars ()
  (concat "^" string-inflection-word-chars))

(defun string-inflection-get-current-word (&optional skip)
  "Gets the symbol near the cursor.  If SKIP is non-nil, skip non-word characters forward."
  (interactive)
  (and skip
       (skip-chars-forward (string-inflection-non-word-chars)))
  (let* ((start (if mark-active
                    (region-end)
                  (progn
                    (skip-chars-forward string-inflection-word-chars)
                    (point))))
         (end (if mark-active
                  (region-beginning)
                (progn
                  (skip-chars-backward string-inflection-word-chars)
                  (point))))
         (str (buffer-substring start end)))
    (prog1
        (if mark-active
            (replace-regexp-in-string "[[:space:]]+" "_" str)
          str)
      (delete-region start end))))

;; --------------------------------------------------------------------------------

(defun string-inflection-camelcase-function (str)
  "foo_bar => FooBar"
  (setq str (string-inflection-underscore-function str))
  (mapconcat 'capitalize (split-string str "_") ""))

(fset 'string-inflection-camelize-function 'string-inflection-camelcase-function)

(defun string-inflection-lower-camelcase-function (str)
  "foo_bar => fooBar"
  (setq str (split-string (string-inflection-underscore-function str) "_"))
  (concat (downcase (car str))
          (mapconcat 'capitalize (cdr str) "")))

(fset 'string-inflection-lower-camelize-function 'string-inflection-lower-camelcase-function)

(defun string-inflection-upcase-function (str)
  "FooBar => FOO_BAR"
  (upcase (string-inflection-underscore-function str)))

(defun string-inflection-underscore-function (str)
  "FooBar => foo_bar"
  (let ((case-fold-search nil))
    (setq str (replace-regexp-in-string "\\([a-z0-9]\\)\\([A-Z]\\)" "\\1_\\2" str))
    (setq str (replace-regexp-in-string "-" "_" str)) ; FOO-BAR => FOO_BAR
    (setq str (replace-regexp-in-string "_+" "_" str))
    (downcase str)))

(defun string-inflection-kebab-case-function (str)
  "foo_bar => foo-bar"
  (let ((case-fold-search nil))
    (setq str (string-inflection-underscore-function str))
    (setq str (replace-regexp-in-string "_" "-" str))))

(defun string-inflection-all-cycle-function (str)
  "foo_bar => FOO_BAR => FooBar => fooBar => foo-bar => foo_bar
   foo     => FOO     => Foo    => foo"
  (cond
   ;; foo => FOO
   ((string-inflection-word-p str)
    (string-inflection-upcase-function str))
   ;; foo_bar => FOO_BAR
   ((string-inflection-underscore-p str)
    (string-inflection-upcase-function str))
   ;; FOO_BAR => FooBar
   ((string-inflection-upcase-p str)
    (string-inflection-camelcase-function str))
   ;; FooBar => fooBar
   ;; Foo    => foo
   ((string-inflection-camelcase-p str)
    (string-inflection-lower-camelcase-function str))
   ;; fooBar => foo-bar
   ((string-inflection-lower-camelcase-p str)
    (string-inflection-kebab-case-function str))
   ;; foo-bar => foo_bar
   (t
    (string-inflection-underscore-function str))))

(defun string-inflection-ruby-style-cycle-function (str)
  "foo_bar => FOO_BAR => FooBar => foo_bar"
  (cond
   ((string-inflection-underscore-p str)
    (string-inflection-upcase-function str))
   ((string-inflection-upcase-p str)
    (string-inflection-camelcase-function str))
   (t
    (string-inflection-underscore-function str))))

(defun string-inflection-java-style-cycle-function (str)
  "fooBar => FOO_BAR => FooBar => fooBar"
  (cond
   ((string-inflection-underscore-p str)
    (string-inflection-upcase-function str))
   ((string-inflection-lower-camelcase-p str)
    (string-inflection-upcase-function str))
   ((string-inflection-upcase-p str)
    (string-inflection-camelcase-function str))
   (t
    (string-inflection-lower-camelcase-function str))))

;; Toggle function. But cycle function.
(defun string-inflection-toggle-function (str)
  "Not so much the case that in all caps when using normal foo_bar <--> FooBar"
  (cond
   ((string-inflection-underscore-p str)
    (string-inflection-camelcase-function str))
   ((string-inflection-camelcase-p str)
    (string-inflection-lower-camelcase-function str))
   (t
    (string-inflection-underscore-function str))))

;; --------------------------------------------------------------------------------

(defun string-inflection-word-p (str)
  "if foo => t"
  (let ((case-fold-search nil))
    (string-match "\\`[a-z0-9]+\\'" str)))

(defun string-inflection-underscore-p (str)
  "if foo_bar => t"
  (let ((case-fold-search nil))
    (string-match "\\`[a-z0-9_]+\\'" str)))

(defun string-inflection-upcase-p (str)
  "if FOO_BAR => t"
  (let ((case-fold-search nil))
    (string-match "\\`[A-Z0-9_]+\\'" str)))

(defun string-inflection-camelcase-p (str)
  "if FooBar => t"
  (let ((case-fold-search nil))
    (and
     (string-match "[a-z]" str)
     (string-match "\\`[A-Z][a-zA-Z0-9]+\\'" str))))

(defun string-inflection-lower-camelcase-p (str)
  "if fooBar => t"
  (let ((case-fold-search nil))
    (and
     (string-match "[A-Z]" str)
     (string-match "\\`[a-z][a-zA-Z0-9]+\\'" str))))

(defun string-inflection-kebab-case-p (str)
  "if foo-bar => t"
  (string-match "-" str))

(provide 'string-inflection)
;;; string-inflection.el ends here
