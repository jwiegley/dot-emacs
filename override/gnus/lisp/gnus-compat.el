;;; gnus-compat.el --- Compatability functions for Gnus

;; Copyright (C) 2012-2014 Free Software Foundation, Inc.

;; Author: Lars Magne Ingebrigtsen <larsi@gnus.org>
;; Keywords: compat

;; This file is part of GNU Emacs.

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

;; This package defines and redefines a bunch of functions for Gnus
;; usage.  The basic (and somewhat unsound) idea is to make all
;; Emacsen look like the current trunk of Emacs.  So it will define
;; functions "missing" in other Emacs instances, and redefine other
;; functions to work like the Emacs trunk versions.

(eval-when-compile (require 'cl))

(ignore-errors
  (require 'help-fns))

;; XEmacs doesn't have this function.
(when (and (not (fboundp 'help-function-arglist))
	   (fboundp 'function-arglist))
  (defun help-function-arglist (def &optional preserve-names)
    "Return a formal argument list for the function DEF.
PRESERVE-NAMES is ignored."
    (cdr (car (read-from-string (downcase (function-arglist def)))))))

;; Modify this function on Emacs 23.1 and earlier to always return the
;; right answer.
(when (and (fboundp 'help-function-arglist)
	   (eq (help-function-arglist 'car) t))
  (defvar gnus-compat-original-help-function-arglist
    (symbol-function 'help-function-arglist))
  (defun help-function-arglist (def &optional preserve-names)
    "Return a formal argument list for the function DEF.
PRESERVE-NAMES is ignored."
    (let ((orig (funcall gnus-compat-original-help-function-arglist def)))
      (if (not (eq orig t))
	  orig
	;; Built-in subrs have the arglist hidden in the doc string.
	(let ((doc (documentation def)))
	  (when (and doc
		     (string-match "\n\n\\((fn\\( .*\\)?)\\)\\'" doc))
	    (cdr (car (read-from-string (downcase (match-string 1 doc)))))))))))

(when (= (length (help-function-arglist 'delete-directory)) 1)
  (defvar gnus-compat-original-delete-directory
    (symbol-function 'delete-directory))
  (defun delete-directory (directory &optional recursive trash)
    "Delete the directory named DIRECTORY.  Does not follow symlinks.
If RECURSIVE is non-nil, all files in DIRECTORY are deleted as well.
TRASH is ignored."
    (interactive "DDirectory: ")
    (if (not recursive)
	(funcall gnus-compat-original-delete-directory directory)
      (dolist (file (directory-files directory t))
	(unless (member (file-name-nondirectory file) '("." ".."))
	  (if (file-directory-p file)
	      (delete-directory file t)
	    (delete-file file))))
      (delete-directory directory))))

;; Emacs 24.0.93
(require 'url)
(when (= (length (help-function-arglist 'url-retrieve)) 5)
  (defvar gnus-compat-original-url-retrieve
    (symbol-function 'url-retrieve))
  (defun url-retrieve (url callback &optional cbargs silent inhibit-cookies)
    "Retrieve URL asynchronously and call CALLBACK with CBARGS when finished."
    (funcall gnus-compat-original-url-retrieve
	     url callback cbargs silent)))

;; XEmacs
(when (and (not (fboundp 'timer-set-function))
	   (fboundp 'set-itimer-function))
  (defun timer-set-function (timer function &optional args)
    "Make TIMER call FUNCTION with optional ARGS when triggering."
    (lexical-let ((function function)
		  (args args))
      (set-itimer-function timer
			   (lambda (process status)
			     (apply function process status args))))))

;; XEmacs 21.4
(unless (fboundp 'bound-and-true-p)
  (defmacro bound-and-true-p (var)
    "Return the value of symbol VAR if it is bound, else nil."
    (and (boundp var)
	 (symbol-value var))))


;; Emacs less than 24.3
(unless (fboundp 'add-face)
  (defun add-face (beg end face)
    "Combine FACE BEG and END."
    (let ((b beg))
      (while (< b end)
	(let ((oldval (get-text-property b 'face)))
	  (put-text-property
	   b (setq b (next-single-property-change b 'face nil end))
	   'face (cond ((null oldval)
			face)
		       ((and (consp oldval)
			     (not (keywordp (car oldval))))
			(cons face oldval))
		       (t
			(list face oldval)))))))))

(unless (fboundp 'move-beginning-of-line)
  (defun move-beginning-of-line (arg)
    (interactive "p")
    (unless (= arg 1)
      (forward-line arg))
    (beginning-of-line)))

(unless (fboundp 'delete-dups)
  (defun delete-dups (list)
    "Destructively remove `equal' duplicates from LIST.
Store the result in LIST and return it.  LIST must be a proper list.
Of several `equal' occurrences of an element in LIST, the first
one is kept."
    (let ((tail list))
      (while tail
	(setcdr tail (delete (car tail) (cdr tail)))
	(setq tail (cdr tail))))
    list))

(unless (fboundp 'declare-function)
  (defmacro declare-function (&rest r)))

(provide 'gnus-compat)

;; gnus-compat.el ends here
