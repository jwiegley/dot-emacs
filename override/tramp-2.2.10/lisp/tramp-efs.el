;;; tramp-efs.el --- Make EFS a foreign method in Tramp

;; Copyright (C) 2003-2014 Free Software Foundation, Inc.

;; Author: Kai Großjohann <kai.grossjohann@gmx.net>
;; Keywords: comm, processes
;; Package: tramp

;; This file is free software: you can redistribute it and/or modify
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

;; This file provides glue between Tramp and EFS.  EFS is hooked into
;; Tramp as a foreign method.  Most of this file has been snarfed from
;; tramp-ftp.el, which does the same for Tramp and Ange-FTP.

;;; Code:

(require 'tramp)

;; Pacify byte-compiler.
(defvar efs-path-format-string)
(defvar efs-path-format-without-user)
(defvar efs-path-host-format)
(defvar efs-path-regexp)
(defvar efs-path-root-regexp)
(defvar efs-path-user-at-host-format)
(defvar package-get-download-sites)

;;;###tramp-autoload
(defconst tramp-efs-method "ftp"
  "Name of the method invoking EFS.")

;; The EFS name format is somewhat restricted.  EFS assumes that the
;; first pair of parentheses is the user and the second is the host.
;; It assumes that there is one character after the host name, and
;; then the localname part follows.  See function `efs-ftp-path' for
;; the code.  If the first pair of parentheses doesn't match anything,
;; then it assumes that the user is not given.  Therefore, we need to
;; be quite careful with the \(...\) constructs we use in our regexes.

(defvar tramp-efs-method-given nil
  "Method tag is given in filename.
To be set in `tramp-efs-file-name-handler'.")

(defvar tramp-efs-method-regexp
  (concat tramp-prefix-regexp
	  (regexp-quote tramp-efs-method)
	  tramp-postfix-method-regexp)
  "Regexp indicating method tag.")

(defun tramp-efs-path-regexp ()
  "Tramp uses this value for `efs-path-regexp'."
  (concat tramp-prefix-regexp
	  (when tramp-efs-method-given
	    (concat
	     (regexp-quote tramp-efs-method)
	     tramp-postfix-method-regexp))
	  "\\(" tramp-user-regexp tramp-postfix-user-regexp "\\)?"
	  "\\(" tramp-host-with-port-regexp "\\)"
	  tramp-postfix-host-regexp
	  "\\(" tramp-localname-regexp "\\)"))

(defun tramp-efs-path-format-string ()
  "Tramp uses this value for `efs-path-format-string'."
  (concat tramp-prefix-format
	  (when tramp-efs-method-given
	    (concat tramp-efs-method tramp-postfix-method-format))
	  "%s" tramp-postfix-user-format
	  "%s" tramp-postfix-host-format
	  "%s"))

(defun tramp-efs-path-format-without-user ()
  "Tramp uses this value for `efs-path-format-without-user'."
  (concat tramp-prefix-format
	  (when tramp-efs-method-given
	    (concat tramp-efs-method tramp-postfix-method-format))
	  "%s" tramp-postfix-host-format
	  "%s"))

(defun tramp-efs-path-user-at-host-format ()
  "Tramp uses this value for `efs-path-user-at-host-format'."
  (concat "%s" tramp-postfix-user-format
	  "%s" tramp-postfix-host-format))

(defun tramp-efs-path-host-format ()
  "Tramp uses this value for `efs-path-host-format'."
  (concat "%s" tramp-postfix-host-format))

(defun tramp-efs-path-root-regexp ()
  "Tramp uses this value for `efs-path-root-regexp'."
  (concat tramp-prefix-regexp
	  (when tramp-efs-method-given
	    (concat
	     (regexp-quote tramp-efs-method)
	     tramp-postfix-method-regexp))
	  "\\(" tramp-user-regexp tramp-postfix-user-regexp "\\)?"
	  "\\(" tramp-host-with-port-regexp "\\)"
	  tramp-postfix-host-regexp))

;; Still need to do `efs-path-root-short-circuit-regexp'.

;; Disable EFS from file-name-handler-alist.

;; There is still an entry for efs-sifn-handler-function
;; in file-name-handler-alist that I don't know how to deal with.

(defun tramp-disable-efs ()
  "Turn EFS off.
This is useful for unified remoting.  See
`tramp-file-name-structure' for details.  Requests suitable for
EFS will be forwarded to EFS.  Also see the variables
`tramp-efs-method', `tramp-default-method', and
`tramp-default-method-alist'.

This function is not needed in Emacsen which include Tramp, but is
present for backward compatibility."
  (let ((a1 (rassq 'efs-file-handler-function
		   file-name-handler-alist))
	(a2 (rassq 'efs-root-handler-function
		   file-name-handler-alist))
	(a3 (rassq 'remote-path-file-handler-function
		   file-name-handler-alist)))
    (setq file-name-handler-alist
	  (delete a1 (delete a2 (delete a3 file-name-handler-alist))))))

(tramp-disable-efs)

(eval-after-load "efs" '(tramp-disable-efs))
(eval-after-load "efs-fnh" '(tramp-disable-efs))

;;;###tramp-autoload
(when (featurep 'xemacs)
  ;; Add EFS method to the method list.
  (add-to-list 'tramp-methods (cons tramp-efs-method nil))

  ;; Add some defaults for `tramp-default-method-alist'.
  (add-to-list 'tramp-default-method-alist
	       (list "\\`ftp\\." nil tramp-efs-method))
  (add-to-list 'tramp-default-method-alist
	       (list nil "\\`\\(anonymous\\|ftp\\)\\'" tramp-efs-method)))

(when (featurep 'xemacs)
  ;; Add all XEmacs download sites to `tramp-default-method-alist'.
  ;; The settings above should be sufficient, but it's better to make
  ;; it explicitly.
  (when (listp package-get-download-sites)
    (mapc (lambda (x)
	    (when (listp x)
	      (add-to-list
	       'tramp-default-method-alist
	       (list (concat "\\`" (nth 1 x) "\\'")
		     "\\`anonymous\\'" tramp-efs-method))))
	  package-get-download-sites)))

;; Add completion function for FTP method.
;;;###tramp-autoload
(eval-after-load 'tramp
  '(tramp-set-completion-function
    tramp-efs-method
    '((tramp-parse-netrc "~/.netrc"))))

;;;###tramp-autoload
(defun tramp-efs-file-name-handler (operation &rest args)
  "Invoke the EFS handler for OPERATION.
First arg specifies the OPERATION, second args is a list of arguments to
pass to the OPERATION."
  (save-match-data
    (or (boundp 'efs-path-regexp)
	(require 'efs-cu))

    ;; Check whether the method is given in a filename.
    (setq tramp-efs-method-given nil)
    (mapc (lambda (x)
	    (and (stringp x)
		 (string-match tramp-efs-method-regexp x)
		 (setq tramp-efs-method-given t)))
	  args)

    (let ((efs-path-regexp              (tramp-efs-path-regexp))
	  (efs-path-format-string       (tramp-efs-path-format-string))
	  (efs-path-format-without-user (tramp-efs-path-format-without-user))
	  (efs-path-user-at-host-format (tramp-efs-path-user-at-host-format))
	  (efs-path-host-format         (tramp-efs-path-host-format))
	  (efs-path-root-regexp         (tramp-efs-path-root-regexp)))
      (cond
       ;; If argument is a symlink, `file-directory-p' and
       ;; `file-exists-p' call the traversed file recursively.  So we
       ;; cannot disable the file-name-handler this case.
       ((memq operation '(file-directory-p file-exists-p))
	(apply 'efs-file-handler-function operation args))
	;; Normally, the handlers must be discarded
	(t (let* ((inhibit-file-name-handlers
		   (list 'tramp-file-name-handler
			 'tramp-completion-file-name-handler
			 (and (eq inhibit-file-name-operation operation)
			      inhibit-file-name-handlers)))
		  (inhibit-file-name-operation operation))
	     (apply 'efs-file-handler-function operation args)))))))

;; This function is called even in case the filename doesn't fit Tramp
;; syntax (see defadvice of `efs-dired-before-readin' and
;; `efs-set-buffer-mode').  So a syntax check must be performed first;
;; otherwise `tramp-dissect-file-name' returns with an error.
;; It must be a `defsubst' in order to push the whole code into
;; tramp-loaddefs.el.  Otherwise, there would be recursive autoloading.
;;;###tramp-autoload
(defsubst tramp-efs-file-name-p (filename)
  "Check if it's a filename that should be forwarded to EFS."
  (when (string-match (nth 0 tramp-file-name-structure) filename)
    (string= (tramp-file-name-method (tramp-dissect-file-name filename))
	     tramp-efs-method)))

;;;###tramp-autoload
(when (featurep 'xemacs)
  (add-to-list 'tramp-foreign-file-name-handler-alist
	       (cons 'tramp-efs-file-name-p 'tramp-efs-file-name-handler)))

;; Deal with other EFS hooks.
;; * dired-before-readin-hook contains efs-dired-before-readin
;; * find-file-hooks contains efs-set-buffer-mode

(defadvice efs-dired-before-readin (around tramp-efs activate)
  "Do nothing for non-EFS names."
  (when (tramp-efs-file-name-p default-directory)
    ad-do-it))

(defadvice efs-set-buffer-mode (around tramp-efs activate)
  "Do nothing for non-EFS names."
  (when (tramp-efs-file-name-p buffer-file-name)
    ad-do-it))

(add-hook 'tramp-unload-hook
	  (lambda ()
	    (unload-feature 'tramp-efs 'force)))

(provide 'tramp-efs)
;;; tramp-efs.el ends here

;; Local Variables:
;; mode: Emacs-Lisp
;; coding: utf-8
;; End:
