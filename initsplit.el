;;; initsplit --- code to split customizations into different files

;; Copyright (C) 2000, 2001 John Wiegley

;; Author: John Wiegley <johnw@gnu.org>
;; Created:  8 Feb 2000
;; Version: 1.6
;; Keywords: lisp
;; X-URL: http://www.gci-net.com/users/j/johnw/emacs.html

;; This program is free software; you can redistribute it and/or
;; modify it under the terms of the GNU General Public License as
;; published by the Free Software Foundation; either version 2, or (at
;; your option) any later version.

;; This program is distributed in the hope that it will be useful, but
;; WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
;; General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with GNU Emacs; see the file COPYING.  If not, write to the
;; Free Software Foundation, Inc., 59 Temple Place - Suite 330,
;; Boston, MA 02111-1307, USA.

;;; Commentary:

;; This file allows you to split Emacs customizations (set via M-x
;; customize) into different files, based on the names of the
;; variables.  It uses a regexp to match against each face and
;; variable name, and associates with a file that the variable should
;; be stored in.

;; To use it, just load the file in your .emacs:
;;
;;   (load "initsplit")
;;
;; If you want configuration files byte-compiled, add this after it:
;;
;;   (add-hook 'after-save-hook 'initsplit-byte-compile-files t)

;; Note that that you *must* load each file that contains your various
;; customizations from your .emacs.  Otherwise, the variables won't
;; all be set, and the next time you use the customize interface, it
;; will delete the settings in those other files.

;; Then, customize the variable `initsplit-customizations-alist', to
;; associate various configuration names with their respective
;; initialization files.

;; I find this module most useful for splitting up Gnus and Viper
;; customizations.

;;; History:

;;; Code:

(defconst initsplit-version "1.6"
  "This version of initsplit.")

(defgroup initsplit nil
  "Code to split customizations into different files."
  :group 'initialization)

;;; User Variables:

(defcustom initsplit-load-hook nil
  "*A hook that gets run after \"initsplit.el\" has been loaded."
  :type 'hook
  :group 'initsplit)

(defcustom initsplit-customizations-alist nil
  "*An alist that describes how to split up init file customizations."
  :type '(repeat
	  (list (regexp  :tag "Var regexp")
		(file    :tag "Custom file")
		(boolean :tag "Byte-compile")))
  :group 'initsplit)

(defcustom initsplit-sort-customizations
  (and (boundp 'emacs-major-version)
       (= emacs-major-version 20))
  "*If non-nil, sort the arguments to `custom-set-variables'."
  :type 'boolean
  :group 'initsplit)

;;; User Functions:

(defun initsplit-narrow-to-custom (&optional faces)
  (goto-char (point-min))
  (let (pos)
    (if (re-search-forward
	 (format "^(custom-set-%s"
		 (if faces "faces" "variables")) nil t)
	(setq pos (match-beginning 0))
      (goto-char (point-max))
      (insert "\n")
      (setq pos (point))
      (insert (format "(custom-set-%s)"
		      (if faces "faces" "variables"))) )
    (goto-char pos))
  (let ((beg (point)))
    (forward-sexp)
    (narrow-to-region beg (point)))
  (goto-char (point-min))
  (forward-line))

(defun initsplit-delete-customizations (&optional faces)
  "Delete all of the customization entries in a buffer."
  (save-restriction
    (initsplit-narrow-to-custom faces)
    (forward-char -1)
    (while (not (looking-at ")"))
      (let ((opoint (point)))
	(forward-sexp)
	(delete-region opoint (point))))))

(defun initsplit-sort-customizations (&optional faces)
  "Sort the customization entries in a buffer."
  (save-restriction
    (initsplit-narrow-to-custom faces)
    (sort-subr
     nil
     (function
      (lambda ()
	(if (looking-at ")")
	    (goto-char (point-max))
	  (forward-char))))
     (function
      (lambda ()
	(backward-up-list 1)
	(forward-sexp)))
     (function
      (lambda ()
	(re-search-forward "'(\\(\\S-+\\)")
	(match-string 1))))))

(defvar initsplit-modified-buffers nil)

(defun initsplit-split-customizations (&optional faces)
  (save-restriction
    (initsplit-narrow-to-custom faces)
    (while (looking-at "^\\s-*\\(;;\\|'(\\(\\S-+\\)\\)")
      (let ((var (match-string 2))
	    (cal initsplit-customizations-alist)
	    found)
	(while (and var cal)
	  (if (not (string-match (caar cal) var))
	      (setq cal (cdr cal))
	    (setq found t)
	    (let ((opoint (point)))
	      (forward-sexp)
	      (kill-region opoint (point))
	      (if (looking-at "^\\s-*)")
		  (delete-indentation)
		(delete-char 1)))
	    (with-current-buffer
		(find-file-noselect (nth 1 (car cal)))
	      (unless (memq (current-buffer) initsplit-modified-buffers)
		(setq initsplit-modified-buffers
		      (cons (current-buffer) initsplit-modified-buffers))
		(initsplit-delete-customizations)
		(initsplit-delete-customizations t))
	      (save-restriction
		(initsplit-narrow-to-custom faces)
		(forward-char -1)
		(insert ?\n)
		(yank)))
	    (setq cal nil)))
	(unless found
	  (forward-sexp)
	  (forward-line))))))

(defun initsplit-split-user-init-file ()
  (save-excursion
    (if (string= (file-truename (buffer-file-name (current-buffer)))
		 (file-truename (or custom-file user-init-file)))
	(let (initsplit-modified-buffers)
	  (initsplit-split-customizations)
	  (initsplit-split-customizations t)
	  (while initsplit-modified-buffers
	    (with-current-buffer (car initsplit-modified-buffers)
	      (when initsplit-sort-customizations
		(initsplit-sort-customizations)
		(initsplit-sort-customizations t))
	      (save-buffer))
	    (setq initsplit-modified-buffers
		  (cdr initsplit-modified-buffers)))
	  (when initsplit-sort-customizations
	    (initsplit-sort-customizations)
	    (initsplit-sort-customizations t))))
    nil))

(add-hook 'write-file-hooks 'initsplit-split-user-init-file t)

(defun initsplit-byte-compile-files ()
  (if (string= (file-truename (buffer-file-name (current-buffer)))
	       (file-truename (or custom-file user-init-file)))
      (byte-compile-file (file-truename
			  (buffer-file-name (current-buffer))))
    (let ((cal initsplit-customizations-alist))
      (while cal
	(if (and (nth 2 (car cal))
		 (string= (file-truename (nth 1 (car cal)))
			  (file-truename
			   (buffer-file-name (current-buffer)))))
	    (byte-compile-file (file-truename
				(buffer-file-name (current-buffer)))))
	(setq cal (cdr cal))))))

;;(add-hook 'after-save-hook 'initsplit-byte-compile-files t)

;;; Internal Functions:

(provide 'initsplit)

(run-hooks 'initsplit-load-hook)

;;; initsplit.el ends here
