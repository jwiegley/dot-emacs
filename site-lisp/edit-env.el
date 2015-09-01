;;; edit-env.el --- display and edit environment variables

;; Copyright (C) 2001 Benjamin Rutt
;;
;; Maintainer: Benjamin Rutt <brutt@bloomington.in.us>
;; Version: 1.0

;; This file is not part of GNU Emacs.

;; This file is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published
;; by the Free Software Foundation; either version 2, or (at your
;; option) any later version.

;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with GNU Emacs; see the file COPYING.  If not, send e-mail to
;; this program's maintainer or write to the Free Software Foundation,
;; Inc., 59 Temple Place, Suite 330; Boston, MA 02111-1307, USA.

;;; Commentary:

;; This file uses the widget library to display, edit, delete and add
;; environment variables.  Inspired by "G c" in a gnus *Group* buffer.
;; Bug reports or patches are welcome, please use the above email
;; address.

;;; Usage:

;; put this file in your load-path and add the line
;;
;; (require 'edit-env)
;;
;; to your ~/.emacs file.
;;
;; Then, type
;;
;; M-x edit-env
;;
;; to enter the environment editor.  To change variables, simply edit
;; their values in place.  To delete variables, delete their values.
;; To add variables, add a new rows to the list at the bottom by
;; pressing [INS]; then, add a new name/value pair of the form
;; VAR=VALUE (e.g. FOO=BAR).  After changing and/or deleting and/or
;; adding environment variables, press the [done] button at the top.
;; Note that environment variable changes will only be visible to your
;; current emacs session or child processes thereof.

;;; Code:

;; XEmacs compatibility stuff
(if (string-match "XEmacs" (emacs-version))
    (require 'overlay))

(require 'widget)

(require 'wid-edit)
(eval-when-compile (require 'cl))

(defvar edit-env-ls nil)
(defvar edit-env-changed-ls nil)
(defvar edit-env-added-ls nil)

(defun edit-env-update ()
  (let ((var nil)
	(value nil)
	(vars-changed nil))
    (when edit-env-changed-ls
      (mapcar
       (lambda (x)
	 (setq var (car x))
	 (setq value (widget-value (cadr x)))
	 (if (equal value "")
	     (setenv var nil) ;; i.e. unset var
	   (setenv var value))
	 (add-to-list 'vars-changed var))
       edit-env-changed-ls)
      (setq edit-env-changed-ls nil))

    (when edit-env-added-ls
      (mapcar
       (lambda (x)
	 (if (and x (not (string-match "^[ \t\n]*$" x)))
	     (progn
	       (let ((splits (split-string x "=")))
		 (if (not (= (length splits) 2))
		     (message "invalid format %s" x)
		   (setq var (car splits))
		   (setq value (cadr splits))
		   (if value (add-to-list 'vars-changed var))
		   (setenv var value))))))
       (widget-value edit-env-added-ls))
      (setq edit-env-added-ls nil))
    (when vars-changed
      ;; Need to regenerate the buffer before burial.  An alternative
      ;; to re-generation followed by burial would be simply to
      ;; kill-buffer.
      (edit-env)
      (message
       (format "Updated environment variable%s %s"
	       (if (> (length vars-changed) 1) "s" "")
	       (mapconcat 'identity vars-changed ", "))))
    (bury-buffer)))

(defun edit-env-mark-changed (widget)
  (add-to-list 'edit-env-changed-ls
	       (list (widget-get widget 'environment-variable-name)
		     widget)))

(defun edit-env ()
  "Display, edit, delete and add environment variables."
  (interactive)
  (setq edit-env-ls nil
	edit-env-changed-ls nil
	edit-env-added-ls nil)
  (switch-to-buffer "*Environment Variable Editor*")
  (kill-all-local-variables)
  (let ((inhibit-read-only t))
    (erase-buffer))
  (let ((all (overlay-lists)))
    ;; Delete all the overlays.
    (mapcar 'delete-overlay (car all))
    (mapcar 'delete-overlay (cdr all)))
  (widget-insert "Edit environment variables below, and press ")
  (let ((pair nil)
	(var nil)
	(val nil)
	(longest-var 0)
	(current-widget nil))
    (setq edit-env-ls (copy-list process-environment))
    (setq edit-env-ls (sort edit-env-ls (lambda (a b) (string-lessp a b))))

    (widget-create 'push-button
		   :notify (lambda (widget &rest ignore)
			     (edit-env-update))
		   :help-echo "press to update environment variables"
		   "done")
    (widget-insert ".\n")

    (mapcar
     (lambda (x)
       (let* ((pair (split-string x "="))
	      (var (car pair))
	      (val (cadr pair)))
	 (setq longest-var (max longest-var (length var)))))
     edit-env-ls)
    (mapcar
     (lambda (x)
       (let* ((pair (split-string x "="))
	      (var (car pair))
	      (val (or (cadr pair) "")))
	 (widget-insert "\n")
	 (widget-insert (format (format "%%%ds" (1+ longest-var)) var))
	 (widget-insert " ")
	 (setq current-widget
	       (widget-create 'editable-field
			      :size (1- (length val))
			      :notify (lambda (widget &rest ignore)
					(edit-env-mark-changed widget))
			      :format "%v" val))
	 (widget-put current-widget 'environment-variable-name var)))
       edit-env-ls)
    (widget-insert "\n\nTo add environment variables, ")
    (widget-insert "add rows of the form VAR=VALUE\n")
    (widget-insert "to the following list:\n")
    (setq edit-env-added-ls
	  (widget-create
	   'editable-list
	   :entry-format "%i %d %v"
	   :value nil
	   '(editable-field :value "")))
    (use-local-map widget-keymap)
    (widget-setup)
    (setq truncate-lines t)
    ;; in future GNU emacs >= 21, auto-show-mode may be removed.
    (when (fboundp 'auto-show-mode)
      (auto-show-mode 1))
    (goto-char (point-min))))

(provide 'edit-env)

;; edit-env.el ends here
