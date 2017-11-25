;;; backup-each-save.el --- backup each savepoint of a file

;; Copyright (C) 2004  Free Software Foundation, Inc.

;; Author: Benjamin Rutt <brutt@bloomington.in.us>
;; Version: 1.4

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

;; Ever wish to go back to an older saved version of a file?  Then
;; this package is for you.  This package copies every file you save
;; in Emacs to a backup directory tree (which mirrors the tree
;; structure of the filesystem), with a timestamp suffix to make
;; multiple saves of the same file unique.  Never lose old saved
;; versions again.

;; To activate globally, place this file in your `load-path', and add
;; the following lines to your ~/.emacs file:
;;
;; (require 'backup-each-save)
;; (add-hook 'after-save-hook 'backup-each-save)

;; To activate only for individual files, add the require line as
;; above to your ~/.emacs, and place a local variables entry at the
;; end of your file containing the statement:
;;
;; eval: (add-hook (make-local-variable 'after-save-hook) 'backup-each-save)
;;
;; NOTE:  I would give a full example of how to do this here, but it
;; would then try to activate it for this file since it is a short
;; file and the docs would then be within the "end of the file" local
;; variables region.  :)

;; To filter out which files it backs up, use a custom function for
;; `backup-each-save-filter-function'.  For example, to filter out
;; the saving of gnus .newsrc.eld files, do:
;;
;; (defun backup-each-save-no-newsrc-eld (filename)
;;   (cond
;;    ((string= (file-name-nondirectory filename) ".newsrc.eld") nil)
;;    (t t)))
;; (setq backup-each-save-filter-function 'backup-each-save-no-newsrc-eld)

;;; Notes:
;; Tested on GNU Emacs 21.3.X and XEmacs (21.4.15 no mule).
;; Features/bug reports/enhancements welcome. -- Benjamin Rutt

;;; ChangeLog
;; v1.0 -> v1.1:  added backup-each-save-filter-function
;; v1.1 -> v1.2:  i)  added backup-each-save-size-limit
;;                ii) fixed "Local Variables" docs, which was inadvertently
;;                    being activated
;; v1.2 -> v1.3:  fix for some emacsen not having `file-remote-p'
;; v1.3 -> v1.4: added footer and autoload

;;; Code:

(defvar backup-each-save-mirror-location "~/.backups")

(defvar backup-each-save-remote-files nil
  "Whether to backup remote files at each save.

Defaults to nil.")

(defvar backup-each-save-time-format "%Y_%m_%d_%H_%M_%S"
  "Format given to `format-time-string' which is appended to the filename.")

(defvar backup-each-save-filter-function 'identity
  "Function which should return non-nil if the file should be backed up.")

(defvar backup-each-save-size-limit 500000
  "Maximum size of a file (in bytes) that should be copied at each savepoint.

If a file is greater than this size, don't make a backup of it.
Setting this variable to nil disables backup suppressions based
on size.")

(unless (fboundp 'file-remote-p) ;; emacs 21.4 on debian at least,
				 ;; doesn't provide file-remote-p
  (defun file-remote-p (file) ;; stolen from files.el
    "Test whether FILE specifies a location on a remote system.
Return an identification of the system if the location is indeed
remote.  The identification of the system may comprise a method
to access the system and its hostname, amongst other things.

For example, the filename \"/user@host:/foo\" specifies a location
on the system \"/user@host:\"."
    (let ((handler (find-file-name-handler file 'file-remote-p)))
      (if handler
	  (funcall handler 'file-remote-p file)
	nil))))

;;;###autoload
(defun backup-each-save ()
  (let ((bfn (buffer-file-name)))
    (when (and (or backup-each-save-remote-files
		   (not (file-remote-p bfn)))
	       (funcall backup-each-save-filter-function bfn)
	       (or (not backup-each-save-size-limit)
		   (<= (buffer-size) backup-each-save-size-limit)))
      (copy-file bfn (backup-each-save-compute-location bfn) t t t))))

(defun backup-each-save-compute-location (filename)
  (let* ((containing-dir (file-name-directory filename))
	 (basename (file-name-nondirectory filename))
	 (backup-container
	  (format "%s/%s"
		  backup-each-save-mirror-location
		  containing-dir)))
    (when (not (file-exists-p backup-container))
      (make-directory backup-container t))
    (format "%s/%s-%s" backup-container basename
	    (format-time-string backup-each-save-time-format))))

(provide 'backup-each-save)
;;; backup-each-save.el ends here
