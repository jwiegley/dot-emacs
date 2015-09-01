;;; attic.el --- maintain backups with a time stamp

;; Copyright (C) 2002 Thomas Link

;; Author: Thomas Link aka samul at web dot de
;; Time-stamp: <2003-03-16>
;; Keywords: backup, files, tools

(defconst attic-version "1.0.1")
(defconst attic-homepage
  "http://members.a1.net/t.link/CompEmacsAttic.html")
 
;; This program is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 2, or (at your option)
;; any later version.

;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with this program; if not, write to the Free Software Foundation,
;; Inc., 59 Temple Place, Suite 330, Boston, MA 02111-1307 USA

;;; Commentary:

;; ;---(:excerpt-beg attic :name desc)---
;; ;---(:excerpt-source "~/Etc/TL-Wiki/CompEmacsAttic")---
;; 
;; ** Description
;; 
;; This is a simple package for maintaining time-stamped backups.
;; 
;; This is how it works: If a file was last saved on the 19th of July 2002
;; and the the current buffer's file is "~/test", the command `attic-store'
;; will save a copy in "~/.attic/last/" and in "~/.attic/020719/". If the
;; variable `attic-compress-cmd' is set, the backuped files will be
;; compressed -- "gzip" is used by default. Later you can use the commands
;; `attic-compare-with-last' and `attic-compare-with-version' to generate
;; an ediff between the current version and one of the backuped ones.
;; 
;; 
;; ** Installation & Usage
;; 
;; Put (require 'attic) (attic-install) into your startup/user init file.
;; Call `attic-store' to make a backup.
;; 
;; 
;; ** Important commands
;; 
;; `attic-store' :: Save a backup.
;; 
;; `attic-store-special' :: Save an annotated backup.
;; 
;; `attic-compare-with-last' :: Compare the current file with its last
;; backuped version.
;; 
;; `attic-compare-with-version' :: Compare the current file with a backuped
;; version.
;; 
;; 
;; The important variables are:
;; 
;; `attic-date-format' :: This variable defines if you want to make daily,
;; weekly, monthly etc. backups.
;; 
;; `attic-compress-cmd' :: Set the command used for compression.
;; 
;; `attic-compress-suffix' :: set the suffix used by `attic-compress-cmd'.
;; 
;; ;---(:excerpt-end attic :name desc)---


;;; Change log:

;; ;---(:excerpt-beg attic :name versionhist)---
;; ;---(:excerpt-source "~/Etc/TL-Wiki/CompEmacsAttic")---
;; 
;; v1.0 :: initial release
;; 
;; ;---(:excerpt-end attic :name versionhist)---


;;; Known Problems

;; ;---(:excerpt-beg attic :name problems)---
;; ;---(:excerpt-source "~/Etc/TL-Wiki/CompEmacsAttic")---
;; 
;; - =attic-compare-with-version= and =attic-compare-with-last= don't work
;; well with certain compressed files.
;; 
;; ;---(:excerpt-end attic :name problems)---


;;Tested with:
;; 21.4 (patch 10) "Military Intelligence" XEmacs Lucid


;;; To do:

;; - Option to save diffs instead of whole files


;;; Code:

(require 'tellib)
(require 'ediff)

(defgroup attic nil
  "Make backups with a time stamp"
  :prefix "attic-"
  :group 'tools)

(defcustom attic-subdir ".attic"
  "*Subdirectory where we should put the backup files
\(relative to the current file's directory)."
  :type 'string
  :group 'attic)

(defcustom attic-date-format "%y%m%d"
  "*Date format used for backups.
See `format-time-string' for an explanation of the symbols.

Caution: The backup is saved in the subdirectory
\"ATTIC-SUBDIR/TIMESTAMP/\". Thus, this variable defines if you want to
make daily, weekly, monthly etc. backups.
"
  :type 'string
  :group 'attic)

(defcustom attic-compress-cmd "gzip -9 --force %S"
  "*Format string defining the command used for compressing backups.
%S will be replaced with the full filename.
Set this to an empty string for disabling compression."
  :type 'string
  :group 'attic)

(defcustom attic-compress-suffix ".gz"
  "*The suffix used by `attic-compress-cmd'."
  :type 'string
  :group 'attic)

(defun attic-get-modification-date (file)
  "Return FILE's modification date."
  (nth 5 (file-attributes file)))

(defun attic-get-time-stamp (file)
  "Return a time-stamp based on FILE's modification date."
  (if (file-readable-p file)
      (let ((modif-time (attic-get-modification-date file)))
	(format-time-string attic-date-format modif-time))
    (tellib-error 'error "Attic: file not readable: " file)))
;;test: (attic-get-time-stamp "~/.bashrc")
;;test: (attic-get-time-stamp "~/.bashrc-dummy")

(defun attic-get-sub-file-name (file version &optional makedir-flag suffix-flag)
  "Return the file name of the backuped VERSION of FILE.

If MAKEDIR-FLAG is non-nil, this function is used if query mode and the
parent directory will be created if necessary.
"
  (let* ((dir  (concat (file-name-directory file)
		       (file-name-as-directory attic-subdir)
		       (file-name-as-directory version)))
	 (file (concat dir
		       (file-name-nondirectory file))))
    (when (and makedir-flag (not (file-readable-p dir)))
      (make-directory dir t))
    (let ((this (if suffix-flag
		    (concat file attic-compress-suffix)
		  file)))
      (if (string-equal version "last")
	  (concat this ".last")
	this))))
;;test: (attic-get-sub-file-name (buffer-file-name) "0000")

(defun attic-get-last-file-name (file &optional makedir-flag suffix-flag)
  "Return the file name of the last backuped version of FILE."
  (let* ((last (with-temp-buffer
		 (insert-file-contents
		  (attic-get-sub-file-name file "last" makedir-flag))
		 (buffer-string)))
	 (last.suff (concat last attic-compress-suffix)))
    (if (and suffix-flag
	     (file-exists-p last.suff))
	last.suff
      last)))
;;test: (attic-get-last-file-name (buffer-file-name))
;;test: (attic-get-last-file-name (buffer-file-name) nil t)

(defun attic-use-compression-p ()
  "Return non-nil, if we may assume that backuped files were compressed."
  (> (length attic-compress-cmd) 0))

;;;###autoload
(defun attic-compare-with-version (&optional version)
  "Compare the current file with its backuped VERSION."
  (interactive)
  (let* ((version (or version
		      (completing-read
		       (format "Compare %s to version: "
			       (file-name-nondirectory (buffer-file-name)))
		       (mapcar (lambda (this)
				 (list (substring this 0 (- (length this) 1))))
			       (tellib-directory-files
				(concat (file-name-directory (buffer-file-name))
					(file-name-as-directory attic-subdir))
				:dirs)))))
	 (file    (buffer-file-name))
	 (last    (if (string-equal version "last")
		      (attic-get-last-file-name file nil t)
		    (attic-get-sub-file-name file version 
					     nil (attic-use-compression-p)))))
    (if (and file last)
	(let ((buff1 (current-buffer))
	      (buff2 (find-file-noselect last t)))
	  (tellib-message 1 'attic "Comparing %s to %s" file last)
	  (ediff-buffers buff1 buff2))
      (tellib-error 'error "Attic: save buffer first"))))

;;;###autoload
(defun attic-compare-with-last ()
  "Compare the current file with its last backuped version."
  (interactive)
  (attic-compare-with-version "last"))

;;;###autoload
(defun attic-last-backuped ()
  "Say when the current file was backuped for the last time."
  (interactive)
  (let ((last (attic-get-last-file-name (buffer-file-name) nil t)))
    (if (file-readable-p last)
	(tellib-message 0 'attic
			(format-time-string "%c"
					    (attic-get-modification-date last)))
      (tellib-error 'error "Attic: can't read" last))))

;;;###autoload
(defun attic-store (&optional note)
  "Save a (compressed) copy of the current file in the attic.
If NOTE is provided, the string will be appended to the timestamp."
  (interactive)
  (let ((file (buffer-file-name))
	(ok   (if (buffer-modified-p)
		  (when (y-or-n-p "Save buffer first? ")
		    (save-buffer)
		    t)
		t)))
    (if (and file ok)
	(let* ((timestamp (concat (attic-get-time-stamp file)
				  (if note
				      (concat "-" note)
				    "")))
	       (lastfile  (attic-get-sub-file-name file "last" t))
	       (destfile  (attic-get-sub-file-name file timestamp t)))
	  (copy-file file destfile t t)
	  (when (file-exists-p lastfile)
	    (delete-file lastfile))
	  (with-temp-buffer
	    (insert destfile)
	    (write-file lastfile))
	  (when (attic-use-compression-p)
	    (shell-command (format attic-compress-cmd destfile)))
	  (tellib-message 1 'attic "Stored %S in %S"
			  (file-name-nondirectory file) destfile))
      (tellib-error 'error "Attic: save buffer first"))))

;;;###autoload
(defun attic-store-special ()
  "Save a (compressed) copy of the current file in the attic.
Ask for a note."
  (interactive)
  (let ((note (read-from-minibuffer "Note: ")))
    (if (not (equal note ""))
	(attic-store (tellib-make-proper-filename note))
      (tellib-message 1 'attic "Aborted!"))))

(defun attic-install (&optional top-install-flag)
  "Install attic related hooks."
  (tellib-installer 'tellib 'attic top-install-flag))

(defun attic-uninstall (&optional top-install-flag)
  "Uninstall attic related hooks."
  (tellib-uninstaller 'tellib 'attic top-install-flag))


(provide 'attic)

;;; attic.el ends here

;;; Local Variables:
;;; auto-recompile:1
;;; time-stamp-format:"%y-%02m-%02d"
;;; excerpt-sources: "~/Etc/TL-Wiki/CompEmacsAttic"
;;; End:
