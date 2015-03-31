;;; filesets-vfs.el --- Some kind of virtual filesystem based on filesets

(eval-and-compile (message "filesets-vfs: BROKEN. This doesn't work!!!"))

;; Copyright (C) 2002 Thomas Link

;; Author: Thomas Link AKA samul AT web DOT de
;; Time-stamp: <2003-04-06>
;; Keywords:

(defconst filesets-vfs-version "0.1")
(defconst filesets-vfs-homepage
  "http://members.a1.net/t.link/CompEmacsFilesets.html")

 
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

;VFS <lisp>filesets-vfs-version</lisp> :: <!--  -->
;~href(filesets-vfs.el.gz,filesets-vfs.el.gz) can be used -- at some time
;in the future -- to integrate =filesets= with the standard Emacs file io
;functions. **This doesn't work yet**, but once it is finished it should
;allow access to filesets via all possible file-related functions. At the
;moment, it's just here to occupy some web space.


;;; Change log:

;;; To do:

;;; Code:

(require 'filesets2)

(defcustom filesets-file-name-regexp '("^|\\(.*\\)|" "\\(.*\\)")
  "*RegExp used for `file-name-handler-alist'.
The format is: |FILESET|FILENAME"
  :set (function filesets-set-default)
  :type '(list :tag "List" :value nil
	       (regexp :tag "Fileset Regexp" :value "")
	       (regexp :tag "Filename Regexp" :value ""))
  :group 'filesets)


;;; File name handler
(defun filesets-file-name-handler-regexp (&optional what)
  "Construct the regexp for matching filenames in filesets."
  (case what
    ((:fileset)
     (car filesets-file-name-regexp))
    ((:filename)
     (cadr filesets-file-name-regexp))
    (t
     (mapconcat #'identity
		filesets-file-name-regexp
		""))))

(defun filesets-file-name-handler-get-dir (type entry filename &optional default)
  "Get the dir part of filename."
  (case type
    ((:tree)
     (let* ((dirpatt (filesets-entry-get-tree entry))
	    (dir     (car dirpatt)))
       dir))
    ((:pattern)
     (let* ((dirpatt (filesets-entry-get-pattern entry))
	    (dir     (filesets-entry-get-pattern--dir dirpatt)))
       dir))
    (t
     default)))

(defun filesets-format-vfs-name (fileset filename)
  "Format a FILENAME belonging to FILESET."
  (format "|%s|%s" fileset filename))

(defconst filesets-file-name-handler-alist
  `(
    (expand-file-name
     ,(lambda (filename &optional default-directory)
	(let ((rv filename))
	  (when (string-match (filesets-file-name-handler-regexp) filename)
	    (let* ((fileset (match-string 1 filename))
		   (entry   (filesets-get-fileset-from-name fileset))
		   (type    (filesets-entry-mode entry))
		   (subfile (match-string 2 filename))
		   (dir     (filesets-file-name-handler-get-dir
			     type entry filename)))
	      (when dir
		(filesets-format-vfs-name fileset
					  (expand-file-name subfile dir)))))
	  rv)))

    (file-name-all-completions
     ;;Return a list of all completions of PARTIAL-FILENAME in DIRECTORY.
     ;;These are all file names in DIRECTORY which begin with PARTIAL-FILENAME.
     ,(lambda (partial-filename directory)
	(if (string-match (filesets-file-name-handler-regexp) directory)
	    (let* ((fileset  (match-string 1 directory))
		   (entry    (filesets-get-fileset-from-name fileset))
		   (type     (filesets-entry-mode entry))
		   (dir      (filesets-file-name-handler-get-dir
			      type entry directory))
		   (subfile  (match-string 2 directory))
		   )
	      ;;handle trees +++
	      (mapcar
	       ;;(lambda (this) (filesets-format-vfs-name fileset this))
	       #'identity
	       (tellib-filter-list
		(mapcar #'tellib-file-name-last-bit
			(filesets-get-filelist-1 entry type nil dir subfile))
		(lambda (this)
		  ;;(message "DBG %s %s" dir this)
		  (let ((case-fold-search nil))
		    (string-match (concat "^"
					  (regexp-quote partial-filename))
				  this))))))
	  nil)))

    (bad-directory-file-name
     ;;Return the file name of the directory named DIRECTORY.
     ;;This is the name of the file that holds the data for the directory.
     ;;This operation exists because a directory is also a file, but its name as
     ;;a directory is different from its name as a file.
     ;;In Unix-syntax, this function just removes the final slash.
     ,(lambda (directory)
	(if (string-match (filesets-file-name-handler-regexp) directory)
	    (let* ((fileset (match-string 1 directory))
		   (entry   (filesets-get-fileset-from-name fileset))
		   (type    (filesets-entry-mode entry))
		   ;;(subfile (match-string 2 directory))
		   (dir     (filesets-file-name-handler-get-dir
			     type entry directory)))
	      (filesets-format-vfs-name fileset
					(directory-file-name dir)))
	  directory)))

    (file-name-completion
     ;;Complete file name PARTIAL-FILENAME in directory DIRECTORY.
     ;;Return the longest prefix common to all file names in DIRECTORY
     ;;that start with PARTIAL-FILENAME.
     ;;If there is only one and PARTIAL-FILENAME matches it exactly, return t.
     ;;Return nil if DIRECTORY contains no name starting with PARTIAL-FILENAME.
     
     ;;File names which end with any member of `completion-ignored-extensions'
     ;;are not considered as possible completions for PARTIAL-FILENAME unless
     ;;there is no other possible completion. `completion-ignored-extensions'
     ;;is not applied to the names of directories.
     ,(lambda (partial-filename directory)
	(if (string-match (filesets-file-name-handler-regexp) directory)
	    (let* ((fileset  (match-string 1 directory))
		   (entry    (filesets-get-fileset-from-name fileset))
		   (type     (filesets-entry-mode entry))
		   (dir      (filesets-file-name-handler-get-dir
			      type entry directory))
		   (subfile  (match-string 2 directory))
		   ;;handle trees +++
		   (filelst
		    (apply #'tellib-zip-1
			   nil
			   (mapcar
			    #'string-to-list
			    (tellib-filter-list
			     (mapcar #'tellib-file-name-last-bit
				     (filesets-get-filelist-1
				      entry type nil dir subfile))
			     (lambda (this)
			       ;;(message "DBG %s %s %s" dir this partial-filename)
			       (let ((case-fold-search nil))
				 (string-match
				  (concat "^"
					  (regexp-quote partial-filename))
				  this))))))))
	      ;;(message "DBG file-name-completion: %s" filelst)
	      (let ((rv (catch 'exit
			  (let (rv)
			    (dolist (char-list filelst rv)
			      (let ((x (car char-list)))
				(if (tellib-andmap #'(lambda (this)
						       (equal this x))
						   (cdr char-list))
				    (setq rv (append rv (list x)))
				  (throw 'exit rv))))))))
		(apply #'string rv)))
	  nil)))

    (file-name-nondirectory
     ,(lambda (filename)
	(if (string-match (filesets-file-name-handler-regexp) filename)
	    (let* (
		   ;;(fileset (match-string 1 filename))
		   ;;(entry   (filesets-get-fileset-from-name fileset))
		   ;;(type    (filesets-entry-mode entry))
		   (subfile (match-string 2 filename)))
	      (file-name-nondirectory subfile))
	  nil)))

    (file-name-directory
     ;;Return the directory component in file name FILENAME.
     ;;Return nil if FILENAME does not include a directory.
     ;;Otherwise return a directory spec.
     ;;Given a Unix syntax file name, returns a string ending in slash.
     ,(lambda (filename)
	;;(message "DBG file-name-directory: filename %s")
	(if (string-match (filesets-file-name-handler-regexp) filename)
	    (let* ((fileset (match-string 1 filename))
		   (entry   (filesets-get-fileset-from-name fileset))
		   (type    (filesets-entry-mode entry))
		   (subfile (match-string 2 filename))
		   (dir     (filesets-file-name-handler-get-dir
			     type entry filename)))
	      ;;(message "DBG file-name-directory: %s %s" fileset subfile)
	      (if dir
		  (filesets-format-vfs-name fileset
					    (or (file-name-directory subfile)
						""))
		(filesets-format-vfs-name fileset "")))
	  nil)))
     
    ;;(substitute-in-file-name substitute-in-file-name)

    (bad-substitute-in-file-name
     ,(lambda (filename)
	(if (string-match (filesets-file-name-handler-regexp) filename)
	    (let* ((fileset (match-string 1 filename))
		   (entry   (filesets-get-fileset-from-name fileset))
		   (type    (filesets-entry-mode entry))
		   ;;(subfile (match-string 2 filename))
		   (dir     (filesets-file-name-handler-get-dir 
			     type entry filename)))
	      ;;(message "DBG: %s %s %s %s" type filename entry fileset)
	      (if dir
		  (filesets-format-vfs-name 
		   fileset
		   (replace-in-string filename
				      (filesets-file-name-handler-regexp :fileset)
				      dir))
		filename)))))
    )
  "Alist of file name handlers.
+++ Requires more work.
Handle ingroups and trees.")

;;;Files
;;test: (expand-file-name "|Current|")
;;test: (file-name-directory "|Current|")
;;test: (file-name-completion "s" "|Current|")
;;test: (file-name-completion "t" "|Current|")
;;test: (substitute-in-file-name "|Current|")
;;test: (file-name-all-completions "" "|Current|")

;;;Tree
;;test: (expand-file-name "|Docs|")
;;test: (substitute-in-file-name "|Docs|")
;;test: (file-name-directory "|Docs|")
;;test: (file-name-completion "A" "|Docs|")
;;test: (file-name-completion "n" "|Docs|Apps/")
;;test: (file-name-all-completions "n" "|Docs|Apps/")

;;;Pattern
;;test: (expand-file-name "|TML Emacs Lisp|")
;;test: (file-name-directory "|TML Emacs Lisp|")
;;test: (file-name-completion "s" "|TML Emacs Lisp|")
;;test: (file-name-completion "t" "|TML Emacs Lisp|")
;;test: (substitute-in-file-name "|TML Emacs Lisp|")
;;test: (file-name-all-completions "" "|TML Emacs Lisp|")

;;;InGroup
;;test: (expand-file-name "|WikiComp|")
;;test: (file-name-directory "|WikiComp|")
;;test: (substitute-in-file-name "|WikiComp|")
;;test: (file-name-completion "C" "|WikiComp|")
;;test: (file-name-completion "CompEmacsFiles" "|WikiComp|CompEmacsFilesets/")
;;test: (file-name-all-completions "" "|WikiComp|CompEmacsFilesets/")

;;test: (expand-file-name "|WikiComp|")
;;test: (file-name-directory "|Current|")
;;test: (file-name-completion "s" "|Current|")
;;test: (file-name-completion "p" "|Current|")
;;test: (file-name-completion "P" "|Current|")
;;test: (file-name-completion "2" "|Projekte-Sci|")
;;test: (file-name-completion "2" "|Projekte-Sci|")
;;test: (file-name-completion "P" "|Docs|")
;;test: (file-name-completion "" "|Docs|")
;;test: (file-name-all-completions "f" "|TML Emacs Lisp|")
;;test: (file-name-all-completions "" "|Docs|")


(defun filesets-file-name-handler (io-primitive &rest args)
  "Handle extended file names."
  (let ((fn (tellib-alist-get filesets-file-name-handler-alist
			      io-primitive
			      nil
			      t))
	rv)
    (let ((inhibit-file-name-handlers (list #'filesets-file-name-handler))
	  (inhibit-file-name-operation io-primitive))
      (if fn
	  (progn
	    (setq rv (apply fn args))
	    (when (equal rv 'filesets-not-supported)
	      (tellib-error 'error "Filesets-VFS: Not supported"
			    io-primitive args)))
	(setq rv (apply io-primitive args))))
    ;;(message "DBG: %s %s %s %s" io-primitive (not (not fn)) args rv)
    rv))

;(defvar filesets-orig-file-name-handler-alist file-name-handler-alist)
;(setq file-name-handler-alist filesets-orig-file-name-handler-alist)

(defun filesets-vfs-install ()
  "Install filesets-vfs hooks."
  (add-to-list 'file-name-handler-alist
	       (cons (filesets-file-name-handler-regexp :fileset)
		     #'filesets-file-name-handler)))

(defun filesets-vfs-deinstall ()
  "Install filesets-vfs hooks."
  (setq file-name-handler-alist
	(delete (cons (filesets-file-name-handler-regexp :fileset)
		      #'filesets-file-name-handler)
		file-name-handler-alist)))

(filesets-vfs-install)
;(filesets-vfs-deinstall)

(provide 'filesets-vfs)

;;; filesets-vfs.el ends here

;;; Local Variables:
;;; auto-recompile:1
;;; time-stamp-format:"%y-%02m-%02d"
;;; End:
