;;; filesets-emacs.el --- filesets supplement for (X)Emacs

;; Copyright (C) 2002 Free Software Foundation, Inc.

;; Author: Thomas Link aka samul at web dot de
;; Time-stamp: <2003-04-06>
;; Keywords: filesets

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

;; This is a supplement to filesets.el for people who don't have
;; tellib.el installed.

;;; Change log:

;;; To do:

;;; Code:

(eval-and-compile
  (when (and (not (featurep 'xemacs))
	     (<= emacs-major-version 21)
	     (<= emacs-minor-version 3))
    (require 'filesets-suppl))

  (if (featurep 'xemacs)
      (defalias 'filesets-error 'error)
    ;; a version by RMS
    (defmacro filesets-error (class &rest args)
      "`error' wrapper."
      `(error (mapconcat 'identity ,args " "))))

  (if (featurep 'xemacs)
      (defalias 'filesets-split-string-by-char 'split-string-by-char)
    (defmacro filesets-split-string-by-char (string sepchar)
      "Split STRING into a list of substrings originally separated by SEPCHAR."
      `(split-string ,string (regexp-quote (char-to-string ,sepchar))))))

(defun filesets-message (level &rest args)
  "Show a message only if LEVEL is higher than `filesets-verbosity'.
This function can be called in two ways:

\(filesets-message LEVEL &rest ARGS): LEVEL will be tested against
`filesets-verbosity'. ARGS will be passed to `message'.

\(filesets-message LEVEL CLASS FORMAT-STRING &rest ARGS): LEVEL will be
tested against CLASS-verbosity \(or `filesets-verbosity' if
CLASS-verbosity isn't defined). FORMAT-STRING will be prepended with
\"CLASS: \".

A level of 0 means: log always.
"
  (let* ((class     (when (symbolp (car args))
		      (car args)))
	 (class$    (symbol-name (or class 'filesets)))
	 (args      (if class
			(append (list (concat (upcase-initials class$)
					      ": " (cadr args)))
				(cddr args))
		      args))
	 (verbosity filesets-verbosity))
    (when (<= level (abs verbosity))
      (apply 'message args)))
  nil)

(defmacro filesets-ormap (filesets-pred filesets-list)
  "Return SUBLIST of FILESETS-LIST, for which \(FILESETS-PRED (car SUBLIST)) is true."
  (let ((list (gensym "filesets-list"))
	(rv   (gensym "filesets-rv")))
    `(let ((,list ,filesets-list)
	   (,rv   nil))
       (while (and (not (null ,list))
		   (null ,rv))
	 (if (funcall ,filesets-pred (car ,list))
	     (setq ,rv ,list)
	   (setq ,list (cdr ,list))))
       ,rv)))

(defmacro filesets-member (filesets-item filesets-list &rest filesets-keys)
  "A clone of `member*'. At the moment only the :test key is supported."
  (let ((filesets-test (plist-get filesets-keys ':test (function equal)))
	(filesets-this (gensym "filesets-this")))
    `(filesets-ormap (lambda (,filesets-this)
		       (funcall ,filesets-test ,filesets-item ,filesets-this)) 
		     ,filesets-list)))

(defmacro filesets-some (filesets-pred filesets-list)
  "Return the value of FILESETS-PRED, if non-nil for an item in FILESETS-LIST."
  (let ((filesets-this (gensym "filesets-this"))
	(filesets-rv   (gensym "filesets-rv")))
    `(catch 'exit
       (dolist (,filesets-this ,filesets-list nil)
	 (let ((,filesets-rv (funcall ,filesets-pred ,filesets-this)))
	   (when ,filesets-rv
	     (throw 'exit ,filesets-rv)))))))

(defmacro filesets-filter-list (filesets-list filesets-cond-fn)
  "Remove all elements not conforming to FILESETS-COND-FN from list FILESETS-LIST.
COND-FN takes one argument: the current element."
  (let ((rv (gensym "filesets-rv")))
    `(let ((,rv nil))
       (dolist (elt ,filesets-list ,rv)
	 (when (funcall ,filesets-cond-fn elt)
	   (setq ,rv (append ,rv (list elt))))))))

(defun filesets-sublist (filesets-list filesets-beg &optional filesets-end)
  "Get the sublist of FILESETS-LIST from FILESETS-BEG to FILESETS-END - 1."
  (let ((rv  nil)
	(i   filesets-beg)
	(top (or filesets-end
		 (length filesets-list))))
    (while (< i top)
      (setq rv (append rv (list (nth i filesets-list))))
      (setq i (+ i 1)))
    rv))

(defun filesets-alist-get (alist key &optional default car-flag)
  "Get KEY's value in the association list ALIST.
Return DEFAULT if not found.  Return \(car value) if CAR-FLAG is non-nil."
  (let* ((elt (assoc key alist)))
    (cond
     (elt
      (if car-flag
	  (cadr elt)
	(cdr elt)))
     (default default)
     (t nil))))

(defun filesets-directory-files (dir &optional
				   what file-pattern dir-pattern full-name-flag)
  "List files or dirs in DIR.
WHAT ... :dirs or :files.
"
  (cond
   ((file-exists-p dir)
    (let ((files           nil)
	  (dirs            nil)
	  (coll-files-flag (not (equal what ':dirs)))
	  (coll-dirs-flag  (not (equal what ':files)))
	  (get-name (lambda (filename)
		      (if full-name-flag
			  (concat (file-name-as-directory dir) filename)
			filename)))
	  (sort-fn (lambda (a b)
		     (string< (upcase a) (upcase b)))))
      (dolist (this (file-name-all-completions "" dir))
	(cond 
	 ((string-match "^\\.+/$" this)
	  nil)
	 ((and coll-dirs-flag (string-match "[:/\\]$" this))
	  (when (or (not dir-pattern)
		    (string-match dir-pattern this))
	    (setq dirs (append dirs (list (funcall get-name this))))))
	 (coll-files-flag
	  (when (or (not file-pattern)
		    (string-match file-pattern this))
	    (setq files (append files (list (funcall get-name this))))))))
      (append (when dirs  (sort (copy-sequence dirs)  sort-fn))
	      (when files (sort (copy-sequence files) sort-fn)))))
   (t
    (filesets-error 'error "Filesets: " dir " does not exist"))))

(defun filesets-file-name-break-up (filename &optional drop-null-elements)
  "Return a list of FILENAME parts.
\"\" at position 0 means: absolute path.
\"\" at the last position means: it's a directory.
If DROP-NULL-ELEMENTS is non-nil, empty strings will be dropped."
  (let ((rv (filesets-split-string-by-char filename directory-sep-char)))
    (if drop-null-elements
	(loop for x in rv
	  when (not (string= x ""))
	  collect x)
      rv)))

(defun filesets-file-name-last-bit (filename)
  "Returns the last bit of FILENAME -- either directory or file."
  (if (file-directory-p filename)
      (file-name-as-directory
       (file-name-nondirectory
	(directory-file-name filename)))
    (file-name-nondirectory filename)))

(require 'filesets2)

(provide 'filesets-emacs)

;;; filesets-emacs.el ends here

;;; Local Variables:
;;; time-stamp-format:"%y-%02m-%02d"
;;; End:
