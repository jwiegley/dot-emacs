;;; CONCORDANCE.EL --- Show concordance table

;; Copyright (C) 2001 Thomas Link

;; Author: Thomas Link AKA thomas DOT link AT a1 DOT net
;; Time-stamp: <2003-03-02>
;; Keywords: text statistics, concordance

(defvar concordance-version "1.5.0")
(defvar concordance-homepage "http://members.a1.net/t.link/filestats.html")
 
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

;; Put this file into your load path -- type "\C-h v load-path" to
;; find a suitable directory. Put

;; (autoload 'concordance "textstats" "Build concordance table" t)

;; into your startup file, which is probably called "~/.emacs.el".
;; Invoke by typing "M-x concordance".

;;; Change log:

;; 1.5

;; - Adaption for use with tellib.el & textstats.el 1.5

;; 1.4

;; - Splitted filestats.el into textstats.el and concordance.el

;;; To do:

;;; Code:

(eval-when-compile
  (require 'cl))

(require 'tellib)
(tellib-require 'textstats "1.5.0")

(require 'info)
(require 'thingatpt)
(require 'timer)
; (require 'cus-edit)

(defgroup concordance nil
  "Show File Statistics."
  :prefix "concordance-"
  :group 'textstats)

(defcustom concordance-match-list nil
  "*Include words matching these regexps in concordance, no matter if
they are excluded or not. See concordance-filter-list's
documentation for details."
  :group 'concordance
  :type '(repeat (sexp :tag "Include")))

(defcustom concordance-filter-list '("[0-9]+" "\\<.\\>" "\\<..\\>")
  "*Concordance: exclude words, which meet either condition in this
list. 

A valid entry can be a regular expression, a function that takes the
word as argument, or a pair of the form (mode-filter . valid
expression). For an explanation of mode-filter see textstats-list's
documentation.

The following is an example to show only defined words when in
Lisp-mode:

	(add-to-list 'concordance-filter-list
		     '((\"Lisp Interaction\" \"Emacs-Lisp\")
		       (lambda (word)
			 (let ((this-sexp (read-from-whole-string word)))
			   (or (not (symbolp this-sexp))
			       (not (fboundp this-sexp)))))))"
  :group 'concordance
  :type '(repeat (sexp :tag "Exclude")))

(defcustom concordance-convert-word 'capitalize
  "*Convert a word before lookup in concordance."
  :type 'sexp
  :group 'textstats)

(defcustom concordance-highlight-p nil
  "*Highlight word index? This takes a while, if the index is large."
  :type 'boolean
  :group 'textstats)

(defcustom concordance-export-field-delimiter "\t"
  "*Concordance export format: field delimiter.
(see `concordance-export')"
  :type '(radio (const :doc "Tab delimited format." "\t")
		(const :doc "Comma delimited format." ",")
		(const :doc "Blank delimited format." " ")
		(const :doc "CVS format." ";")
		(string :tag "Other"))
  :group 'concordance)

(defcustom concordance-export-record-new-record ""
  "*Concordance export format: new record delimiter.
(see `concordance-export')"
  :type '(radio (const :doc "None" "")
		(string :tag "Other"))
  :group 'concordance)

(defcustom concordance-export-record-delimiter "\n"
  "*Concordance export format: record delimiter.
(see `concordance-export')"
  :type '(radio (const :doc "Linefeed" "\n")
		(string :tag "Other"))
  :group 'concordance)

(defcustom concordance-export-text-qualifier-begin ""
  "*Concordance export format: begin text.
(see `concordance-export')"
  :type '(radio (const :doc "None" "")
		(const :doc "Quote" "\"")
		(const :doc "Single quote" "'")
		(string :tag "Other"))
  :group 'concordance)

(defcustom concordance-export-text-qualifier-end ""
  "*Concordance export format: end text.
(see `concordance-export')"
  :type '(radio (const :doc "None" "")
		(const :doc "Quote" "\"")
		(const :doc "Single quote" "'")
		(string :tag "Other"))
  :group 'concordance)

(defcustom concordance-export-prolog ""
  "*Concordance export format: prolog.
(see `concordance-export')"
  :type 'string
  :group 'concordance)

(defcustom concordance-export-epilog ""
  "*Concordance export format: epilog.
(see `concordance-export')"
  :type 'string
  :group 'concordance)

(defvar concordance-table nil)
(defvar concordance-word-prefix "- ")

(make-local-variable 'concordance-table)


(defun concordance-p nil
  "Whether to compute a concordance for current buffer."
  (if (member "Concordance" textstats-stat-list-names)
      t
    nil))

(defun concordance (&optional filter-list match-list)
  "Build concordance table for current buffer.

filter-list ... don't include words matching these regexps
match-list ... include words matching these regexps"
  (interactive)
  (if (or (not (eq major-mode 'textstats-mode))
	  (unwind-protect (pop-to-buffer textstats-target-buffer)
	    nil))
      (progn
	(add-hook 'textstats-quit-hooks
		  (lambda ()
		    (textstats-eval-in-target-buffer
		     (setq concordance-table nil))))
	(setq textstats-auto-hide-predicates 
	      (cons #'concordance-p textstats-auto-hide-predicates))
	(define-key textstats-mode-map (kbd "c")
	  'concordance)
	(define-key textstats-mode-map (kbd "S")
	  'concordance-export)
	(when filter-list
	  (setq concordance-filter-list filter-list))
	(when match-list
	  (setq concordance-match-list match-list))
	(textstats
	 '((:name "Concordance" 
		  :fun concordance-make
		  :view (lambda (b u r) (concordance-view b u r))
		  :on-select concordance-at-point
		  :pre-hook (lambda (b)
			      (set-buffer b)
			      (setq concordance-table nil))))
	 t))))

(defun concordance-export nil
  "Export a concordance table.

File format:
A. `concordance-export-prolog'
B. Rows:
	1. `concordance-export-record-new-record'
	2. `concordance-export-text-qualifier-begin'
	3. WORD
	4. `concordance-export-text-qualifier-end'
	5. `concordance-export-field-delimiter'
	6. NUMBER OF OCCURANCES
	7. `concordance-export-field-delimiter'
	8. POSITION (as word count from the file's beginning)
	... repeat 7, 8 for every occurance of WORD
	9. `concordance-export-record-delimiter'
C. `concordance-export-epilog'"
  (interactive)
  (if (and (eq major-mode 'textstats-mode) 
	   (textstats-target-buffer-still-alive-p))
      (let* ((init-filename (or (buffer-file-name textstats-target-buffer)
				(concat (getenv "HOME") "Concordance")
				"Concordance"))
	     (filename
	      (if (concordance-p)
		  (read-file-name
		   "Save concordance to file: "
		   nil nil nil
		   (concat (file-name-nondirectory
			    (file-name-sans-extension
			     init-filename))
			   "-Concordance."
			   (if (and (equal
				     ";" 
				     concordance-export-field-delimiter)
				    (equal
				     "\n"
				     concordance-export-record-delimiter))
			       "cvs"
			     "txt")))
		(progn
		  (message "Make concordance first.")
		  nil))))
	(if (and filename
		 (not (equal filename "")))
	    (textstats-eval-in-target-buffer
	     (let ((table concordance-table))
	       (with-temp-file 
		   filename
		 (insert concordance-export-prolog)
		 (mapc #'(lambda (this-entry)
			   (let* ((this-word (nth 0 this-entry))
				  (this-count (nth 1 this-entry))
				  (this-pos-list (nth 2 this-entry)))
			     (message "Export to %s" filename)
			     (insert concordance-export-record-new-record)
			     (insert concordance-export-text-qualifier-begin
				     this-word
				     concordance-export-text-qualifier-end
				     concordance-export-field-delimiter
				     (number-to-string this-count))
			     (dolist (this-pos this-pos-list)
			       (insert concordance-export-field-delimiter
				       (number-to-string this-pos)))
			     (insert concordance-export-record-delimiter)))
		       table)
		 (insert concordance-export-epilog))))))))

(defun concordance-word-at-point nil
  "Get word at point (if `thing-at-point' is not available)."
  (let* ((start (point))
	 (end (progn 
		(backward-word 1)
		(point)))
	 (wdd (buffer-substring start end)))
    (forward-word 1)
    wdd))

(defun concordance-make nil
  "Concordance book keeping for word at point."
  (if (forward-word 1)
      (let ((wd (thing-at-point 'word)))
	(when (or (not (concordance-filter-word wd))
		  (concordance-match-word wd))
	  (let ((prct (/ (* 100 (point)) (point-max))))
	    (when (= (mod prct 10) 0)
	      (message "Building concordance ... %s%%" prct)))
	  ;;(set-text-properties 0 (length wd) nil wd)
	  ;;(remove-text-properties 0 (length wd) nil wd)
	  (concordance-inc wd))
	1)
    nil))

(defun concordance-filter-word (word &optional filter-list)
  "Returns non-nil if word should be filtered
(see `concordance-filter-list')"
  (let ((this-filter-list (or filter-list
			      concordance-filter-list)))
    (concordance-check-word word this-filter-list)))

(defun concordance-match-word (word &optional match-list)
  "Returns non-nil if word should be indexed unconditionally
(see `concordance-match-list')"
  (let* ((this-match-list (or match-list
			      concordance-match-list)))
    (concordance-check-word word this-match-list)))

(defun concordance-check-word (word this-filter-list)
  "Helper function for `concordance-match-word' and
`concordance-filter-word'."
  (catch 'exit
    (mapc #'(lambda (this-filter)
	      (let ((flt
		     (if (or (functionp this-filter) (stringp this-filter))
			 this-filter
		       (if (and (listp this-filter)
				(textstats-check-mode-p (car this-filter) 
							(current-buffer)))
			   (cadr this-filter)
			 nil))))
		(cond ((and (stringp flt) (string-match flt word))
		       (throw 'exit t))
		      ((and (functionp flt) (funcall flt word))
		       (throw 'exit t))
		      (t nil))))
	  this-filter-list)
    nil))

(defun concordance-inc (word)
  "Increase WORD's count in concordance table."
  (let* ((word (eval `(,concordance-convert-word ,word)))
	 (hd (assoc word concordance-table)))
    (if hd
	(setcdr hd (list (1+ (cadr hd))
			 (cons textstats-counter (caddr hd))))
      (setq concordance-table
	    (cons (list word 1 `(,textstats-counter))
		  concordance-table)))))

(defun concordance-viewer (buffer results)
  "Display concordance table in BUFFER."
  (textstats-message "Textstats: viewing concordance")
  (let ((fc (when concordance-highlight-p
	      '(info-xref :highlight))))
    ;;results: (("Bar" 1 (3)) ("Foo" 2 (2 1)))
    (mapc #'(lambda (this-result)
	      (let* ((wd       (nth 0 this-result))
		     (n        (nth 1 this-result))
		     (pos-list (nth 2 this-result)))
		(textstats-insert buffer nil
				  (format "%s'%s' (%d): "
					  concordance-word-prefix wd n))
		(textstats-insert buffer fc (reverse pos-list) " ")
		(textstats-insert buffer nil "\n")))
	  results)))

(defun concordance-view (buffer unit result)
  "Prepare displaying of concordance table and call `concordance-viewer'."
  (textstats-insert buffer nil (textstats-format-result unit "") "\n")
  (set-buffer buffer)
  (concordance-viewer 
   buffer
   (textstats-eval-in-target-buffer
    (textstats-message "Textstats: sorting concordance")
    (sort (copy-sequence concordance-table)
	  (lambda (a b)
	    (string< (car a) (car b))))))
  (set-buffer buffer)
  (setq buffer-read-only nil)
  (goto-char (point-min)))


;; inspired by Alex Schroeder's <alex AT gnu.org> wiki.el
(defun concordance-at-point ()
  "Find occurance of the word under mouse pointer in concordance."
  (interactive)
  (let ((pos (if (thing-at-point-looking-at " [0-9]+")
		 (unwind-protect
		     (string-to-number (match-string 0))
		   nil)
	       nil)))
    (if (and pos (> pos 0))
	(let ((word
	       (if (search-backward
		    (concat "\n" concordance-word-prefix) nil t)
		   (progn
		     (forward-word 1)
		     (thing-at-point 'word))
		 nil)))
	  (if word
	      (textstats-eval-in-target-buffer
	       (pop-to-buffer (current-buffer))
	       (goto-char (point-min))
	       (forward-word pos)
	       (mark-word -1)
	       (if running-xemacs (recenter))
	       (message "Find '%s' (word %d) in %s" 
			word pos (buffer-name))))))))


(provide 'concordance)

;;; CONCORDANCE.EL ends here

;;; Local Variables:
;;; auto-recompile:1
;;; time-stamp-format:"%y-%02m-%02d"
;;; End:
