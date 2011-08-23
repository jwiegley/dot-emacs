;;; c-includes --- find all header files included by a source file

;; Copyright (C) 1999, 2000 John Wiegley

;; Author: John Wiegley <johnw@gnu.org>
;; Created: 23 Mar 1999
;; Version: 1.4
;; Keywords: c languages
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

;; After setting `c-includes-path' appropriately, you can run the
;; command `M-x c-includes' to find all of the include files that get
;; brought in by a particular source file.
;;
;; It will create a buffer called "*Includes*" that will list all of
;; the included files, nested according to their inclusion depth.
;;
;; If you provide a prefix argument to `c-includes', it will ask you
;; for a regular expression, and will display all lines along the
;; include path containing that regular expression.  Pressing C-c C-c
;; on any of those lines will go that location.
;;
;; Lastly, for the programmer in all of us, if you call `c-includes'
;; non-interactively, and pass t as the second argument, it will
;; return back to you a list of the include file names, to do with as
;; you please.  See the docstring.

;;; History:

;; Changes in 1.4:

;; * `c-includes-mode-hook' now gets called in the *Includes* buffer
;;   after setting everything up.  This was simply an omission in 1.3.

;; Changes in 1.3:

;; * Made the *Includes* buffer use view-mode and outline-minor-mode,
;;   with `outline-regexp' set appropriately.
;;
;; * No longer relies upon font-lock for faces.
;;
;; * c-includes is not a minor mode anymore.  The *Includes* buffer is
;;   created as a regular temp buffer, with some additional keys set,
;;   and outline-minor-mode turned on.
;;
;; * Added the file `c-includes-current-file', which I recommend
;;   binding to C-c C-i in c++-mode and c-mode.  You can also achieve
;;   this by customizing `c-includes-binding' to t.
;;
;; * Change mousing behavior so that it doesn't change the window
;;   looking at the *Includes* buffer.
;;
;; * If you use C-c C-c on a line in the *Includes* which states that
;;   a certain include file is being opened or closed, that file will
;;   be visited.  Before, nothing would happen.
;;
;; * There are several variations now when mousing or using C-c C-c on
;;   a line that names an include file:
;;
;;   C-M-mouse-2
;;   C-u C-c C-c  moves point to any "corresponding" information
;;                on a "-" line, this goes to the "+" line
;;                on a "!" line, it goes to the first "+" line
;;
;;     M-mouse-2
;;   M-0 C-c C-c  open the file directly
;;
;;     S-mouse-2
;;   M-- C-c C-c  moves point in *Includes* to parent include file
;;                if you do this from a search-hit line, it will move
;;                point to the include file in which the match was
;;                found.
;;
;;       mouse-2
;;       C-c C-c  shows you where this file was #include'd
;;
;; * All of this special info is kept in text properties, rather than
;;   cluttering the buffer.
;;
;; * Special identifier characters now only occur at the beginning of
;;   the include file name.

;; Changes in 1.1:

;; * If a header can't be found, and has no extension, but there IS a
;;   header with an extension that has the same basename, then we
;;   assume that was the header that was meant.
;;
;; * The display is now ordered in the same way as what cpp would see,
;;   making your regexp searches more realistic.
;;
;; * Files included with double quotes are searched for first relative
;;   to the current directory.
;;
;; * `c-includes' now always asks for a regular expression, rather
;;   than relying on a prefix argument.
;;
;; * The mark gets pushed in the *Includes* buffer whenever you jump
;;   around, to enable you to get back easily.
;;
;; * When a file is included that has already been included, its name
;;   is now output, along with the line number within the *Includes*
;;   buffer where it was first included.  Pressing C-c C-c on that
;;   line will take you to the location of the first inclusion.

;;; Code:

(defconst c-includes-version "1.4a"
  "This version of c-includes.")

;;; User Variables:

(defcustom c-includes-path
  '("/usr/include" "/usr/include/sys")
  "*List of paths to search for include files."
  :type '(repeat string)
  :group 'c)

;;;###autoload
(defun c-includes-add-binding ()
  "Set binding for C-c C-i in cc-mode."
  (local-set-key (kbd "C-c C-i") 'c-includes-current-file))

(defcustom c-includes-binding nil
  "*If non-nil, bind C-c C-i to `c-includes-current-file' in cc-mode."
  :set (lambda (symbol value)
	 (if value
	     (add-hook 'c-mode-common-hook 'c-includes-add-binding)
	   (remove-hook 'c-mode-common-hook 'c-includes-add-binding))
	 (setq c-includes-binding value))
  :type 'boolean
  :group 'c
  :require 'c-includes)

(defface c-includes-open-face
  '((t (:foreground "red")))
  "*The face used to indicate that an include file was opened.")

(defface c-includes-close-face
  '((t (:foreground "dark red")))
  "*The face used to indicate that an include file was closed.")

(defface c-includes-already-face
  '((t (:foreground "purple")))
  "*The face used to indicate that a file was already opened.")

(defface c-includes-unknown-face
  '((t (:foreground "red" :bold t)))
  "*The face used to indicate that an include file was not found.")

(defcustom c-includes-mode-hook nil
  "*A series of functions to be run upon entering c-includes mode."
  :type 'hook
  :group 'c)

;;; Internal Variables:

(defvar c-includes-buffer "*Includes*"
  "The name of the buffer used by c-includes mode.")

(defvar c-found-paths nil
  "Internal variable used to store discovered paths.")

;;; User Functions:

;;;###autoload
(defun c-includes-current-file (&optional regexp)
  "Find all of the header file included by the current file."
  (interactive "sSearch for regexp in #include files: ")
  (c-includes buffer-file-name regexp))

;;;###autoload
(defun c-includes (filename &optional regexp)
  "Find all of the header files included by FILENAME.
REGEXP, if non-nil, is a regular expression to search for within
FILENAME and the files that it includes.  The output will be
structured in the same order that the compiler will see it, enabling
you to determine order of occurrence."
  (interactive "fFind all includes brought in by: \nsSearch for regexp: ")
  (with-output-to-temp-buffer c-includes-buffer
    (c-includes-search filename nil nil nil t 0 regexp))
  (with-current-buffer c-includes-buffer
    (outline-minor-mode 1)
    (make-local-variable 'outline-regexp)
    (setq outline-regexp "^=> +")
    (local-set-key [mouse-2]
		   (function
		    (lambda (event)
		      (interactive "e")
		      (c-includes-mode-mouse-goto event 'parent-line))))
    (local-set-key [S-mouse-2]
		   (function
		    (lambda (event)
		      (interactive "e")
		      (c-includes-mode-mouse-goto event 'parent-bufline))))
    (local-set-key [C-M-mouse-2]
		   (function
		    (lambda (event)
		      (interactive "e")
		      (c-includes-mode-mouse-goto event 'other-bufline))))
    (local-set-key [M-mouse-2]
		   (function
		    (lambda (event)
		      (interactive "e")
		      (c-includes-mode-mouse-goto event))))
    (local-set-key "\C-c\C-c" 'c-includes-mode-goto-occurrence)
    (local-set-key [return]   'c-includes-mode-goto-occurrence)
    (run-hooks 'c-includes-mode-hook))
  (message "Searching files...done"))

;;; Internal Functions:

(defun c-includes-display-file (filename depth begd face
					 parent-line parent-bufline
					 other-bufline)
  "Insert FILENAME into the current buffer, prettily.
DEPTH is the nesting level, and BEGD is initial character with which
to begin the string.  FACE is the face to use for the line just
output.  PARENT-BUFLINE, PARENT-BUFLINE and OTHER-BUFLINE are used for
navigational purpose, and correspond to: the line within the source
code file where this file was #include'd, the line within the buffer
that this line's parent is located at, and any other corresponding
line information, such as relating multiple inclusions to the first
occurrence."
  (with-current-buffer c-includes-buffer
    (goto-char (point-max))
    (let ((beg (point)))
      (insert "=> " (make-string (* depth 2) ? ))
      (insert begd filename)
      (set-text-properties beg (point)
			   (list 'face face
				 'parent-line parent-line
				 'parent-bufline parent-bufline
				 'other-bufline other-bufline))
      (insert "\n"))
    (c-includes-current-line)))

(defun c-includes-search (filename &optional linenum parent-bufline
				   found-paths insert depth regexp)
  "Search for all #include lines in FILENAME.
FOUND-PATHS should be a list of include files not to traverse into.
If INSERT is non-nil, then the information found by this function will
be inserted before point in the current buffer.  DEPTH is used when
inserting to keep track of the current nesting level.  REGEXP, if
non-nil, specifies a regular expression to search for within the
include files.  NOTE that only `c-includes' should set any but the
first argument."
  (let (bufline (this-linenum linenum))
    (if (not insert)
	(setq found-paths (cons filename
				found-paths))
      (message "Searching file %s..." filename)
      (setq bufline (c-includes-display-file
		     filename depth "+"
		     'c-includes-open-face
		     this-linenum parent-bufline nil))
      (setq found-paths
	    (cons (cons filename bufline)
		  found-paths)))
    (with-temp-buffer
      (insert-file-contents filename)
      (goto-char (point-min))
      (while (not (eobp))
	(if (looking-at
	     "^[ \t]*#[ \t]*include[ \t]*\\([\"<]\\)\\([^\">\n]+\\)[\">]")
	    (let ((file (match-string-no-properties 2))
		  (inc-type (match-string-no-properties 1)))
	      (if (not (file-exists-p file))
		  (let ((dirs c-includes-path))
		    (if (string= inc-type "\"")
			(setq dirs (cons "." dirs)))
		    (while dirs
		      (let ((try (concat (car dirs) "/" file)))
			(if (and (not (file-exists-p try))
				 (not (file-name-extension try))
				 (file-exists-p (concat try ".h")))
			    (setq file (concat try ".h")
				  dirs nil)
			  (if (file-exists-p try)
			      (setq file try
				    dirs nil))))
		      (setq dirs (cdr dirs)))))
	      (if (not (file-exists-p file))
		  (if insert
		      (c-includes-display-file
		       file (and depth (1+ depth)) "?"
		       'c-includes-unknown-face
		       (+ (c-includes-current-line) 1)
		       parent-bufline nil))
		(let ((prev (or (and insert
				     (assoc file found-paths))
				(and (not insert)
				     (member file found-paths)))))
		  (if (not prev)
		      (setq found-paths
			    (c-includes-search
			     file (+ (c-includes-current-line) 1)
			     bufline found-paths insert
			     (and depth (1+ depth)) regexp))
		    (if insert
			(c-includes-display-file
			 file (and depth (1+ depth)) "!"
			 'c-includes-already-face
			 (+ (c-includes-current-line) 1)
			 bufline (cdr prev)))))))
	  (let ((beg (point))
		(eol (save-excursion (end-of-line) (point))))
	    (if (and insert regexp (> (length regexp) 0)
		     (re-search-forward regexp eol t))
		(let ((string (buffer-substring beg eol))
		      (line (1+ (c-includes-current-line beg))))
		  (with-current-buffer c-includes-buffer
		    (goto-char (point-max))
		    (setq beg (point))
		    (insert "   " (number-to-string line))
		    (setq eol (point))
		    (insert ":" string "\n")
		    (put-text-property beg eol 'face 'bold))))))
	(forward-line)))
    (when insert
      (c-includes-display-file filename depth "-"
			       'c-includes-close-face
			       this-linenum parent-bufline bufline))
    found-paths))

(defun c-includes-current-line (&optional pos)
  "Return the current line of point, or POS, in the current buffer."
  (count-lines (point-min) (or pos (point))))

(defun c-includes-mode-mouse-goto (event &optional which)
  "In C Includes mode, go to the occurrence whose line you click on."
  (interactive "e")
  (select-window (posn-window (event-end event)))
  (goto-char (posn-point (event-end event)))
  (c-includes-mode-goto-occurrence which))

(defun c-includes-parent-file ()
  "Based on the location of point, find parent including file."
  (let ((count 0) file)
    (while (and count
		(re-search-backward "^=> +\\([-+]\\)\\(.+\\)$"
				    nil t))
      (if (string= (match-string 1) "+")
	  (if (= count 0)
	      (setq count nil
		    file (match-string-no-properties 2))
	    (setq count (1- count)))
	(setq count (1+ count))))
    file))

(defun c-includes-mode-goto-occurrence (&optional which)
  "Go to the occurrence the current line describes."
  (interactive
   (list (cond ((null current-prefix-arg)
		'parent-line)
	       ((eq current-prefix-arg '-)
		'parent-bufline)
	       ((numberp current-prefix-arg)
		t)
	       (t 'other-bufline))))
  (beginning-of-line)
  (cond ((looking-at "^ *\\([0-9]+\\):")
	 (if (eq which 'parent-bufline)
	     (c-includes-parent-file)
	   (let ((line (string-to-number (match-string 1)))
		 (file (save-excursion (c-includes-parent-file))))
	     (when file
	       (push-mark)
	       (find-file-other-window file)
	       (goto-line line)))))
	((looking-at "^=> +\\([-+?!]\\)\\(.+\\)$")
	 (push-mark)
	 (cond ((eq which 'parent-line)
		(let ((line (get-text-property (match-beginning 2)
					       'parent-line))
		      (file (save-excursion
			      (if (string= (match-string 1) "-")
				  (forward-line))
			      (c-includes-parent-file))))
		  (when file
		    (find-file-other-window file)
		    (and line (goto-line line)))))
	       ((memq which '(parent-bufline other-bufline))
		(let ((line (get-text-property (match-beginning 2)
					       which)))
		  (and line (goto-line line))))
	       (t
		(find-file-other-window (match-string 2)))))))

(provide 'c-includes)

;;; c-includes.el ends here
