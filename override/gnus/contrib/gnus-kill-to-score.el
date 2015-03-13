;;; gnus-kill-to-score.el --- translate simple kill files to score files
;; Copyright (C) 1995 Free Software Foundation, Inc.

;; Author: Ethan Bradford <ethanb@phys.washington.edu>
;; Keywords: news

;; This file is not part of GNU Emacs.

;; GNU Emacs is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 2, or (at your option)
;; any later version.

;; GNU Emacs is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with GNU Emacs; see the file COPYING.  If not, write to
;; the Free Software Foundation, 675 Mass Ave, Cambridge, MA 02139, USA.

;;; Commentary:

;;; If you don't like the changes which were made, edit out the new code from
;;; the SCORE file and revert the kill file from the backup (.KILL~).

;;; Caveats:
;;;  -> Sometimes commands in a kill file work together.  For example, killing
;;;     the negative of a pattern used to be done by killing all, then
;;;     unkilling.  If the unkill fails to translate (which is likely), the
;;;     configuration will be invalid, with the kill translated to a
;;;     score entry and the unkill left as a kill.
;;;  -> The score entries are always applied to all entries in a file, unlike
;;;     gnus-kill, which only applies to marked entries if the fourth argument
;;;     is t.
;;;  -> If the kill file did anything funny with marks, it will be translated
;;;     wrong.
;;;  -> Doesn't delete comments, so won't delete file w/ only comments.

;;; Code:

(require 'gnus)
(require 'gnus-score)
(load-library "gnus-kill")

(defvar gnus-convert-loads nil
  "If t, kill-file loads are converted to score-file loads.
If nil, we ask whether to convert.  Otherwise we don't load or ask.")

(defun gnus-convert-kill-name-to-score-name (kill-file)
  (concat
   (if (string-equal (file-name-nondirectory kill-file) "KILL")
       (concat (file-name-directory kill-file) "all")
     (substring kill-file 0 (string-match ".KILL$" kill-file)))
   ".SCORE"))

(defun gnus-convert-one-kill-file (kill-file)
  "Convert (as far as possible) the elements of KILL-FILE into a score file.
See also the variable gnus-convert-loads."
  (interactive "f")
  (let* ((mark-below (or gnus-summary-mark-below gnus-summary-default-score 0))
	 (expunge-below gnus-summary-expunge-below)
	 (score-file-name (gnus-convert-kill-name-to-score-name kill-file))
	 beg form command recognized)
    (message "Converting kill file %s..." kill-file)
    (gnus-score-load score-file-name)
    (find-file kill-file)
    (goto-char (point-min))
    (gnus-kill-file-mode)
    (while (progn
	     (setq beg (point))
	     (setq recognized nil)
	     (setq form (condition-case nil
			    (read (current-buffer))
			  (error nil))))
      (setq command (car form))

      (if (eq command 'load)
	  (let ((loaded-kill-file-name
		 (condition-case nil
		     (expand-file-name
		      (gnus-convert-kill-name-to-score-name
		       (eval (nth 1 form))))
		   (error nil))))
	    (if (stringp loaded-kill-file-name)
		(progn
		  (if (string-match
		       (expand-file-name
			(or (file-name-directory gnus-kill-files-directory)
			   "~/News/"))
		       loaded-kill-file-name)
		      (setq loaded-kill-file-name
			    (substring loaded-kill-file-name (match-end 0))))
		  (if (or (eq gnus-convert-loads t)
			  (and (not gnus-convert-loads)
			       (message
				"Convert kill-file load to score-file load for %s (y, n, a=always, v=never)? " loaded-kill-file-name)
			       (let ((c (upcase (read-char-exclusive))))
				 (if (= c ?A)
				     (setq gnus-convert-loads t)
				   (if (= c ?V)
				       (setq gnus-convert-loads 'never)))
				 (or (= c ?A) (= c ?Y) (= c ?\ )))))
		      (progn
			(gnus-score-set 'files (list loaded-kill-file-name))
			(setq recognized t))))))

	;; The only other thing we understand is some form of gnus-kill
	;; Check all the fields because they influence whether we recognize.
	(let
	    ((header (condition-case nil (eval (nth 1 form)) (error nil)))
	     (match (condition-case nil (eval (nth 2 form)) (error nil)))
	     (cmd (nth 3 form))
	     (all (condition-case nil (eval (nth 4 form)) (error nil)))
	     (date nil)
	     (score nil))		;score also indicates if a cmd was
				      ;recognized.
	  (if (and (listp cmd) (or (eq (car cmd) 'quote)
				   (eq (car cmd) 'function)))
	      (setq cmd (nth 1 cmd)))
	  (if (and (listp cmd) (eq (car cmd) 'lambda))
	      (setq cmd (nth 2 cmd)))
	  (if (and (listp cmd) (eq (length cmd) 1))
	      (setq cmd (car cmd)))
	  (cond
	   ((eq command 'gnus-kill)
	    (cond
	     ((not cmd) ;; Simple kill
	      (setq score (- gnus-score-interactive-default-score)))

	     ((and (eq cmd 'gnus-summary-unkill) all) ;; An unkill
	      (setq score gnus-score-interactive-default-score))

	     ((not (listp cmd))) ; Only cmds w/ args from here on.

	     ((and (eq (car cmd) 'gnus-summary-mark-as-read) ;mod of standard
		   (not (nth 1 cmd)))
	      (if (eqs (nth 2 cmd) " ")
		  (if all 
		      (setq score gnus-score-interactive-default-score))
		(setq score (- gnus-score-interactive-default-score))))

	     ((apply (lambda (c)	; Matching the unkill in the FAQ
		      (and (listp c)
			   (eq (car c) 'gnus-summary-clear-mark-forward)
			   (= (nth 1 c) 1)))
		     (list (if (eq (car cmd) 'if) (nth 2 cmd) cmd)))
	      (setq score gnus-score-interactive-default-score))

	     ((and ;; Old (ding) gnus kill form.
	       (= (length cmd) 2)
	       (eq (car cmd) 'gnus-summary-raise-score))
	      (setq score (nth 1 cmd)))
	     ))
	   ((eq command 'gnus-raise)
	    (setq score (nth 2 form)))
	   ((eq command 'gnus-lower)
	    (setq score (- (nth 2 form))))
	   ((eq command 'expire-kill)
	    (if (= (length form) 3)
		(progn
		  (setq date (nth 2 form))
		  (setq score (- gnus-score-interactive-default-score))))))
	  (if (and score (stringp header) (stringp match))
	      (progn
		(gnus-summary-score-entry
		 header match 'r score date nil t)
		(setq recognized t)))))
      (if recognized
	  (delete-region beg (point))
	(message "Cannot convert this form:") (sit-for 0 500)
	(print form) (sit-for 0 500)))

    ;; Eliminate white space and delete the file if it is empty, else save.
    (goto-char (point-min))
    (delete-region (point)
		   (progn
		     (if (re-search-forward "[^ \t\n]" nil 'end)
			 (backward-char 1))
		     (point)))
    (and (buffer-modified-p) (save-buffer))
    (if (= (point-min) (point-max))
	(progn
	  (message "Deleting %s; it is now empty." kill-file)
	  (delete-file kill-file))
      (message "%s was not completed converted." kill-file))

    (gnus-score-save)
    (kill-buffer (current-buffer))))

(defun gnus-convert-kill-file-directory (kill-directory)
  "Convert kill files in KILL-DIRECTORY into score files.
Uses gnus-convert-one-kill-file.
See also the variable gnus-convert-loads."
  (interactive "DDirectory to convert (empty string = current kill directory): ")
  (if (string= kill-directory "")
      (setq kill-directory (or gnus-kill-files-directory "~/News")))
  (let ((all-kill-files (directory-files kill-directory)))
    (while all-kill-files
      (if (string-match "\\(.\\|^\\)KILL$" (car all-kill-files))
	  (gnus-convert-one-kill-file
	   (expand-file-name (car all-kill-files) kill-directory)))
      (setq all-kill-files (cdr all-kill-files)))))
