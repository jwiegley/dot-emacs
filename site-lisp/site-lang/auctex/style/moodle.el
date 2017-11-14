;;; moodle.el --- AUCTeX style for `moodle.sty' (v0.5)

;; Copyright (C) 2017 Free Software Foundation, Inc.

;; Author: Arash Esbati <arash@gnu.org>
;; Maintainer: auctex-devel@gnu.org
;; Created: 2017-06-10
;; Keywords: tex

;; This file is part of AUCTeX.

;; AUCTeX is free software; you can redistribute it and/or modify it
;; under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 3, or (at your option)
;; any later version.

;; AUCTeX is distributed in the hope that it will be useful, but
;; WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
;; General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with AUCTeX; see the file COPYING.  If not, write to the Free
;; Software Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA
;; 02110-1301, USA.

;;; Commentary:

;; This file adds support for `moodle.sty' (v0.5) from 2016/01/11.

;; In multi environments, the correct answer is marked with `\item*'.
;; This style adds asterisk to the list of key=values queried after
;; \item in this environment in order to make the input procedure
;; easier.

;;; Code:

(defvar LaTeX-moodle-key-val-options
  '(("points")
    ("default grade")
    ("penalty")
    ("fraction")
    ("feedback"))
  "Key=value options for moodle macros and environments.")

(defun LaTeX-moodle-question-env-with-args (env)
  "Insert ENV provided by moodle.sty incl. arguments and first \\item."
  (LaTeX-insert-environment
   env
   (let ((opts (TeX-read-key-val
		t
		(cond (;; 3.3.1 Multiple Choice
		       (string= env "multi")
		       (append '(("shuffle"   ("true" "false"))
				 ("numbering" ("alph" "Alph" "arabic"
					       "roman" "Roman" "none"))
				 ("single"    ("true" "false"))
				 ("multiple"  ("true" "false")))
			       (when (string= "cloze" (LaTeX-current-environment))
				 '(("vertical" ("true" "false"))
				   ("horizonal" ("true" "false"))))
			       LaTeX-moodle-key-val-options))
		      ;; 3.3.3 Short Answer
		      ((string= env "shortanswer")
		       (append '(("case sensitive" ("true" "false"))
				 ("usecase"        ("true" "false")))
			       (when (string= "cloze" (LaTeX-current-environment))
				 '(("vertical" ("true" "false"))
				   ("horizonal" ("true" "false"))))
			       LaTeX-moodle-key-val-options))
		      ;; 3.3.4 Essay Questions
		      ((string= env "essay")
		       (append '(("response required" ("true" "false"))
				 ("response format"   ("html" "file"
						       "html+file"
						       "text" "monospaced"))
				 ("response field lines")
				 ("attachments allowed"  ("0" "1" "2" "3"
							  "unlimited"))
				 ("attachments required" ("0" "1" "2" "3"))
				 ("response template"))
			       (when (string= "cloze" (LaTeX-current-environment))
				 '(("vertical" ("true" "false"))
				   ("horizonal" ("true" "false"))))
			       LaTeX-moodle-key-val-options))
		      ;; 3.4 Matching Questions
		      ((string= env "matching")
		       (append '(("shuffle"       ("true" "false"))
				 ("drag and drop" ("true" "false"))
				 ("dd"            ("true" "false")))
			       LaTeX-moodle-key-val-options))
		      (t (append
			  (when (string= "cloze" (LaTeX-current-environment))
			    '(("vertical" ("true" "false"))
			      ("horizonal" ("true" "false"))))
			  LaTeX-moodle-key-val-options)))))
	 (qname (unless (string= "cloze" (LaTeX-current-environment))
		  (TeX-read-string (TeX-argument-prompt nil nil "Question name")))))
     (concat
      (when (and opts (not (string= opts "")))
	(format "[%s]" opts))
      (when (and qname (not (string= qname "")))
	(format "{%s}" qname)))))
  (if (TeX-active-mark)
      (progn
	(LaTeX-find-matching-begin)
	(end-of-line 1))
    (end-of-line 0))
  (delete-char 1)
  (when (looking-at (concat "^[ \t]+$\\|"
			    "^[ \t]*" TeX-comment-start-regexp "+[ \t]*$"))
    (delete-region (point) (line-end-position)))
  (delete-horizontal-space)
  ;; Deactivate the mark here in order to prevent `TeX-parse-macro'
  ;; from swapping point and mark and the \item ending up right after
  ;; \begin{...}.
  (TeX-deactivate-mark)
  ;; Query and insert the question text.
  (let ((qtext (TeX-read-string (TeX-argument-prompt nil nil "Question Text"))))
    (when (and qtext (not (string= qtext "")))
      (newline)
      (indent-according-to-mode)
      (insert qtext)
      (LaTeX-fill-paragraph)))
  (LaTeX-insert-item)
  ;; The inserted \item may have outdented the first line to the
  ;; right.  Fill it, if appropriate.
  (when (and (not (looking-at "$"))
	     (not (assoc env LaTeX-indent-environment-list))
	     (> (- (line-end-position) (line-beginning-position))
		(current-fill-column)))
    (LaTeX-fill-paragraph nil)))

(defun LaTeX-moodle-item-argument ()
  "Insert an \\item with optional argument in environments of moodle package."
  ;; Do not query for an optional argument here, this happens below:
  (let ((TeX-insert-macro-default-style 'mandatory-args-only))
    (TeX-insert-macro "item"))
  ;; Add * to `LaTeX-moodle-key-val-options' in multi environment and
  ;; query for the key=values:
  (let ((opts
	 (TeX-read-key-val t (if (string= "multi" (LaTeX-current-environment))
				 (append '(("*")) LaTeX-moodle-key-val-options)
			       LaTeX-moodle-key-val-options))))
    ;; Insert key=values; if * is chosen, drop []:
    (when (and opts (not (string= opts "")))
      (delete-horizontal-space)
      (if (string= opts "*")
	  (insert opts)
	(insert LaTeX-optop opts LaTeX-optcl))))
  (just-one-space)
  ;; Bonus point: Insert the macro \answer in matching environment:
  (when (string= "matching" (LaTeX-current-environment))
    (save-excursion
      (insert TeX-esc "answer")
      (just-one-space))))

(TeX-add-style-hook
 "moodle"
 (lambda ()

   (LaTeX-add-environments
    ;; 3.2 Quiz and Question Environments
    '("quiz"
      (lambda (environment)
	(LaTeX-insert-environment
	 environment
	 (let ((opts (TeX-read-key-val t LaTeX-moodle-key-val-options))
	       (bank (TeX-read-string (TeX-argument-prompt nil nil "Question bank name"))))
	   (concat
	    (when (and opts (not (string= opts "")))
	      (format "[%s]" opts))
	    (format "{%s}" bank))))))
    ;; 3.5 Cloze Questions
    '("cloze" "Question bank name"))

   ;; Make other environments available to AUCTeX:
   (dolist (env '("multi" "numerical" "shortanswer" "essay" "matching"))
     (LaTeX-add-environments `(,env LaTeX-moodle-question-env-with-args))
     (add-to-list 'LaTeX-item-list `(,env . LaTeX-moodle-item-argument) t))

   (TeX-add-symbols
    '("moodleset"
      (TeX-arg-eval
       (lambda ()
	 (let ((opts (TeX-read-key-val optional
				       (append '(("ppi")) LaTeX-moodle-key-val-options))))
	   (format "%s" opts)))))

    ;; 5 Graphics
    '("ghostscriptcommand" "File name")
    '("imagemagickcommand" "File name")
    '("opensslcommand"     "File name"))

   ;; Fontification
   (when (and (featurep 'font-latex)
	      (eq TeX-install-font-lock 'font-latex-setup))
     (font-latex-add-keywords '(("moodleset"          "{")
				("ghostscriptcommand" "{")
				("imagemagickcommand" "{")
				("opensslcommand"     "{"))
			      'function)
     (font-latex-add-keywords '(("answer" "")
				;; Cater for a fontified starred \item
				("item"   "*["))
			      'textual)))
 LaTeX-dialect)

(defvar LaTeX-moodle-package-options
  '("draft")
  "Package options for the moodle package.")

;;; moodle.el ends here
