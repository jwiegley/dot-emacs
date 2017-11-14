;;; fancyvrb.el --- AUCTeX style for `fancyvrb.sty' version 2.8.

;; Copyright (C) 2013, 2014, 2016, 2017 Free Software Foundation, Inc.

;; Maintainer: auctex-devel@gnu.org
;; Author: Mosè Giordano <mose@gnu.org>
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

;; This file adds support for `fancyvrb.sty' version 2.8.

;; This style has some capabilities to parse user defined macros,
;; environments and saved blocks with `SaveVerbatim' environments and
;; offer them for completion.  After defining a new macro or
;; environment, hit `C-c C-n' to parse the document.  In case of
;; `SaveVerbatim', a second `C-c C-n' might be necessary.

;; The command `\CustomVerbatimEnvironment' is not mentioned in the
;; documenation; hence this command is removed from this style.  Use
;; `\DefineVerbatimEnvironment' for new environments and customize the
;; standard ones with `\RecustomVerbatimEnvironment'.

;; The entries in `LaTeX-fancyvrb-key-val-options' cover also some
;; keys which are not mentioned in the manual of the package.

;;; Code:

;; Needed for auto-parsing.
(require 'tex)

(defvar LaTeX-fancyvrb-key-val-options
  '(("commentchar" ("none"))
    ("gobble")
    ("formatcom")
    ;; Undocumented key
    ("formatcom*")
    ("fontfamily" ("tt" "courier" "helvetica"))
    ("fontsize"   ("auto" "\\tiny" "\\scriptsize"
		   "\\footnotesize" "\\small" "\\normalsize"
		   "\\large" "\\Large" "\\LARGE" "\\huge" "\\Huge"))
    ("fontshape"  ("auto" "n" "it" "sl" "sc" "scit"))
    ("fontseries" ("auto" "m" "b" "bx" "sb" "c" "l" "lc"))
    ("frame" ("none" "leftline" "topline" "bottomline" "lines" "single"))
    ("framerule")
    ("framesep")
    ("rulecolor" ("none"))
    ("fillcolor" ("none"))
    ("label" ("none"))
    ("labelposition" ("none" "topline" "bottomline" "all"))
    ("numbers" ("none" "left" "right"))
    ("numbersep")
    ("firstnumber" ("auto" "last" "integer"))
    ("stepnumber")
    ("numberblanklines" ("true" "false"))
    ("firstline")
    ("lastline")
    ("showspaces" ("true" "false"))
    ("showtabs" ("true" "false"))
    ("obeytabs" ("true" "false"))
    ("tabsize")
    ("baselinestretch" ("auto" "dimension"))
    ("commandchars" ("none"))
    ("xleftmargin")
    ("xrightmargin")
    ("resetmargins" ("true" "false"))
    ("hfuzz")
    ("samepage" ("true" "false"))
    ("codes")
    ;; Undocumented key
    ("codes*")
    ("defineactive")
    ;; Undocumented key
    ("defineactive*")
    ;; Actually, the following options are used only by the `BVerbatim'
    ;; environment.
    ("boxwidth" ("auto" "dimension"))
    ("baseline" ("b" "c" "t"))
    ;; The next key applies only to `\SaveVerb' macro.
    ("aftersave"))
  "Key=value options for fancyvrb macros and environments.")

(defvar LaTeX-fancyvrb-key-val-options-local nil
  "Buffer-local key=value options for fancyvrb macros and environments.
This variable is intended for packages like \"fvextra\" which
provide new key=values for fancyvrb environments.  New key=values
should be appended to this variable.")
(make-variable-buffer-local 'LaTeX-fancyvrb-key-val-options-local)

(defvar LaTeX-fancyvrb-base-macros
  '("VerbatimInput" "BVerbatimInput" "LVerbatimInput"
    "SaveVerb" "UseVerb" "Verb")
  "List of base macros available with fancyvrb package.
Starred versions are not included in this list.")

(defvar LaTeX-fancyvrb-base-environments
  '("Verbatim" "BVerbatim" "LVerbatim" "SaveVerbatim" "VerbatimOut")
  "List of base environments available with fancyvrb package.
Starred versions are not included in this list.")

(defvar LaTeX-fancyvrb-key-val-skip-regexp
  (concat
   "\\(?:\\[[^][]*"
     "\\(?:{[^}{]*"
       "\\(?:{[^}{]*"
	 "\\(?:{[^}{]*}[^}{]*\\)*"
       "}[^}{]*\\)*"
     "}[^][]*\\)*"
   "\\]\\)?")
  "Helper regexp to skip over an optional argument.")

;; Setup for defining new Verbatim commands:

(TeX-auto-add-type "fancyvrb-macro" "LaTeX")

(defvar LaTeX-fancyvrb-macro-regexp
  `(,(concat "\\\\\\(Rec\\|C\\)ustomVerbatimCommand"
	     "[ \t\n\r]*{?[ \t\n\r]*\\\\\\([A-Za-z]+\\)[ \t\n\r]*}?"
	     "[ \t\n\r]*{[ \t\n\r]*\\([A-Za-z]+\\)[ \t\n\r]*}")
    (2 3 1) LaTeX-auto-fancyvrb-macro)
  "Matches macros by fancyvrb package.")

;; Setup for defining new Verbatim environments:

(TeX-auto-add-type "fancyvrb-environment" "LaTeX")

(defvar LaTeX-fancyvrb-environment-regexp
  `(,(concat "\\\\DefineVerbatimEnvironment"
	     "[ \t\n\r]*{[ \t\n\r]*\\([A-Za-z0-9]+\\)[ \t\n\r]*}"
	     "[ \t\n\r]*{[ \t\n\r]*\\([A-Za-z]+\\)[ \t\n\r]*}")
    (1 2) LaTeX-auto-fancyvrb-environment)
  "Matches new environments defined by fancyvrb package.")

;; Setup for names in SaveVerb macros:

(TeX-auto-add-type "fancyvrb-saveverb" "LaTeX")

(defvar LaTeX-fancyvrb-saveverb-regexp
  `(,(concat "\\\\SaveVerb"
	     LaTeX-fancyvrb-key-val-skip-regexp
	     "{\\([^}]+\\)}")
    1 LaTeX-auto-fancyvrb-saveverb)
  "Match the name under which verbatim text is saved by SaveVerb macro.")

;; Setup for names in SaveVerbatim environments:

(TeX-auto-add-type "fancyvrb-saveverbatim" "LaTeX")

(defvar LaTeX-fancyvrb-saveverbatim-regexp
  `(,(concat "\\\\begin{SaveVerbatim}"
	     LaTeX-fancyvrb-key-val-skip-regexp
	     "{\\([^}]+\\)}")
    1 LaTeX-auto-fancyvrb-saveverbatim)
  "Match the name under which verbatim text is saved by SaveVerbatim environment.")

(defun LaTeX-fancyvrb-auto-prepare ()
  "Clear various LaTeX-auto-fancyvrb-* variables before parsing."
  (setq LaTeX-auto-fancyvrb-macro        nil
	LaTeX-auto-fancyvrb-environment  nil
	LaTeX-auto-fancyvrb-saveverb     nil
	LaTeX-auto-fancyvrb-saveverbatim nil))

(defun LaTeX-fancyvrb-auto-cleanup ()
  "Process parsed elements for fancyvrb package."
  (LaTeX-fancyvrb-arg-define-macro nil t)
  (LaTeX-fancyvrb-arg-define-environment nil t))

(add-hook 'TeX-auto-prepare-hook #'LaTeX-fancyvrb-auto-prepare t)
(add-hook 'TeX-auto-cleanup-hook #'LaTeX-fancyvrb-auto-cleanup t)
(add-hook 'TeX-update-style-hook #'TeX-auto-parse t)

(defun LaTeX-fancyvrb-arg-define-macro (optional &optional cleanup recustom)
  "Query and insert a new verbatim macro with fancyvrb package.
If OPTIONAL is non-nil, insert the arguments in brackets.  If
CLEANUP is non-nil, do not insert any arguments in the buffer and
update only various AUCTeX variables for verbatim macros.  If
RECUSTOM is non-nil, delete macros from the variable
`TeX-symbol-list' before adding the new ones."
  (let ((new-mac (unless cleanup
		   (if recustom
		       (completing-read
			(TeX-argument-prompt optional nil "Verbatim macro: \\" t)
			(mapcar #'car (apply #'append LaTeX-fancyvrb-macro-list)))
		     (TeX-read-string
		      (TeX-argument-prompt optional nil "New verbatim macro: \\" t)))))
	(base-mac (unless cleanup
		    (completing-read (TeX-argument-prompt optional nil "Based on macro")
				     LaTeX-fancyvrb-base-macros)))
	(rec-flag (if recustom "Rec" "C")))
    ;; We are (re-)defining a macro: Insert user queried input and use
    ;; `LaTeX-add-fancyvrb-macros' on the input
    (unless cleanup
      (TeX-argument-insert new-mac optional TeX-esc)
      (TeX-argument-insert base-mac optional)
      (TeX-argument-insert
       (TeX-read-key-val optional LaTeX-fancyvrb-key-val-options-local) optional)
      (LaTeX-add-fancyvrb-macros `(,new-mac ,base-mac ,rec-flag))))
  ;;
  ;; Now run the procdure: Do not use the function
  ;; `LaTeX-fancyvrb-macro-list' here which will remove dupes from the
  ;; variable `LaTeX-fancyvrb-macro-list' depending on car; we need
  ;; the variable as is, hence (apply #'append ...);
  (dolist (elt (apply #'append LaTeX-fancyvrb-macro-list))
    (let ((mac-name (nth 0 elt))
	  (base-mac (nth 1 elt))
	  (flag     (nth 2 elt)))
      ;; If we're Rec-ustomizing, delete the entry first from
      ;; `TeX-symbol-list':
      (when (string= flag "Rec")
	(setq TeX-symbol-list
	      (assq-delete-all (car (assoc mac-name (TeX-symbol-list))) TeX-symbol-list)))
      ;; Now add the new item: Start with new macros for loading
      ;; files:
      (cond ((member base-mac '("VerbatimInput" "BVerbatimInput" "LVerbatimInput"))
	     (TeX-add-symbols
	      `(,mac-name
		[ TeX-arg-key-val LaTeX-fancyvrb-key-val-options-local ]
		LaTeX-fancyvrb-arg-file-relative))
	     (when (and (fboundp 'font-latex-add-keywords)
			(fboundp 'font-latex-update-font-lock))
	       (font-latex-add-keywords `((,mac-name "[{"))
					'reference)))
	    ;; New macros for saving verbatim text:
	    ((string= base-mac "SaveVerb")
	     (TeX-add-symbols
	      `(,mac-name
		[ TeX-arg-key-val LaTeX-fancyvrb-key-val-options-local ]
		(TeX-arg-eval
		 (lambda ()
		   (let ((name (TeX-read-string
				(TeX-argument-prompt optional nil "Save name"))))
		     (LaTeX-add-fancyvrb-saveverbs name)
		     (format "%s" name))))
		TeX-arg-verb))
	     (when (and (fboundp 'font-latex-add-keywords)
			(fboundp 'font-latex-update-font-lock))
	       (font-latex-add-keywords `((,mac-name "[{"))
					'textual)))
	    ;; New macros for using previously saved text:
	    ((string= base-mac "UseVerb")
	     (TeX-add-symbols
	      `(,mac-name
		(TeX-arg-eval
		 completing-read
		 (TeX-argument-prompt optional nil "Saved name")
		 (LaTeX-fancyvrb-saveverb-list))))
	     (when (and (fboundp 'font-latex-add-keywords)
			(fboundp 'font-latex-update-font-lock))
	       (font-latex-add-keywords `((,mac-name "{"))
					'textual)))
	    ;; Anything else is considered as verbatim typesetting macro:
	    (t
	     (TeX-add-symbols
	      `(mac-name
		[ TeX-arg-key-val LaTeX-fancyvrb-key-val-options-local ]
		TeX-arg-verb))
	     (add-to-list 'LaTeX-verbatim-macros-with-delims-local mac-name t)
	     (when (and (fboundp 'font-latex-add-keywords)
			(fboundp 'font-latex-update-font-lock))
	       (font-latex-add-keywords `((,mac-name "["))
					'textual))))))
  ;; Update font-lock:
  (when (and (fboundp 'font-latex-add-keywords)
	     (fboundp 'font-latex-update-font-lock)
	     (eq TeX-install-font-lock 'font-latex-setup))
    (font-latex-update-font-lock t)))

(defun LaTeX-fancyvrb-arg-define-environment (optional &optional cleanup)
  "Query and insert a new verbatim environment with fancyvrb package.
If OPTIONAL is non-nil, insert the arguments in brackets.  If
CLEANUP is non-nil, do not insert any arguments in the buffer and
update only various AUCTeX variables for verbatim environments."
  (let ((new-env (unless cleanup
		   (TeX-read-string
		    (TeX-argument-prompt optional nil "New verbatim environment"))))
	(base-env (unless cleanup
		    (completing-read (TeX-argument-prompt optional nil "Based on environment")
				     LaTeX-fancyvrb-base-environments))))
    ;; We are defining a new env: First insert the arguments and the
    ;; run `LaTeX-add-fancyvrb-environments' on '(new-env base-env).
    ;; If base-env is SaveVerbatim, run
    ;; `LaTeX-add-fancyvrb-saveverbatims' on new-env as well.
    (unless cleanup
      (TeX-argument-insert (car new-env) optional)
      (TeX-argument-insert base-env optional)
      (TeX-argument-insert
       (TeX-read-key-val optional LaTeX-fancyvrb-key-val-options-local) optional)
      (LaTeX-add-fancyvrb-environments `(,new-env ,base-env))
      (when (string= base-env "SaveVerbatim")
	(LaTeX-add-fancyvrb-saveverbatims new-env)))
    ;;
    ;; Now run the procdure:
    (dolist (elt (LaTeX-fancyvrb-environment-list))
      (let ((env (car elt))
	    (type (cadr elt)))
	(cond ((string= type "VerbatimOut")
	       (LaTeX-add-environments
		`(,env (lambda (env)
			 (let ((options (TeX-read-key-val t LaTeX-fancyvrb-key-val-options-local))
			       (file (TeX-read-string "Output file: ")))
			   (LaTeX-insert-environment
			    env
			    (concat
			     (unless (zerop (length options))
			       (concat LaTeX-optop options LaTeX-optcl))
			     (concat TeX-grop file TeX-grcl))))))))
	      ((string= type "SaveVerbatim")
	       (TeX-auto-add-regexp `(,(concat "\\\\begin{"
					       env
					       "}"
					       LaTeX-fancyvrb-key-val-skip-regexp
					       "{\\([^}]+\\)}")
				      1 LaTeX-auto-fancyvrb-saveverbatim)))
	      (t
	       ;; Regular verbatim environments have a starred
	       ;; version; so add them here; the non-starred additions
	       ;; to `LaTeX-verbatim-environments-local' and
	       ;; `LaTeX-indent-environment-list' are done outside
	       ;; (cond ...):
	       (LaTeX-add-environments
		`(,env LaTeX-env-args
		       [ TeX-arg-key-val LaTeX-fancyvrb-key-val-options-local ]))
	       (LaTeX-add-environments
		`(,(concat env "*") LaTeX-env-args
		  [ TeX-arg-key-val LaTeX-fancyvrb-key-val-options-local ]))
	       (add-to-list 'LaTeX-verbatim-environments-local (concat env "*"))
	       (add-to-list 'LaTeX-indent-environment-list
			    `(,(concat env "*") current-indentation) t)))
	;; These apply for all environments defined:
	(add-to-list 'LaTeX-verbatim-environments-local env)
	(add-to-list 'LaTeX-indent-environment-list `(,env current-indentation) t)))
    ;; Update font-lock:
    (when (and (fboundp 'font-latex-add-keywords)
	       (fboundp 'font-latex-update-font-lock)
	       (eq TeX-install-font-lock 'font-latex-setup))
      (font-latex-update-font-lock t))))

(defun LaTeX-fancyvrb-arg-file-relative (optional)
  "Query and insert a file name relative to current master file.
If OPTIONAL is non-nil, insert the file name in brackets."
  (TeX-argument-insert
   (file-relative-name
    (read-file-name (TeX-argument-prompt optional nil "File"))
    (TeX-master-directory))
   optional))

(TeX-add-style-hook
 "fancyvrb"
 (lambda ()
   (TeX-auto-add-regexp LaTeX-fancyvrb-macro-regexp)
   (TeX-auto-add-regexp LaTeX-fancyvrb-environment-regexp)
   (TeX-auto-add-regexp LaTeX-fancyvrb-saveverb-regexp)
   (TeX-auto-add-regexp LaTeX-fancyvrb-saveverbatim-regexp)
   (TeX-run-style-hooks
    "keyval")

   ;; Activate the buffer-local version of key-vals.
   (setq LaTeX-fancyvrb-key-val-options-local
	 (copy-alist LaTeX-fancyvrb-key-val-options))

   (TeX-add-symbols
    ;; Verbatim material in footnotes
    "VerbatimFootnotes"
    ;; Improved verbatim commands
    '("Verb" [TeX-arg-key-val LaTeX-fancyvrb-key-val-options-local] TeX-arg-verb)
    '("DefineShortVerb" (TeX-arg-eval
			 TeX-read-string
			 (TeX-argument-prompt optional nil "Character")
			 TeX-esc))
    '("UndefineShortVerb" (TeX-arg-eval
			   TeX-read-string
			   (TeX-argument-prompt optional nil "Character")
			   TeX-esc))
    ;; Verbatim environments
    '("fvset" (TeX-arg-key-val LaTeX-fancyvrb-key-val-options-local))
    ;; Changing individual line formatting
    "FancyVerbFormatLine"
    ;; Line numbering
    "theFancyVerbLine"
    ;; Selection of lines to print
    "FancyVerbStartString"
    "FancyVerbStopString"

    ;; Personalized environments
    '("DefineVerbatimEnvironment"
      LaTeX-fancyvrb-arg-define-environment)
    '("RecustomVerbatimEnvironment"
      (TeX-arg-eval completing-read
		    (TeX-argument-prompt optional nil "Verbatim environment")
		    LaTeX-fancyvrb-base-environments)
      (TeX-arg-eval completing-read
		    (TeX-argument-prompt optional nil "Based on environment")
		    LaTeX-fancyvrb-base-environments)
      (TeX-arg-key-val LaTeX-fancyvrb-key-val-options-local))

    '("CustomVerbatimCommand"
      LaTeX-fancyvrb-arg-define-macro)
    '("RecustomVerbatimCommand"
      (LaTeX-fancyvrb-arg-define-macro nil t))

    ;; Saving and restoring verbatim text and environments
    '("SaveVerb"
      [TeX-arg-key-val LaTeX-fancyvrb-key-val-options-local]
      (TeX-arg-eval
       (lambda ()
	 (let ((name (TeX-read-string
		      (TeX-argument-prompt optional nil "Save name"))))
	   (LaTeX-add-fancyvrb-saveverbs name)
	   (format "%s" name))))
      TeX-arg-verb)
    '("UseVerb" (TeX-arg-eval
		 completing-read
		 (TeX-argument-prompt optional nil "Saved name")
		 (LaTeX-fancyvrb-saveverb-list)))
    '("UseVerbatim" (TeX-arg-eval completing-read
				  (TeX-argument-prompt optional nil "Saved name")
				  (LaTeX-fancyvrb-saveverbatim-list)))
    '("LUseVerbatim" (TeX-arg-eval completing-read
				   (TeX-argument-prompt optional nil "Saved name")
				   (LaTeX-fancyvrb-saveverbatim-list)))
    '("BUseVerbatim" (TeX-arg-eval completing-read
				   (TeX-argument-prompt optional nil "Saved name")
				   (LaTeX-fancyvrb-saveverbatim-list)))

    ;; Writing and reading verbatim files
    '("VerbatimInput" [TeX-arg-key-val LaTeX-fancyvrb-key-val-options-local]
      LaTeX-fancyvrb-arg-file-relative)
    '("BVerbatimInput" [TeX-arg-key-val LaTeX-fancyvrb-key-val-options-local]
      LaTeX-fancyvrb-arg-file-relative)
    '("LVerbatimInput" [TeX-arg-key-val LaTeX-fancyvrb-key-val-options-local]
      LaTeX-fancyvrb-arg-file-relative))

   (LaTeX-add-environments
    '("Verbatim" LaTeX-env-args
      [TeX-arg-key-val LaTeX-fancyvrb-key-val-options-local])
    '("Verbatim*" LaTeX-env-args
      [TeX-arg-key-val LaTeX-fancyvrb-key-val-options-local])
    '("BVerbatim" LaTeX-env-args
      [TeX-arg-key-val LaTeX-fancyvrb-key-val-options-local])
    '("BVerbatim*" LaTeX-env-args
      [TeX-arg-key-val LaTeX-fancyvrb-key-val-options-local])
    '("LVerbatim" LaTeX-env-args
      [TeX-arg-key-val LaTeX-fancyvrb-key-val-options-local])
    '("LVerbatim*" LaTeX-env-args
      [TeX-arg-key-val LaTeX-fancyvrb-key-val-options-local])
    '("SaveVerbatim"
      (lambda (env)
	(let ((options (TeX-read-key-val t LaTeX-fancyvrb-key-val-options-local))
	      (name (TeX-read-string "Save name: ")))
	  (LaTeX-insert-environment
	   env
	   (concat
	    (unless (zerop (length options))
	      (concat LaTeX-optop options LaTeX-optcl))
	    (concat TeX-grop name TeX-grcl)))
	  (LaTeX-add-fancyvrb-saveverbatims name))))
    '("VerbatimOut"
      (lambda (env)
	(let ((options (TeX-read-key-val t LaTeX-fancyvrb-key-val-options-local))
	      (file (TeX-read-string "Output file: ")))
	  (LaTeX-insert-environment
	   env
	   (concat (unless (zerop (length options))
		     (concat LaTeX-optop options LaTeX-optcl))
		   (concat TeX-grop file TeX-grcl)))))))

   (LaTeX-add-counters
    "FancyVerbLine")

   ;; Filling
   (add-to-list 'LaTeX-verbatim-environments-local "Verbatim")
   (add-to-list 'LaTeX-verbatim-environments-local "Verbatim*")
   (add-to-list 'LaTeX-verbatim-environments-local "BVerbatim")
   (add-to-list 'LaTeX-verbatim-environments-local "BVerbatim*")
   (add-to-list 'LaTeX-verbatim-environments-local "LVerbatim")
   (add-to-list 'LaTeX-verbatim-environments-local "LVerbatim*")
   (add-to-list 'LaTeX-verbatim-environments-local "SaveVerbatim")
   (add-to-list 'LaTeX-verbatim-environments-local "VerbatimOut")
   (make-local-variable 'LaTeX-indent-environment-list)
   (add-to-list 'LaTeX-indent-environment-list '("Verbatim" current-indentation) t)
   (add-to-list 'LaTeX-indent-environment-list '("Verbatim*" current-indentation) t)
   (add-to-list 'LaTeX-indent-environment-list '("BVerbatim" current-indentation) t)
   (add-to-list 'LaTeX-indent-environment-list '("BVerbatim*" current-indentation) t)
   (add-to-list 'LaTeX-indent-environment-list '("LVerbatim" current-indentation) t)
   (add-to-list 'LaTeX-indent-environment-list '("LVerbatim*" current-indentation) t)
   (add-to-list 'LaTeX-indent-environment-list '("SaveVerbatim" current-indentation) t)
   (add-to-list 'LaTeX-indent-environment-list '("VerbatimOut" current-indentation) t)
   (add-to-list 'LaTeX-verbatim-macros-with-delims-local "Verb")

   ;; Fontification
   (when (and (fboundp 'font-latex-add-keywords)
	      (fboundp 'font-latex-update-font-lock)
	      (eq TeX-install-font-lock 'font-latex-setup))
     (font-latex-add-keywords '(("CustomVerbatimCommand"       "{{{")
				("RecustomVerbatimCommand"     "{{{")
				("DefineVerbatimEnvironment"   "{{{")
				("RecustomVerbatimEnvironment" "{{{")
				("DefineShortVerb"   "{")
				("UndefineShortVerb" "{")
				("fvset"             "{"))
			      'function)
     (font-latex-add-keywords '(("VerbatimInput"  "[{")
				("BVerbatimInput" "[{")
				("LVerbatimInput" "[{"))
			      'reference)
     (font-latex-add-keywords '(("Verb" "[") ; The second argument should
					; actually be verbatim.
				("SaveVerb"     "[{")
				("UseVerb"      "{")
				("UseVerbatim"  "{")
				("LUseVerbatim" "{")
				("BUseVerbatim" "{"))
			      'textual)
     ;; Tell font-lock about the update.
     (font-latex-update-font-lock t)))
 LaTeX-dialect)

(defvar LaTeX-fancyvrb-package-options nil
  "Package options for the fancyvrb package.")

;;; fancyvrb.el ends here
