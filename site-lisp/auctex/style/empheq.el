;;; empheq.el --- AUCTeX style for `empheq.sty' (v2.14)

;; Copyright (C) 2016, 2017 Free Software Foundation, Inc.

;; Author: Arash Esbati <arash@gnu.org>
;; Maintainer: auctex-devel@gnu.org
;; Created: 2016-08-07
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

;; This file adds support for `empheq.sty' (v2.14) from 2014/08/04.
;; `empheq.sty' is part of TeXLive.

;;; Code:

;; Needed for compiling `pushnew':
(eval-when-compile (require 'cl))

;; Needed for auto-parsing.
(require 'tex)

(defvar LaTeX-empheq-key-val-options
  `(("box")
    ("innerbox")
    ("left" ,(mapcar
	      (lambda (x)
		(concat TeX-esc x))
	      '("empheqlbrace"
		"empheqlbrack"
		"empheqlangle"
		"empheqlparen"
		"empheqlvert"
		"empheqlVert"
		"empheqlfloor"
		"empheqlceil"
		"empheqbiglbrace"
		"empheqbiglbrack"
		"empheqbiglangle"
		"empheqbiglparen"
		"empheqbiglvert"
		"empheqbiglVert"
		"empheqbiglfloor"
		"empheqbiglceil")))
    ("right" ,(mapcar
	       (lambda (x)
		 (concat TeX-esc x))
	       '("empheqrbrace"
		 "empheqrbrack"
		 "empheqrangle"
		 "empheqrparen"
		 "empheqrvert"
		 "empheqrVert"
		 "empheqrfloor"
		 "empheqrceil"
		 "empheqbigrbrace"
		 "empheqbigrbrack"
		 "empheqbigrangle"
		 "empheqbigrparen"
		 "empheqbigrvert"
		 "empheqbigrVert"
		 "empheqbigrfloor"
		 "empheqbigrceil")))
    ("outerbox")
    ("marginbox"))
  "Key=value options for environments from empheq.sty.")

(defvar LaTeX-empheq-key-val-options-local nil
  "Buffer-local key=value options for environments from empheq.sty.")
(make-local-variable 'LaTeX-empheq-key-val-options-local)

(defvar LaTeX-empheq-supported-amsmath-envs
  '("equation"  "equation*"
    "align"     "align*"
    "gather"    "gather*"
    "flalign"   "flalign*"
    "alignat"   "alignat*"
    "multline"  "multline*")
  "List of amsmath environments supported by empheq package.")

(defvar LaTeX-empheq-package-options
  '("overload" "overload2" "ntheorem" "newmultline" "oldmultline")
  "Package options for the empheq package.")

;; Setup for \Declare(Left|Right)Delimiter:

(TeX-auto-add-type "empheq-declaredelimiter" "LaTeX")

(defvar LaTeX-empheq-declaredelimiter-regexp
  `(,(concat "\\\\Declare\\(Left\\|Right\\)Delimiter"
	     "[ \t\n\r%]*"
	     "\\(?:\\[[^]]*\\]\\)?"
	     "[ \t\n\r%]*"
	     "{"
	     (regexp-quote TeX-esc)
	     "\\([^}]+\\)}")
    (2 1) LaTeX-auto-empheq-declaredelimiter)
  "Matches the argument of \\Declare(Left|Right)Delimiter from empheq package.")

(defun LaTeX-empheq-auto-prepare ()
  "Clear `LaTeX-auto-empheq-declaredelimiter' before parsing."
  (setq LaTeX-auto-empheq-declaredelimiter nil))

(defun LaTeX-empheq-auto-cleanup ()
  "Process parsed delimiters."
  (dolist (delim (mapcar #'car (LaTeX-empheq-declaredelimiter-list)))
    (TeX-add-symbols (concat "empheq" delim)
		     (concat "empheqbig" delim)))
  (LaTeX-empheq-update-key-val-options))

(add-hook 'TeX-auto-prepare-hook #'LaTeX-empheq-auto-prepare t)
(add-hook 'TeX-auto-cleanup-hook #'LaTeX-empheq-auto-cleanup t)
(add-hook 'TeX-update-style-hook #'TeX-auto-parse t)

(defun LaTeX-empheq-update-key-val-options ()
  "Update `LaTeX-empheq-key-val-options-local' if the function
`LaTeX-empheq-declaredelimiter-list' returns non-nil."
  (when (LaTeX-empheq-declaredelimiter-list)
    (let ((lvals (cadr (assoc "left" LaTeX-empheq-key-val-options)))
	  (rvals (cadr (assoc "right" LaTeX-empheq-key-val-options)))
	  (tmp (copy-alist LaTeX-empheq-key-val-options))
	  lval rval)
      (dolist (delims (LaTeX-empheq-declaredelimiter-list))
	(let ((delim (car delims))
	      (where (cadr delims)))
	  (if (string= where "Left")
	      (progn
		(pushnew (concat TeX-esc "empheq" delim) lval :test #'equal)
		(pushnew (concat TeX-esc "empheqbig" delim) lval :test #'equal))
	    (progn
	      (pushnew (concat TeX-esc "empheq" delim) rval :test #'equal)
	      (pushnew (concat TeX-esc "empheqbig" delim) rval :test #'equal)))))
      (when lval
	(setq tmp (assq-delete-all (car (assoc "left" tmp)) tmp))
	(setq lvals (append lval lvals))
	(push (list "left" lvals) tmp))
      (when rval
	(setq tmp (assq-delete-all (car (assoc "right" tmp)) tmp))
	(setq rvals (append rval rvals))
	(push (list "right" rvals) tmp))
      (setq LaTeX-empheq-key-val-options-local
	    (copy-alist tmp)))))

(defun LaTeX-empheq-env (env)
  "Query for a supported amsmath environment and insert it accordingly."
  (let* ((keyvals (TeX-read-key-val t LaTeX-empheq-key-val-options-local))
	 (amsenv (completing-read
		  (TeX-argument-prompt nil nil "amsmath environment")
		  LaTeX-empheq-supported-amsmath-envs))
	 (ncols (when (or (string= amsenv "alignat")
			  (string= amsenv "alignat*"))
		  (TeX-read-string
		   (TeX-argument-prompt nil nil "Number of columns"))))
	 num)
    (LaTeX-insert-environment
     env
     (concat
      (when (and keyvals (not (string= keyvals "")))
	(concat LaTeX-optop keyvals LaTeX-optcl))
      TeX-grop
      (if (and ncols (not (string= ncols "")))
	  (concat amsenv "=" ncols)
	(symbol-value 'amsenv))
      TeX-grcl))
    (when (and (assoc amsenv LaTeX-label-alist)
	       (LaTeX-label amsenv 'environment))
      (LaTeX-newline)
      (indent-according-to-mode))
    (when (and ncols (not (string= ncols "")))
      (setq num (string-to-number ncols))
      (save-excursion
	(insert (make-string (+ num num -1) ?&))))))

(defun LaTeX-empheq-env-overload (env &optional _ignore)
  "Insert amsmath ENV's when option overload is given to empheq package.
This function combines the capabilities of `LaTeX-env-label' and
`LaTeX-amsmath-env-alignat'.  It overwrites the definitions of
`amsmath.el'."
  (if (or (string= env "alignat")
	  (string= env "alignat*"))
      (let ((ncols (TeX-read-string
		    (TeX-argument-prompt nil nil "Number of columns")))
	    (keyvals (TeX-read-key-val t
				       LaTeX-empheq-key-val-options-local
				       "empheq options (k=v)")))
	(LaTeX-insert-environment env (concat TeX-grop ncols TeX-grcl
					      (when (and keyvals (not (string= keyvals "")))
						(concat LaTeX-optop keyvals LaTeX-optcl))))
	(LaTeX-item-equation-alignat t))
    (let ((keyvals
	   (TeX-read-key-val t LaTeX-empheq-key-val-options-local "empheq options (k=v)")))
      (LaTeX-insert-environment env (when (and keyvals (not (string= keyvals "")))
				      (concat LaTeX-optop keyvals LaTeX-optcl)))
      (when (and (assoc env LaTeX-label-alist)
		 (LaTeX-label env 'environment))
	(LaTeX-newline)
	(indent-according-to-mode)))))

(defun LaTeX-empheq-item-equation ()
  "Insert contents to terminate a line in multi-line equations environment.
Put line break macro on the last line.  Next, if the current
environment wants \\label, insert it also.  And insert suitable
number of ampersands if possible."
  (let ((env (LaTeX-current-environment))
	amsenv ncols match)
    (save-excursion
      (LaTeX-find-matching-begin)
      (re-search-forward (concat (regexp-quote TeX-esc)
				 "begin" TeX-grop env TeX-grcl))
      (when (looking-at "[ \t\n\r%]*\\[")
	(forward-sexp))
      (re-search-forward "[ \t\n\r%]*{\\([^}]+\\)}")
      (setq match (TeX-replace-regexp-in-string "[ \t\n\r%]" ""
						(match-string-no-properties 1)))
      (if (string-match "=" match)
	  (progn
	    (setq amsenv (car (split-string match "=")))
	    (setq ncols (string-to-number (cadr (split-string match "=")))))
	(setq amsenv match)))
    ;; Do not ask for "\\" if in "equation" or "equation*" since these
    ;; are single line equations only
    (if (or (string= amsenv "equation")
	    (string= amsenv "equation*"))
	;; Nullify the effect of `M-RET'
	(progn
	  (message "This environment does not support multi-line equations")
	  (end-of-line 0)
	  (kill-line 1))
      (progn
	(end-of-line 0)
	(just-one-space)
	(TeX-insert-macro "\\")
	(forward-line 1)
	(indent-according-to-mode)))
    ;; Add a new label only if not in "equation"
    (when (and (not (string= amsenv "equation"))
	       (assoc amsenv LaTeX-label-alist)
	       (LaTeX-label amsenv 'environment))
      (LaTeX-newline)
      (indent-according-to-mode))
    (when ncols
      (save-excursion
	(insert (make-string (+ ncols ncols -1) ?&))))))

(TeX-add-style-hook
 "empheq"
 (lambda ()

   ;; Add empheq to parser
   (TeX-auto-add-regexp LaTeX-empheq-declaredelimiter-regexp)

   ;; Load amsmath.el and mathtools.el
   (TeX-run-style-hooks "amsmath" "mathtools")

   ;; Add elements from `LaTeX-mathtools-package-options' only once
   ;; and not every time the style hook runs
   (dolist (elt LaTeX-mathtools-package-options)
     (add-to-list 'LaTeX-empheq-package-options elt))

   ;; Local version of key-val options
   (setq LaTeX-empheq-key-val-options-local
	 (copy-alist LaTeX-empheq-key-val-options))

   ;; Initial update of key-vals
   (LaTeX-empheq-update-key-val-options)

   (LaTeX-add-environments
    '("empheq" LaTeX-empheq-env))

   ;; Add "empheq" to `LaTeX-item-list' and run
   ;; `LaTeX-empheq-item-equation' when `M-RET' is invoked
   (add-to-list 'LaTeX-item-list '("empheq" . LaTeX-empheq-item-equation) t)

   ;; Reftex support: Use `reftex-add-label-environments'
   (when (fboundp 'reftex-add-label-environments)
     (reftex-add-label-environments '(("empheq" ?e nil nil t))))

   (TeX-add-symbols
    '("empheqset" (TeX-arg-key-val LaTeX-empheq-key-val-options-local))

    ;; 1.4 Special delimiters
    ;; Normal
    '("empheqlbrace" TeX-arg-insert-right-brace-maybe)
    '("empheqrbrace")
    '("empheqlbrack" TeX-arg-insert-right-brace-maybe)
    '("empheqrbrack")
    '("empheqlangle" TeX-arg-insert-right-brace-maybe)
    '("empheqrangle")
    '("empheqlparen" TeX-arg-insert-right-brace-maybe)
    '("empheqrparen")
    '("empheqlvert" TeX-arg-insert-right-brace-maybe)
    '("empheqrvert")
    '("empheqlVert" TeX-arg-insert-right-brace-maybe)
    '("empheqrVert")
    '("empheqlfloor" TeX-arg-insert-right-brace-maybe)
    '("empheqrfloor")
    '("empheqlceil" TeX-arg-insert-right-brace-maybe)
    '("empheqrceil")
    ;; Bigger
    '("empheqbiglbrace" TeX-arg-insert-right-brace-maybe)
    '("empheqbigrbrace")
    '("empheqbiglbrack" TeX-arg-insert-right-brace-maybe)
    '("empheqbigrbrack")
    '("empheqbiglangle" TeX-arg-insert-right-brace-maybe)
    '("empheqbigrangle")
    '("empheqbiglparen" TeX-arg-insert-right-brace-maybe)
    '("empheqbigrparen")
    '("empheqbiglvert" TeX-arg-insert-right-brace-maybe)
    '("empheqbigrvert")
    '("empheqbiglVert" TeX-arg-insert-right-brace-maybe)
    '("empheqbigrVert")
    '("empheqbiglfloor" TeX-arg-insert-right-brace-maybe)
    '("empheqbigrfloor")
    '("empheqbiglceil" TeX-arg-insert-right-brace-maybe)
    '("empheqbigrceil"))

   ;; Append delimiters to `TeX-braces-association'
   (make-local-variable 'TeX-braces-association)
   (let ((delimiters '(("\\empheqlbrace" . "\\empheqrbrace")
		       ("\\empheqlbrack" . "\\empheqrbrack")
		       ("\\empheqlangle" . "\\empheqrangle")
		       ("\\empheqlparen" . "\\empheqrparen")
		       ("\\empheqlvert"  . "\\empheqrvert")
		       ("\\empheqlVert"  . "\\empheqrVert")
		       ("\\empheqlfloor" . "\\empheqrfloor")
		       ("\\empheqlceil"  . "\\empheqrceil")
		       ("\\empheqbiglbrace" . "\\empheqbigrbrace")
		       ("\\empheqbiglbrack" . "\\empheqbigrbrack")
		       ("\\empheqbiglangle" . "\\empheqbigrangle")
		       ("\\empheqbiglparen" . "\\empheqbigrparen")
		       ("\\empheqbiglvert"  . "\\empheqbigrvert")
		       ("\\empheqbiglVert"  . "\\empheqbigrVert")
		       ("\\empheqbiglfloor" . "\\empheqbigrfloor")
		       ("\\empheqbiglceil"  . "\\empheqbigrceil"))))
     (dolist (elt delimiters)
       (add-to-list 'TeX-braces-association elt t)))

   ;; 2.2.1 Using multline
   (when (LaTeX-provided-package-options-member "empheq" "oldmultline")
     (LaTeX-add-environments
      '("MTmultlined" LaTeX-mathtools-env-multlined)))

   ;; 2.2.2 The overload option
   ;; I simplify it and ignore the additional feature overload2:
   (when (or (LaTeX-provided-package-options-member "empheq" "overload")
	     (LaTeX-provided-package-options-member "empheq" "overload2"))
     (LaTeX-add-environments
      '("align"      LaTeX-empheq-env-overload)
      '("alignat"    LaTeX-empheq-env-overload)
      '("equation"   LaTeX-empheq-env-overload)
      '("flalign"    LaTeX-empheq-env-overload)
      '("gather"     LaTeX-empheq-env-overload)
      '("multline"   LaTeX-empheq-env-overload)
      '("align*"     LaTeX-env-args [TeX-arg-key-val LaTeX-empheq-key-val-options-local])
      '("alignat*"   LaTeX-empheq-env-overload)
      '("equation*"  LaTeX-env-args [TeX-arg-key-val LaTeX-empheq-key-val-options-local])
      '("flalign*"   LaTeX-env-args [TeX-arg-key-val LaTeX-empheq-key-val-options-local])
      '("gather*"    LaTeX-env-args [TeX-arg-key-val LaTeX-empheq-key-val-options-local])
      '("multline*"  LaTeX-env-args [TeX-arg-key-val LaTeX-empheq-key-val-options-local])

      ;; Original definitions are stored prefixed with "AmS"
      '("AmSalign"      LaTeX-env-label)
      '("AmSalignat"    LaTeX-amsmath-env-alignat)
      '("AmSequation"   LaTeX-env-label)
      '("AmSflalign"    LaTeX-env-label)
      '("AmSgather"     LaTeX-env-label)
      '("AmSmultline"   LaTeX-env-label)
      '("AmSalign*")
      '("AmSalignat*"   LaTeX-amsmath-env-alignat)
      '("AmSequation*")
      '("AmSflalign*")
      '("AmSgather*")
      '("AmSmultline*"))

     ;; Append original definitions to `LaTeX-label-alist'
     (let ((envs '("AmSalign"
		   "AmSalignat"
		   "AmSequation"
		   "AmSflalign"
		   "AmSgather"
		   "AmSmultline")))
       (dolist (env envs)
	 (add-to-list 'LaTeX-label-alist `(,env . LaTeX-amsmath-label) t)))

     ;; RefTeX support: Add original definitions with `reftex-add-label-environments'
     (when (fboundp 'reftex-add-label-environments)
       (let ((envs '(("AmSalign"     ?e nil nil eqnarray-like)
		     ("AmSequation"  ?e nil nil t)
		     ("AmSgather"    ?e nil nil eqnarray-like)
		     ("AmSmultline"  ?e nil nil t)
		     ("AmSflalign"   ?e nil nil eqnarray-like)
		     ("AmSalignat"   ?e nil nil alignat-like))))
	 (dolist (env envs)
	   (reftex-add-label-environments `(,env)))))

     ;; Append original definitions to `LaTeX-item-list'; functions
     ;; are provided by amsmath.el
     (let ((envs '(("AmSalign" . LaTeX-item-equation)
		   ("AmSalign*" . LaTeX-item-equation)
		   ("AmSflalign" . LaTeX-item-equation)
		   ("AmSalignat" . LaTeX-item-equation-alignat)
		   ("AmSalignat*" . LaTeX-item-equation-alignat)
		   ("AmSflalign*" . LaTeX-item-equation)
		   ("AmSgather" . LaTeX-item-equation)
		   ("AmSgather*" . LaTeX-item-equation)
		   ("AmSmultline" . LaTeX-item-equation)
		   ("AmSmultline*" . LaTeX-item-equation))))
       (dolist (env envs)
	 (add-to-list 'LaTeX-item-list env t)))

     ;; Ispell skip lists:
     (TeX-ispell-skip-setcdr
      `(,(cons (concat "\\(AmS\\(?:align\\(?:\\*\\|at\\*?\\)?\\|"
		       "equation\\*?\\|flalign\\*?\\|gather\\*?\\|multline\\*?\\)\\)")
	       (concat "\\\\end{"
		       "\\(AmS\\(?:align\\(?:\\*\\|at\\*?\\)?\\|"
		       "equation\\*?\\|flalign\\*?\\|gather\\*?\\|multline\\*?\\)\\)}")))))

   ;; 3.2 Support for ntheorem
   (LaTeX-add-lengths "mintagvsep")

   ;; 4.1 Creating your own delimiters
   (TeX-add-symbols
    '("DeclareLeftDelimiter"
      [ "Space adjustment" ]
      (TeX-arg-eval
       (lambda ()
	 (let ((delim (TeX-read-string (concat "Delimiter: " TeX-esc))))
	   (TeX-add-symbols (concat "empheq" delim)
			    (concat "empheqbig" delim))
	   (LaTeX-add-empheq-declaredelimiters `(,delim "Left"))
	   (LaTeX-empheq-update-key-val-options)
	   (concat TeX-esc delim)))))

    '("DeclareRightDelimiter"
      [ "Space adjustment" ]
      (TeX-arg-eval
       (lambda ()
	 (let ((delim (TeX-read-string (concat "Delimiter: " TeX-esc))))
	   (TeX-add-symbols (concat "empheq" delim)
			    (concat "empheqbig" delim))
	   (LaTeX-add-empheq-declaredelimiters `(,delim "Right"))
	   (LaTeX-empheq-update-key-val-options)
	   (concat TeX-esc delim))))))

   ;; 4.2 Fine-tuning of delimiters
   (LaTeX-add-lengths "EmphEqdelimitershortfall")
   (LaTeX-add-counters "EmphEqdelimiterfactor")

   (TeX-add-symbols
    ;; 4.3 Scaling material yourself
    '("EmphEqdisplayheight" 0)
    '("EmphEqdisplaydepth"  0)
    ;; 6.1 New empheq-like environments
    '("EmphEqMainEnv" 0)
    '("endEmphEqMainEnv" 0))

   ;; Fontification
   (when (and (featurep 'font-latex)
	      (eq TeX-install-font-lock 'font-latex-setup))
     (font-latex-add-keywords '(("empheqset"             "{")
				("DeclareLeftDelimiter"  "[{")
				("DeclareRightDelimiter" "[{"))
			      'function)
     ;; Append our addition so that we don't interfere with user customizations
     (make-local-variable 'font-latex-math-environments)
     (add-to-list 'font-latex-math-environments "empheq" t)
     (when (or (LaTeX-provided-package-options-member "empheq" "overload")
	       (LaTeX-provided-package-options-member "empheq" "overload2"))
       (let ((envs '(;; Do not insert the starred versions here;
		     ;; function `font-latex-match-math-envII' takes
		     ;; care of it
		     "AmSalign"
		     "AmSalignat"
		     "AmSequation"
		     "AmSflalign"
		     "AmSgather"
		     "AmSmultline")))
	 (dolist (env envs)
	   (add-to-list 'font-latex-math-environments env t))))))
 LaTeX-dialect)

;;; empheq.el ends here
