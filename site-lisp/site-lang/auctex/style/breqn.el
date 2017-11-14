;;; breqn.el --- AUCTeX style for `breqn.sty' (v0.98e)

;; Copyright (C) 2017 Free Software Foundation, Inc.

;; Author: Arash Esbati <arash@gnu.org>
;; Maintainer: auctex-devel@gnu.org
;; Created: 2017-01-06
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

;; This file adds support for `breqn.sty' (v0.98e) from 2017/01/27.
;; `breqn.sty' is part of TeXLive.

;; In breqn documentation, there is the following statement:
;;
;;   9 Various environment options
;;
;;   Use of the normal \label command instead of the label option
;;   works, I think, most of the time (untested).
;;
;; To be on the safe side, a label should be written in the optional
;; argument of an environment as value to the `label' key, e.g.:
;;
;;   \begin{dmath}[label={eq:42}]
;;     ...
;;   \end{dmath}
;;
;; This style achieves this requirement by using the function
;; `LaTeX-env-label-as-keyval'.

;;; Code:

(defvar LaTeX-breqn-key-val-options
  '(("style" ("\\tiny" "\\scriptsize" "\\footnotesize" "\\small"
	      "\\normalsize" "\\large" "\\Large" "\\LARGE"
	      "\\huge" "\\Huge"))
    ("number")
    ("indentstep")
    ("compact")
    ("spread")
    ("frame")
    ("framesep")
    ("background")
    ("color")
    ("breakdepth"))
  "Key=value options for breqn environments.
The keys \"label\" and \"labelprefix\" are omitted.")

(defvar LaTeX-breqn-key-val-options-local nil
  "Buffer-local key=value options for breqn environments.")
(make-variable-buffer-local 'LaTeX-breqn-key-val-options-local)

(defvar LaTeX-breqn-key-val-label-regexp
  `(,(concat
      "\\\\begin{"
      (regexp-opt '("dmath" "dseries" "dgroup" "darray"))
      "}"
      "\\(?:\\[[^][]*"
	"\\(?:{[^}{]*"
	  "\\(?:{[^}{]*"
	    "\\(?:{[^}{]*}[^}{]*\\)*"
	  "}[^}{]*\\)*"
	"}[^][]*\\)*"
      "label[ \t]*=[ \t]*{\\([^}]+\\)}"
      "\\(?:[^]]*\\)*"
      "\\]\\)")
    1 LaTeX-auto-label)
  "Matches the label inside an optional argument after \\begin{<breqn-env's>}.")

(defun LaTeX-breqn-env (env)
  "Insert ENV from breqn package incl. optional key=val argument.
Keys offered for key=val query depend on ENV.  \"label\" and
\"labelprefix\" are omitted."
  (let ((keyvals
	 (TeX-read-key-val t
			   (cond ((or (string= env "dgroup")
				      (string= env "dgroup*"))
				  (append '(("noalign") ("brace"))
					  LaTeX-breqn-key-val-options-local))
				 ((or (string= env "darray")
				      (string= env "darray*"))
				  (append '(("noalign") ("brace") ("cols" ("{}")))
					  LaTeX-breqn-key-val-options-local))
				 (t LaTeX-breqn-key-val-options-local)))))
    (LaTeX-insert-environment env (when (and keyvals
					     (not (string= keyvals "")))
				    (concat LaTeX-optop keyvals LaTeX-optcl)))
    (LaTeX-env-label-as-keyval nil nil keyvals env)))

(defun LaTeX-breqn-update-color-keys ()
  "Update color relevant keys from `LaTeX-breqn-key-val-options-local'."
  (when (or (member "xcolor" (TeX-style-list))
	    (member "color" (TeX-style-list)))
    (let* ((colorcmd (if (member "xcolor" (TeX-style-list))
			 #'LaTeX-xcolor-definecolor-list
		       #'LaTeX-color-definecolor-list))
	   (keys '("color" "background"))
	   (tmp (copy-alist LaTeX-breqn-key-val-options-local)))
      (dolist (x keys)
	(setq tmp (assq-delete-all (car (assoc x tmp)) tmp))
	(push (list x (mapcar #'car (funcall colorcmd))) tmp))
      (setq LaTeX-breqn-key-val-options-local
	    (copy-alist tmp)))))

(add-hook 'TeX-auto-cleanup-hook #'LaTeX-breqn-update-color-keys t)
(add-hook 'TeX-update-style-hook #'TeX-auto-parse t)

(TeX-add-style-hook
 "breqn"
 (lambda ()

   ;; Local version of key-val options
   (setq LaTeX-breqn-key-val-options-local
	 (copy-alist LaTeX-breqn-key-val-options))

   ;; Add breqn to parser:
   (TeX-auto-add-regexp LaTeX-breqn-key-val-label-regexp)

   ;; Tell AUCTeX that we want to prefix the labels with `LaTeX-equation-label':
   (let ((envs '("dmath"  "dseries" "dgroup" "darray")))
     (dolist (env envs)
       (add-to-list 'LaTeX-label-alist `(,env . LaTeX-equation-label) t)))

   ;; For RefTeX, we must distinguish between equation and eqnarray-like:
   ;; breqn env == equivalent -- starred
   ;; dmath     == equation   -- dmath*   == unnumbered
   ;; dseries   == equation   -- dseries* == unnumbered
   ;; dgroup    == align      -- dgroup*  == unnumbered
   ;; darray    == eqnarray   -- darray*  == unnumbered
   (when (fboundp 'reftex-add-label-environments)
     (dolist (env '("dmath" "dseries" "dgroup"))
       (reftex-add-label-environments `((,env ?e nil nil t))))
     (reftex-add-label-environments '(("darray" ?e nil nil eqnarray-like))))

   (LaTeX-add-environments
    '("dmath" LaTeX-breqn-env)
    '("dmath*" LaTeX-breqn-env)
    '("dseries" LaTeX-breqn-env)
    '("dseries*" LaTeX-breqn-env)
    '("dgroup" LaTeX-breqn-env)
    '("dgroup*" LaTeX-breqn-env)
    '("darray" LaTeX-breqn-env)
    '("darray*" LaTeX-breqn-env)
    '("dsuspend"))

   (TeX-add-symbols
    '("condition"  [ "Punctuation mark (default ,)" ] t)
    '("condition*" [ "Punctuation mark (default ,)" ] t)
    '("hiderel" t))

   ;; Fontification
   (when (and (featurep 'font-latex)
	      (eq TeX-install-font-lock 'font-latex-setup)
	      (boundp 'font-latex-math-environments))
     (make-local-variable 'font-latex-math-environments)
     (let ((envs '(;; Do not insert the starred versions here;
		   ;; function `font-latex-match-math-envII' takes
		   ;; care of it
		   "dmath" "dseries" "dgroup" "darray")))
       (dolist (env envs)
	 (add-to-list 'font-latex-math-environments env t)))))
 LaTeX-dialect)

(defvar LaTeX-breqn-package-options nil
  "Package options for the breqn package.")

;;; breqn.el ends here
