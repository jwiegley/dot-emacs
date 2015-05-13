;;; minted.el --- AUCTeX style for `minted.sty'

;; Copyright (C) 2014, 2015 Free Software Foundation, Inc.

;; Author: Tassilo Horn <tsdh@gnu.org>
;; Maintainer: auctex-devel@gnu.org
;; Created: 2014-12-19
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

;; This file adds support for `minted.sty'.

;;; Code:

(require 'tex)

(defvar LaTeX-minted-key-val-options
  '(("autogobble" ("true" "false"))
    ("baselinestretch" ("auto"))
    ("bgcolor")
    ("codetagify")
    ("encoding")
    ("outencoding")
    ("firstline")
    ("firstnumber" ("auto"))
    ("fontfamily" ("tt" "courier" "helvetica"))
    ("fontseries" ("auto"))
    ("fontsize" ("auto" "\\tiny" "\\large" "\\scriptsize" "\\Large"
		 "\\footnotesize" "\\LARGE" "\\small" "\\huge"
		 "\\normalsize" "\\Huge"))
    ("fontshape" ("auto"))
    ("formatcom")
    ("frame" ("none" "leftline" "topline" "bottomline" "lines" "single"))
    ("framerule")
    ("framesep")
    ("funcnamehighlighting" ("true" "false"))
    ("gobble")
    ("keywordcase" ("lower" "upper" "capitalize"))
    ("label")
    ("labelposition" ("none" "topline" "bottomline" "all"))
    ("lastline")
    ("linenos" ("true" "false"))
    ("numbers" ("left" "right"))
    ("mathescape" ("true" "false"))
    ("numberblanklines" ("true" "false"))
    ("numbersep")
    ("obeytabs" ("true" "false"))
    ("python3" ("true" "false"))
    ("resetmargins" ("true" "false"))
    ("rulecolor")
    ("samepage" ("true" "false"))
    ("showspaces" ("true" "false"))
    ("showtabs" ("true" "false"))
    ("startinline" ("true" "false"))
    ("style")
    ("stepnumber")
    ("stripnl")
    ("tabsize")
    ("texcl" ("true" "false"))
    ("texcomments" ("true" "false"))
    ("xleftmargin")
    ("xrightmargin"))
  "Key=value options for minted macros and environments.")

(defvar LaTeX-minted-pygmentize-program (executable-find "pygmentize"))

(defvar LaTeX-minted-language-list nil)

(defun LaTeX-minted-language-list (&rest _ignored)
  (or LaTeX-minted-language-list
      (when LaTeX-minted-pygmentize-program
	(with-temp-buffer
	  (shell-command (concat LaTeX-minted-pygmentize-program " -L lexers")
			 (current-buffer))
	  (goto-char (point-min))
	  (let (languages)
	    (while (re-search-forward "^\\*[[:space:]]\\([^:]+\\):" nil t)
	      (dolist (lang (split-string (match-string 1) "[[:space:],]" t))
		(push lang languages)))
	    languages)))))

(defun LaTeX-arg-minted-language (optional &optional prompt)
  (TeX-argument-insert
   (completing-read (TeX-argument-prompt optional prompt "Language")
		    (LaTeX-minted-language-list))
   optional))

(defvar LaTeX-minted-auto-newminted nil)
(defvar LaTeX-minted-newminted-regexp
  '("\\\\newminted\\(?:\\[\\([^]]+\\)\\]\\)?{\\([^}]+\\)}{[^}]*}"
    (1 2) LaTeX-minted-auto-newminted))

(defvar LaTeX-minted-auto-newmint nil)
(defvar LaTeX-minted-newmint-regexp
  '("\\\\newmint\\(?:\\[\\([^]]+\\)\\]\\)?{\\([^}]+\\)}{[^}]*}"
    (1 2) LaTeX-minted-auto-newmint))

(defvar LaTeX-minted-auto-newmintinline nil)
(defvar LaTeX-minted-newmintinline-regexp
  '("\\\\newmintinline\\(?:\\[\\([^]]+\\)\\]\\)?{\\([^}]+\\)}{[^}]*}"
    (1 2) LaTeX-minted-auto-newmintinline))

(defvar LaTeX-minted-auto-newmintedfile nil)
(defvar LaTeX-minted-newmintedfile-regexp
  '("\\\\newmintedfile\\(?:\\[\\([^]]+\\)\\]\\)?{\\([^}]+\\)}{[^}]*}"
    (1 2) LaTeX-minted-auto-newmintedfile))

(defun LaTeX-minted-auto-prepare ()
  (setq LaTeX-minted-auto-newminted     nil
	LaTeX-minted-auto-newmint       nil
	LaTeX-minted-auto-newmintinline nil
	LaTeX-minted-auto-newmintedfile nil))

(defun LaTeX-minted-auto-cleanup ()
  ;; \newminted{lang}{opts} => new langcode and langcode* envs.
  ;; \newminted[envname]{lang}{opts} => new envname/envname* envs.
  (dolist (name-lang LaTeX-minted-auto-newminted)
    (let* ((env (if (> (length (car name-lang)) 0)
		    (car name-lang)
		  (concat (cadr name-lang) "code")))
	   (env* (concat env "*")))
      (add-to-list 'LaTeX-auto-environment (list env))
      (add-to-list 'LaTeX-auto-environment
		   (list env* 'LaTeX-env-args
			 '(TeX-arg-key-val LaTeX-minted-key-val-options)))
      (add-to-list 'LaTeX-indent-environment-list `(,env current-indentation))
      (add-to-list 'LaTeX-indent-environment-list `(,env* current-indentation))
      (add-to-list 'LaTeX-verbatim-environments-local env)
      (add-to-list 'LaTeX-verbatim-environments-local env*)))
  ;; \newmint{foo}{opts} => \foo|code|
  ;; \newmint[macname]{foo}{opts} => \macname|code|
  (dolist (name-lang LaTeX-minted-auto-newmint)
    (let ((lang (if (> (length (car name-lang)) 0)
		    (car name-lang)
		  (cadr name-lang))))
      (add-to-list 'TeX-auto-symbol lang)
      (add-to-list 'LaTeX-verbatim-macros-with-delims-local lang)))
  ;; \newmintinline{foo}{opts} => \fooinline|code|
  ;; \newmintinline[macname]{foo}{opts} => \macname|code|
  (dolist (name-lang LaTeX-minted-auto-newmintinline)
    (let ((lang (if (> (length (car name-lang)) 0)
		    (car name-lang)
		  (cadr name-lang))))
      (add-to-list 'TeX-auto-symbol lang)
      (add-to-list 'LaTeX-verbatim-macros-with-delims-local (concat lang "inline"))))
  ;; \newmintedfile{foo}{opts} => \foofile{file-name}
  ;; \newmintedfile[macname]{foo}{opts} => \macname{file-name}
  (dolist (name-lang LaTeX-minted-auto-newmintedfile)
    (let ((lang (if (> (length (car name-lang)) 0)
		    (car name-lang)
		  (cadr name-lang))))
      (add-to-list 'TeX-auto-symbol (list lang 'TeX-arg-file))))
  (when (and (fboundp 'font-latex-add-keywords)
	     (fboundp 'font-latex-set-syntactic-keywords)
	     (eq TeX-install-font-lock 'font-latex-setup))
    ;; Refresh font-locking so that the verbatim envs take effect.
    (font-latex-set-syntactic-keywords)
    (setq font-lock-set-defaults nil)
    (font-lock-set-defaults)))

(add-hook 'TeX-auto-prepare-hook #'LaTeX-minted-auto-prepare t)
(add-hook 'TeX-auto-cleanup-hook #'LaTeX-minted-auto-cleanup t)
(add-hook 'TeX-update-style-hook #'TeX-auto-parse t)

(TeX-add-style-hook
 "minted"
 (lambda ()
   ;; New symbols
   (TeX-add-symbols
    '("mint" LaTeX-arg-minted-language TeX-arg-verb)
    '("mintinline" LaTeX-arg-minted-language TeX-arg-verb)
    '("listoflistings")
    '("newminted" ["Environment Name"] LaTeX-arg-minted-language
      (TeX-arg-key-val LaTeX-minted-key-val-options))
    '("newmint" ["Macro Name"] LaTeX-arg-minted-language
      (TeX-arg-key-val LaTeX-minted-key-val-options))
    '("newmintinline" ["Macro Name"] LaTeX-arg-minted-language
      (TeX-arg-key-val LaTeX-minted-key-val-options))
    '("newmintedfile" ["Macro Name"] LaTeX-arg-minted-language
      (TeX-arg-key-val LaTeX-minted-key-val-options)))

   ;; New environments
   (LaTeX-add-environments
    '("minted" LaTeX-env-args [TeX-arg-key-val LaTeX-minted-key-val-options]
      LaTeX-arg-minted-language)
    '("listing" ["Float Position"]))

   ;; Add to the auto parser
   (TeX-auto-add-regexp LaTeX-minted-newminted-regexp)
   (TeX-auto-add-regexp LaTeX-minted-newmint-regexp)
   (TeX-auto-add-regexp LaTeX-minted-newmintinline-regexp)
   (TeX-auto-add-regexp LaTeX-minted-newmintedfile-regexp)

   ;; Filling
   (make-local-variable 'LaTeX-indent-environment-list)
   (add-to-list 'LaTeX-indent-environment-list
		'("minted" current-indentation))
   (add-to-list 'LaTeX-verbatim-environments-local "minted")
   ;; FIXME: That doesn't work because \mintinline has 2 args and only the
   ;; second argument is verbatim.
   ;;(add-to-list 'LaTeX-verbatim-macros-with-delims-local "mintinline")

   ;; Fontification
   (when (and (fboundp 'font-latex-add-keywords)
	      (fboundp 'font-latex-set-syntactic-keywords)
	      (eq TeX-install-font-lock 'font-latex-setup))
     (font-latex-add-keywords '(;; FIXME: Those have the form \mint{lang}|code|
				;; so ideally the verbatim arg should be
				;; recognized.
				"mint" "mintinline")
			      'function)
     ;; For syntactic fontification, e.g. verbatim constructs.
     (font-latex-set-syntactic-keywords)
     ;; Tell font-lock about the update.
     (setq font-lock-set-defaults nil)
     (font-lock-set-defaults)))
 LaTeX-dialect)

(defvar LaTeX-minted-package-options '("section" "chapter" "cache"
				       "outputdir" "cachedir"
				       "langlinenos")
  "Package options for the minted package.")

;;; minted.el ends here
