;;; minted.el --- AUCTeX style for `minted.sty' (v2.4.1)

;; Copyright (C) 2014-2017 Free Software Foundation, Inc.

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

;; This file adds support for `minted.sty' (v2.4.1) from 2016/10/31.

;;; Code:

(require 'tex)

(defvar LaTeX-minted-key-val-options
  '(("autogobble" ("true" "false"))
    ("baselinestretch" ("auto"))
    ("beameroverlays" ("true" "false"))
    ("breakafter")
    ("breakaftergroup" ("true" "false"))
    ("breakaftersymbolpre")
    ("breakaftersymbolpost")
    ("breakanywhere" ("true" "false"))
    ("breakanywheresymbolpre")
    ("breakanywheresymbolpost")
    ("breakautoindent" ("true" "false"))
    ("breakbefore")
    ("breakbeforegroup" ("true" "false"))
    ("breakbeforesymbolpre")
    ("breakbeforesymbolpost")
    ("breakbytoken" ("true" "false"))
    ("breakbytokenanywhere" ("true" "false"))
    ("breakindent")
    ("breakindentnchars")
    ("breaklines" ("true" "false"))
    ("breaksymbol")
    ("breaksymbolleft")
    ("breaksymbolright")
    ("breaksymbolindent")
    ("breaksymbolindentnchars")
    ("breaksymbolindentleft")
    ("breaksymbolindentleftnchars")
    ("breaksymbolindentright")
    ("breaksymbolseprightnchars")
    ("breaksymbolsep")
    ("breaksymbolsepnchars")
    ("breaksymbolsepleft")
    ("breaksymbolsepleftnchars")
    ("breaksymbolsepright")
    ("breaksymbolseprightnchars")
    ("bgcolor")
    ("codetagify")
    ("curlyquotes" ("true" "false"))
    ("encoding")
    ("escapeinside")
    ("firstline")
    ("firstnumber" ("auto" "last" "integer"))
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
    ("highlightcolor")
    ("highlightlines")
    ("keywordcase" ("lower" "upper" "capitalize"))
    ("label")
    ("labelposition" ("none" "topline" "bottomline" "all"))
    ("lastline")
    ("linenos" ("true" "false"))
    ("numberfirstline" ("true" "false"))
    ("numbers" ("left" "right" "both" "none"))
    ("mathescape" ("true" "false"))
    ("numberblanklines" ("true" "false"))
    ("numbersep")
    ("obeytabs" ("true" "false"))
    ("outencoding")
    ("python3" ("true" "false"))
    ("resetmargins" ("true" "false"))
    ("rulecolor")
    ("samepage" ("true" "false"))
    ("showspaces" ("true" "false"))
    ("showtabs" ("true" "false"))
    ("space")
    ("spacecolor")
    ("startinline" ("true" "false"))
    ;; FIXME: It would be nice to use the function
    ;; `LaTeX-minted-style-list' here, but with a file local var like:
    ;;     %%% TeX-command-extra-options: "-shell-escape"
    ;; in a .tex file, Emacs asks to apply a variable which is not
    ;; safe and does not restore the frame; the splitted frame
    ;; remains.  I couldn't figure out why, so for now, I add the
    ;; styles from Pygments version 2.1.3 here.
    ("style" ("colorful" "default" "emacs" "friendly" "fruity" "igor"
	      "lovelace" "manni" "monokai" "murphy" "native"
	      "paraiso-dark" "paraiso-light" "pastie" "perldoc"
	      "rrt" "tango" "trac" "vim" "vs" "xcode"))
    ("stepnumber")
    ("stepnumberfromfirst")
    ("stepnumberoffsetvalues" ("true" "false"))
    ("stripall" ("true" "false"))
    ("stripnl" ("true" "false"))
    ("tab")
    ("tabcolor")
    ("tabsize")
    ("texcl" ("true" "false"))
    ("texcomments" ("true" "false"))
    ("xleftmargin")
    ("xrightmargin"))
  "Key=value options for minted macros and environments.")

(defvar LaTeX-minted-key-val-options-local nil
  "Buffer-local key=value options for minted macros and environments.")
(make-variable-buffer-local 'LaTeX-minted-key-val-options-local)

(defvar LaTeX-minted-pygmentize-program (executable-find "pygmentize"))

(defvar LaTeX-minted-language-list nil
  "List containing languages provided by pymentize program.")

(defun LaTeX-minted-language-list (&rest _ignored)
  "Return a list of languages provided by pymentize program.
Update the variable `LaTeX-minted-language-list' if still nil."
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
	    (setq LaTeX-minted-language-list languages))
	  LaTeX-minted-language-list))))

(defun LaTeX-arg-minted-language (optional &optional prompt)
    "Insert a selected pygmentize language as argument for macros from minted.sty.
If OPTIONAL is non-nil, insert it as optional argument in
brackets.  PROMPT replaces the standard one."
  (TeX-argument-insert
   (completing-read (TeX-argument-prompt optional prompt "Language")
		    (LaTeX-minted-language-list))
   optional))

(defvar LaTeX-minted-style-list nil
  "List containing styles provided by pymentize program.")

(defun LaTeX-minted-style-list (&rest _ignored)
  "Return a list of styles provided by pymentize program.
Update the variable `LaTeX-minted-style-list' if still nil."
  (or LaTeX-minted-style-list
      (when LaTeX-minted-pygmentize-program
	(with-temp-buffer
	  (shell-command (concat LaTeX-minted-pygmentize-program " -L styles")
			 (current-buffer))
	  (goto-char (point-min))
	  (let (styles)
	    (while (re-search-forward "^\\*[[:space:]]\\([^:]+\\):" nil t)
	      (dolist (style (split-string (match-string 1) "[[:space:],]" t))
		(push style styles)))
	    (setq LaTeX-minted-style-list styles))
	  LaTeX-minted-style-list))))

(defun LaTeX-arg-minted-style (optional &optional prompt)
  "Insert a selected pygmentize style as argument for macros from minted.sty.
If OPTIONAL is non-nil, insert it as optional argument in
brackets.  PROMPT replaces the standard one."
  (TeX-argument-insert
   (completing-read (TeX-argument-prompt optional prompt "Style")
		    (LaTeX-minted-style-list))
   optional))

(defun LaTeX-minted-update-key-vals ()
  "Update color related key-vals in `LaTeX-minted-key-val-options-local'.
This function checks if one of the packages \"xcolor.sty\" or
\"xcolor.sty\" is loaded and appends defined colors as values to
color related key.  \"xcolor.sty\" is preferred if both packages
are loaded."
  (when (or (member "xcolor" (TeX-style-list))
	    (member "color" (TeX-style-list)))
    (let* ((colorcmd (if (member "xcolor" (TeX-style-list))
			 #'LaTeX-xcolor-definecolor-list
		       #'LaTeX-color-definecolor-list))
	   (colorkeys '("bgcolor" "highlightcolor"
			"rulecolor" "spacecolor" "tabcolor"))
	   (opts (copy-alist LaTeX-minted-key-val-options-local)))
      (dolist (key colorkeys)
	(setq opts (assq-delete-all (car (assoc key opts)) opts))
	(push (list key (mapcar #'car (funcall colorcmd)))
	      opts))
      (setq LaTeX-minted-key-val-options-local
	    (copy-alist opts)))))

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
	LaTeX-minted-auto-newmintedfile nil
	LaTeX-minted-language-list      nil
	LaTeX-minted-style-list         nil))

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
			 '(TeX-arg-key-val LaTeX-minted-key-val-options-local)))
      (add-to-list 'LaTeX-indent-environment-list `(,env current-indentation) t)
      (add-to-list 'LaTeX-indent-environment-list `(,env* current-indentation) t)
      (add-to-list 'LaTeX-verbatim-environments-local env)
      (add-to-list 'LaTeX-verbatim-environments-local env*)))
  ;; \newmint{foo}{opts} => \foo[key=vals]|code|
  ;; \newmint[macname]{foo}{opts} => \macname[key=vals]|code|
  (dolist (name-lang LaTeX-minted-auto-newmint)
    (let ((lang (if (> (length (car name-lang)) 0)
		    (car name-lang)
		  (cadr name-lang))))
      (add-to-list 'TeX-auto-symbol
		   `(,lang [ TeX-arg-key-val LaTeX-minted-key-val-options-local ]
			   TeX-arg-verb))
      (add-to-list 'LaTeX-verbatim-macros-with-delims-local lang)
      (when (and (fboundp 'font-latex-add-keywords)
		 (fboundp 'font-latex-update-font-lock)
		 (eq TeX-install-font-lock 'font-latex-setup))
	(font-latex-add-keywords `((,lang "[")) 'textual))))
  ;; \newmintinline{foo}{opts} => \fooinline[key=vals]|code| or
  ;;                              \fooinline[key=vals]{code}
  ;; \newmintinline[macname]{foo}{opts} => \macname[key=vals]|code| or
  ;;                                       \macname[key=vals]{code}
  (dolist (name-lang LaTeX-minted-auto-newmintinline)
    (let ((lang (if (> (length (car name-lang)) 0)
		    (car name-lang)
		  (concat (cadr name-lang) "inline"))))
      (add-to-list 'TeX-auto-symbol
		   `(,lang [ TeX-arg-key-val LaTeX-minted-key-val-options-local ]
			  TeX-arg-verb))
      (add-to-list 'LaTeX-verbatim-macros-with-delims-local lang)
      (add-to-list 'LaTeX-verbatim-macros-with-braces-local lang)
      (when (and (fboundp 'font-latex-add-keywords)
		 (fboundp 'font-latex-update-font-lock)
		 (eq TeX-install-font-lock 'font-latex-setup))
	(font-latex-add-keywords `((,lang "[")) 'textual))))
  ;; \newmintedfile{foo}{opts} => \foofile[key=vals]{file-name}
  ;; \newmintedfile[macname]{foo}{opts} => \macname[key=vals]{file-name}
  (dolist (name-lang LaTeX-minted-auto-newmintedfile)
    (let ((lang (if (> (length (car name-lang)) 0)
		    (car name-lang)
		  (concat (cadr name-lang) "file"))))
      (add-to-list 'TeX-auto-symbol
		   `(,lang [ TeX-arg-key-val LaTeX-minted-key-val-options-local ]
			   TeX-arg-file))))
  (when (and (fboundp 'font-latex-update-font-lock)
	     (eq TeX-install-font-lock 'font-latex-setup))
    ;; Refresh font-locking so that the verbatim envs take effect.
    (font-latex-update-font-lock t))
  ;; Also update the key=vals
  (LaTeX-minted-update-key-vals))

(add-hook 'TeX-auto-prepare-hook #'LaTeX-minted-auto-prepare t)
(add-hook 'TeX-auto-cleanup-hook #'LaTeX-minted-auto-cleanup t)
(add-hook 'TeX-update-style-hook #'TeX-auto-parse t)

(defun LaTeX-minted-add-syntactic-keywords-extra (type macro)
  "Add MACRO from minted.sty to `font-latex-syntactic-keywords-extra'.
TYPE is one of the symbols `brace' or `delim' indicating how
verbatim text is enclosed after the macro.  MACRO is a string or
a list of strings."
  (let ((syntax (if (eq type 'brace)
		    '((1 "|") (2 "|"))
		  '((1 "\"") (2 ".") (3 "\""))))
	regexp)
    (when (listp macro)
      (setq macro (regexp-opt macro "\\(?:")))
    (setq regexp `(,(concat
		     ;; The backslash
		     (regexp-quote TeX-esc)
		     ;; Name of the macro(s)
		     macro
		     ;; The optional argument
		     "\\(?:\\[[^][]*\\(?:\\[[^][]*\\][^][]*\\)*\\]\\)?"
		     ;; The first mandatory argument
		     "\\(?:{[^}]+}\\)"
		     ;; With 'brace, allow braced sub-groups otherwise
		     ;; we stop matching too early.  With 'delim, copy
		     ;; font-latex.el:
		     (if (eq type 'brace)
			 (concat "\\({\\)"
				   "\\(?:[^}{]*"
				     "\\(?:{[^}{]*"
				       "\\(?:{[^}{]*"
					 "\\(?:{[^}{]*}[^}{]*\\)*"
				       "}[^}{]*\\)*"
				     "}[^}{]*\\)*"
				   "\\)"
				 "\\(}\\)")
		       (concat
			;; Opening delimiter
			"\\([^a-z@*\n\f{]\\).*?"
			;; Closing delimiter
			"\\(" (regexp-quote TeX-esc) "*\\)\\(\\1\\)")))))
    (add-to-list 'font-latex-syntactic-keywords-extra (append regexp syntax))))

(TeX-add-style-hook
 "minted"
 (lambda ()

   ;; Activate local-version of key=vals
   (setq LaTeX-minted-key-val-options-local
	 (copy-alist LaTeX-minted-key-val-options))

   ;; New symbols
   (TeX-add-symbols
    '("mint"
      [ TeX-arg-key-val LaTeX-minted-key-val-options-local ]
      LaTeX-arg-minted-language TeX-arg-verb)
    '("mintinline"
      [ TeX-arg-key-val LaTeX-minted-key-val-options-local ]
      LaTeX-arg-minted-language TeX-arg-verb)
    '("newminted" ["Environment Name"] LaTeX-arg-minted-language
      (TeX-arg-key-val LaTeX-minted-key-val-options-local))
    '("newmint" ["Macro Name"] LaTeX-arg-minted-language
      (TeX-arg-key-val LaTeX-minted-key-val-options-local))
    '("newmintinline" ["Macro Name"] LaTeX-arg-minted-language
      (TeX-arg-key-val LaTeX-minted-key-val-options-local))
    '("newmintedfile" ["Macro Name"] LaTeX-arg-minted-language
      (TeX-arg-key-val LaTeX-minted-key-val-options-local))
    ;; 3.3 Formatting source code
    '("inputminted"
      [ TeX-arg-key-val LaTeX-minted-key-val-options-local ]
      (LaTeX-arg-minted-language)
      TeX-arg-file)
    ;; 3.4 Using different styles
    '("usemintedstyle"
      [ LaTeX-arg-minted-language ] LaTeX-arg-minted-style)
    ;; 5.2 Macro option usage
    '("setminted"
      [ LaTeX-arg-minted-language ]
      (TeX-arg-key-val LaTeX-minted-key-val-options-local))
    '("setmintedinline"
      [ LaTeX-arg-minted-language ]
      (TeX-arg-key-val LaTeX-minted-key-val-options-local)))

   ;; New environments
   (LaTeX-add-environments
    '("minted" LaTeX-env-args [TeX-arg-key-val LaTeX-minted-key-val-options-local]
      LaTeX-arg-minted-language))

   ;; 4 Floating listings: If option "newfloat" is given, run the
   ;; style hook and use the interface provided by the style,
   ;; otherwise add "listing" manually
   (if (or (LaTeX-provided-package-options-member "minted" "newfloat")
	   (LaTeX-provided-package-options-member "minted" "newfloat=true"))
       (progn
	 (TeX-run-style-hooks "newfloat")
	 (LaTeX-add-newfloat-DeclareFloatingEnvironments
	  '("listing" "verbatim")))
     (LaTeX-add-environments '("listing" ["Float Position"]))
     (TeX-add-symbols '("listoflistings")
		      '("listingscaption")
		      '("listoflistingscaption"))
     (add-to-list (make-local-variable 'LaTeX-indent-environment-list)
		  '("listing" current-indentation) t)
     (add-to-list 'LaTeX-label-alist '("listing" . LaTeX-listing-label) t)
     (when (fboundp 'reftex-add-label-environments)
       (reftex-add-label-environments
	'(("listing" ?l "lst:" "~\\ref{%s}" caption nil nil)))))

   ;; Add to the auto parser
   (TeX-auto-add-regexp LaTeX-minted-newminted-regexp)
   (TeX-auto-add-regexp LaTeX-minted-newmint-regexp)
   (TeX-auto-add-regexp LaTeX-minted-newmintinline-regexp)
   (TeX-auto-add-regexp LaTeX-minted-newmintedfile-regexp)

   ;; Filling
   (add-to-list (make-local-variable 'LaTeX-indent-environment-list)
		'("minted" current-indentation) t)
   (add-to-list 'LaTeX-verbatim-environments-local "minted")

   ;; Fontification
   (when (and (fboundp 'font-latex-add-keywords)
	      (fboundp 'font-latex-update-font-lock)
	      (eq TeX-install-font-lock 'font-latex-setup))
     (font-latex-add-keywords '(("usemintedstyle"  "[{")
				("setminted"       "[{")
				("setmintedinline" "[{")
				("newminted"       "[{{")
				("newmint"         "[{{")
				("newmintinline"   "[{{")
				("newmintedfile"   "[{{"))
			      'function)
     (font-latex-add-keywords '(("inputminted" "[{{")
				("mint"        "[{")
				("mintinline"  "[{"))
			      'textual)
     ;; Add \mint & \mintinline to
     ;; `font-latex-syntactic-keywords-extra' and cater for their
     ;; special syntax: \mint[optional]{lang}{verbatim} or
     ;;                 \mint[optional]{lang}|verbatim|
     (LaTeX-minted-add-syntactic-keywords-extra 'brace
						'("mint" "mintinline"))
     (LaTeX-minted-add-syntactic-keywords-extra 'delim
						'("mint" "mintinline"))
     ;; Tell font-lock about the update.
     (font-latex-update-font-lock t)))
 LaTeX-dialect)

(defvar LaTeX-minted-package-options '("chapter"     "cache"
				       "cachedir"    "finalizecache"
				       "frozencache" "draft"
				       "final"       "kpsewhich"
				       "langlinenos" "newfloat"
				       "outputdir"   "section")
  "Package options for the minted package.")

;;; minted.el ends here
