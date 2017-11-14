;;; doc.el --- AUCTeX style for `doc.sty'

;; Copyright (C) 2004, 2008, 2016 Free Software Foundation, Inc.

;; Author: Frank Küster <frank@kuesterei.ch>
;; Maintainer: auctex-devel@gnu.org
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

;; This file adds support for `doc.sty'.

;;; Code:

(defun LaTeX-env-no-comment (environment)
  "Insert ENVIRONMENT and make sure there is no commented empty line inside."
  (LaTeX-insert-environment environment
			    (when (string-equal environment "macro")
			      (let ((macroname (TeX-read-string
						(TeX-argument-prompt nil nil "Macro")
						TeX-esc)))
				(format "{%s}" macroname))))
  (unless (TeX-active-mark)
    (when (save-excursion
	    (beginning-of-line)
	    (looking-at (concat "[ \t]+$\\|[ \t]*"
				TeX-comment-start-regexp "+[ \t]*$")))
      (delete-region (line-beginning-position) (line-end-position))
      (indent-according-to-mode))))

(defun LaTeX-doc-after-insert-macrocode (env start end)
  "Make sure the macrocode environment is properly formatted after insertion."
  (when (TeX-member env '("macro" "macrocode" "macrocode*") 'string-equal)
    (save-excursion
      (goto-char end)
      (skip-chars-backward " \t")
      (when (bolp)
	(insert "%")
	(indent-according-to-mode))
      (goto-char start)
      (skip-chars-backward " \t")
      (when (bolp)
	(insert "%")
	(indent-according-to-mode)))))

(TeX-add-style-hook
 "doc"
 (lambda ()
   (add-to-list (make-local-variable 'LaTeX-indent-environment-list)
		'("macrocode" current-indentation) t)
   (add-to-list 'LaTeX-indent-environment-list
		'("macrocode*" current-indentation) t)
   (add-to-list 'LaTeX-indent-environment-list
		'("macro" current-indentation) t)
   (add-hook 'LaTeX-after-insert-env-hooks 'LaTeX-doc-after-insert-macrocode
	     nil t)
   (LaTeX-add-environments
    "theglossary"
    '("macrocode" LaTeX-env-no-comment)
    '("macrocode*" LaTeX-env-no-comment)
    '("macro" LaTeX-env-no-comment))
   (TeX-add-symbols
    "EnableCrossrefs"
    "DisableCrossrefs"
    '("DoNotIndex" t)
    "DontCheckModules"
    "CheckModules"
    "Module"
    '("DescribeMacro" (TeX-arg-eval
		       (lambda ()
			 (let ((name (TeX-read-string
				      (TeX-argument-prompt optional nil "Macro")
				      TeX-esc)))
			   (format "%s" name)))))
    '("DescribeEnv" "Environment")
    "verbatim"
    "verb"
    '("parg" "Argument")
    '("oarg" "Argument")
    '("marg" "Argument")
    '("meta" "Text")
    '("cs" "Name")
    '("cmd" (TeX-arg-eval
	     (lambda ()
	       (let ((name (TeX-read-string
			    (TeX-argument-prompt optional nil "Name")
			    TeX-esc)))
		 (format "%s" name)))))
    "makelabel"
    '("MacroFont" t)
    '("AltMacroFont" t)
    "PrintMacroName"
    "PrintDescribeMacro"
    "PrintDescribeEnv"
    "PrintEnvName"
    "MakePrivateLetters"
    "actualchar"
    "quotechar"
    "levelchar"
    "encapchar"
    "verbatimchar"
    "SpecialIndex"
    "SpecialMainIndex"
    "SpecialMainEnvIndex"
    "SpecialUsageIndex"
    "SpecialEnvIndex"
    "SortIndex"
    "LeftBraceIndex"
    "RightBraceIndex"
    "PercentIndex"
    "OldMakeindex"
    "PercentIndex"
    "IndexPrologue"
    "IndexParms"
    "subitem"
    "subsubitem"
    "indexspace"
    "efill"
    "pfill"
    "PrintIndex"
    '("changes" "version" TeX-arg-date t)
    "generalname"
    "RecordChanges"
    "GlossaryPrologue"
    "GlossaryParms"
    "PrintChanges"
    "AlsoImplementation"
    '("StopEventually" t)
    "OnlyDescription"
    "Finale"
    "IndexInput"
    "maketitle"
    "MakeShortVerb"
    "DeleteShortVerb"
    "MakeShortverb"
    "DeleteShortverb"
    "CheckSum"
    "CharacterTable"
    "CharTableChanges"
    "CodelineNumbered"
    "CodelineIndex"
    "PageIndex"
    "theCodelineNo"
    "DocstyleParms"
    "MakePercentIgnore"
    "MakePercentComment"
    '("DocInput"
      (TeX-arg-eval
       (lambda ()
	 (let ((file (file-relative-name
		      (read-file-name
		       "File to input: " nil nil nil nil
		       (lambda (x)
			 (string-match "\\.fdd$\\|\\.dtx$" x)))
		      (TeX-master-directory))))
	   (format "%s" file)))))
    '("DocInclude"
      (TeX-arg-eval
       (lambda ()
	 (let ((file (file-relative-name
		      (read-file-name
		       "File to include: " nil nil nil nil
		       (lambda (x)
			 (string-match "\\.fdd$\\|\\.dtx$" x)))
		      (TeX-master-directory))))
	   (format "%s" file)))))
    "GetFileInfo"
    "filename"
    "fileinfo")
   (TeX-run-style-hooks "shortvrb")
   (LaTeX-add-lengths "MacrocodeTopsep" "MacroTopsep" "MacroIndent"))
 LaTeX-dialect)

;; Local Variables:
;; coding: iso-8859-1
;; End:
