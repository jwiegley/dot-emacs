;;; ltxtable.el --- AUCTeX style for `ltxtable.sty' (v0.2)

;; Copyright (C) 2015 Free Software Foundation, Inc.

;; Author: Arash Esbati <arash@gnu.org>
;; Maintainer: auctex-devel@gnu.org
;; Created: 2015-03-14
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

;; This file adds support for `ltxtable.sty' (v0.2) from 1995/12/11.
;; `ltxtable.sty' is part of TeXLive.

;;; Code:

(defvar LaTeX-ltxtable-file-regexp
  `(,(concat "\\\\LTXtable"
	     "{\\(?:[^}]+\\)}"
	     "{\\(\\.*[^#}%\\\\\\.\n\r]+\\)\\(\\.[^#}%\\\\\\.\n\r]+\\)?}")
    1 TeX-auto-file)
  "Matches the file argument of \\LTXtable marco from ltxtable package.
The regexp for the 2. argument is the same as for \"input\" and
\"include\" entries in `LaTeX-auto-regexp-list'.")

(TeX-add-style-hook
 "ltxtable"
 (lambda ()
   (TeX-run-style-hooks "tabularx" "longtable")

   (TeX-add-symbols
    '("LTXtable"
      (TeX-arg-length "Width" "1.0\\linewidth")
      (TeX-arg-eval
       (lambda ()
	 (let ((longtable (file-relative-name
			   (read-file-name "File with longtable: "))))
	   (format "%s" longtable))))))

   ;; Make sure that \LTXtable stays in its own line:
   (LaTeX-paragraph-commands-add-locally "LTXtable")

   ;; Tell AUCTeX about a new file-include command:
   (TeX-auto-add-regexp LaTeX-ltxtable-file-regexp)

   ;; Tell RefTeX about a new file-include command: Add
   ;; LTXtable{<width>} as a regexp (without \) to
   ;; `reftex-include-file-commands' and run
   ;; `reftex-compile-variables'.  Do this all only once.
   (when (and (boundp 'reftex-include-file-commands)
	      (not (string-match "LTXtable"
				 (mapconcat #'identity reftex-include-file-commands "|"))))
     (add-to-list 'reftex-include-file-commands "LTXtable{\\(?:[^}]+\\)}" t)
     (reftex-compile-variables))

   ;; Fontification
   (when (and (featurep 'font-latex)
	      (eq TeX-install-font-lock 'font-latex-setup))
     (font-latex-add-keywords '(("LTXtable"  "{{"))
			      'textual)))
 LaTeX-dialect)

(defvar LaTeX-ltxtable-package-options nil
  "Package options for the ltxtable package.")

;;; ltxtable.el ends here
