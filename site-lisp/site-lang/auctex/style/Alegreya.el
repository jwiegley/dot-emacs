;;; Alegreya.el --- AUCTeX style for `Alegreya.sty' (v2015/10/22)

;; Copyright (C) 2015 Free Software Foundation, Inc.

;; Author: Arash Esbati <arash@gnu.org>
;; Maintainer: auctex-devel@gnu.org
;; Created: 2015-09-12
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

;; This file adds support for `Alegreya.sty' (v2015/10/22).
;; `Alegreya.sty' is part of TeXLive.

;;; Code:

(TeX-add-style-hook
 "Alegreya"
 (lambda ()

   ;; Run style hook for packages loaded by Alegreya
   (TeX-run-style-hooks "textcomp")

   ;; Load `fontaxes' or `fontspec' dep. on `type1' option:
   (if (or (LaTeX-provided-package-options-member "Alegreya" "type1")
	   (LaTeX-provided-package-options-member "Alegreya" "type1=true"))
       (TeX-run-style-hooks "fontaxes")
     (TeX-run-style-hooks "fontspec"))

   (TeX-add-symbols
    ;; Should be used in preamble only
    '("useosf")
    ;; Text commands
    '("Alegreya"      -1)
    '("AlegreyaBlack" -1)
    '("AlegreyaLF"    -1)
    '("AlegreyaOsF"   -1)
    '("AlegreyaTLF"   -1)
    '("AlegreyaTOsF"  -1)
    '("textsu"         t)  ; superior figures
    '("sufigures"     -1)  ;
    '("textin"         t)  ; inferior figures
    '("infigures"     -1))

   ;; Fontification
   (when (and (featurep 'font-latex)
	      (eq TeX-install-font-lock 'font-latex-setup))
     (font-latex-add-keywords '(("textsu"    "{")
				("textin"    "{"))
			      'type-command)
     (font-latex-add-keywords '(("Alegreya"      "")
				("AlegreyaBlack" "")
				("AlegreyaLF"    "")
				("AlegreyaOsF"   "")
				("AlegreyaTLF"   "")
				("AlegreyaTOsF"  "")
				("sufigures"     "")
				("infigures"     ""))
			      'type-declaration)))
 LaTeX-dialect)

(defvar LaTeX-Alegreya-package-options-list
  '(("lining"       ("true" "false"))
    ("lf"           ("true" "false"))
    ("oldstyle"     ("true" "false"))
    ("osf"          ("true" "false"))
    ("tabular"      ("true" "false"))
    ("tf"           ("true" "false"))
    ("proportional" ("true" "false"))
    ("pf"           ("true" "false"))
    ("black"        ("true" "false"))
    ("type1"        ("true" "false"))
    ("scaled")
    ("scale"))
  "Package options for the Alegreya package.")

(defun LaTeX-Alegreya-package-options ()
  "Prompt for package options for the Alegreya package."
  (TeX-read-key-val t LaTeX-Alegreya-package-options-list))

;;; Alegreya.el ends here
