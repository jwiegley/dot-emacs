;;; AlegreyaSans.el --- AUCTeX style for `AlegreyaSans.sty' (v2015/10/22)

;; Copyright (C) 2015 Free Software Foundation, Inc.

;; Author: Arash Esbati <esbati'at'gmx.de>
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

;; This file adds support for `AlegreyaSans.sty' (v2015/10/22).
;; `AlegreyaSans.sty' is part of TeXLive.

;;; Code:

(TeX-add-style-hook
 "AlegreyaSans"
 (lambda ()

   ;; Run style hook for packages loaded by AlegreyaSans
   (TeX-run-style-hooks "textcomp")

   ;; Load `fontaxes' or `fontspec' dep. on `type1' option:
   (if (or (LaTeX-provided-package-options-member "AlegreyaSans" "type1")
	   (LaTeX-provided-package-options-member "AlegreyaSans" "type1=true"))
       (TeX-run-style-hooks "fontaxes")
     (TeX-run-style-hooks "fontspec"))

   (TeX-add-symbols
    ;; Should be used in preamble only
    '("useosf")
    ;; Text commands
    '("AlegreyaSans"           -1)
    '("AlegreyaSansLF"         -1)
    '("AlegreyaSansOsF"        -1)
    '("AlegreyaSansTLF"        -1)
    '("AlegreyaSansTOsF"       -1)
    '("AlegreyaSansThin"       -1)
    '("AlegreyaSansLight"      -1)
    '("AlegreyaSansMedium"     -1)
    '("AlegreyaSansExtraBold"  -1)
    '("AlegreyaSansBlack"      -1)
    '("textsu"                  t)  ; superior figures
    '("sufigures"              -1)  ;
    '("textin"                  t)  ; inferior figures
    '("infigures"              -1))

   ;; Fontification
   (when (and (featurep 'font-latex)
	      (eq TeX-install-font-lock 'font-latex-setup))
     (font-latex-add-keywords '(("textsu"    "{")
				("textin"    "{"))
			      'type-command)
     (font-latex-add-keywords '(("AlegreyaSans"           "")
				("AlegreyaSansLF"         "")
				("AlegreyaSansOsF"        "")
				("AlegreyaSansTLF"        "")
				("AlegreyaSansTOsF"       "")
				("AlegreyaSansLight"      "")
				("AlegreyaSansMedium"     "")
				("AlegreyaSansExtraBold"  "")
				("AlegreyaSansBlack"      "")
				("sufigures"              "")
				("infigures"              ""))
			      'type-declaration)))
 LaTeX-dialect)

(defvar LaTeX-AlegreyaSans-package-options-list
  '(("lining"       ("true" "false"))
    ("lf"           ("true" "false"))
    ("oldstyle"     ("true" "false"))
    ("osf"          ("true" "false"))
    ("tabular"      ("true" "false"))
    ("tf"           ("true" "false"))
    ("proportional" ("true" "false"))
    ("pf"           ("true" "false"))
    ("black"        ("true" "false"))
    ("extrabold"    ("true" "false"))
    ("thin"         ("true" "false"))
    ("light"        ("true" "false"))
    ("medium"       ("true" "false"))
    ("type1"        ("true" "false"))
    ("sfdefault"    ("true" "false"))
    ("scaled")
    ("scale"))
  "Package options for the AlegreyaSans package.")

(defun LaTeX-AlegreyaSans-package-options ()
  "Prompt for package options for the AlegreyaSans package."
  (TeX-read-key-val t LaTeX-AlegreyaSans-package-options-list))

;;; AlegreyaSans.el ends here
