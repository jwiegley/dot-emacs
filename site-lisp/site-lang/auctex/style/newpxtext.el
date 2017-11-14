;;; newpxtext.el --- AUCTeX style for `newpxtext.sty' (v1.232)

;; Copyright (C) 2015 Free Software Foundation, Inc.

;; Author: Arash Esbati <arash@gnu.org>
;; Maintainer: auctex-devel@gnu.org
;; Created: 2015-05-02
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

;; This file adds support for `newpxtext.sty' (v1.232) from 2015/04/15.
;; `newpxtext.sty' is part of TeXLive.

;;; Code:

(TeX-add-style-hook
 "newpxtext"
 (lambda ()

   ;; Run style hook for various packages loaded by newpxtext
   (TeX-run-style-hooks "textcomp" "fontaxes")

   ;; New symbols
   (TeX-add-symbols
    '("useosf"          0)  ; Only preamble command
    '("useproportional" 0)  ; Only preamble command
    '("lfstyle"        -1)  ; lf declaration
    '("tlfstyle"       -1)  ; tlf declaration
    '("osfstyle"       -1)  ; osf declaration
    '("tosfstyle"      -1)  ; tosf declaration
    '("sustyle"        -1)  ; sup style declaration
    '("textlf"          t)  ; lf command
    '("texttlf"         t)  ; tlf command
    '("textosf"         t)  ; osf command
    '("texttosf"        t)  ; tosf command
    '("textsu"          t)) ; sup style command

   ;; Fontification
   (when (and (featurep 'font-latex)
              (eq TeX-install-font-lock 'font-latex-setup))
     (font-latex-add-keywords '(("textlf"    "{")
                                ("texttlf"   "{")
                                ("textosf"   "{")
                                ("texttosf"  "{")
				("textsu"    "{"))
                              'type-command)
     (font-latex-add-keywords '(("lfstyle"   "")
                                ("tlfstyle"  "")
                                ("osfstyle"  "")
				("tosfstyle" "")
				("sustyle"   ""))
                              'type-declaration)))
 LaTeX-dialect)

(defvar LaTeX-newpxtext-package-options
  '("defaultsups" "scosf" "largesc"
    "scaled" "helvratio"
    "tighter" "looser" "spacing" "stretch" "shrink"
    "lining" "lf" "oldstyle" "osf" "tabular"
    "p" "proportional" "theoremfont")
  "Package options for the newpxtext package.")

;;; newpxtext.el ends here
