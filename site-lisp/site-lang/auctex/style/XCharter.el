;;; XCharter.el --- AUCTeX style for `XCharter.sty' (v1.05)

;; Copyright (C) 2014 Free Software Foundation, Inc.

;; Author: Arash Esbati <arash@gnu.org>
;; Maintainer: auctex-devel@gnu.org
;; Created: 2014-10-30
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

;; This file adds support for `XCharter.sty' (v1.05) from 2014/07/03.
;; `XCharter.sty' is part of TeXLive.

;;; Code:

(TeX-add-style-hook
 "XCharter"
 (lambda ()

   ;; Run style hook for various packages loaded by XCharter
   (TeX-run-style-hooks "textcomp" "fontaxes")

   ;; New symbols
   (TeX-add-symbols

    ;; Only preamble commands
    '("useosf"  0)
    '("useosfI" 0)

    ;; Text commands
    '("textsu"     t)   ; superior figures
    '("sustyle"   -1)   ;
    '("textlf"     t)   ; lining figures
    '("lfstyle"   -1)   ;
    '("textosf"    t)   ; oldstyle figures
    '("textosfI"   t)   ; oldstyle figures alternate
    '("osfstyle"  -1))  ; whatever oldstyle option is in force

   ;; Fontification
   (when (and (featurep 'font-latex)
              (eq TeX-install-font-lock 'font-latex-setup))
     (font-latex-add-keywords '(("textsu"    "{")
                                ("textlf"    "{")
                                ("textosf"   "{")
                                ("textosfI"  "{"))
                              'type-command)
     (font-latex-add-keywords '(("sustyle"   "")
                                ("lfstyle"   "")
                                ("osfstyle"  ""))
                              'type-declaration)))
 LaTeX-dialect)

(defvar LaTeX-XCharter-package-options
  '("lining" "lf" "oldstyle" "osf" "oldstyleI" "osfI"
    "scaled" "sups")
  "Package options for the XCharter package.")

;;; XCharter.el ends here
