;;; fontaxes.el --- AUCTeX style for `fontaxes.sty' version v1.0d

;; Copyright (C) 2014 Free Software Foundation, Inc.

;; Author: Arash Esbati <arash@gnu.org>
;; Maintainer: auctex-devel@gnu.org
;; Created: 2014-10-12
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

;; This file adds support for `fontaxes.sty' version v1.0d from
;; 2014/03/23.  `fontaxes.sty' is part of TeXLive.

;; Thanks to Mosè Giordano for his perceptive comments on
;; implementation of "figureversion".

;;; Code:

(TeX-add-style-hook
 "fontaxes"
 (lambda ()
   (TeX-add-symbols
    ;; Various font shapes
    '("swshape"           -1)  ; swash shape
    '("sscshape"          -1)  ; spaced small caps
    '("fontprimaryshape"   t)
    '("fontsecondaryshape" t)
    '("swdefault"          t)
    '("sscdefault"         t)
    '("ulcdefault"         t)

    ;; Figure versions
    '("figureversion"
      (TeX-arg-eval mapconcat 'identity
                    (TeX-completing-read-multiple
                     "Style, alignment: "
                     '(("text") ("osf")
                       ("lining") ("lf")
                       ("tabular") ("tab")
                       ("proportional") ("prop"))) ","))
    '("txfigures" -1)  ; style: text figures (osf)
    '("lnfigures" -1)  ; style: lining figures
    '("tbfigures" -1)  ; alignment: tabular figures
    '("prfigures" -1)  ; alignment: proportional figures
    '("fontfigurestyle"
      (TeX-arg-eval completing-read "Style: "
                    '(("text") ("lining"))))
    '("fontfigurealignment"
      (TeX-arg-eval completing-read "Alignment: "
                    '(("tabular") ("proportional"))))
    '("fontbasefamily" t)

    ;; Math versions
    '("boldmath"         -1)  ; math weight
    '("unboldmath"       -1)  ;
    '("tabularmath"      -1)  ; math figure alignment
    '("proportionalmath" -1)  ;
    '("mathweight"
      (TeX-arg-eval completing-read "Math weight: "
                    '(("bold") ("normal"))))
    '("mathfigurealignment"
      (TeX-arg-eval completing-read "Math figure alignment: "
                    '(("tabular") ("proportional"))))

    ;; Additional commands
    '("textsw"              t)
    '("textssc"             t)
    '("textulc"             t)
    '("textfigures"         t)
    '("liningfigures"       t)
    '("tabularfigures"      t)
    '("proportionalfigures" t))

   ;; Fontification
   (when (and (featurep 'font-latex)
              (eq TeX-install-font-lock 'font-latex-setup))
     (font-latex-add-keywords '(("textfigures"         "{")
                                ("liningfigures"       "{")
                                ("tabularfigures"      "{")
                                ("proportionalfigures" "{"))
                              'type-command)
     (font-latex-add-keywords '(("textsw"              "{")
                                ("textssc"             "{")
                                ("textulc"             "{"))
                              'bold-command)
     (font-latex-add-keywords '(("swshape"             "")
                                ("sscshape"            ""))
                              'bold-declaration)
     (font-latex-add-keywords '(("figureversion"       "{"))
                              'variable)))
 LaTeX-dialect)

(defvar LaTeX-fontaxes-package-options nil
  "Package options for the fontaxes package.")

;;; fontaxes.el ends here
