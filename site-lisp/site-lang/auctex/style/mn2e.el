;;; mn2e.el --- AUCTeX style for `mn2e.cls' version 2.2.

;; Copyright (C) 2015 Free Software Foundation, Inc.

;; Maintainer: auctex-devel@gnu.org
;; Author: Mosè Giordano <mose@gnu.org>
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

;; This file adds support for `mn2e.cls' version 2.2.

;;; Code:

(TeX-add-style-hook
 "mn2e"
 (lambda ()
   (if (LaTeX-provided-class-options-member "mn2e" "usegraphicx")
       (TeX-run-style-hooks "graphicx"))
   (if (LaTeX-provided-class-options-member "mn2e" "usenatbib")
       (TeX-run-style-hooks "natbib"))
   (if (LaTeX-provided-class-options-member "mn2e" "usedcolumn")
       (TeX-run-style-hooks "dcolumn"))
   (TeX-add-symbols
    ;; 4.5.3 Bold Greek
    "balpha"
    "bbeta"
    "bgamma"
    "bdelta"
    "bepsilon"
    "bzeta"
    "boldeta"
    "btheta"
    "biota"
    "bkappa"
    "blambda"
    "bmu"
    "bnu"
    "bxi"
    "bpi"
    "brho"
    "bsigma"
    "btau"
    "bupsilon"
    "bphi"
    "bchi"
    "bpsi"
    "bomega"
    "bvarepsilon"
    "bvartheta"
    "bvarpi"
    "bvarrho"
    "bvarsigma"
    "bvarphi"
    ;; 4.5.5 Special symbols
    "getsto"
    "cor"
    "lid"
    "gid"
    "sol"
    "sog"
    "lse"
    "gse"
    "grole"
    "leogr"
    "loa"
    "goa"
    "sun"
    "earth"
    "degr"
    "diameter"
    "sq"
    "squareforqed"
    "fd"
    "fh"
    "fm"
    "fs"
    "fdg"
    "farcm"
    "farcs"
    "fp"
    "arcmin"
    "arcsec"
    "micron"
    ;; Authors' notes
    '("title" ["Short title"] "Long title")
    '("author" ["Short author(s)"] (LaTeX-arg-author "Long author(s)"))
    "newauthor"
    "nokeywords"
    "plate"
    "contcaption"
    '("bmath" "Math text")
    '("mathbfss" "Text")
    '("textbfss" "Text")
    '("mathbfit" "Text")
    '("textbfit" "Text")
    ;; Editors' notes
    "pagerange"
    "volume"
    "pubyear"
    "journal"
    "bsp")
   (if (LaTeX-provided-class-options-member "mn2e" "useAMS")
       (TeX-add-symbols
	;; 4.5.4 Upright Greek characters
	"upi"
	"umu"
	"upartial"
	"leqslant"
	"geqslant"
	"la"
	"ga"))
   (LaTeX-add-environments
    "keywords"
    "abstract"
    "proof")
   (LaTeX-add-pagestyles
    "headings"
    "myheadings"
    "titlepage"
    "plate")
   (LaTeX-add-counters
    "part"
    "section"
    "subsection"
    "subsubsection"
    "paragraph"
    "subparagraph"
    "dummy"
    "table"
    "figure")
   (LaTeX-add-lengths
    "realparindent"
    "bibhang")

   ;; Fontification
   (when (and (featurep 'font-latex)
	      (eq TeX-install-font-lock 'font-latex-setup))
     (font-latex-add-keywords '(("author" "[{")
				("title" "[{")
				("newauthor")
				("nokeywords" "{")
				("plate" "{")
				("contcaption" "{")
				("pagerange" "{")
				("volume" "{")
				("pubyear" "{")
				("journal")
				("bsp"))
			      'function)))
 LaTeX-dialect)

(defvar LaTeX-mn2e-class-options
  '("useAMS" "usegraphicx" "usenatbib" "usedcolumn"
    "doublespacing" "galley" "landscape" "letters" "onecolumn" "referee")
  "Package options for the mn2e package.")

;; mn2e.el ends here
