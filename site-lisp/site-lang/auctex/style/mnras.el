;;; mnras.el --- AUCTeX style for `mnras.cls' version 3.0.

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

;; This file adds support for `mnras.cls' version 3.0.

;;; Code:

(TeX-add-style-hook
 "mnras"
 (lambda ()
   (if (LaTeX-provided-class-options-member "mnras" "usegraphicx")
       (TeX-run-style-hooks "graphicx"))
   (if (LaTeX-provided-class-options-member "mnras" "usenatbib")
       (TeX-run-style-hooks "natbib"))
   (if (LaTeX-provided-class-options-member "mnras" "usedcolumn")
       (TeX-run-style-hooks "dcolumn"))
   (TeX-run-style-hooks
    "geometry"
    "fixltx2e"
    "hyperref")
   (TeX-add-symbols
    ;; 5  Title page
    '("title" ["Short title"] "Long title")
    '("author" ["Short author(s)"] (LaTeX-arg-author "Long author(s)"))
    "newauthor"
    ;; 7.2  Special symbols
    '("bmath" 1)
    '("mathbfit" 1)
    '("mathbfss" 1)
    ;; 7.2  Special symbols -- Table 1
    "sun"
    "earth"
    "degr"
    "diameter"
    "sq"
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
    ;; 7.2  Special symbols -- Table 2
    "upi"
    "umu"
    "upartial"
    "leqslant"
    "geqslant"
    "la"
    "ga"
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
    ;; 7.3  Ions
    '("ion" 2)
    ;; A  Journal abbreviations -- Table A1 
    "aap"
    "astap"
    "aapr"
    "aaps"
    "actaa"
    "afz"
    "aj"
    "ao"
    "applopt"
    "aplett"
    "apj"
    "apjl"
    "apjlett"
    "apjs"
    "apjsupp"
    "apss"
    "araa"
    "arep"
    "aspc"
    "azh"
    "baas"
    "bac"
    "bain"
    "caa"
    "cjaa"
    "fcp"
    "gca"
    "grl"
    "iaucirc"
    "icarus"
    "japa"
    "jcap"
    "jcp"
    "jgr"
    "jqsrt"
    "jrasc"
    "memras"
    "memsai"
    "mnassa"
    "na"
    "nar"
    "nat"
    "nphysa"
    "pra"
    "prb"
    "prc"
    "prd"
    "pre"
    "prl"
    "pasa"
    "pasp"
    "pasj"
    "physrep"
    "physscr"
    "planss"
    "procspie"
    "rmxaa"
    "qjras"
    "sci"
    "skytel"
    "solphys"
    "sovast"
    "ssr"
    "zap")
   
   (LaTeX-add-environments
    "keywords"
    "proof")

   ;; Fontification
   (when (and (featurep 'font-latex)
	      (eq TeX-install-font-lock 'font-latex-setup))
     (font-latex-add-keywords '(("author" "[{")
				("title" "[{")
				("newauthor"))
			      'function))))

(defvar LaTeX-mnras-class-options
  '("letters"  "onecolumn" "doublespacing" "referee" "galley" "landscape"
    "usenatbib" "usegraphicx" "useAMS" "usedcolumn")
  "Package options for the mnras package.")

;; mnras.el ends here
