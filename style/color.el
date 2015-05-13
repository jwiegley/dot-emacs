;;; color.el --- AUCTeX style for `color.sty' (v1.1a)

;; Copyright (C) 2015 Free Software Foundation, Inc.

;; Author: Arash Esbati <esbati'at'gmx.de>
;; Maintainer: auctex-devel@gnu.org
;; Created: 2015-01-16
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

;; This file adds support for `color.sty' (v1.1a) from 2014/10/28.
;; `color.sty' is part of TeXLive.

;; Many thanks to Tassilo Horn for his percetive comments on
;; implementation of this style and testing.

;;; Code:

(defvar LaTeX-color-colour-models
  '("cmyk" "gray" "named" "rgb")
  "List of color models provided by `color.sty'.")

(defvar LaTeX-color-dvipsnames-colors
  '("Apricot"        "Aquamarine"      "Bittersweet"  "Black"
    "Blue"           "BlueGreen"       "BlueViolet"   "BrickRed"
    "Brown"          "BurntOrange"     "CadetBlue"    "CarnationPink"
    "Cerulean"       "CornflowerBlue"  "Cyan"         "Dandelion"
    "DarkOrchid"     "Emerald"         "ForestGreen"  "Fuchsia"
    "Goldenrod"      "Gray"            "Green"        "GreenYellow"
    "JungleGreen"    "Lavender"        "LimeGreen"    "Magenta"
    "Mahogany"       "Maroon"          "Melon"        "MidnightBlue"
    "Mulberry"       "NavyBlue"        "OliveGreen"   "Orange"
    "OrangeRed"      "Orchid"          "Peach"        "Periwinkle"
    "PineGreen"      "Plum"            "ProcessBlue"  "Purple"
    "RawSienna"      "Red"             "RedOrange"    "RedViolet"
    "Rhodamine"      "RoyalBlue"       "RoyalPurple"  "RubineRed"
    "Salmon"         "SeaGreen"        "Sepia"        "SkyBlue"
    "SpringGreen"    "Tan"             "TealBlue"     "Thistle"
    "Turquoise"      "Violet"          "VioletRed"    "White"
    "WildStrawberry" "Yellow"          "YellowGreen"  "YellowOrange")
  "List of colors defined by package option `dvipsnames' from `color.sty'.")

;; Needed for auto-parsing.
(require 'tex)

;; Plug color into the parser -- after that we have the following:
;; 1. LaTeX-auto-color-definecolor: Name of temporary variable used
;; when parsing.
;; 2. LaTeX-add-color-definecolors: Name of function to add
;; information to add to #3.
;; 3. LaTeX-color-definecolor-list: Name of variable holding buffer
;; local information.
;; 4. LaTeX-color-definecolors-changed: Name of variable indicating
;; that #3 has changed.
(TeX-auto-add-type "color-definecolor" "LaTeX")

(defvar LaTeX-color-definecolor-regexp
  '("\\\\definecolor{\\([^}]+\\)}{\\([^}]+\\)}{\\([^}]+\\)}"
    1 LaTeX-auto-color-definecolor)
  "Matches the arguments of `\\definecolor' from `color'
package.")

(defun LaTeX-color-auto-prepare ()
  "Clear `LaTeX-auto-color-definecolor' before parsing."
  (setq	LaTeX-auto-color-definecolor nil))

(defun LaTeX-color-auto-cleanup ()
  "Move parsed colors from `LaTeX-auto-color-definecolor' to
`LaTeX-color-definecolor-list'."
  ;; \definecolor{<name>}{<model>}{<colour-spec>}
  ;; color=<name>, ignored=<model>, ignored=<colour-spec>
  (dolist (color LaTeX-auto-color-definecolor)
    (add-to-list 'LaTeX-color-definecolor-list (list color))))

(add-hook 'TeX-auto-prepare-hook #'LaTeX-color-auto-prepare t)
(add-hook 'TeX-auto-cleanup-hook #'LaTeX-color-auto-cleanup t)
(add-hook 'TeX-update-style-hook #'TeX-auto-parse t)

(defun TeX-arg-color-definecolor (optional &optional prompt)
  "Insert arguments of `\\definecolor' from `color.sty'."
  ;; \definecolor{<name>}{<model>}{<color spec>}
  ;; Ask for <name>, add to our list and insert it
  (let ((colorname (TeX-read-string "Color name: ")))
    (LaTeX-add-color-definecolors colorname)
    (TeX-argument-insert colorname optional))
  ;; Ask and insert <model>
  (let ((model (completing-read
		(TeX-argument-prompt optional prompt "Color model")
		(if (not (or (LaTeX-provided-package-options-member "color" "dvips")
			     (LaTeX-provided-package-options-member "color" "dvipsnames")))
		    (remove "named" LaTeX-color-colour-models)
		  LaTeX-color-colour-models))))
    (TeX-argument-insert model optional)
    ;; Depending on <model>, ask for <color spec> and insert it
    (cond (;; <cmyk> model
	   (string-equal model "cmyk")
	   (let ((cyan    (TeX-read-string "Value Cyan (between 0,1): "))
		 (magenta (TeX-read-string "Value Magenta (between 0,1): "))
		 (yellow  (TeX-read-string "Value Yellow (between 0,1): "))
		 (black   (TeX-read-string "Value Black (between 0,1): ")))
	     (TeX-argument-insert
	      (concat cyan "," magenta "," yellow "," black) optional)))
	  ;; <rgb> model
	  ((string-equal model "rgb")
	   (let ((red   (TeX-read-string "Value Red (between 0,1): "))
		 (green (TeX-read-string "Value Green (between 0,1): "))
		 (blue  (TeX-read-string "Value Blue (between 0,1): ")))
	     (TeX-argument-insert
	      (concat red "," green "," blue) optional)))
	  ;; <gray> model
	  ((string-equal model "gray")
	   (let ((grayness (TeX-read-string "Value Gray (between 0,1): ")))
	     (TeX-argument-insert grayness optional)))
	  ;; <named> model takes the dvipsnames
	  ((string-equal model "named")
	   (let ((color (completing-read "Named Color: "
					 LaTeX-color-dvipsnames-colors)))
	     (TeX-argument-insert color optional))))))

(defun TeX-arg-color (optional &optional prompt)
  "Insert arguments of various color commands from `color.sty'."
  ;; \color{<name>} or \color[<model>]{<color spec>}
  ;; First, ask for <model>.  `named' is removed here from completion
  ;; if package option is not given
  (let ((model (completing-read
		(TeX-argument-prompt t prompt "Color model")
		(if (not (or (LaTeX-provided-package-options-member "color" "dvips")
			     (LaTeX-provided-package-options-member "color" "dvipsnames")))
		    (remove "named" LaTeX-color-colour-models)
		  LaTeX-color-colour-models))))
    (if (string-equal model "")
	;; if empty, ask for <name> with completion
	(let ((color (completing-read
		      (TeX-argument-prompt optional prompt "Color name")
		      (LaTeX-color-definecolor-list))))
	  (TeX-argument-insert color optional))
      ;; if not empty, insert [<model>] and proceed
      (insert (concat LaTeX-optop model LaTeX-optcl))
      (cond (;; <cmyk> model
	     (string-equal model "cmyk")
	     (let ((cyan    (TeX-read-string "Value Cyan (between 0,1): "))
		   (magenta (TeX-read-string "Value Magenta (between 0,1): "))
		   (yellow  (TeX-read-string "Value Yellow (between 0,1): "))
		   (black   (TeX-read-string "Value Black (between 0,1): ")))
	       (TeX-argument-insert
		(concat cyan "," magenta "," yellow "," black) optional)))
	    ;; <rgb> model
	    ((string-equal model "rgb")
	     (let ((red   (TeX-read-string "Value Red (between 0,1): "))
		   (green (TeX-read-string "Value Green (between 0,1): "))
		   (blue  (TeX-read-string "Value Blue (between 0,1): ")))
	       (TeX-argument-insert
		(concat red "," green "," blue) optional)))
	    ;; <gray> model
	    ((string-equal model "gray")
	     (let ((grayness (TeX-read-string "Value Gray (between 0,1): ")))
	       (TeX-argument-insert grayness optional)))
	    ;; <named> model; allowed are dvipsnames.
	    ((string-equal model "named")
	     (let ((color (completing-read "Named Color: "
					   LaTeX-color-dvipsnames-colors)))
	       (TeX-argument-insert color optional)))))))

(defun TeX-arg-color-fcolorbox (optional &optional prompt)
  "Insert arguments of `\\fcolorbox' from `color.sty'. "
  ;; \fcolorbox{<frame color name>}{<box color name>}{<text>} or
  ;; \fcolorbox[<model>]{<frame color spec>}{<box color spec>}{<text>}
  ;; First, ask for <model>; remove `named' again
  (let ((model (completing-read
		(TeX-argument-prompt t prompt "Color model")
		(if (not (or (LaTeX-provided-package-options-member "color" "dvips")
			     (LaTeX-provided-package-options-member "color" "dvipsnames")))
		    (remove "named" LaTeX-color-colour-models)
		  LaTeX-color-colour-models))))
    (if (string-equal model "")
	;; if empty, ask for <frame color spce> with completion
	(let ((frame-color (completing-read
			    (TeX-argument-prompt optional prompt "Frame color name")
			    (LaTeX-color-definecolor-list)))
	      (box-color   (completing-read
			    (TeX-argument-prompt optional prompt "Box color name")
			    (LaTeX-color-definecolor-list))))
	  (TeX-argument-insert frame-color optional)
	  (TeX-argument-insert box-color   optional))
      ;; if not empty, insert [<model>] and cater for 2 mandatory args.
      (insert (concat LaTeX-optop model LaTeX-optcl))
      (cond (;; <cmyk> model
	     (string-equal model "cmyk")
	     (let ((cyan    (TeX-read-string "Frame value Cyan (between 0,1): "))
		   (magenta (TeX-read-string "Frame value Magenta (between 0,1): "))
		   (yellow  (TeX-read-string "Frame value Yellow (between 0,1): "))
		   (black   (TeX-read-string "Frame value Black (between 0,1): ")))
	       (TeX-argument-insert
		(concat cyan "," magenta "," yellow "," black) optional))
	     (let ((cyan    (TeX-read-string "Box value Cyan (between 0,1): "))
		   (magenta (TeX-read-string "Box value Magenta (between 0,1): "))
		   (yellow  (TeX-read-string "Box value Yellow (between 0,1): "))
		   (black   (TeX-read-string "Box value Black (between 0,1): ")))
	       (TeX-argument-insert
		(concat cyan "," magenta "," yellow "," black) optional)))
	    ;; <rgb> model
	    ((string-equal model "rgb")
	     (let ((red   (TeX-read-string "Frame value Red (between 0,1): "))
		   (green (TeX-read-string "Frame value Green (between 0,1): "))
		   (blue  (TeX-read-string "Frame value Blue (between 0,1): ")))
	       (TeX-argument-insert
		(concat red "," green "," blue) optional))
	     (let ((red   (TeX-read-string "Box value Red (between 0,1): "))
		   (green (TeX-read-string "Box value Green (between 0,1): "))
		   (blue  (TeX-read-string "box value Blue (between 0,1): ")))
	       (TeX-argument-insert
		(concat red "," green "," blue) optional)))
	    ;; <gray> model
	    ((string-equal model "gray")
	     (let ((grayness (TeX-read-string "Frame value Gray (between 0,1): ")))
	       (TeX-argument-insert grayness optional))
	     (let ((grayness (TeX-read-string "Box value Gray (between 0,1): ")))
	       (TeX-argument-insert grayness optional)))
	    ;; <named> model; allowed are dvipsnames.
	    ((string-equal model "named")
	     (let ((color (completing-read "Frame named Color: "
					   LaTeX-color-dvipsnames-colors)))
	       (TeX-argument-insert color optional))
	     (let ((color (completing-read "Box named Color: "
					   LaTeX-color-dvipsnames-colors)))
	       (TeX-argument-insert color optional)))))))

(TeX-add-style-hook
 "color"
 (lambda ()
   ;; Add color to the parser.
   (TeX-auto-add-regexp LaTeX-color-definecolor-regexp)

   ;; Add list of colors which are always available.
   (LaTeX-add-color-definecolors
    "black" "blue" "cyan" "green" "magenta" "red" "white" "yellow")

   ;; Add dvips colors in conjunction with `usenames'.
   (when (and (LaTeX-provided-package-options-member "color" "usenames")
	      (or (LaTeX-provided-package-options-member "color" "dvips")
		  (LaTeX-provided-package-options-member "color" "dvipsnames")))
     (apply #'LaTeX-add-color-definecolors LaTeX-color-dvipsnames-colors))

   (TeX-add-symbols
    ;; \definecolor{<name>}{<model>}{<color spec>}
    '("definecolor" TeX-arg-color-definecolor)

    ;; \color{<name>} or \color[<model>]{<color spec>}
    '("color" TeX-arg-color)

    ;; \textcolor{<name>}{<text>} or
    ;; \textcolor[<model>]{<color spec>}{<text>}
    '("textcolor" TeX-arg-color "Text")

    ;; \pagecolor{<name>} or
    ;; \pagecolor[<model>]{<color spec>}
    '("pagecolor" TeX-arg-color)

    ;; \nopagecolor
    '("nopagecolor" 0)

    ;; \colorbox{<name>}{<text>} or
    ;; \colorbox[<model>]{<color spec>}{<text>}
    '("colorbox" TeX-arg-color "Text")

    ;; \fcolorbox{<frame color name>}{<box color name>}{<text>} or
    ;; \fcolorbox[<model>]{<frame color spec>}{<box color spec>}{<text>}
    '("fcolorbox" TeX-arg-color-fcolorbox "Text"))

   ;; Fontification
   (when (and (featurep 'font-latex)
	      (eq TeX-install-font-lock 'font-latex-setup))
     (font-latex-add-keywords '(("color"         "[{")
				("pagecolor"     "[{"))
			      'type-declaration)
     (font-latex-add-keywords '(("textcolor"     "[{{")
				("colorbox"      "[{{" )
				("fcolorbox"     "[{{{"))
			      'type-command)
     (font-latex-add-keywords '(("definecolor"    "{{{"))
			      'function)))
 LaTeX-dialect)

(defvar LaTeX-color-package-options
  '("debugshow" "dvipdf" "dvipdfm" "dvipdfmx" "dvips" "dvipsnames"
    "dvipsone" "dviwin" "dviwindo" "emtex" "monochrome" "nodvipsnames"
    "oztex" "pctex32" "pctexhp" "pctexps" "pctexwin" "pdftex" "tcidvi"
    "textures" "truetex" "usenames" "vtex" "xdvi" "xetex")
  "Package options for the color package.")

;;; color.el ends here
