;; xcolor.el --- AUCTeX style for `xcolor.sty' (v2.12)

;; Copyright (C) 2016--2017 Free Software Foundation, Inc.

;; Author: Arash Esbati <arash@gnu.org>
;; Maintainer: auctex-devel@gnu.org
;; Created: 2015-07-04
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

;; This file adds support for `xcolor.sty' (v2.12) from 2016/05/11.
;; `xcolor.sty' is part of TeXLive.

;; `xcolor.sty' and `color.sty' share many command namens, but the
;; number of arguments is not always identical -- `xcolor.sty'
;; commands take more arguments.  In order to make the commands and
;; font-locking work correctly, we follow this strategy: If
;; `xcolor.sty' is loaded after `color.sty', everything works fine.
;; For the way around, we guard the definitions for `color.sty' with:
;;
;;     (unless (member "xcolor" (TeX-style-list))
;;       (<define stuff for color.sty>))
;;
;; to make sure that we define stuff for `color.sty' only if AUCTeX
;; style for `xcolor.sty' is not already loaded.

;;; Code:

(defvar LaTeX-xcolor-core-color-models
  '("rgb" "cmy" "cmyk" "hsb" "gray")
  "List of core color models provided by xcolor.sty.")

(defvar LaTeX-xcolor-num-color-models
  '("RGB" "HTML" "HSB" "Gray" "HsB" "tHsB" "wave")
  "List of integer and decimal color models provided by xcolor.sty.")

(defvar LaTeX-xcolor-pseudo-color-models
  '("named")
  "List of pseudo color models provided by xcolor.sty.")

(defvar LaTeX-xcolor-type-color-models
  '("named" "ps")
  "List of type color models provided by xcolor.sty.")

(defvar LaTeX-xcolor-base-colors
  '("red"    "green" "blue"     "cyan"      "magenta" "yellow" "black"
    "gray"   "white" "darkgray" "lightgray" "brown"   "lime"   "olive"
    "orange" "pink"  "purple"   "teal"      "violet")
  "List of colors defined and always available from xcolor.sty.")

(defvar LaTeX-xcolor-dvipsnames-colors
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
  "List of colors defined by package option dvipsnames from xcolor.sty.")

(defvar LaTeX-xcolor-svgnames-colors
  '("AliceBlue"      "DarkTurquoise" "LightSalmon"       "PaleVioletRed"
    "AntiqueWhite"   "DarkViolet"    "LightSeaGreen"     "PapayaWhip"
    "Aqua"           "DeepPink"      "LightSkyBlue"      "PeachPuff"
    "Aquamarine"     "DeepSkyBlue"   "LightSlateBlue"    "Peru"
    "Azure"          "DimGray"       "LightSlateGray"    "Pink"
    "Beige"          "DimGrey"       "LightSlateGrey"    "Plum"
    "Bisque"         "DodgerBlue"    "LightSteelBlue"    "PowderBlue"
    "Black"          "FireBrick"     "LightYellow"       "Purple"
    "BlanchedAlmond" "FloralWhite"   "Lime"              "Red"
    "Blue"           "ForestGreen"   "LimeGreen"         "RosyBrown"
    "BlueViolet"     "Fuchsia"       "Linen"             "RoyalBlue"
    "Brown"          "Gainsboro"     "Magenta"           "SaddleBrown"
    "BurlyWood"      "GhostWhite"    "Maroon"            "Salmon"
    "CadetBlue"      "Gold"          "MediumAquamarine"  "SandyBrown"
    "Chartreuse"     "Goldenrod"     "MediumBlue"        "SeaGreen"
    "Chocolate"      "Gray"          "MediumOrchid"      "Seashell"
    "Coral"          "Green"         "MediumPurple"      "Sienna"
    "CornflowerBlue" "GreenYellow"   "MediumSeaGreen"    "Silver"
    "Cornsilk"       "Grey"          "MediumSlateBlue"   "SkyBlue"
    "Crimson"        "Honeydew"      "MediumSpringGreen" "SlateBlue"
    "Cyan"           "HotPink"       "MediumTurquoise"   "SlateGray"
    "DarkBlue"       "IndianRed"     "MediumVioletRed"   "SlateGrey"
    "DarkCyan"       "Indigo"        "MidnightBlue"      "Snow"
    "DarkGoldenrod"  "Ivory"         "MintCream"         "SpringGreen"
    "DarkGray"       "Khaki"         "MistyRose"         "SteelBlue"
    "DarkGreen"      "Lavender"      "Moccasin"          "Tan"
    "DarkGrey"       "LavenderBlush" "NavajoWhite"       "Teal"
    "DarkKhaki"      "LawnGreen"     "Navy"              "Thistle"
    "DarkMagenta"    "LemonChiffon"  "NavyBlue"          "Tomato"
    "DarkOliveGreen" "LightBlue"     "OldLace"           "Turquoise"
    "DarkOrange"     "LightCoral"    "Olive"             "Violet"
    "DarkOrchid"     "LightCyan"     "OliveDrab"         "VioletRed"
    "DarkRed"        "LightGoldenrod" "Orange"           "Wheat"
    "DarkSalmon"     "LightGoldenrodYellow" "OrangeRed"  "White"
    "DarkSeaGreen"   "LightGray"     "Orchid"            "WhiteSmoke"
    "DarkSlateBlue"  "LightGreen"    "PaleGoldenrod"     "Yellow"
    "DarkSlateGray"  "LightGrey"     "PaleGreen"         "YellowGreen"
    "DarkSlateGrey"  "LightPink"     "PaleTurquoise")
  "List of colors defined by package option svgnames from xcolor.sty.")

(defvar LaTeX-xcolor-x11names-colors
  '("AntiqueWhite1"     "DeepSkyBlue1"  "LightYellow1"  "RoyalBlue1"
    "AntiqueWhite2"     "DeepSkyBlue2"  "LightYellow2"  "RoyalBlue2"
    "AntiqueWhite3"     "DeepSkyBlue3"  "LightYellow3"  "RoyalBlue3"
    "AntiqueWhite4"     "DeepSkyBlue4"  "LightYellow4"  "RoyalBlue4"
    "Aquamarine1"       "DodgerBlue1"   "Magenta1"      "Salmon1"
    "Aquamarine2"       "DodgerBlue2"   "Magenta2"      "Salmon2"
    "Aquamarine3"       "DodgerBlue3"   "Magenta3"      "Salmon3"
    "Aquamarine4"       "DodgerBlue4"   "Magenta4"      "Salmon4"
    "Azure1"            "Firebrick1"    "Maroon1"       "SeaGreen1"
    "Azure2"            "Firebrick2"    "Maroon2"       "SeaGreen2"
    "Azure3"            "Firebrick3"    "Maroon3"       "SeaGreen3"
    "Azure4"            "Firebrick4"    "Maroon4"       "SeaGreen4"
    "Bisque1"           "Gold1"         "MediumOrchid1" "Seashell1"
    "Bisque2"           "Gold2"         "MediumOrchid2" "Seashell2"
    "Bisque3"           "Gold3"         "MediumOrchid3" "Seashell3"
    "Bisque4"           "Gold4"         "MediumOrchid4" "Seashell4"
    "Blue1"             "Goldenrod1"    "MediumPurple1" "Sienna1"
    "Blue2"             "Goldenrod2"    "MediumPurple2" "Sienna2"
    "Blue3"             "Goldenrod3"    "MediumPurple3" "Sienna3"
    "Blue4"             "Goldenrod4"    "MediumPurple4" "Sienna4"
    "Brown1"            "Green1"        "MistyRose1"    "SkyBlue1"
    "Brown2"            "Green2"        "MistyRose2"    "SkyBlue2"
    "Brown3"            "Green3"        "MistyRose3"    "SkyBlue3"
    "Brown4"            "Green4"        "MistyRose4"    "SkyBlue4"
    "Burlywood1"        "Honeydew1"     "NavajoWhite1"  "SlateBlue1"
    "Burlywood2"        "Honeydew2"     "NavajoWhite2"  "SlateBlue2"
    "Burlywood3"        "Honeydew3"     "NavajoWhite3"  "SlateBlue3"
    "Burlywood4"        "Honeydew4"     "NavajoWhite4"  "SlateBlue4"
    "CadetBlue1"        "HotPink1"      "OliveDrab1"    "SlateGray1"
    "CadetBlue2"        "HotPink2"      "OliveDrab2"    "SlateGray2"
    "CadetBlue3"        "HotPink3"      "OliveDrab3"    "SlateGray3"
    "CadetBlue4"        "HotPink4"      "OliveDrab4"    "SlateGray4"
    "Chartreuse1"       "IndianRed1"    "Orange1"       "Snow1"
    "Chartreuse2"       "IndianRed2"    "Orange2"       "Snow2"
    "Chartreuse3"       "IndianRed3"    "Orange3"       "Snow3"
    "Chartreuse4"       "IndianRed4"    "Orange4"       "Snow4"
    "Chocolate1"        "Ivory1"        "OrangeRed1"    "SpringGreen1"
    "Chocolate2"        "Ivory2"        "OrangeRed2"    "SpringGreen2"
    "Chocolate3"        "Ivory3"        "OrangeRed3"    "SpringGreen3"
    "Chocolate4"        "Ivory4"        "OrangeRed4"    "SpringGreen4"
    "Coral1"            "Khaki1"        "Orchid1"       "SteelBlue1"
    "Coral2"            "Khaki2"        "Orchid2"       "SteelBlue2"
    "Coral3"            "Khaki3"        "Orchid3"       "SteelBlue3"
    "Coral4"            "Khaki4"        "Orchid4"       "SteelBlue4"
    "Cornsilk1"         "LavenderBlush1" "PaleGreen1"    "Tan1"
    "Cornsilk2"         "LavenderBlush2" "PaleGreen2"    "Tan2"
    "Cornsilk3"         "LavenderBlush3" "PaleGreen3"    "Tan3"
    "Cornsilk4"         "LavenderBlush4" "PaleGreen4"    "Tan4"
    "Cyan1"             "LemonChiffon1" "PaleTurquoise1" "Thistle1"
    "Cyan2"             "LemonChiffon2" "PaleTurquoise2" "Thistle2"
    "Cyan3"             "LemonChiffon3" "PaleTurquoise3" "Thistle3"
    "Cyan4"             "LemonChiffon4" "PaleTurquoise4" "Thistle4"
    "DarkGoldenrod1"    "LightBlue1"    "PaleVioletRed1" "Tomato1"
    "DarkGoldenrod2"    "LightBlue2"    "PaleVioletRed2" "Tomato2"
    "DarkGoldenrod3"    "LightBlue3"    "PaleVioletRed3" "Tomato3"
    "DarkGoldenrod4"    "LightBlue4"    "PaleVioletRed4" "Tomato4"
    "DarkOliveGreen1"   "LightCyan1"    "PeachPuff1"     "Turquoise1"
    "DarkOliveGreen2"   "LightCyan2"    "PeachPuff2"     "Turquoise2"
    "DarkOliveGreen3"   "LightCyan3"    "PeachPuff3"     "Turquoise3"
    "DarkOliveGreen4"   "LightCyan4"    "PeachPuff4"     "Turquoise4"
    "DarkOrange1"       "LightGoldenrod1" "Pink1"        "VioletRed1"
    "DarkOrange2"       "LightGoldenrod2" "Pink2"        "VioletRed2"
    "DarkOrange3"       "LightGoldenrod3" "Pink3"        "VioletRed3"
    "DarkOrange4"       "LightGoldenrod4" "Pink4"        "VioletRed4"
    "DarkOrchid1"       "LightPink1"    "Plum1"          "Wheat1"
    "DarkOrchid2"       "LightPink2"    "Plum2"          "Wheat2"
    "DarkOrchid3"       "LightPink3"    "Plum3"          "Wheat3"
    "DarkOrchid4"       "LightPink4"    "Plum4"          "Wheat4"
    "DarkSeaGreen1"     "LightSalmon1"  "Purple1"        "Yellow1"
    "DarkSeaGreen2"     "LightSalmon2"  "Purple2"        "Yellow2"
    "DarkSeaGreen3"     "LightSalmon3"  "Purple3"        "Yellow3"
    "DarkSeaGreen4"     "LightSalmon4"  "Purple4"        "Yellow4"
    "DarkSlateGray1"    "LightSkyBlue1" "Red1"           "Gray0"
    "DarkSlateGray2"    "LightSkyBlue2" "Red2"           "Green0"
    "DarkSlateGray3"    "LightSkyBlue3" "Red3"           "Grey0"
    "DarkSlateGray4"    "LightSkyBlue4" "Red4"           "Maroon0"
    "DeepPink1"         "LightSteelBlue1" "RosyBrown1"   "Purple0"
    "DeepPink2"         "LightSteelBlue2" "RosyBrown2"
    "DeepPink3"         "LightSteelBlue3" "RosyBrown3"
    "DeepPink4"         "LightSteelBlue4" "RosyBrown4")
  "List of colors defined by package option x11names from xcolor.sty.")

(defvar LaTeX-xcolor-color-models
  (append LaTeX-xcolor-core-color-models
	  LaTeX-xcolor-num-color-models
	  LaTeX-xcolor-pseudo-color-models)
  "Combine three variables `LaTeX-xcolor-core-color-models',
`LaTeX-xcolor-num-color-models' and `LaTeX-xcolor-pseudo-color-models'.")

(defun LaTeX-xcolor-color-models (&optional no-named)
  "Return the value of variable `LaTeX-xcolor-color-models'.
If NO-NAMED is non-nil, remove \"named\" and return the
remainder."
  (if no-named
      (remove "named" LaTeX-xcolor-color-models)
    (symbol-value 'LaTeX-xcolor-color-models)))

;; Needed for auto-parsing.
(require 'tex)

;; Setup AUCTeX parser for \definecolor(set):
(TeX-auto-add-type "xcolor-definecolor" "LaTeX")
(TeX-auto-add-type "xcolor-definecolorset" "LaTeX")

(defvar LaTeX-xcolor-definecolor-regexp
  (eval-when-compile
    `(,(concat "\\\\"
	       (regexp-opt '("definecolor"  "providecolor"
			     "preparecolor" "colorlet"))
	       "\\(?:\\[\\(?:[^]]*\\)\\]\\)?{\\([^}]+\\)}")
      1 LaTeX-auto-xcolor-definecolor))
  "Match the argument of various color defining macros from xcolor package.")

(defvar LaTeX-xcolor-definecolorset-regexp
  `(,(concat "\\\\\\(?:define\\|provide\\|prepare\\)"
	     "colorset"
	     "\\(?:\\[\\(?:[^]]*\\)\\]\\)?"
	     "{\\(?:[^}]+\\)}"
	     "{\\([^}]+\\)}"
	     "{\\([^}]+\\)}"
	     "{\\([^}]+\\)}")
    (1 2 3) LaTeX-auto-xcolor-definecolorset)
  "Match the argument of various color-set defining macros from
xcolor package.")

(defun LaTeX-xcolor-auto-prepare ()
  "Clear `LaTeX-auto-xcolor-definecolor' before parsing."
  (setq LaTeX-auto-xcolor-definecolor nil
	LaTeX-auto-xcolor-definecolorset nil))

(defun LaTeX-xcolor-auto-cleanup ()
  "Process the parsed elements from `LaTeX-auto-xcolor-definecolorset'."
  (dolist (colset (LaTeX-xcolor-definecolorset-list))
    (let ((head (car colset))
	  (tail (cadr colset))
	  (cols (split-string
		 (TeX-replace-regexp-in-string "[ %\n\r\t]" "" (nth 2 colset))
		 "\\(,[^;]+;\\|,[^;]+$\\)" t)))
      (dolist (color cols)
	(LaTeX-add-xcolor-definecolors (concat head color tail))))))

(add-hook 'TeX-auto-prepare-hook #'LaTeX-xcolor-auto-prepare t)
(add-hook 'TeX-auto-cleanup-hook #'LaTeX-xcolor-auto-cleanup t)
(add-hook 'TeX-update-style-hook #'TeX-auto-parse t)

(defun TeX-arg-xcolor-definecolor (optional)
  "Insert arguments of \\definecolor and similar macros from
xcolor.sty."
  ;; \definecolor[<type>]{<name>}{<model-list>}{<spec-list>}
  (let* ((xcoltype  (completing-read
		     (TeX-argument-prompt t nil "Type")
		     LaTeX-xcolor-type-color-models))
	 (xcolname  (TeX-read-string
		     (TeX-argument-prompt optional nil "Color name")))
	 (xcolmodel (completing-read
		     (TeX-argument-prompt optional nil "Model (list)")
		     (if (string= xcoltype "named")
			 (LaTeX-xcolor-color-models t)
		       LaTeX-xcolor-color-models)))
	 (xcolspec  (if (string= xcolmodel "named")
			(completing-read
			 (TeX-argument-prompt optional nil "Color")
			 (LaTeX-xcolor-definecolor-list))
		      (TeX-read-string
		       (TeX-argument-prompt optional nil (concat xcolmodel " spec (list)"))))))
    (when (and xcoltype (not (string= xcoltype "")))
      (insert (format "[%s]" xcoltype)))
    (TeX-argument-insert xcolname optional)
    (LaTeX-add-xcolor-definecolors xcolname)
    (TeX-argument-insert xcolmodel optional)
    (TeX-argument-insert xcolspec optional)))

(defun TeX-arg-xcolor-definecolorset (optional)
  "Insert arguments of \\definecolorset and similar macros from
xcolor.sty."
  (let ((xcoltype (completing-read
		   (TeX-argument-prompt t nil "Type")
		   LaTeX-xcolor-type-color-models))
	(xcolmodel (completing-read
		    (TeX-argument-prompt optional nil "Model")
		    (LaTeX-xcolor-color-models t))))
    (when (and xcoltype (not (string= xcoltype "")))
      (insert (format "[%s]" xcoltype)))
    (TeX-argument-insert xcolmodel optional)))

(defun TeX-arg-xcolor (optional)
  "Insert arguments of various color commands from xcolor.sty."
  ;; \color{<name>} or \color[<model-list>]{<spec-list>}
  (let* ((xcolmodel (completing-read
		     (TeX-argument-prompt t nil "Model (list)")
		     (LaTeX-xcolor-color-models t)))
	 (xcolor (if (and xcolmodel (not (string= xcolmodel "")))
		     (TeX-read-string
		      (TeX-argument-prompt optional nil (concat xcolmodel " spec (list)")))
		   (completing-read
		    (TeX-argument-prompt optional nil "Color")
		    (LaTeX-xcolor-definecolor-list)))))
    (when (and xcolmodel (not (string= xcolmodel "")))
      (insert (format "[%s]" xcolmodel)))
    (TeX-argument-insert xcolor optional)))

(defun TeX-arg-xcolor-fcolorbox (optional)
  "Insert arguments of \\fcolorbox from xcolor.sty."
  ;;\fcolorbox[<frame model>]{<frame spec>}[<background model>]{<background spec>}{<text>}
  (let* ((xfrmodel (completing-read
		    (TeX-argument-prompt t nil "(Frame) Color model")
		    LaTeX-xcolor-color-models))
	 (xfrspec  (if (or (string= xfrmodel "")
			   (string= xfrmodel "named"))
		       (completing-read
			(TeX-argument-prompt optional nil "Frame color spec")
			(LaTeX-xcolor-definecolor-list))
		     (TeX-read-string
		      (TeX-argument-prompt optional nil "Frame color spec"))))
	 (xbgmodel (completing-read
		    (TeX-argument-prompt t nil "Background Color model")
		    LaTeX-xcolor-color-models))
	 (xbgspec  (if (or (string= xfrmodel "")
			   (string= xfrmodel "named")
			   (string= xbgmodel "")
			   (string= xbgmodel "named"))
		       (completing-read
			(TeX-argument-prompt optional nil "Background color spec")
			(LaTeX-xcolor-definecolor-list))
		     (TeX-read-string
		      (TeX-argument-prompt optional nil "Background color spec")))))
    (when (and xfrmodel (not (string= xfrmodel "")))
      (insert (format "[%s]" xfrmodel)))
    (TeX-argument-insert xfrspec optional)
    (when (and xbgmodel (not (string= xbgmodel "")))
      (insert (format "[%s]" xbgmodel)))
    (TeX-argument-insert xbgspec optional)))


(TeX-add-style-hook
 "xcolor"
 (lambda ()
   ;; Add color to the parser.
   (TeX-auto-add-regexp LaTeX-xcolor-definecolor-regexp)
   (TeX-auto-add-regexp LaTeX-xcolor-definecolorset-regexp)

   ;; Add list of colors which are always available.
   (apply #'LaTeX-add-xcolor-definecolors LaTeX-xcolor-base-colors)

   ;; Add dvips colors in conjunction with `dvipsnames*?'.
   (when (or (LaTeX-provided-package-options-member "xcolor" "dvipsnames")
	     (LaTeX-provided-package-options-member "xcolor" "dvipsnames*"))
     (apply #'LaTeX-add-xcolor-definecolors LaTeX-xcolor-dvipsnames-colors))

   ;; For `svgnames*?'
   (when (or (LaTeX-provided-package-options-member "xcolor" "svgnames")
	     (LaTeX-provided-package-options-member "xcolor" "svgnames*"))
     (apply #'LaTeX-add-xcolor-definecolors LaTeX-xcolor-svgnames-colors))

   ;; For `x11ames*?'
   (when (or (LaTeX-provided-package-options-member "xcolor" "x11names")
	     (LaTeX-provided-package-options-member "xcolor" "x11names*"))
     (apply #'LaTeX-add-xcolor-definecolors LaTeX-xcolor-x11names-colors))

   (TeX-add-symbols
    ;; 2.5.2 Color definition in xcolor
    ;; \definecolor[<type>]{<name>}{<model-list>}{<spec-list>}
    '("definecolor" TeX-arg-xcolor-definecolor)

    ;; \providecolor[<type>]{<name>}{<model-list>}{<spec-list>}
    '("providecolor" TeX-arg-xcolor-definecolor)

    ;; \colorlet[<type>]{<name>}[<num model>]{<color>}
    '("colorlet"
      [ TeX-arg-eval completing-read
		     (TeX-argument-prompt optional nil "Type")
		     LaTeX-xcolor-type-color-models ]
      (TeX-arg-eval
       (lambda ()
	 (let ((xcolor (TeX-read-string
			(TeX-argument-prompt optional nil "Color"))))
	   (LaTeX-add-xcolor-definecolors xcolor)
	   (format "%s" xcolor))))
      [ TeX-arg-eval completing-read
		     (TeX-argument-prompt optional nil "Model")
		     (LaTeX-xcolor-color-models t) ]
      (TeX-arg-eval completing-read
		    (TeX-argument-prompt optional nil "Color")
		    (LaTeX-xcolor-definecolor-list)))

    ;; 2.5.3 Defining sets of colors
    ;; \definecolorset[<type>]{<model-list>}{<head>}{<tail>}{<set spec>}
    '("definecolorset" TeX-arg-xcolor-definecolorset "Head" "Tail" t)

    ;; \providecolorset[<type>]{<model-list>}{<head>}{<tail>}{<set spec>}
    '("providecolorset" TeX-arg-xcolor-definecolorset "Head" "Tail" t)

    ;; 2.5.4 Immediate and deferred definitions
    ;; \preparecolor[<type>]{<name>}{<model-list>}{<spec-list>}
    '("preparecolor" TeX-arg-xcolor-definecolor)

    ;; \preparecolorset[<type>]{<model-list>}{<head>}{<tail>}{<set spec>}
    '("preparecolorset" TeX-arg-xcolor-definecolorset "Head" "Tail" t)

    ;; \definecolors{<id-list>}
    '("definecolors" t)

    ;; \providecolors{<id-list>}
    '("providecolors" t)

    ;; 2.6 Color application
    ;; 2.6.1 Standard color commands

    ;; \color{<name>} or \color[<model>]{<color spec>}
    '("color" TeX-arg-xcolor)

    ;; \textcolor{<name>}{<text>} or
    ;; \textcolor[<model>]{<color spec>}{<text>}
    '("textcolor" TeX-arg-xcolor "Text")

    ;; \pagecolor{<name>} or
    ;; \pagecolor[<model>]{<color spec>}
    '("pagecolor" TeX-arg-xcolor)

    ;; \nopagecolor
    '("nopagecolor" 0)

    ;; 2.6.2 Colored boxes
    ;; \colorbox{<name>}{<text>} or
    ;; \colorbox[<model>]{<color spec>}{<text>}
    '("colorbox" TeX-arg-xcolor "Text")

    ;; \fcolorbox{<frame color>}{<box color>}{<text>} or
    ;; \fcolorbox[<model>]{<frame spec>}{<background spec>}{<text>} or
    ;; \fcolorbox[<frame model>]{<frame spec>}[<background model>]{<background spec>}{<text>}
    '("fcolorbox" TeX-arg-xcolor-fcolorbox "Text")

    ;; 2.6.4 Color testing
    ;; \testcolor{<name>} or
    ;; \testcolor[<model>]{<color spec>}
    '("testcolor" TeX-arg-xcolor)

    ;; 2.7 Color blending
    '("blendcolors"
      (TeX-arg-eval completing-read
		    (TeX-argument-prompt optional nil "Mix expr")
		    (LaTeX-xcolor-definecolor-list)))
    '("blendcolors*"
      (TeX-arg-eval completing-read
		    (TeX-argument-prompt optional nil "Mix expr")
		    (LaTeX-xcolor-definecolor-list)))

    ;; 2.8 Color masks and separation
    '("maskcolors"
      [ TeX-arg-eval completing-read
		     (TeX-argument-prompt optional nil "Model")
		     (LaTeX-xcolor-color-models t) ]
      (TeX-arg-eval completing-read
		    (TeX-argument-prompt optional nil "Color")
		    (LaTeX-xcolor-definecolor-list)))

    ;; 2.9 Color series
    '("definecolorseries"
      "Name"
      (TeX-arg-eval completing-read
		    (TeX-argument-prompt optional nil "Core model")
		    LaTeX-xcolor-core-color-models)
      (TeX-arg-eval completing-read
		    (TeX-argument-prompt optional nil "Method")
		    '("step" "grad" "last"))
      [ t ] nil [ nil ] nil)

    '("resetcolorseries" [ "Div." ] "Name")

    ;; 2.13 Color information
    ;; \extractcolorspec{<color>}{<cmd>}
    '("extractcolorspec"
      (TeX-arg-eval completing-read
		    (TeX-argument-prompt optional nil "Color")
		    (LaTeX-xcolor-definecolor-list))
      (TeX-arg-define-macro "Command: \\"))

    ;; \extractcolorspecs{<color>}{<model-cmd>}{<color-cmd>}
    '("extractcolorspecs"
      (TeX-arg-eval completing-read
		    (TeX-argument-prompt optional nil "Color")
		    (LaTeX-xcolor-definecolor-list))
      (TeX-arg-define-macro "Model command: \\")
      (TeX-arg-define-macro "Color command: \\"))

    ;; \tracingcolors = <integer>
    '("tracingcolors"
      (TeX-arg-literal "="))

    ;; 2.14 Color conversion
    ;; \convertcolorspec{<model>}{<spec>}{<target model>}{cmd>}
    '("convertcolorspec"
      (TeX-arg-eval completing-read
		    (TeX-argument-prompt optional nil "Model")
		    (LaTeX-xcolor-color-models))
      (TeX-arg-eval TeX-read-string
		    (TeX-argument-prompt optional nil "Spec"))
      (TeX-arg-eval completing-read
		    (TeX-argument-prompt optional nil "Model")
		    (LaTeX-xcolor-color-models t))
      (TeX-arg-define-macro "Macro: \\")) ) ; close TeX-add-symbols

   ;; 2.12 Color in tables
   ;; These commands are available with `table' package option
   (when (LaTeX-provided-package-options-member "xcolor" "table")
     ;; Run style hook to colortbl.sty
     (TeX-run-style-hooks "colortbl")

     ;; Add additional commands:
     (TeX-add-symbols
      ;; \rowcolors[<commands>]{<row>}{<odd-row color>}{<even-row color>}
      '("rowcolors"
	(TeX-arg-conditional (y-or-n-p "With optional commands? ")
			     ( [ t ] )
			     (ignore))
	"Row"
	(TeX-arg-eval completing-read
		      (TeX-argument-prompt optional nil "Odd-row color")
		      (LaTeX-xcolor-definecolor-list))
	(TeX-arg-eval completing-read
		      (TeX-argument-prompt optional nil "Even-row color")
		      (LaTeX-xcolor-definecolor-list)))
      '("rowcolors*"
	(TeX-arg-conditional (y-or-n-p "With optional commands? ")
			     ( [ t ] )
			     (ignore))
	"Row"
	(TeX-arg-eval completing-read
		      (TeX-argument-prompt optional nil "Odd-row color")
		      (LaTeX-xcolor-definecolor-list))
	(TeX-arg-eval completing-read
		      (TeX-argument-prompt optional nil "Even-row color")
		      (LaTeX-xcolor-definecolor-list)))
      '("showrowcolors" 0)
      '("hiderowcolors" 0))
     (LaTeX-add-counters "rownum"))

   ;; 2.6.4 Color testing
   (LaTeX-add-environments
    '("testcolors" LaTeX-env-args
      [ TeX-arg-eval mapconcat #'identity
		     (TeX-completing-read-multiple
		      (TeX-argument-prompt optional nil "Color models")
		      (LaTeX-xcolor-color-models t))
		     "," ] ))

   ;; Fontification
   (when (and (featurep 'font-latex)
	      (eq TeX-install-font-lock 'font-latex-setup))
     (font-latex-add-keywords '(("color"             "[{")
				("pagecolor"         "[{"))
			      'type-declaration)
     (font-latex-add-keywords '(("textcolor"         "[{{")
				("colorbox"          "[{{" )
				("fcolorbox"         "[{[{{"))
			      'type-command)
     (font-latex-add-keywords '(("definecolor"       "[{{{")
				("providecolor"      "[{{{")
				("colorlet"          "[{[{")
				("definecolorset"    "[{{{{")
				("providecolorset"   "[{{{{")
				("preparecolor"      "[{{{")
				("preparecolorset"   "[{{{{")
				("definecolors"      "{")
				("providecolors"     "{")
				("testcolor"         "[{")
				("blendcolors"       "*{")
				("maskcolors"        "[{")
				("definecolorseries" "{{{[{[{")
				("resetcolorseries"  "[{")
				("extractcolorspec"  "{{")
				("extractcolorspecs" "{{{")
				("convertcolorspec"  "{{{{")
				("rowcolors"         "*[{{{"))
			      'function)))
 LaTeX-dialect)

(defvar LaTeX-xcolor-package-options
  '(;; options that determine the color driver
    "dvips" "xdvi" "dvipdf" "dvipdfm" "dvipdfmx" "pdftex" "dvipsone"
    "dviwindo" "emtex" "dviwin" "oztex" "textures" "pctexps" "pctexwin"
    "pctexhp" "pctex32" "truetex" "tcidvi" "vtex" "xetex"

    ;; options that determine the target color model
    "natural" "rgb" "cmy" "cmyk" "hsb" "gray" "RGB" "HTML"
    "HSB" "Gray" "monochrome"

    ;; options that control predefined colors loading
    "dvipsnames" "dvipsnames*" "svgnames" "svgnames*" "x11names" "x11names*"

    ;; options that determine which other packages to load
    "table" "fixpdftex" "hyperref"

    ;; options that influence the behaviour of other commands
    "prologue" "kernelfbox" "xcdraw" "noxcdraw" "fixinclude"
    "showerrors" "hideerrors")
  "Package options for the xcolor package.")

;;; xcolor.el ends here
