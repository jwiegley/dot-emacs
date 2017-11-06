;;; fontspec.el --- AUCTeX style for `fontspec.sty' version 2.6a.

;; Copyright (C) 2013, 2017 Free Software Foundation, Inc.

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

;; This file adds support for `fontspec.sty' version 2.6a.  Starting
;; with `fontspec.sty' v2.4, the order of mandatory font names and
;; optional font features in related macros has changed, i.e. optional
;; argument comes after the mandatory one.  This change is now (April
;; 2017) implemented in this file.  Fontification support retains
;; backward compatibilty.

;;; Code:

(defvar LaTeX-fontspec-font-features
  '(;; 5 Font selection
    ("Extension" (".otf" ".ttf" ".ttc" ".dfont"))
    ("Path")
    ;; 6.1 More control over font shape selection
    ("BoldFont")
    ("ItalicFont")
    ("BoldItalicFont")
    ("SlantedFont")
    ("BoldSlantedFont")
    ("SmallCapsFont")
    ;; 6.2 Specifically choosing the NFSS family
    ("NFSSFamily")
    ("FontFace")
    ;; 11 Different features for different font shapes
    ("UprightFeatures")
    ("BoldFeatures")
    ("ItalicFeatures")
    ("BoldItalicFeatures")
    ("SlantedFeatures")
    ("BoldSlantedFeatures")
    ("SmallCapsFeatures")
    ;; 13 Different features for different font sizes
    ("SizeFeatures")
    ;; 14 Font independent options
    ("Color")
    ("Scale" ("MatchLowercase" "MatchUppercase"))
    ("WordSpace")
    ("PunctuationSpace")
    ("HyphenChar")
    ("OpticalSize")
    ("AutoFakeBold")
    ("AutoFakeSlant")
    ("FakeSlant")
    ("FakeStretch")
    ("FakeBold")
    ("LetterSpace")
    ;; 16 OpenType options
    ("Ligatures" ("Required"      "RequiredOff"
		  "Common"        "CommonOff"
		  "Contextual"    "ContextualOff"
		  "Rare"          "RareOff"
		  "Discretionary" "DiscretionaryOff"
		  "Historic"      "HistoricOff"
		  "TeX"
		  "ResetAll"))
    ("Letters" ("Uppercase"           "UppercaseOff"
		"SmallCaps"           "SmallCapsOff"
		"PetiteCaps"          "PetiteCapsOff"
		"UppercaseSmallCaps"  "UppercaseSmallCapsOff"
		"UppercasePetiteCaps" "UppercasePetiteCapsOff"
		"Unicase"             "UnicaseOff"
		"ResetAll"))
    ("Numbers" ("Uppercase"    "UppercaseOff"
		"Lowercase"    "LowercaseOff"
		"Lining"       "LiningOff"
		"OldStyle"     "OldStyleOff"
		"Proportional" "ProportionalOff"
		"Monospaced"   "MonospacedOff"
		"SlashedZero"  "SlashedZeroOff"
		"Arabic"       "ArabicOff"
		"ResetAll"))
    ("Contextuals" ("Swash"       "SwashOff"
		    "Alternate"   "AlternateOff"
		    "WordInitial" "WordInitialOff"
		    "WordFinal"   "WordFinalOff"
		    "LineFinal"   "LineFinalOff"
		    "Inner"       "InnerOff"
		    "ResetAll"))
    ("VerticalPosition" ("Superior"           "SuperiorOff"
			 "Inferior"           "InferiorOff"
			 "Numerator"          "NumeratorOff"
			 "Denominator"        "DenominatorOff"
			 "ScientificInferior" "ScientificInferiorOff"
			 "Ordinal"            "OrdinalOff"
			 "ResetAll"))
    ("Fraction" ("On" "Off" "Reset" "Alternate" "AlternateOff" "ResetAll"))
    ("StylisticSet")
    ("CharacterVariant")
    ("Alternate" ("Random"))
    ("Style" ("Alternate"      "AlternateOff"
	      "Italic"         "ItalicOff"
	      "Ruby"           "RubyOff"
	      "Swash"          "SwashOff"
	      "Cursive"        "CursiveOff"
	      "Historic"       "HistoricOff"
	      "TitlingCaps"    "TitlingCapsOff"
	      "HorizontalKana" "HorizontalKanaOff"
	      "VerticalKana"   "VerticalKanaOff"
	      "ResetAll"))
    ("Diacritics" ("MarkToBase" "MarkToBaseOff"
		   "MarkToMark" "MarkToMarkOff"
		   "AboveBase"  "AboveBaseOff"
		   "BelowBase"  "BelowBaseOff"
		   "ResetAll"))
    ("Kerning" ("Uppercase" "UppercaseOff" "On" "Off" "Reset" "ResetAll"))
    ("CharacterWidth" ("Proportional"          "ProportionalOff"
		       "Full"                  "FullOff"
		       "Half"                  "HalfOff"
		       "Third"                 "ThirdOff"
		       "Quarter"               "QuarterOff"
		       "AlternateProportional" "AlternateProportionalOff"
		       "AlternateHalf"         "AlternateHalfOff"
		       "ResetAll"))
    ("Annotation")
    ("CJKShape" ("Traditional"
		 "Simplified"
		 "JIS1978"
		 "JIS1983"
		 "JIS1990"
		 "Expert"
		 "NLC"))
    ("Vertical" ("RotatedGlyphs"         "RotatedGlyphsOff"
		 "AlternatesForRotation" "AlternatesForRotationOff"
		 "Alternates"            "AlternatesOff"
		 "KanaAlternates"        "KanaAlternatesOff"
		 "Kerning"               "KerningOff"
		 "AlternateMetrics"      "AlternateMetricsOff"
		 "HalfMetrics"           "HalfMetricsOff"
		 "ProportionalMetrics"   "ProportionalMetricsOff"
		 "ResetAll"))
    ;; 25 Going behind fontspec's back: Offer only an excerpt of all
    ;; possible tags:
    ("RawFeature" ("frac" "lnum" "onum" "pnum" "smcp" "tnum" "zero")))
  "Font features options for macros of the fontspec package.")

(defvar LaTeX-fontspec-font-features-local nil
  "Buffer-local font features options for macros of the fontspec package.")
(make-variable-buffer-local 'LaTeX-fontspec-font-features-local)

(defvar LaTeX-fontspec-font-list nil
  "List of the fonts accessible to fontspec.")

(defun LaTeX-fontspec-arg-font (optional &optional prompt)
  "Prompt for a font name with completion.
If OPTIONAL is non-nil, insert the resulting value as an optional
argument, otherwise as a mandatory one.  Use PROMPT as the prompt
string.

Customize `LaTeX-fontspec-arg-font-search' in order to decide how
to retrieve the list of fonts."
  (unless LaTeX-fontspec-font-list
    (when (if (eq LaTeX-fontspec-arg-font-search 'ask)
	      (not (y-or-n-p "Find font yourself? "))
	    LaTeX-fontspec-arg-font-search)
      (message "Searching for fonts...")
      (with-temp-buffer
	(shell-command "luaotfload-tool --list=basename" t)
	;; Search for the font base names and full names, and add them to
	;; `LaTeX-fontspec-font-list'.  The list is in the form
	;;     <base name><TAB><full name><TAB><version>
	(while
	    (re-search-forward "^\\([^\n\r\t]*\\)\t\\([^\n\r\t]*\\)\t.*$" nil t)
	  (add-to-list 'LaTeX-fontspec-font-list (match-string-no-properties 1))
	  (add-to-list 'LaTeX-fontspec-font-list
		       (match-string-no-properties 2))))))
  (TeX-argument-insert
   (completing-read
    (TeX-argument-prompt optional prompt "Font name")
    (or LaTeX-fontspec-font-list LaTeX-fontspec-font-list-default))
   optional))

(defun LaTeX-fontspec-update-font-features ()
  "Update Color key=values in `LaTeX-fontspec-font-features-local'."
  ;; Check if any color defininig package is loaded and update the
  ;; key=values for coloring.  Prefer xcolor.sty if both packages are
  ;; loaded.
  (when (or (member "xcolor" (TeX-style-list))
	    (member "color" (TeX-style-list)))
    (let* ((colorcmd (if (member "xcolor" (TeX-style-list))
			 #'LaTeX-xcolor-definecolor-list
		       #'LaTeX-color-definecolor-list))
	   (tmp (copy-alist LaTeX-fontspec-font-features-local)))
      (setq tmp (assq-delete-all (car (assoc "Color" tmp)) tmp))
      (push (list "Color" (mapcar #'car (funcall colorcmd))) tmp)
      (setq LaTeX-fontspec-font-features-local
	    (copy-alist tmp)))))

;; Setup for \newfontfamily and \newfontface:
(TeX-auto-add-type "fontspec-newfontcmd" "LaTeX")

(defvar LaTeX-fontspec-newfontcmd-regexp
  '("\\\\newfontfa\\(?:ce\\|mily\\)[ \t\n\r%]*\\\\\\([a-zA-Z]+\\)"
    1 LaTeX-auto-fontspec-newfontcmd)
  "Matches new macros defined with \\newfontface and \\newfontfamily.")

(defun LaTeX-fontspec-auto-prepare ()
  "Clear `LaTeX-auto-fontspec-newfontcmd' before parsing."
  (setq LaTeX-auto-fontspec-newfontcmd nil))

(defun LaTeX-fontspec-auto-cleanup ()
  "Process parsed elements for fontspec package."
  (dolist (mac (mapcar #'car (LaTeX-fontspec-newfontcmd-list)))
    ;; Add macro to list of known macros
    (TeX-add-symbols mac)
    ;; Cater for fontification
    (when (and (featurep 'font-latex)
	       (eq TeX-install-font-lock 'font-latex-setup))
      (font-latex-add-keywords `((,mac ""))
			       'type-declaration)))
  ;; Update values of Color key:
  (LaTeX-fontspec-update-font-features))

(add-hook 'TeX-auto-prepare-hook #'LaTeX-fontspec-auto-prepare t)
(add-hook 'TeX-auto-cleanup-hook #'LaTeX-fontspec-auto-cleanup t)
(add-hook 'TeX-update-style-hook #'TeX-auto-parse t)

(TeX-add-style-hook
 "fontspec"
 (lambda ()
   (TeX-check-engine-add-engines 'luatex 'xetex)
   (TeX-run-style-hooks "expl3" "xparse")

   ;; Add fontspec to the parser.
   (TeX-auto-add-regexp LaTeX-fontspec-newfontcmd-regexp)

   ;; Activate the buffer local version of font features:
   (setq LaTeX-fontspec-font-features-local
	 (copy-alist LaTeX-fontspec-font-features))

   (TeX-add-symbols
    ;; 4.3 Commands for old-style and lining numbers: \oldstylenums is
    ;; already provided by LaTeX, so just add \liningnums here
    '("liningnums" "Numbers")

    ;; 4.5 Emphasis and nested emphasis
    ;; \emshape seems to be an internal macro
    "emshape"
    '("emfontdeclare" t)
    "emreset"

    ;; 4.6 Strong emphasis
    '("strong" t)
    '("strongfontdeclare" t)
    "strongreset"

    ;; 5 Font selection
    '("fontspec"
      LaTeX-fontspec-arg-font
      [TeX-arg-key-val LaTeX-fontspec-font-features-local "Font features"])

    ;; Default font families
    '("setmainfont"
      (LaTeX-fontspec-arg-font "Main font name")
      [TeX-arg-key-val LaTeX-fontspec-font-features-local "Font features"])
    '("setsansfont"
      (LaTeX-fontspec-arg-font "Sans font name")
      [TeX-arg-key-val LaTeX-fontspec-font-features-local "Font features"])
    '("setmonofont"
      (LaTeX-fontspec-arg-font "Mono font name")
      [TeX-arg-key-val LaTeX-fontspec-font-features-local "Font features"])

    ;; 5.3 Querying whether a font exists
    '("IfFontExistsTF" LaTeX-fontspec-arg-font 2)

    ;; 6 commands to select font families
    '("newfontfamily" TeX-arg-define-macro
      LaTeX-fontspec-arg-font
      [TeX-arg-key-val LaTeX-fontspec-font-features-local "Font features"])

    '("newfontface" TeX-arg-define-macro
      LaTeX-fontspec-arg-font
      [TeX-arg-key-val LaTeX-fontspec-font-features-local "Font features"])

    ;; 6.4 Math(s) fonts
    '("setmathrm" "Font name" [ "Font features" ])
    '("setmathsf" "Font name" [ "Font features" ])
    '("setmathtt" "Font name" [ "Font features" ])
    '("setboldmathrm" "Font name" [ "Font features" ])

    ;; 8 Default settings
    '("defaultfontfeatures" [ LaTeX-fontspec-arg-font ]
      (TeX-arg-key-val LaTeX-fontspec-font-features-local "Font features"))
    '("defaultfontfeatures+" [ LaTeX-fontspec-arg-font ]
      (TeX-arg-key-val LaTeX-fontspec-font-features-local "Font features"))

    ;; 10 Working with the currently selected features
    '("IfFontFeatureActiveTF"
      [TeX-arg-key-val LaTeX-fontspec-font-features-local "Font feature"] 2)

    ;; Changing the currently selected features
    '("addfontfeatures"
      (TeX-arg-key-val LaTeX-fontspec-font-features-local "Font features"))

    ;; 23 Defining new features
    '("newAATfeature"
      (TeX-arg-eval completing-read
		    (TeX-argument-prompt optional nil "Existing feature")
		    LaTeX-fontspec-font-features-local)
      "New option" 2)

    '("newopentypefeature"
      (TeX-arg-eval completing-read
		    (TeX-argument-prompt optional nil "Existing feature")
		    LaTeX-fontspec-font-features-local)
      "New option" t)

    '("newfontfeature" "New feature" t)

    ;; 24 Defining new scripts and languages
    '("newfontscript" "Script name" "OpenType tag")
    '("newfontlanguage" "Language name" "OpenType tag")

    ;; 26 Renaming existing features & options
    '("aliasfontfeature"
      (TeX-arg-eval completing-read
		    (TeX-argument-prompt optional nil "Existing feature")
		    LaTeX-fontspec-font-features-local)
      "New name")

    '("aliasfontfeatureoption"
      (TeX-arg-eval
       (lambda ()
	 (let* ((key (completing-read
		      (TeX-argument-prompt optional nil "Feature")
		      LaTeX-fontspec-font-features-local))
		(val (completing-read
		      (TeX-argument-prompt optional nil "Existing name")
		      (cadr (assoc key LaTeX-fontspec-font-features-local)))))
	   (TeX-argument-insert key optional)
	   (format "%s" val))))
      "New name") )

   (LaTeX-add-environments
    ;; 4.6 Strong emphasis
    '("strong"))

   ;; Fontification
   (when (and (featurep 'font-latex)
	      (eq TeX-install-font-lock 'font-latex-setup))
     (font-latex-add-keywords '(("fontspec"    "[{[")
				("setmainfont" "[{[")
				("setsansfont" "[{[")
				("setmonofont" "[{[")
				("newfontfamily" "\\[{[")
				("newfontface"   "\\[{[")
				("setmathrm" "[{[")
				("setmathsf" "[{[")
				("setmathtt" "[{[")
				("setboldmathrm" "[{[")
				("defaultfontfeatures" "+[{")
				("addfontfeature"  "{")
				("addfontfeatures" "{")
				("newfontscript"   "{{")
				("newfontlanguage" "{{")
				("emfontdeclare"   "{")
				("strongfontdeclare"  "{")
				("newAATfeature"      "{{{{")
				("newopentypefeature" "{{{")
				("newfontfeature"     "{{")
				("aliasfontfeature"   "{{")
				("aliasfontfeatureoption" "{{{"))
			      'function)
     (font-latex-add-keywords '(("liningnums"    "{"))
			      'type-command)
     (font-latex-add-keywords '(("strong"    "{"))
			      'bold-command)))
 LaTeX-dialect)

(defvar LaTeX-fontspec-package-options
  '("tuenc" "euenc" "math" "no-math" "config" "no-config" "quiet" "silent")
  "Package options for the fontspec package.")

;;; fontspec.el ends here
