;;; polyglossia.el --- AUCTeX style for `polyglossia.sty' version 1.42.0.

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

;; This file adds support for `polyglossia.sty' version 1.42.0.

;;; TODO:

;;  -- Create language specific styles with names `gloss-<lang>.el'.  They
;;     should add `text<lang>' macros, `<lang>' environments (`Arabic' for
;;     `arabic' language), and the others language-specific commands.

;;; Code:

(require 'tex) ;Indispensable when compiling the call to `TeX-auto-add-type'.

(TeX-auto-add-type "polyglossia-lang" "LaTeX")

;; Self Parsing -- see (info "(auctex)Hacking the Parser").
(defvar LaTeX-polyglossia-lang-regexp
  (concat "\\\\set\\(defaultlanguage\\|mainlanguage\\|otherlanguages?\\)"
	  "[ \t\n\r]*\\(?:\\[\\(.*\\)\\]\\)?[ \t\n\r]*{\\([A-Za-z, ]+\\)}")
  "Matches languages set with polyglossia macros.")

(defvar LaTeX-polyglossia-setkeys-regexp
  (concat "\\\\setkeys"
	  "[ \t\n\r]*{\\([A-Za-z]+\\)}[ \t\n\r]*{\\([^}]*\\)}")
  "Matches polyglossia languages options set using \"\setkeys\".")

(defvar LaTeX-auto-polyglossia-lang nil
  "Temporary for parsing polyglossia languages.")

(defvar LaTeX-auto-polyglossia-setkeys nil
  "Temporary for parsing polyglossia language options.")

(defun LaTeX-polyglossia-prepare ()
  "Clear some polyglossia variables before use."
  (setq LaTeX-auto-polyglossia-lang nil
	LaTeX-auto-polyglossia-setkeys nil
	LaTeX-polyglossia-lang-list nil))

(defun LaTeX-polyglossia-cleanup ()
  "Move languages and their options from
`LaTeX-auto-polyglossia-lang' to `LaTeX-polyglossia-lang-list'."
  ;; Example: now the value of `LaTeX-auto-polyglossia-lang' is something like
  ;;   '(("danish" "defaultlanguage" "")
  ;;     ("arabic" "otherlanguage" "locale=tunisia,numerals=maghrib")
  ;;     ("german" "otherlanguage" "spelling=new,script=latin")
  ;;     ("icelandic,brazil,sanskrit" "otherlanguages" ""))
  ;; We want to end up with a list like
  ;;   '(("danish" "defaultlanguage")
  ;;     ("arabic" "otherlanguage" "locale=tunisia" "numerals=maghrib")
  ;;     ("german" "otherlanguage" "spelling=new" "script=latin")
  ;;     ("icelandic" "otherlanguages")
  ;;     ("brazil" "otherlanguages")
  ;;     ("sanskrit" "otherlanguages" "script=Devanagari"))
  ;; with "script=Devanagari" option to "sanskrit" language set using
  ;; "\setkeys".
  ;; In each element of the alist, the key is the language, the second value is
  ;; the polyglossia command which set the language, the rest of values is the
  ;; list of options given to the language.
  (let (opts otheropts)
    (mapc
     (lambda (elt)
       (mapc
	(lambda (language)
	  ;; `opts' is the string of options for `language', set using
	  ;; "\setdefaultlanguage" or "\setotherlanguage".
	  (setq opts (cdr (cdr elt)))
	  ;; `otheropts' is the string of options for `language' set using
	  ;; "\setkeys".
	  (setq otheropts
		(car (cdr (assoc language LaTeX-auto-polyglossia-setkeys))))
	  (add-to-list
	   'LaTeX-polyglossia-lang-list
	   (append
	    (list language) (list (nth 1 elt))
	    (unless (equal opts '(""))
	      (LaTeX-listify-package-options (car opts)))
	    (if otheropts (LaTeX-listify-package-options otheropts))) t))
	(LaTeX-listify-package-options (car elt))))
     LaTeX-auto-polyglossia-lang)))

(add-hook 'TeX-auto-prepare-hook #'LaTeX-polyglossia-prepare)
(add-hook 'TeX-auto-cleanup-hook #'LaTeX-polyglossia-cleanup)
(add-hook 'TeX-update-style-hook #'TeX-auto-parse t)
;; Run style hooks for every active language.  This *has* to be done after
;; `TeX-auto-parse'.
(add-hook 'TeX-update-style-hook #'LaTeX-polyglossia-load-languages t)

(defvar LaTeX-polyglossia-language-list
  '("albanian" "amharic" "arabic" "armenian" "asturian" "bahasai" "bahasam"
    "basque" "bengali" "brazil" "breton" "bulgarian" "catalan" "coptic"
    "croatian" "czech" "danish" "divehi" "dutch" "english" "esperanto"
    "estonian" "farsi" "finnish" "french" "friulan" "galician" "german" "greek"
    "hebrew" "hindi" "icelandic" "interlingua" "irish" "italian" "kannada"
    "khmer" "korean" "lao" "latin" "latvian" "lithuanian" "lsorbian" "magyar"
    "malayalam" "marathi" "nko" "norsk" "nynorsk" "occitan" "piedmontese"
    "polish" "portuges" "romanian" "romansh" "russian" "samin" "sanskrit"
    "scottish" "serbian" "slovak" "slovenian" "spanish" "swedish" "syriac"
    "tamil" "telugu" "thai" "tibetan" "turkish" "turkmen" "ukrainian" "urdu"
    "usorbian" "vietnamese" "welsh")
  "List of languages supported by the polyglossia LaTeX package.")

(defun LaTeX-polyglossia-active-languages ()
  "Return a list of polyglossia languages used in the document.
The last language is the default one."
  (let (active-languages default)
    (mapc
     (lambda (elt)
       (setq default (or (string-equal "defaultlanguage" (nth 1 elt))
			 (string-equal "mainlanguage" (nth 1 elt))))
       ;; Append the language to the list if it's the default one.
       (add-to-list 'active-languages (car elt) default))
     LaTeX-polyglossia-lang-list)
    active-languages))

(defun LaTeX-polyglossia-lang-option-member (language option)
  "Return non-nil if OPTION has been given to polyglossia LANGUAGE.
The value is actually the tail of the list of options given to LANGUAGE."
  (member option (cdr (cdr (assoc language LaTeX-polyglossia-lang-list)))))

(defun LaTeX-arg-polyglossia-lang (_optional default multiple setkeys)
  "Prompt for language and its options with completion and insert them
as arguments.

This function is triggered by \"\setdefaultlanguage\",
\"\setotherlanguage\", \"\setotherlanguages\", and \"\setkeys\"
macros by polyglossia package.

OPTIONAL is ignored, if DEFAULT is non-nil treat inserted
language as default, if MULTIPLE is non-nil prompt for multiple
languages, if SETKEYS is non-nil insert options as second
mandatory argument."
  ;; DEFAULT =  t , MULTIPLE = nil, SETKEYS = nil: "\setdefaultlanguage".
  ;; DEFAULT = nil, MULTIPLE = nil, SETKEYS = nil: "\setotherlanguage".
  ;; DEFAULT = nil, MULTIPLE =  t , SETKEYS = nil: "\setotherlanguages".
  ;; DEFAULT = nil, MULTIPLE = nil, SETKEYS =  t : "\setkeys".
  (let ((language (funcall
		   (if multiple
		       'TeX-completing-read-multiple
		     'completing-read)
		   (if multiple "Languages: " "Language: ")
		   (if setkeys
		       (LaTeX-polyglossia-active-languages)
		     LaTeX-polyglossia-language-list)))
	var  options)
    (if multiple
	(mapc (lambda (elt) (TeX-run-style-hooks (concat "gloss-" elt)))
	      language)
      (TeX-run-style-hooks (concat "gloss-" language)))
    ;; "\setotherlanguages" doesn't take options, don't prompt for them.
    (setq options
	  (if multiple ""
	    (setq var (intern (format "LaTeX-polyglossia-%s-options-list" language)))
	    (if (and (boundp var) (symbol-value var))
		;; "\setdefaultlanguage" and "\setotherlanguage" use `options'
		;; as first optional argument; "\setkeys" uses `options' as
		;; second mandatory argument.
		(TeX-read-key-val (not setkeys) (symbol-value var))
	      ;; When `LaTeX-polyglossia-<lang>-options-list' is nil or not
	      ;; defined, don't prompt for options.
	      "")))
    (unless setkeys
      (let ((TeX-arg-opening-brace LaTeX-optop)
	    (TeX-arg-closing-brace LaTeX-optcl))
	(TeX-argument-insert options t)))
    (if multiple
	(setq language (mapconcat 'identity language ",")))
    (TeX-argument-insert language nil)
    (if setkeys
	(TeX-argument-insert options nil))))

(defun LaTeX-arg-polyglossiasetup-options (optional)
  "Prompt for setup options of polyglossia package.
If OPTIONAL is non-nil, insert the resulting value as an optional
argument, otherwise as a mandatory one."
  (TeX-arg-key-val optional
		   '(("language") ;; TODO: add completion in `fontspec.el', see
				  ;; "\newfontlanguage"s in `fontspec-xetex.sty'.
		     ("hyphennames")
		     ("script") ;; TODO: add completion in `fontspec.el', see
				;; "\newfontscript"s in `fontspec-xetex.sty'.
		     ("direction" ("RL" "LR"))
		     ("scripttag")
		     ("langtag")
		     ("hyphenmins")
		     ("frenchspacing" ("true" "false"))
		     ("indentfirst" ("true" "false"))
		     ("fontsetup" ("true" "false"))
		     ;; The following options aren't already implemented but are
		     ;; present in `polyglossia.sty' comments.
		     ;; ("nouppercase" ("true" "false"))
		     ;; ("localalph")
		     ;; ("localnumber")
		     )))

(defun LaTeX-polyglossia-load-languages ()
  "Load style files of babel active languages."
  (mapc (lambda (elt) (TeX-run-style-hooks (concat "gloss-" elt)))
	(LaTeX-polyglossia-active-languages)))

(TeX-add-style-hook
 "polyglossia"
 (lambda ()
   (TeX-check-engine-add-engines 'luatex 'xetex)
   (TeX-auto-add-regexp
    `(,LaTeX-polyglossia-lang-regexp (3 1 2) LaTeX-auto-polyglossia-lang))
   (TeX-auto-add-regexp
    `(,LaTeX-polyglossia-setkeys-regexp (1 2) LaTeX-auto-polyglossia-setkeys))
   (TeX-run-style-hooks "etoolbox" "makecmds" "xkeyval" "fontspec")
   (TeX-add-symbols
    '("setdefaultlanguage" (LaTeX-arg-polyglossia-lang  t  nil nil))
    '("setmainlanguage"    (LaTeX-arg-polyglossia-lang  t  nil nil))
    '("setotherlanguage"   (LaTeX-arg-polyglossia-lang nil nil nil))
    '("setotherlanguages"  (LaTeX-arg-polyglossia-lang nil  t  nil))
    '("setkeys"            (LaTeX-arg-polyglossia-lang nil nil  t ))
    '("PolyglossiaSetup"   (TeX-arg-eval completing-read "Language: "
					 (LaTeX-polyglossia-active-languages))
      LaTeX-arg-polyglossiasetup-options)
    "selectbackgroundlanguage"
    '("resetdefaultlanguage" ["argument"] 1)
    "normalfontlatin"
    "rmfamilylatin"
    "sffamilylatin"
    "ttfamilylatin"
    "selectlanguage"
    "foreignlanguage")

   (TeX-declare-expert-macros
    "polyglossia"
    "PolyglossiaSetup" "selectbackgroundlanguage" "resetdefaultlanguage"
    "normalfontlatin" "rmfamilylatin" "sffamilylatin" "ttfamilylatin"
    "selectlanguage" "foreignlanguage")

   ;; Fontification
   (when (and (featurep 'font-latex)
	      (eq TeX-install-font-lock 'font-latex-setup))
     (font-latex-add-keywords '(("setdefaultlanguage" "[{")
				("setmainlanguage" "[{")
				("setotherlanguage" "[{")
				("setotherlanguages" "{")
				("setkeys" "{{"))
			      'function)))
 LaTeX-dialect)

;; TODO: move each option variable in its specific `gloss-<lang>.el' file.
(defvar LaTeX-polyglossia-arabic-options-list
  '(("calendar" ("gregorian" "islamic"))
    ("locale" ("default" "mashriq" "libya" "algeria" "tunisia" "morocco" "mauritania"))
    ("numerals" ("mashriq" "maghrib"))
    ("abjadjimnotail" ("false" "true")))
  "Arabic language options for the polyglossia package.")

(defvar LaTeX-polyglossia-bengali-options-list
  '(("numerals" ("Western" "Devanagari"))
    ("changecounternumbering" ("true" "false")))
  "Bengali language options for the polyglossia package.")

(defvar LaTeX-polyglossia-catalan-options-list
  '(("babelshorthands" ("true" "false")))
  "Catalan language options for the polyglossia package.")

(defvar LaTeX-polyglossia-dutch-options-list
  '(("babelshorthands" ("true" "false")))
  "Dutch language options for the polyglossia package.")

(defvar LaTeX-polyglossia-english-options-list
  '(("variant" ("american" "usmax" "british" "australian" "newzealand"))
    ("ordinalmonthday" ("true" "false")))
  "English language options for the polyglossia package.")

(defvar LaTeX-polyglossia-farsi-options-list
  '(("numerals" ("western" "eastern"))
    ;; ("locale") ;; not yet implemented
    ;; ("calendar") ;; not yet implemented
    )
  "Farsi language options for the polyglossia package.")

(defvar LaTeX-polyglossia-german-options-list
  '(("variant" ("german" "austrian" "swiss"))
    ("spelling" ("new" "old"))
    ("latesthyphen" ("true" "false"))
    ("babelshorthands" ("true" "false"))
    ("script" ("latin" "fraktur")))
  "German language options for the polyglossia package.")

(defvar LaTeX-polyglossia-greek-options-list
  '(("variant" ("monotonic" "polytonic" "ancient"))
    ("numerals" ("greek" "arabic"))
    ("attic" ("true" "false")))
  "Greek language options for the polyglossia package.")

(defvar LaTeX-polyglossia-hebrew-options-list
  '(("numerals" ("hebrew" "arabic"))
    ("calendar" ("hebrew" "gregorian")))
  "Hebrew language options for the polyglossia package.")

(defvar LaTeX-polyglossia-hindi-options-list
  '(("numerals" ("Western" "Devanagari")))
  "Hindi language options for the polyglossia package.")

(defvar LaTeX-polyglossia-lao-options-list
  '(("numerals" ("lao" "arabic")))
  "Lao language options for the polyglossia package.")

(defvar LaTeX-polyglossia-russian-options-list
  '(("spelling" ("modern" "old"))
    ("babelshorthands" ("true" "false")))
  "Russian language options for the polyglossia package.")

(defvar LaTeX-polyglossia-sanskrit-options-list
  '(("Script" ("Devanagari")))
  "Sanskrit language options for the polyglossia package.")

(defvar LaTeX-polyglossia-serbian-options-list
  '(("script" ("cyrillic" "latin")))
  "Serbian language options for the polyglossia package.")

(defvar LaTeX-polyglossia-syriac-options-list
  '(("numerals" ("western" "eastern" "abjad")))
  "Syriac language options for the polyglossia package.")

(defvar LaTeX-polyglossia-thai-options-list
  '(("numerals" ("thai" "arabic")))
  "Thai language options for the polyglossia package.")

(defvar LaTeX-polyglossia-package-options
  '("babelshorthands" "localmarks" "nolocalmarks" "quiet")
  "Package options for the polyglossia package.")

;;; polyglossia.el ends here
