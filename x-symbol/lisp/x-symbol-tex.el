;;; x-symbol-tex.el --- token language "TeX macro" for package x-symbol

;; Copyright (C) 1996-2003 Free Software Foundation, Inc.
;;
;; Author: Christoph Wedler <wedler@users.sourceforge.net>
;; Maintainer: (Please use `M-x x-symbol-package-bug' to contact the maintainer)
;; Version: 4.5.X
;; Keywords: WYSIWYG, LaTeX, wp, math, internationalization
;; X-URL: http://x-symbol.sourceforge.net/

;; This program is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 2, or (at your option)
;; any later version.
;;
;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.
;;
;; You should have received a copy of the GNU General Public License
;; along with this program; if not, write to the Free Software
;; Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.

;;; Commentary:

;; If you want to use package x-symbol, please visit the URL (use
;; \\[x-symbol-package-web]) and read the info (use \\[x-symbol-package-info]).

;; Token language tex is registered in x-symbol-hooks.

;;; Code:

(provide 'x-symbol-tex)

(eval-when-compile
  (require 'cl)
  (require 'x-symbol-macs)
  (require 'x-symbol))

(eval-when-compile
  (defvar TeX-master)
  (defvar file) (defvar line) (defvar offset)
  (defvar string) (defvar after-string))

;; (defgroup x-symbol-tex ...) in x-symbol-hooks.el
;; (defcustom x-symbol-tex-name ...) in x-symbol-hooks.el
;; (defcustom x-symbol-tex-modes ...) in x-symbol-hooks.el


;;;===========================================================================
;;;  Auto-style
;;;===========================================================================

(defcustom x-symbol-tex-auto-style
  '(;; during eval, `buffer-file-name' is sans-version and mode-suffixes
    (if buffer-file-name (string-match "\\.tex\\'" buffer-file-name) t)
    (if x-symbol-mode
	(x-symbol-auto-coding-alist x-symbol-tex-auto-coding-alist nil
				    (if x-symbol-tex-coding-master
					'x-symbol-tex-auto-coding-alist)))
    x-symbol-coding (not x-symbol-mode)
    x-symbol-mode x-symbol-mode)
  "Values for X-Symbol's buffer-local variables with language `tex'.
See language access `x-symbol-LANG-auto-style'."
  :group 'x-symbol-tex
  :group 'x-symbol-mode
  :type 'x-symbol-auto-style)

(defcustom x-symbol-tex-auto-coding-alist
  '(("\\\\usepackage[ \t]*\\[\\([A-Za-z]+[0-9]+\\)\\]{inputenc}" 1
     ("latin1" . iso-8859-1)
     ("latin2" . iso-8859-2)
     ("latin3" . iso-8859-3)
     ("latin5" . iso-8859-9)
     ("latin9" . iso-8859-15))
    ("\\`[ \t]*%&.*[  \t]+--?translate-file[ \t]*=[ \t]*i\\([A-Za-z]+[0-9]+\\)-" 1
     ("l1" . iso-8859-1)
     ("l2" . iso-8859-2)))
  "*Alist used to determine the file coding with language `tex'.
Used in the default value of `x-symbol-tex-auto-style'.  See variable
`x-symbol-auto-coding-alist' for details."
  :group 'x-symbol-tex
  :group 'x-symbol-mode
  :type 'x-symbol-auto-coding)

(defcustom x-symbol-tex-coding-master 'TeX-master
  "*If non-nil, symbol of local variable with name of master file.
Used inside function `x-symbol-tex-auto-coding-alist'."
  :group 'x-symbol-tex
  :group 'x-symbol-mode
  :type 'boolean)


;;;===========================================================================
;;;  General language accesses, see `x-symbol-language-access-alist'
;;;===========================================================================

(defcustom x-symbol-tex-modeline-name "tex"
  "Modeline name of token language `tex'.
See language access `x-symbol-LANG-modeline-name'."
  :group 'x-symbol-tex
  :type 'string)

(defcustom x-symbol-tex-header-groups-alist nil
  "Header/submenu specification of the specific menu for language `tex'.
See language access `x-symbol-LANG-header-groups-alist'."
  :group 'x-symbol-tex
  :group 'x-symbol-input-init
  :type 'x-symbol-headers)

(defcustom x-symbol-tex-electric-ignore 'x-symbol-tex-default-electric-ignore
  "Specification restricting input method ELECTRIC with language `tex'.
See language access `x-symbol-LANG-electric-ignore'."
  :group 'x-symbol-tex
  :group 'x-symbol-input-control
  :type 'x-symbol-function-or-regexp)

(defcustom x-symbol-tex-electric-ignore-regexp "[A-Za-z]~\\'"
  "*Regexp matching contexts not to be used for input method ELECTRIC.
Used by `x-symbol-tex-default-electric-ignore'."
  :group 'x-symbol-tex
  :group 'x-symbol-input-control
  :type '(choice (const :tag "None" nil) regexp))

(defcustom x-symbol-tex-token-suppress-space t
  "*If non-nil, suppress space after text-mode control words.
If non-nil, inserting SPC without prefix argument after a text-mode only
control word will only replace the control word with the character
according to `x-symbol-token-input', it will not insert the space."
  :group 'x-symbol-tex
  :group 'x-symbol-input-control
  :type 'boolean)

(defvar x-symbol-tex-extra-menu-items
  '(("Conversion"
     "---"
     ["tex: Decode Accented Letters (alt)" x-symbol-tex-xdecode-latex
      :active (and x-symbol-mode (not buffer-read-only))]
     ["tex: Remove Braces around Letters" x-symbol-tex-xdecode-old
      :active (and x-symbol-mode (not buffer-read-only))]))
  "Extra menu entries in menu for language `tex'.
See language access `x-symbol-LANG-extra-menu-items'.")

(defvar x-symbol-tex-token-grammar
  '(x-symbol-make-grammar
    :encode-spec x-symbol-tex-encode
    :decode-regexp "\\\\\\(?:[@A-Za-z]+\\|[-{}#_&|%$]\\|[.~^\"'`=]\\(?:[A-Za-z]\\|{}\\|\\(\\\\\\)[ij][@A-Za-z]?\\)\\)"
    :decode-spec x-symbol-tex-decode
    :input-regexp ("\\\\\\(?:[.~^\"'`=]\\\\[ij]\\|[ckvuHr]\\(?: [A-Za-z]\\|{ ?}\\)\\)\\'" "\\\\\\(?:[@A-Za-z]+\\|[-{}#_&|%$]\\|[.~^\"'`=]\\(?:[A-Za-z]\\|{}\\)\\)\\'")
    :input-spec x-symbol-tex-token-input
    :token-list x-symbol-tex-default-token-list
    :after-init x-symbol-tex-after-init-language)
  "Grammar of token language `tex'.
See language access `x-symbol-LANG-token-grammar'.")

;; The following vars could be made customizable, but it would not be a good
;; idea if different users have a different decode behavior:

(defvar x-symbol-tex-verb-delimiter-regexp "[-!#$&*+/=?^|~]"
  "Regexp matching delimiters of \verb arguments not to be decoded.")
;; by default: not letter, digits, punctuation and quotation

(defvar x-symbol-tex-env-verbatim-regexp "{verbatim\\*?}"
  "Regexp matching environments with a contents not to be decoded.
The regexp should also match the surrounding braces.")

(defvar x-symbol-tex-env-tabbing-regexp "{tabbing}"
  "Regexp matching environments with a contents not to be decoded.
The regexp should also match the surrounding braces.")

(defvar x-symbol-tex-user-table nil
  "User table defining TeX macros, used in `x-symbol-tex-table'.")

(defvar x-symbol-tex-generated-data nil
  "Generated data for token language `tex'.
See language access `x-symbol-LANG-generated-data'.")


;;;===========================================================================
;;;  Image support
;;;===========================================================================

(defcustom x-symbol-tex-master-directory 'x-symbol-tex-default-master-directory
  "Specification of the master directory for images for language `tex'.
See language access `x-symbol-LANG-master-directory'."
  :group 'x-symbol-tex
  :group 'x-symbol-image-language
  :type 'function)

(defcustom x-symbol-tex-image-searchpath
  (let ((dirs (or (getenv "TEXPICTS") (getenv "TEXINPUTS")))
	dir result)
    (if dirs (setq dirs (if (fboundp 'split-path)
			    (split-path dirs)
			  (parse-colon-path dirs))))
    (while dirs
      (when (setq dir (pop dirs))
	(or (member dir '("" "/"))	; `parse-colon-path': foo// -> /
	    (member (setq dir (file-name-as-directory dir)) result)
	    (push dir result))))
    (nreverse (if (member "./" result) result (cons "./" result))))
  "Search path for implicitly relative image file names.
See language access `x-symbol-LANG-image-searchpath'."
  :group 'x-symbol-tex
  :group 'x-symbol-image-language
  :type '(repeat directory))

(defcustom x-symbol-tex-image-cached-dirs '("figures/")
  "Directory parts of images stored in the memory cache.
See language access `x-symbol-LANG-image-cached-dirs'."
  :group 'x-symbol-tex
  :group 'x-symbol-image-language
  :type '(repeat string))

(defcustom x-symbol-tex-image-keywords
  ;; keep it short!
  '("\\.\\(eps\\|ps\\(tex\\)?\\|gif\\|png\\|jpe?g\\|pdf\\)\\'"
    ("\\\\epsf\\(box\\|file\\)[ \t]*\\(\\[[^][\n]*\\]\\)?{\\([^ \t\n,{}]+\\.e?ps\\)}" 3)
    ("\\\\e?psfig[ \t]*{file=\\([^ \t\n,{}]+\\.e?ps\\)[^\n{}]*}" 1)
    ("\\\\includegraphics\\*?[ \t]*\\(\\[[^][\n]*\\]\\)?\\(\\[[^][\n]*\\]\\)?{\\([^ \t\n,{}]+\\)}" 3 ".\\.[^./]+\\'" ".eps")
    ("\\\\input[ \t]*{\\([^ \t\n,{}]+\\.pstex\\)_t}" 1))
  "Keywords for image insertion commands of language `tex'.
See language access `x-symbol-LANG-image-keywords'."
  :group 'x-symbol-tex
  :group 'x-symbol-image-language
  :type 'x-symbol-image-keywords)


;;;===========================================================================
;;;  Super- and Subscripts
;;;===========================================================================

(defcustom x-symbol-tex-subscript-matcher 'x-symbol-tex-subscript-matcher
  "Function matching super-/subscripts for language `tex'.
See language access `x-symbol-LANG-subscript-matcher'."
  :group 'x-symbol-tex
  :type 'function)

(defcustom x-symbol-tex-invisible-braces nil
  "TODO"
  :group 'x-symbol-tex
  :type 'boolean)

(defcustom x-symbol-tex-font-lock-allowed-faces
  '(tex-math-face
    font-lock-string-face font-lock-doc-string-face font-latex-math-face)
  "*Faces which are allowed when fontifying simple super- and subscripts.
Package x-symbol only uses super- and subscripts if they are in braces,
if the \"^\"/\"_\" has not been fontified yet or is only fontified with
faces which appear in this list.  Value t means, always use super- and
subscripts."
  :group 'x-symbol-tex
  :type '(repeat (symbol :tag "Face name"))) ; face would create faces... :-(

(defvar x-symbol-tex-font-lock-regexp
  "[^\000-\040\134\177-\237]\\([_^]\\)\\([^ \t\n\f%\\}^_$#&~]\\|\\\\[@A-Za-z]+\\)"
  "Regexp matching the prefix of super-/subscripts.
The first regexp group should match the super-/subscript command.")

(defvar x-symbol-tex-font-lock-limit-regexp "[\n^_]"
  "Regexp matching the limit for the end of super-/subscripts.
This regexp should match the end of line.")


;;;===========================================================================
;;;  Charsym Info
;;;===========================================================================

(defface x-symbol-tex-math-face
  '((((class color) (background light))
     (:foreground "purple3")))
  "*Face, normally used for tokens only allowed in TeX's math mode.
Used in `x-symbol-tex-class-face-alist'."
  :group 'x-symbol-tex
  :group 'x-symbol-info-general)

(defface x-symbol-tex-text-face
  '((((class color) (background light))
     (:foreground "Royalblue")))
  "*Face, normally used for tokens only allowed in TeX's text mode.
Used in `x-symbol-tex-class-face-alist'."
  :group 'x-symbol-tex
  :group 'x-symbol-info-general)

(defcustom x-symbol-tex-class-alist
  '((text)
    (math)
    (accent "accent" (x-symbol-info-face))
    (aletter "acc.letter" (x-symbol-info-face))
    (letter "letter" (x-symbol-info-face))
    (greek "greek" (x-symbol-info-face))
    (ordinary "ordinary" (x-symbol-info-face))
    (binop "binop" (x-symbol-info-face))
    (bigop "bigop" (x-symbol-info-face))
    (relation "relation" (x-symbol-info-face))
    (delim "delimiter" (x-symbol-info-face))
    (punct "punctuation" (x-symbol-info-face))
    (quote "quote" (x-symbol-info-face))
    (space "space" (x-symbol-info-face))
    (special "special" (x-symbol-info-face))
    (latexsym "latexsym.sty" (x-symbol-emph-info-face)) ; w/ latexsym or amssymb
    (amssymb "amssymb.sty" (x-symbol-emph-info-face))
    (stmaryrd "stmaryrd.sty" (x-symbol-emph-info-face))
    (T1 "T1 fontenc.sty" (x-symbol-emph-info-face))
    (correct-T1 "correct: T1 fontenc.sty" (x-symbol-info-face))
    (inputenc "inputenc.sty" (x-symbol-emph-info-face)) ; v0.97
    (inputenc-unavail "inputenc.sty: unavailable" (x-symbol-emph-info-face))
;;;    (inputenc-incorrect "old inputenc: incorrect" . red) ; IMHO
    (gobbles-spc "gobbles space" (x-symbol-info-face))
    (user "user" (x-symbol-emph-info-face))
    (VALID "unknown TeX class" (x-symbol-emph-info-face))
    (INVALID "no TeX macro" (x-symbol-emph-info-face)))
  "Token classes displayed by info in echo area, for language `tex'.
See language access `x-symbol-LANG-class-alist'."
  :group 'x-symbol-tex
  :group 'x-symbol-info-strings
  :type 'x-symbol-class-info)

(defcustom x-symbol-tex-class-face-alist
  '((math x-symbol-tex-math-face (x-symbol-tex-math-face))
    (text x-symbol-tex-text-face (x-symbol-tex-text-face)))
  "Color scheme in language specific grid and info, for language `tex'.
See language access `x-symbol-LANG-class-face-alist'."
  :group 'x-symbol-tex
  :group 'x-symbol-input-init
  :group 'x-symbol-info-general
  :type 'x-symbol-class-faces)


;;;===========================================================================
;;;  Misc
;;;===========================================================================

;;;###autoload
(defun x-symbol-tex-auto-coding-alist (alist &optional limit)
  "Find encoding in file `x-symbol-tex-coding-master'.
For ALIST and LIMIT, see `x-symbol-auto-coding-alist'."
  ;; called inside `save-excursion'
  (and (local-variable-p x-symbol-tex-coding-master (current-buffer))
       ;; I don't like the idea of having to visit a second file in order to
       ;; visit first one, but people have complained about X-Symbol not
       ;; recognizing \usepackage[latinN]{inputenc} in the master file...  Not
       ;; only that, a file should describe its encoding itself...
       (stringp (symbol-value x-symbol-tex-coding-master))
       (condition-case nil
	   (let ((master (expand-file-name
			  (symbol-value x-symbol-tex-coding-master))))
	     ;; I have absolutely no intention to use `find-file-noselect'
	     ;; here, i.e., decode the master file via X-Symbol in order to get
	     ;; the correct coding for the current buffer
	     (set-buffer (get-buffer-create " x-symbol master"))
	     (insert-file-contents master nil nil nil
				   ;; 5th arg not t with empty accessible part
				   ;; (XEmacs bug workaround: would infloop)
				   (> (point-max) (point-min)))
	     (x-symbol-auto-coding-alist alist limit))
	 (error nil))))

(defun x-symbol-tex-default-master-directory ()
  "Convert NAME to absolute file name, respecting `TeX-master'.
Variable `TeX-master' should be buffer-local and a string to be used.
Used as default value of `x-symbol-tex-master-directory'."
  (and (local-variable-p 'TeX-master (current-buffer))
       (stringp TeX-master)
       (file-name-directory (expand-file-name TeX-master))))

(defun x-symbol-tex-default-electric-ignore (context charsym)
  "Non nil, if CONTEXT should not be replaced by input method ELECTRIC.
Return non-nil if `x-symbol-tex-electric-ignore-regexp' matches CONTEXT
or if CHARSYM represents a TeX macro which can only be used in math mode
whereas point is in a text area or vice versa.  This function uses
package \"texmathp\" whose variables you might want to customize.  Used
as default value for `x-symbol-tex-electric-ignore'."
  (or (and x-symbol-tex-electric-ignore-regexp
	   (string-match x-symbol-tex-electric-ignore-regexp context))
      (condition-case nil
	  (let ((class (car (gethash charsym
				     (x-symbol-generated-token-classes
				      x-symbol-tex-generated-data)))))
	    (cond ((eq class 'math) (not (texmathp)))
		  ((eq class 'text) (texmathp))))
	(error nil))))


;;;===========================================================================
;;;  The tables
;;;===========================================================================

(defun x-symbol-tex-default-token-list (tokens)
  (if (stringp tokens)
      (list (cons (if (string-match "\\\\ \\'" tokens)
		      (concat (substring tokens 0 (match-beginning 0)) "{ }")
		    tokens)
		  (if (string-match "\\\\[A-Za-z]+\\'" tokens) t)))
    (mapcar (lambda (x)
	      (cons x (if (string-match "\\\\[A-Za-z]+\\'" x) 'math)))
	    tokens)))

(defun x-symbol-tex-after-init-language ()
  (let ((decode-obarray (x-symbol-generated-decode-obarray
			 x-symbol-tex-generated-data))
	(tex-accent '(nil tex-accent)))
    (set (intern "\\begin" decode-obarray) '(nil tex-begin))
    (set (intern "\\end" decode-obarray)   '(nil tex-end))
    (set (intern "\\verb" decode-obarray)  '(nil tex-verb))
    (set (intern "\\c" decode-obarray) tex-accent)
    (set (intern "\\k" decode-obarray) tex-accent)
    (set (intern "\\v" decode-obarray) tex-accent)
    (set (intern "\\u" decode-obarray) tex-accent)
    (set (intern "\\H" decode-obarray) tex-accent)
    (set (intern "\\r" decode-obarray) tex-accent)))


;;;===========================================================================
;;;  The tables
;;;===========================================================================

(defvar x-symbol-tex-required-fonts nil
  "Features providing required fonts for language `tex'.
See language access `x-symbol-LANG-required-fonts'.")

(defvar x-symbol-tex-latin1-table
  '((nobreakspace (space) . "\\nobreakspace")
    (exclamdown (text punct) . "\\textexclamdown")
    (cent (text inputenc-unavail) . "\\textcent")
    (sterling (ordinary) . "\\pounds")
    (currency (text inputenc) . "\\textcurrency")
    (yen (text inputenc-unavail) . "\\textyen")
    (brokenbar (text inputenc-unavail) . "\\textbrokenbar")
    (section (ordinary) . "\\S")
    (diaeresis (text accent) . "\\\"{}")
    (copyright (text ordinary) . "\\textcopyright")
    (ordfeminine (text ordinary inputenc) . "\\textordfeminine")
    (guillemotleft (text quote T1) . "\\guillemotleft")
    (notsign (math ordinary) "\\lnot" "\\neg")
    (hyphen (special) "\\-")
    (registered (text ordinary) . "\\textregistered")
    (macron (text accent) . "\\={}")
    (degree (text ordinary inputenc) . "\\textdegree")
    (plusminus (math binop) "\\pm")
    (twosuperior (math ordinary inputenc) "\\mathtwosuperior")
    (threesuperior (math ordinary inputenc) "\\maththreesuperior")
    (acute (text accent) . "\\'{}")
    (mu1 (math greek user) "\\mathmicro")
    (paragraph (ordinary) . "\\P")
    (periodcentered (text punct) . "\\textperiodcentered")
    (cedilla (text accent) . "\\c\\ ")
    (onesuperior (math ordinary inputenc) "\\mathonesuperior")
    (masculine (text ordinary inputenc) . "\\textordmasculine")
    (guillemotright (text quote T1) . "\\guillemotright")
    (onequarter (text ordinary inputenc) . "\\textonequarter")
    (onehalf (text ordinary inputenc) . "\\textonehalf")
    (threequarters (text ordinary inputenc) . "\\textthreequarters")
    (questiondown (text punct) . "\\textquestiondown")
    (Agrave (text aletter) . "\\`A")
    (Aacute (text aletter) . "\\'A")
    (Acircumflex (text aletter) . "\\^A")
    (Atilde (text aletter) . "\\~A")
    (Adiaeresis (text aletter) . "\\\"A")
    (Aring (text aletter) . "\\AA")
    (AE (text letter) . "\\AE")
    (Ccedilla (text aletter) . "\\c C")
    (Egrave (text aletter) . "\\`E")
    (Eacute (text aletter) . "\\'E")
    (Ecircumflex (text aletter) . "\\^E")
    (Ediaeresis (text aletter) . "\\\"E")
    (Igrave (text aletter) . "\\`I")
    (Iacute (text aletter) . "\\'I")
    (Icircumflex (text aletter) . "\\^I")
    (Idiaeresis (text aletter) . "\\\"I")
    (ETH (text letter T1) . "\\DH")
    (Ntilde (text aletter) . "\\~N")
    (Ograve (text aletter) . "\\`O")
    (Oacute (text aletter) . "\\'O")
    (Ocircumflex (text aletter) . "\\^O")
    (Otilde (text aletter) . "\\~O")
    (Odiaeresis (text aletter) . "\\\"O")
    (multiply (math binop) "\\times")
    (Ooblique (text letter) . "\\O")
    (Ugrave (text aletter) . "\\`U")
    (Uacute (text aletter) . "\\'U")
    (Ucircumflex (text aletter) . "\\^U")
    (Udiaeresis (text aletter) . "\\\"U")
    (Yacute (text aletter) . "\\'Y")
    (THORN (text letter T1) . "\\TH")
    (ssharp (text letter) . "\\ss")
    (agrave (text aletter) . "\\`a")
    (aacute (text aletter) . "\\'a")
    (acircumflex (text aletter) . "\\^a")
    (atilde (text aletter) . "\\~a")
    (adiaeresis (text aletter) . "\\\"a")
    (aring (text aletter) . "\\aa")
    (ae (text letter) . "\\ae")
    (ccedilla (text aletter) . "\\c c")
    (egrave (text aletter) . "\\`e")
    (eacute (text aletter) . "\\'e")
    (ecircumflex (text aletter) . "\\^e")
    (ediaeresis (text aletter) . "\\\"e")
    (igrave (text aletter) . "\\`\\i")
    (iacute (text aletter) . "\\'\\i")
    (icircumflex (text aletter) . "\\^\\i")
    (idiaeresis (text aletter) . "\\\"\\i")
    (eth (text letter T1) . "\\dh")
    (ntilde (text aletter) . "\\~n")
    (ograve (text aletter) . "\\`o")
    (oacute (text aletter) . "\\'o")
    (ocircumflex (text aletter) . "\\^o")
    (otilde (text aletter) . "\\~o")
    (odiaeresis (text aletter) . "\\\"o")
    (division (math binop) "\\div")
    (oslash (text letter) . "\\o")
    (ugrave (text aletter) . "\\`u")
    (uacute (text aletter) . "\\'u")
    (ucircumflex (text aletter) . "\\^u")
    (udiaeresis (text aletter) . "\\\"u")
    (yacute (text aletter) . "\\'y")
    (thorn (text letter T1) . "\\th")
    (ydiaeresis (text aletter) . "\\\"y"))
  "Table defining TeX macros, see `x-symbol-tex-table'.")

(defvar x-symbol-tex-latinN-table
  '((Aogonek (text aletter T1) . "\\k A")
    (breve (text accent) . "\\u{}")
    (Lslash (text letter) . "\\L")
    (Lcaron (text aletter correct-T1) . "\\v L")
    (Sacute (text aletter) . "\\'S")
    (Scaron (text aletter) . "\\v S")
    (Scedilla (text aletter) . "\\c S")
    (Tcaron (text aletter) . "\\v T")
    (Zacute (text aletter) . "\\'Z")
    (Zcaron (text aletter) . "\\v Z")
    (Zdotaccent (text aletter) . "\\.Z")
    (aogonek (text aletter T1) . "\\k a")
    (ogonek (text accent T1) . "\\k\\ ")
    (lslash (text letter) . "\\l")
    (lcaron (text aletter correct-T1) . "\\v l")
    (sacute (text aletter) . "\\'s")
    (caron (text accent) . "\\v{}")
    (scaron (text aletter) . "\\v s")
    (scedilla (text aletter) . "\\c s")
    (tcaron (text aletter correct-T1) . "\\v t")
    (zacute (text aletter) . "\\'z")
    (hungarumlaut (text accent) . "\\H{}")
    (zcaron (text aletter) . "\\v z")
    (zdotaccent (text aletter) . "\\.z")
    (Racute (text aletter) . "\\'R")
    (Abreve (text aletter) . "\\u A")
    (Lacute (text aletter) . "\\'L")
    (Cacute (text aletter) . "\\'C")
    (Ccaron (text aletter) . "\\v C")
    (Eogonek (text aletter T1) . "\\k E")
    (Ecaron (text aletter) . "\\v E")
    (Dcaron (text aletter) . "\\v D")
    (Dbar (text letter inputenc T1) . "\\DJ")
    (Nacute (text aletter) . "\\'N")
    (Ncaron (text aletter) . "\\v N")
    (Ohungarumlaut (text aletter) . "\\H O")
    (Rcaron (text aletter) . "\\v R")
    (Uring (text aletter) . "\\r U")
    (Uhungarumlaut (text aletter) . "\\H U")
    (Tcedilla (text aletter) . "\\c T")
    (racute (text aletter) . "\\'r")
    (abreve (text aletter) . "\\u a")
    (lacute (text aletter) . "\\'l")
    (cacute (text aletter) . "\\'c")
    (ccaron (text aletter) . "\\v c")
    (eogonek (text aletter T1) . "\\k e")
    (ecaron (text aletter) . "\\v e")
    (dcaron (text aletter correct-T1) . "\\v d")
    (dbar (text letter inputenc T1) . "\\dj")
    (nacute (text aletter) . "\\'n")
    (ncaron (text aletter) . "\\v n")
    (ohungarumlaut (text aletter) . "\\H o")
    (rcaron (text aletter) . "\\v r")
    (uring (text aletter) . "\\r u")
    (uhungarumlaut (text aletter) . "\\H u")
    (tcedilla (text aletter) . "\\c t")
    (dotaccent (text accent) . "\\.{}")
    (Hbar (text letter inputenc-unavail) . "\\textmalteseH")
    (Hcircumflex (text aletter) . "\\^H")
    (Idotaccent (text aletter) . "\\.I")
    (Gbreve (text aletter) . "\\u G")
    (Jcircumflex (text aletter) . "\\^J")
    (hbar (text letter inputenc-unavail) . "\\textmalteseh")
    (hcircumflex (text aletter) . "\\^h")
    (dotlessi (text letter) . "\\i")
    (gbreve (text aletter) . "\\u g")
    (jcircumflex (text aletter) . "\\^\\j")
    (Cdotaccent (text aletter) . "\\.C")
    (Ccircumflex (text aletter) . "\\^C")
    (Gdotaccent (text aletter) . "\\.G")
    (Gcircumflex (text aletter) . "\\^G")
    (Ubreve (text aletter) . "\\u U")
    (Scircumflex (text aletter) . "\\^S")
    (cdotaccent (text aletter) . "\\.c")
    (ccircumflex (text aletter) . "\\^c")
    (gdotaccent (text aletter) . "\\.g")
    (gcircumflex (text aletter) . "\\^g")
    (ubreve (text aletter) . "\\u u")
    (scircumflex (text aletter) . "\\^s")
    (euro (text ordinary inputenc-unavail) . "\\texteuro")
    (OE (text letter) . "\\OE")
    (oe (text letter) . "\\oe")
    (Ydiaeresis (text aletter) . "\\\"Y"))
  "Table defining TeX macros, see `x-symbol-tex-table'.")

;; Characters w/ NEW weren't defined before, w/ (NEW) were defined at other
;; positions.  If we get problems in the nomule version (e.g., w/ font-lock),
;; we could be forced to move these characters to the xsymb1 font.
(defvar x-symbol-tex-xsymb0-table
  ;; With elems (SYMBOL (TEX-CLASS ...) TEX-MACRO ...)
  '((numbersign1 (ordinary) "\\#")	; NEW
    ;;(existential)
    (suchthat (math relation) "\\ni" "\\owns")
    (asterisk1 (math binop) "\\ast")		; NEW
    ;;(comma1 (mark) "\\quotesinglbase")	; not in {}! (spacing)
    (period1 (math punct) "\\ldotp")		; (NEW)
    (colon1 (math punct) "\\colon")		; (NEW)
    (congruent (math relation) "\\cong")
    (Delta (math greek) "\\Delta")
    (Phi (math greek) "\\Phi")
    (Gamma (math greek) "\\Gamma")
    (theta1 (math greek) "\\vartheta")
    (Lambda (math greek) "\\Lambda")
    (Pi (math greek) "\\Pi")
    (Theta (math greek) "\\Theta")
    (Sigma (math greek) "\\Sigma")
    (sigma1 (math greek) "\\varsigma")
    (Omega (math greek) "\\Omega")
    (Xi (math greek) "\\Xi")
    (Psi (math greek) "\\Psi")
    ;;(therefore (math relation) "\\therefore")
    (perpendicular (math ordinary) "\\bot")	; (NEW)
    (underscore1 (ordinary) "\\_")	; NEW
    ;;(radicalex)
    (alpha (math greek) "\\alpha")
    (beta (math greek) "\\beta")
    (chi (math greek) "\\chi")
    (delta (math greek) "\\delta")
    (epsilon (math greek) "\\epsilon")
    (phi (math greek) "\\phi")
    (gamma (math greek) "\\gamma")
    (eta (math greek) "\\eta")
    (iota (math greek) "\\iota")
    (phi1 (math greek) "\\varphi")
    (kappa (math greek) "\\kappa")
    (lambda (math greek) "\\lambda")
    (mu (math greek) "\\mu")
    (nu (math greek) "\\nu")
    (pi (math greek) "\\pi")
    (theta (math greek) "\\theta")
    (rho (math greek) "\\rho")
    (sigma (math greek) "\\sigma")
    (tau (math greek) "\\tau")
    (upsilon (math greek) "\\upsilon")
    (omega1 (math greek) "\\varpi")
    (omega (math greek) "\\omega")
    (xi (math greek) "\\xi")
    (psi (math greek) "\\psi")
    (zeta (math greek) "\\zeta")
    (bar1 (math relation) "\\mid")		; (NEW)
    (similar (math relation) "\\sim")
    (Upsilon1 (math greek) "\\Upsilon")
    (minute (math ordinary) "\\prime")
    (lessequal (math relation) "\\leq" "\\le")
    ;;(fraction)
    (infinity (math ordinary) "\\infty")
    (florin (text ordinary user) . "\\textflorin") ; NEW
    (club (math ordinary) "\\clubsuit")
    (diamond (math ordinary) "\\diamondsuit")
    (heart (math ordinary) "\\heartsuit")
    (spade (math ordinary) "\\spadesuit")
    (arrowboth (math relation) "\\leftrightarrow")
    (arrowleft (math relation) "\\gets" "\\leftarrow")
    (arrowup (math relation delim) "\\uparrow")
    (arrowright (math relation) "\\to" "\\rightarrow")
    (arrowdown (math relation delim) "\\downarrow")
    (ring (text accent) . "\\r{}")	; NEW
    ;;(second)
    (greaterequal (math relation) "\\geq" "\\ge")
    (proportional (math relation) "\\propto")
    (partialdiff (math ordinary) "\\partial")
    (bullet (math binop) "\\bullet")
    (notequal (math relation) "\\neq" "\\ne")
    (equivalence (math relation) "\\equiv")
    (approxequal (math relation) "\\approx")
    (ellipsis (ordinary gobbles-spc) "\\ldots")
    ;;(carriagereturn)
    (aleph (math letter) "\\aleph")
    (Ifraktur (math letter) "\\Im")
    (Rfraktur (math letter) "\\Re")
    (weierstrass (math letter) "\\wp")
    (circlemultiply (math binop) "\\otimes")
    (circleplus (math binop) "\\oplus")
    (emptyset (math ordinary) "\\emptyset")
    (intersection (math binop) "\\cap")
    (union (math binop) "\\cup")
    (propersuperset (math relation) "\\supset")
    (reflexsuperset (math relation) "\\supseteq")
    (notsubset (math relation user) "\\nsubset")
    (propersubset (math relation) "\\subset")
    (reflexsubset (math relation) "\\subseteq")
    (element (math relation) "\\in")
    (notelement (math relation) "\\notin")
    (angle (ordinary gobbles-spc) "\\angle")
    (gradient (math ordinary) "\\nabla")
    (product (math bigop) "\\prod")
    (radical (math ordinary) "\\surd")
    (periodcentered1 (math binop) "\\cdot")	; (NEW)
    (logicaland (math binop) "\\land" "\\wedge")
    (logicalor (math binop) "\\lor" "\\vee")
    (arrowdblboth (math relation) "\\Leftrightarrow" "\\lequiv")
    (arrowdblleft (math relation) "\\Leftarrow")
    (arrowdblup (math relation delim) "\\Uparrow")
    (arrowdblright (math relation) "\\Rightarrow")
    (arrowdbldown (math relation delim) "\\Downarrow")
    (lozenge (math ordinary amssymb) "\\lozenge")
    (angleleft (math delim) "\\langle")	; (NEW)
    (trademark (text ordinary) . "\\texttrademark")
    (summation (math bigop) "\\sum")
    (angleright (math delim) "\\rangle") ; (NEW)
    (integral (math bigop) "\\int"))
  "Table defining TeX macros, see `x-symbol-tex-table'.")

(defvar x-symbol-tex-xsymb1-table
  ;; With elems (SYMBOL (TEX-CLASS ...) TEX-MACRO ...)
  '((verticaldots (ordinary gobbles-spc) "\\vdots")
    (backslash1 (text ordinary) . "\\textbackslash")
    (dagger (ordinary) . "\\dag")
    (percent2 (ordinary) "\\%")		; NEW
    (guilsinglright (text quote T1) . "\\guilsinglright")
    (NG (text letter T1) . "\\NG")
    (dotlessj (text letter) . "\\j")
    (ng (text letter T1) . "\\ng")
    (sharp (math ordinary) "\\sharp")
    (ceilingleft (math delim) "\\lceil")
    (ceilingright (math delim) "\\rceil")
    (star (math binop) "\\star")
    (lozenge1 (math ordinary latexsym) "\\Diamond")
    (braceleft2 (delim) "\\{")		; \lbrace is math-only
    (circleslash (math binop) "\\oslash")
    (braceright2 (delim) "\\}")		; \rbrace is math-only
    (triangle1 (math binop) "\\bigtriangleup")
    (smltriangleright (math binop) "\\triangleright")
    (triangleleft (math binop latexsym) "\\lhd")
    (triangle (math ordinary) "\\triangle")
    (triangleright (math binop latexsym) "\\rhd")
    (trianglelefteq (math binop latexsym) "\\unlhd")
    (trianglerighteq (math binop latexsym) "\\unrhd")
    (periodcentered2 (math punct) "\\cdotp")
    (dotequal (math relation) "\\doteq")
    (wrong (math binop) "\\wr")
    (natural (math ordinary) "\\natural")
    (flat (math ordinary) "\\flat")
    (epsilon1 (math greek) "\\varepsilon")
    (hbarmath (math letter) "\\hbar")
    (imath (math letter) "\\imath")
    (kappa1 (math greek amssymb) "\\varkappa")
    (jmath (math letter) "\\jmath")
    (ell (math letter) "\\ell")
    (amalg (math binop) "\\amalg")
    (rho1 (math greek) "\\varrho")
    (top (math ordinary) "\\top")
    (Mho (math greek latexsym) "\\mho")
    (floorleft (math delim) "\\lfloor")
    (floorright (math delim) "\\rfloor")
    (perpendicular1 (math relation) "\\perp")
    (box (math ordinary latexsym) "\\Box")
    (asciicircum1 (text ordinary) . "\\textasciicircum")
    (asciitilde1 (text ordinary) . "\\textasciitilde")
    (leadsto (math relation latexsym) "\\leadsto")
    (longarrowleft (math relation) "\\longleftarrow")
    (arrowupdown (math relation delim) "\\updownarrow")
    (longarrowright (math relation) "\\longrightarrow")
    (longmapsto (math relation) "\\longmapsto")
    (longarrowdblboth (math relation) "\\Longleftrightarrow")
    (longarrowdblleft (math relation) "\\Longleftarrow")
    (arrowdblupdown (math relation delim) "\\Updownarrow")
    (longarrowdblright (math relation) "\\Longrightarrow")
    (mapsto (math relation) "\\mapsto")
    (iff (math relation) "\\iff")
    (hookleftarrow (math relation) "\\hookleftarrow")
    (hookrightarrow (math relation) "\\hookrightarrow")
    (arrownortheast (math relation) "\\nearrow")
    (arrowsoutheast (math relation) "\\searrow")
    (arrownorthwest (math relation) "\\nwarrow")
    (arrowsouthwest (math relation) "\\swarrow")
    (rightleftharpoons (math relation) "\\rightleftharpoons")
    (leftharpoondown (math relation) "\\leftharpoondown")
    (rightharpoondown (math relation) "\\rightharpoondown")
    (leftharpoonup (math relation) "\\leftharpoonup")
    (rightharpoonup (math relation) "\\rightharpoonup")
    (bardbl (math ordinary delim) "\\|") ; removed \Vert
    (bardbl1 (math relation) "\\parallel")
    (backslash2 (math ordinary delim) "\\backslash")
    (backslash3 (math binop) "\\setminus")
    (diagonaldots (math ordinary) "\\ddots")
    (simequal (math relation) "\\simeq")
    (digamma (math ordinary amssymb) "\\digamma")
    (asym (math relation) "\\asymp")
    (minusplus (math binop) "\\mp")
    (bowtie (math relation) "\\bowtie")
    (centraldots (math ordinary) "\\cdots")
    (visiblespace (text ordinary) . "\\textvisiblespace")
    (dagger1 (math binop) "\\dagger")
    (circledot (math binop) "\\odot")
    (propersqsuperset (math relation latexsym) "\\sqsupset")
    (reflexsqsuperset (math relation) "\\sqsupseteq")
    (gradient1 (math binop) "\\bigtriangledown")
    (propersqsubset (math relation latexsym) "\\sqsubset")
    (reflexsqsubset (math relation) "\\sqsubseteq")
    (smllozenge (math binop) "\\diamond")
    (lessless (math relation) "\\ll")
    (greatergreater (math relation) "\\gg")
    (unionplus (math binop) "\\uplus")
    (sqintersection (math binop) "\\sqcap")
    (squnion (math binop) "\\sqcup")
    (frown (math relation) "\\frown")
    (smile (math relation) "\\smile")
    (reflexprec (math relation) "\\preceq")
    (reflexsucc (math relation) "\\succeq")
    (properprec (math relation) "\\prec")
    (propersucc (math relation) "\\succ")
    (bardash (math relation) "\\vdash")
    (dashbar (math relation) "\\dashv")
    (bardashdbl (math relation) "\\models")
    (smlintegral (math ordinary) "\\smallint")
    (circleintegral (math bigop) "\\oint")
    (coproduct (math bigop) "\\coprod")
    (bigcircledot (math bigop) "\\bigodot")
    (bigcirclemultiply (math bigop) "\\bigotimes")
    (bigcircleplus (math bigop) "\\bigoplus")
    (biglogicaland (math bigop) "\\bigwedge")
    (biglogicalor (math bigop) "\\bigvee")
    (bigintersection (math bigop) "\\bigcap")
    (bigunion (math bigop) "\\bigcup")
    (bigunionplus (math bigop) "\\biguplus")
    (bigsqunion (math bigop) "\\bigsqcup")
    (bigcircle (math binop) "\\bigcirc")
    (guilsinglleft (text quote T1) . "\\guilsinglleft")
    (circleminus (math binop) "\\ominus")
    (smltriangleleft (math binop) "\\triangleleft")
    (existential1 (math ordinary) "\\exists")
    (daggerdbl1 (math binop) "\\ddagger")
    (daggerdbl (ordinary) . "\\ddag")
    (bigbowtie (math relation latexsym) "\\Join")
    (circ (math binop) "\\circ")
    (grave (text accent) . "\\`{}")	; NEW
    (circumflex (text accent) . "\\^{}") ; NEW
    (tilde (text accent) . "\\~{}")	; NEW
    (longarrowboth (math relation) "\\longleftrightarrow")
    (endash (text ordinary) . "\\textendash") ; NEW
    (emdash (text ordinary) . "\\textemdash")
    (ampersand2 (ordinary) "\\&")	; NEW
    (universal1 (math ordinary) "\\forall")
    (booleans (math letter user) "\\setB")
    (complexnums (math letter user) "\\setC")
    (natnums (math letter user) "\\setN")
    (rationalnums (math letter user) "\\setQ")
    (realnums (math letter user) "\\setR")
    (integers (math letter user) "\\setZ")
    (lesssim (math relation amssymb) "\\lesssim")
    (greatersim (math relation amssymb) "\\gtrsim")
    (lessapprox (math relation amssymb) "\\lessapprox")
    (greaterapprox (math relation amssymb) "\\gtrapprox")
    (definedas (math relation amssymb) "\\triangleq")
    (circleminus1 (math binop amssymb) "\\circleddash")
    (circleasterisk (math binop amssymb) "\\circledast")
    (circlecirc (math binop amssymb) "\\circledcirc")
    (dollar1 (ordinary) "\\$")
    (therefore1 (math relation amssymb) "\\therefore")
    (coloncolon (math relation user) "\\coloncolon")
    (bigsqintersection (math bigop stmaryrd) "\\bigsqcap")
    (semanticsleft (math delim stmaryrd) "\\llbracket")
    (semanticsright (math delim stmaryrd) "\\rrbracket")
    (cataleft (math delim stmaryrd) "\\llparenthesis")
    (cataright (math delim stmaryrd) "\\rrparenthesis")
    ;;(quotedblbase (mark T1) "\\quotedblbase") ; not in {}! (spacing)
    ;;(quotedblleft (mark) . "\\textquotedblleft") ; not in {}! (spacing)
    ;;(quotedblright (mark) . "\\textquotedblright") ; not in {}! (spacing)
    ;;(perthousand)
    )
  "Table defining TeX macros, see `x-symbol-tex-table'.")

(defvar x-symbol-tex-table
  (append x-symbol-tex-user-table
	  '(nil)
	  x-symbol-tex-latin1-table
	  x-symbol-tex-latinN-table
	  x-symbol-tex-xsymb0-table
	  x-symbol-tex-xsymb1-table)
  "Table defining `tex' tokens for the characters.
See language access `x-symbol-LANG-table'.  Use
`x-symbol-tex-user-table' to define private TeX macros or shadow
existing ones.")


;;;===========================================================================
;;;  Super- and Subscripts
;;;===========================================================================

(defun x-symbol-tex-subscript-matcher (limit)
  (block nil
    (let (beg mid)
      (or (bolp) (backward-char))
      ;; (backward-char) is not necessary in the loop because: if a simple =
      ;; braces-less subscript is not allowed according to the "allowed" faces,
      ;; then a directly following _ or ^ is also not allowed...
      (while (re-search-forward x-symbol-tex-font-lock-regexp limit t)
	(setq beg (match-beginning 1)
	      mid (match-beginning 2))
	(if (if (eq (char-after mid) ?\{)
		(let ((end (save-restriction
			     (narrow-to-region
			      (point)
			      (save-excursion
				(re-search-forward
				 x-symbol-tex-font-lock-limit-regexp
				 limit 'limit)
				(point)))
			     (ignore-errors (scan-lists (point) 1 1)))))
		  (when (and end (eq (char-before end) ?}))
		    (goto-char end)
		    (store-match-data
		     (if x-symbol-tex-invisible-braces
			 (list beg end
			       beg (1+ mid)
			       (1+ mid) (1- end)
			       (1- end) end)
		       (list beg end beg mid mid end)))
		    t))
	      (or (eq x-symbol-tex-font-lock-allowed-faces t)
		  (let ((faces (plist-get (text-properties-at beg) 'face)))
		    (cond ((null faces))
			  ((consp faces)
			   (while (and faces (memq (car faces) x-symbol-tex-font-lock-allowed-faces))
			     (setq faces (cdr faces)))
			   (null faces))
			  ((memq faces
				 x-symbol-tex-font-lock-allowed-faces))))))
	    (return (if (eq (char-after beg) ?_)
			'x-symbol-sub-face
		      'x-symbol-sup-face)))))))


;;;===========================================================================
;;;  Conversion
;;;===========================================================================

(defun x-symbol-tex-encode (encode-table fchar-table fchar-fb-table)
  (let (char)
    (x-symbol-encode-for-charsym ((encode-table fchar-table fchar-fb-table)
				  token)
      (and (eq (char-before) ?\\)
	   (x-symbol-even-escapes-before-p (1- (point)) ?\\)
	   (insert ?\ ))
      (insert (car token))
      (delete-char x-symbol-encode-rchars)
      (when (cdr token)			; \MACRO
	(setq char (char-after))
	(cond ((memq char '(?\ ?\t ?\n ?\r nil))
	       ;; faster than any `looking-at' or `or'ed `eq's
	       (or (eq (cdr token) 'math)
		   (insert-before-markers "{}")))
	      ((or (and (<= ?a char) (<= char ?z))
		   (and (<= ?@ char) (<= char ?Z)))
	       ;; much faster than any `looking-at', XEmacs' 3-arg `<=' is
	       ;; slower than `and'ed 2-arg `<='s
	       (insert-before-markers " ")))))))

(defun x-symbol-tex-decode (decode-regexp decode-obarray unique)
  (let ((in-tabbing nil)
	retry charsym after)
    (x-symbol-decode-for-charsym ((decode-regexp decode-obarray)
				  token beg end)
	(if (setq retry (match-beginning 1))
	    (goto-char retry))
      (cond ((and (eq (char-before beg) ?\\)
		  (x-symbol-even-escapes-before-p (1- beg) ?\\))
	     (if (setq retry (match-beginning 1)) (goto-char retry)))
	    ((and in-tabbing
		  (memq (char-after (1+ beg)) '(?\` ?\' ?= ?-)))
	     (if (setq retry (match-beginning 1)) (goto-char retry)))
	    ((x-symbol-decode-unique-test token unique))
	    ;; would be bad to decode a part only because of unique decoding
	    ((setq charsym (car token))
	     (if (eq (cadr token) t)	; text-mode \MACRO
		 (unless
		     (cond ((eq (setq after (char-after)) ?\ )
			    (setq after (char-after (incf end)))
			    (if unique
				(not (or (and (<= ?a after) (<= after ?z))
					 (and (<= ?@ after) (<= after ?Z))))
			      (memq after '(?\ ?\t ?\n ?\r ?% nil))))
			   ((eq after ?\{)
			    (if (eq (char-after (incf end)) ?\})
				(or (memq (char-after (incf end))
					  '(?\ ?\t ?\n ?\r nil))
				    (decf end 2))
			      (decf end))
			    nil)
			   (t
			    (memq (char-after) '(?\t ?\n ?\r ?% nil))))
		   (goto-char end)
		   (insert-before-markers (gethash charsym
						   x-symbol-cstring-table))
		   (delete-region beg end))
	       (replace-match (gethash charsym x-symbol-cstring-table) t t)))
	    ;; special definitions -------------------------------------------
	    ((eq (setq charsym (cadr token)) 'tex-begin) ; \begin
	     (skip-chars-forward " \t")
	     (cond ((looking-at x-symbol-tex-env-verbatim-regexp)
		    (setq retry (concat "\\\\end[ \t]*"
					(regexp-quote (match-string 0))))
		    (while (and (re-search-forward retry nil t)
				(not (x-symbol-even-escapes-before-p
				      (match-beginning 0) ?\\)))))
		   ((looking-at x-symbol-tex-env-tabbing-regexp)
		    (setq in-tabbing t))))
	    ((eq charsym 'tex-end)	; \end
	     (skip-chars-forward " \t")
	     (and in-tabbing
		  (looking-at x-symbol-tex-env-tabbing-regexp)
		  (setq in-tabbing nil)))
	    ((eq charsym 'tex-verb)	; \verb
	     (skip-chars-forward " \t")
	     (when (looking-at x-symbol-tex-verb-delimiter-regexp)
	       (setq after (char-after))
	       (forward-char)
	       (while (not (or (eq (char-after) after) (eobp)))
		 (forward-char))))
	    ((eq charsym 'tex-accent)	; accents \c, \k, \v, \u, \H, \r
	    ;; there are 41 chars using these accents => do something special
	    ;; here instead using an complicated regexp for the main search
	     (when (looking-at " [A-Za-z]\\|{}")
	       (goto-char (setq end (match-end 0)))
	       (when (setq token (symbol-value
				  (intern-soft (buffer-substring beg end)
					       decode-obarray)))
		 (unless (x-symbol-decode-unique-test token unique)
		   (goto-char end)
		   (insert-before-markers (gethash (car token)
						   x-symbol-cstring-table))
		   (delete-region beg end)))))))))

(defun x-symbol-tex-token-input (input-regexp decode-obarray command-char)
  (let ((res (x-symbol-match-token-before
	      '(?\\ (math . "[a-z@-Z]") (t . "[a-z@-Z]"))
	      input-regexp decode-obarray command-char)))
    (and x-symbol-tex-token-suppress-space
	 (eq (caddr res) t)		; text mode \MACRO
	 (eq command-char ?\ )
	 (null prefix-arg)
	 (setq prefix-arg 0))
    res))


;;;===========================================================================
;;;  AucTeX, preview-latex
;;;===========================================================================

(defun x-symbol-tex-translate-locations (file-buffer beg end locations)
  ;;(set-buffer conv-buffer)
  (let ((char-offset (1- beg))
	changed
	;; Kludge to prevent undo list truncation:
	(undo-limit most-positive-fixnum) ; Emacs
	(undo-strong-limit most-positive-fixnum) ; Emacs
	(undo-high-threshold -1)	; XEmacs
	(undo-threshold -1))		; XEmacs
    (setq buffer-undo-list t)
    (erase-buffer)
    (insert-buffer-substring file-buffer beg end)
    (map-extents (lambda (e dummy) (delete-extent e) nil))
    (setq buffer-undo-list nil)
    (x-symbol-encode-all)
    (let* ((curr (car locations))
	   (file (aref curr 0))
	   (line (aref curr 1))
	   string after-string)
      (while curr
	(when buffer-undo-list
	  (setq string (aref curr 2))
	  (if (number-or-marker-p string)
	      (setq string (- string char-offset))
	    (goto-char 1)
	    (setq string (or (and (stringp (setq after-string (aref curr 3)))
				  (search-forward (concat string after-string)
						  nil t)
				  (- (point) (length after-string)))
			     (search-forward string nil t))))
	  (when string
	    (aset curr 2 (copy-marker string t))
	    ;; The second arg t is important in both Emacs and XEmacs: this is
	    ;; a marker which should keep its correct position after the
	    ;; `primitive-undo's, the encoding has already been done.
	    (aset curr 3 beg)
	    (push curr changed)))
	(or (and (setq locations (cdr locations))
		 (eq line (aref (setq curr (car locations)) 1))
		 (equal file (aref curr 0)))
	    (setq curr nil))))
    (when changed
      (let ((tail buffer-undo-list)
	    mpos)
	(setq buffer-undo-list t)
	(while tail (setq tail (primitive-undo (length tail) tail)))
	(dolist (curr changed)
	  (setq mpos (aref curr 2))
	  (aset curr 2 (+ char-offset mpos))
	  (aset curr 3 beg)
	  (set-marker mpos nil))))
    locations))

(put 'x-symbol-tex-error-location 'TeX-translate-via-list
     'x-symbol-tex-preview-locations)

(defun x-symbol-tex-error-location ()
  (unless (string= string " ")
    (save-excursion
      (set-buffer (find-file-noselect file))
      (when x-symbol-mode
	(save-restriction
	  (widen)
	  (let ((file-buffer (current-buffer))
		(conv-buffer (get-buffer-create " x-symbol error location"))
		(location (vector nil nil string
				  (and (boundp 'after-string) after-string)))
		beg end pos)
	    (goto-line (+ offset line))
	    (setq beg (point))
	    (end-of-line)
	    (setq end (point))
	    (set-buffer conv-buffer)
	    (erase-buffer)
	    (when (fboundp 'set-buffer-multibyte)
	      (set-buffer-multibyte t))
	    (x-symbol-inherit-from-buffer file-buffer)
	    (x-symbol-tex-translate-locations file-buffer beg end
					      (list location))
	    ;; narrow-to-region gets confused otherwise...
	    (set-buffer file-buffer)
	    (when (numberp (setq pos (aref location 2)))
	      (setq string (buffer-substring beg pos))
	      (and (boundp 'after-string)
		   (setq after-string (buffer-substring pos end))))))))))

(defun x-symbol-tex-preview-locations (locations)
  (when locations
    (prog1 locations
      (let* ((conv-buffer (get-buffer-create " x-symbol error location"))
	     file
	     (dir default-directory))
	(save-excursion
	  (set-buffer conv-buffer)
	  (erase-buffer)
	  (when (fboundp 'set-buffer-multibyte)
	    (set-buffer-multibyte t))
	  (while locations
	    (setq file (aref (car locations) 0))
	    (set-buffer (find-file-noselect (expand-file-name file dir)))
	    (if x-symbol-mode
		(save-restriction
		  (widen)
		  (goto-char 1)
		  (let ((file-buffer (current-buffer))
			(pline 1)
			(line (aref (car locations) 1))
			beg end)
		    (set-buffer conv-buffer)
		    (x-symbol-inherit-from-buffer file-buffer)
		    (while line
		      (set-buffer file-buffer)
		      (if (>= line pline)
			  (if (eq selective-display t)
			      (re-search-forward "[\n\C-m]"
						 nil 'end (- line pline))
			    (forward-line (- line pline)))
			(goto-line line))
		      (setq beg (point))
		      (end-of-line)
		      (setq end (point))
		      (set-buffer conv-buffer)
		      (setq locations
			    (x-symbol-tex-translate-locations file-buffer
							      beg end
							      locations))
		      (setq pline line
			    line (and locations
				      (equal (aref (car locations) 0) file)
				      (aref (car locations) 1))))
		    ;; narrow-to-region gets confused otherwise...
		    (set-buffer file-buffer)))
	      (while (and (setq locations (cdr locations))
			  (equal (aref (car locations) 0) file))))))))))


;;;===========================================================================
;;;  Extra decoding = executed after normal decoding
;;;===========================================================================

(defun x-symbol-tex-xdecode-old (&optional beg end)
  "Remove braces around text-mode characters like {C}."
  (interactive (and (region-active-p) (list (region-beginning) (region-end))))
  (unless (eq x-symbol-language 'tex)
    (error "Command is meant to be used with token language `tex'"))
  (unless x-symbol-mode
    (error "Command is meant to be used if X-Symbol mode is enabled"))
  (or beg (setq beg (point-min)))
  (or end (setq end (point-max)))
  (save-excursion
    (save-restriction
      (narrow-to-region beg end)
      (let ((first-change-hook nil)	; no `flyspell-mode' here
	    (after-change-functions nil) ; no fontification!
	    (count 0)
	    (case-fold-search (x-symbol-grammar-case-function
			       x-symbol-tex-token-grammar))
	    (regexp (if (featurep 'mule)
			"{[^\000-\177]}"
		      "{\\(?:[\240-\377]\\|[\200-\237][\240-\377]\\)}"))
	    (token-classes (x-symbol-generated-token-classes
			    x-symbol-tex-generated-data))
	    charsym
	    (end (make-marker)))
	(goto-char (point-min))
	(while (re-search-forward regexp nil t)
	  (set-marker end (point))
	  (goto-char (1+ (match-beginning 0)))
	  (when (and (setq charsym (x-symbol-encode-charsym-after))
		     (x-symbol-even-escapes-before-p (match-beginning 0) ?\\)
		     (eq (car (gethash charsym token-classes)) 'text))
	    (goto-char (match-beginning 0))
	    (delete-char 1)
	    (goto-char end)
	    (delete-char -1)
	    (incf count)))
	(if font-lock-mode (x-symbol-fontify (point-min) (point-max)))
	(set-marker end nil)
	(if (interactive-p)
	    (message "Converted %d old TeX sequences like {C} in %s"
		     count (x-symbol-region-text t)))))))

(defvar x-symbol-tex-xdecode-obarray nil)

(defun x-symbol-tex-xdecode-latex (&optional beg end)
  "Decode LaTeX sequences for accented characters like \'{C}."
  (interactive (and (region-active-p) (list (region-beginning) (region-end))))
  (unless (eq x-symbol-language 'tex)
    (error "Command is meant to be used with token language `tex'"))
  (unless x-symbol-mode
    (error "Command is meant to be used if X-Symbol mode is enabled"))
  (or beg (setq beg (point-min)))
  (or end (setq end (point-max)))
  (unless x-symbol-tex-xdecode-obarray
    (let ((re "\\`\\(\\\\[.~^\"'`=ckvuHr]\\) ?\\([A-Za-z]\\|\\\\[ij]\\)\\'")
	  (ij (list (cons "\\i" (gethash 'dotlessi x-symbol-cstring-table))
		    (cons "\\j" (gethash 'dotlessj x-symbol-cstring-table))))
	  alist)
      (maphash (lambda (charsym value)
		 (setq value (car value))
		 (when (string-match re value)
		   (push (list (format "%s{%s}"
				       (match-string 1 value)
				       (or (cdr (assoc (match-string 2 value)
						       ij))
					   (match-string 2 value)))
			       charsym nil)
			 alist)))
	       (x-symbol-generated-encode-table x-symbol-tex-generated-data))
      (setq x-symbol-tex-xdecode-obarray (x-symbol-alist-to-obarray alist))))
  (save-excursion
    (save-restriction
      (narrow-to-region beg end)
      (let ((first-change-hook nil)	; no `flyspell-mode' here
	    (after-change-functions nil)) ; no fontification!
	(goto-char (point-min))
	(x-symbol-decode-lisp
	 '(?\\)
	 (format "\\\\[.~^\"'`=ckvuHr]{\\(?:[A-Za-z]\\|%s\\|%s\\)}"
		 (gethash 'dotlessi x-symbol-cstring-table)
		 (gethash 'dotlessj x-symbol-cstring-table))
	 x-symbol-tex-xdecode-obarray nil)
	(if font-lock-mode (x-symbol-fontify (point-min) (point-max)))
	(if (interactive-p)
	    (message "Decoded alternative TeX sequences like \\'{C} in %s"
		     (x-symbol-region-text t)))))))

;;; Local IspellPersDict: .ispell_xsymb
;;; x-symbol-tex.el ends here
