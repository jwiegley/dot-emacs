;;; x-symbol-sgml.el --- token language "SGML entity" for package x-symbol

;; Copyright (C) 1996-1999, 2002, 2003 Free Software Foundation, Inc.
;;
;; Author: Christoph Wedler <wedler@users.sourceforge.net>
;; Maintainer: (Please use `M-x x-symbol-package-bug' to contact the maintainer)
;; Version: 4.5
;; Keywords: WYSIWYG, HTML, wp, math, internationalization
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

;; Token language sgml is registered in x-symbol-hooks.

;;; Code:

(provide 'x-symbol-sgml)


;;;===========================================================================
;;;  Auto-style
;;;===========================================================================

(defcustom x-symbol-sgml-auto-style
  '((not (memq major-mode '(sgml-mode xml-mode)))
    (x-symbol-auto-coding-alist x-symbol-sgml-auto-coding-alist)
    x-symbol-coding (not x-symbol-mode)
    x-symbol-mode x-symbol-mode)
  "Values for X-Symbol's buffer-local variables with language `sgml'.
See language access `x-symbol-LANG-auto-style'."
  :group 'x-symbol-sgml
  :group 'x-symbol-mode
  :type 'x-symbol-auto-style)

(defcustom x-symbol-sgml-auto-coding-alist
  '(("<meta\\s-+http-equiv\\s-*=\\s-*\"content-type\"\\s-*content\\s-*=\\s-*\"text/html\\s-*;\\s-*charset\\s-*=\\s-*\\([A-Za-z0-9---]+\\)\"\\s-*>" 1
     ("iso-8859-1" . iso-8859-1)
     ("iso-8859-2" . iso-8859-2)
     ("iso-8859-3" . iso-8859-3)
     ("iso-8859-9" . iso-8859-9)
     ("iso-8859-15" . iso-8859-15)))
  "*Alist used to determine the file coding with language `sgml'.
Used in the default value of `x-symbol-sgml-auto-style'.  See variable
`x-symbol-auto-coding-alist' for details."
  :group 'x-symbol-sgml
  :group 'x-symbol-mode
  :type 'x-symbol-auto-coding)


;;;===========================================================================
;;;  Miscellaneous variables
;;;===========================================================================

(defface x-symbol-sgml-symbol-face
  '((((class color) (background light))
     (:foreground "orange4")))
  "*Face used for entities with name representing non-Latin-1 characters.
Used in `x-symbol-sgml-class-face-alist'."
  :group 'x-symbol-sgml
  :group 'x-symbol-info-general)

(defface x-symbol-sgml-noname-face
  '((((class color) (background light))
     (:foreground "red4")))
  "*Face used for Latin-N character entities without name.
Used in `x-symbol-sgml-class-face-alist'."
  :group 'x-symbol-sgml
  :group 'x-symbol-info-general)

(defcustom x-symbol-sgml-modeline-name "sgml"
  "Modeline name of token language `sgml'.
See language access `x-symbol-LANG-modeline-name'."
  :group 'x-symbol-sgml
  :type 'string)

(defcustom x-symbol-sgml-header-groups-alist
  '(("Operator" bigop operator)
    ("Relation" relation)
    ("Arrow, Punctuation" arrow triangle shape
     white line dots punctuation quote parenthesis)
    ("Symbol" symbol currency mathletter setsymbol)
    ("Greek Letter" greek greek1)
    ("Misc. Letter" letter slash)
    ("Cedilla, Ogonek" cedilla ogonek)
    ("Dotaccent, Ring" dotaccent ring)
    ("Tilde, Breve" tilde breve)
    ("Circumflex, Caron" circumflex caron)
    ("Diaeresis, Umlaut" diaeresis hungarumlaut)
    ("Acute, Grave" acute grave))
  "Header/submenu specification of the specific menu for language `sgml'.
See language access `x-symbol-LANG-header-groups-alist'."
  :group 'x-symbol-sgml
  :group 'x-symbol-input-init
  :type 'x-symbol-headers)

(defcustom x-symbol-sgml-class-alist
  '((symbol)
    (noname "SGML char-ref" (x-symbol-emph-info-face))
    (VALID "SGML entity" (x-symbol-info-face))
    (INVALID "no SGML entity" (x-symbol-emph-info-face)))
  "Token classes displayed by info in echo area, for language `sgml'.
See language access `x-symbol-LANG-class-alist'."
  :group 'x-symbol-sgml
  :group 'x-symbol-info-strings
  :type 'x-symbol-class-info)

(defcustom x-symbol-sgml-class-face-alist
  '((symbol x-symbol-sgml-symbol-face (x-symbol-sgml-symbol-face))
    (noname x-symbol-sgml-noname-face (x-symbol-sgml-noname-face)))
  "Color scheme in language specific grid and info, for language `sgml'.
See language access `x-symbol-LANG-class-face-alist'."
  :group 'x-symbol-sgml
  :group 'x-symbol-input-init
  :group 'x-symbol-info-general
  :type 'x-symbol-class-faces)

(defcustom x-symbol-sgml-electric-ignore nil
  "Specification restricting input method ELECTRIC with language `sgml'.
See language access `x-symbol-LANG-electric-ignore'."
  :group 'x-symbol-sgml
  :group 'x-symbol-input-control
  :type 'x-symbol-function-or-regexp)

(defvar x-symbol-sgml-token-list 'x-symbol-sgml-token-list-name
  "Symbol specifying the token definition for language `sgml'.
Allowed values are
 - `x-symbol-sgml-token-list-name': the canonical token for a character
   is a entity references,
 - `x-symbol-sgml-token-list-code': the canonical token for a character
   is a character references,
 - `x-symbol-sgml-token-list-netscape': the canonical token for a
   Latin-1 character is a entity references, for others, it is a
   character references.  Bug workaround for Netscape, v4.6 or lower.

The value is used by function `x-symbol-sgml-default-token-list' which
is used for the definition of the conversion tables.  See
`x-symbol-sgml-token-grammar'.")

(defvar x-symbol-sgml-token-grammar
  '(x-symbol-make-grammar
    :decode-regexp "&[#0-9A-Za-z]+;"
    :token-list x-symbol-sgml-default-token-list)
  "Grammar of token language `sgml'.
See language access `x-symbol-LANG-token-grammar'.")

(defvar x-symbol-sgml-user-table nil
  "User table defining SGML entities, used in `x-symbol-sgml-table'.")

(defvar x-symbol-sgml-generated-data nil
  "Generated data for token language `sgml'.
See language access `x-symbol-LANG-generated-data'.")


;;;===========================================================================
;;;  Image support
;;;===========================================================================

(defcustom x-symbol-sgml-master-directory 'ignore
  "Function returning the directory of the master file or nil.
See `x-symbol-image-parse-buffer'."
  :group 'x-symbol-sgml
  :group 'x-symbol-image-language
  :type 'function)

(defcustom x-symbol-sgml-image-searchpath '("./")
  "Search path for implicitly relative image file names.
See language access `x-symbol-LANG-image-searchpath'."
  :group 'x-symbol-sgml
  :group 'x-symbol-image-language
  :type '(repeat directory))

(defcustom x-symbol-sgml-image-cached-dirs '("images/" "pictures/")
  "Directory parts of images stored in the memory cache.
See language access `x-symbol-LANG-image-cached-dirs'."
  :group 'x-symbol-sgml
  :group 'x-symbol-image-language
  :type '(repeat string))

(defcustom x-symbol-sgml-image-file-truename-alist
  '(("\\`file:" . "")
    ("\\`[A-Za-z]+:"))
  "Alist used to determine the file name of an image URL.
Each element looks like
  (REGEXP) or
  (REGEXP . NEWTEXT) or
  (REGEXP FUNCTION ARG...)
If the the image file name is matched by REGEXP, the corresponding
element is processed, if no REGEXP matches, the image file name is used
as it is.  With the first form, the image command will not be
highlighted.  With the second form, replace text matched by REGEXP with
NEWTEXT, see `replace-match' for details.  With the third form,
FUNCTION, call FUNCTION with the image file name and the remaining
arguments ARGs to get the true file name.

E.g., I add the following element to this variable:
  (\"\\\\`http://www\\\\.fmi\\\\.uni-passau\\\\.de/~wedler/\" \. \"~/public_html/\")"
  :group 'x-symbol-sgml
  :group 'x-symbol-image-language
  :type '(repeat (cons :format "%v"
		       :value ("" . "")	; doesn't work (custom bug?)
		       regexp
		       (choice ;;:value ""
			       (const :tag "Not highlighted" nil)
			       (string :tag "Replace match with")
			       (cons :tag "Call"
				     function
				     (repeat :tag "With arguments" sexp))))))

(defcustom x-symbol-sgml-image-keywords
  '("\\.\\(gif\\|png\\|jpe?g\\)\\'"
    ("<img[ \t][^\n>]*src=\"\\([^\n\"]+\\)\"[^\n>]*>"
     x-symbol-sgml-image-file-truename 1))
  "Keywords for image insertion commands of language `sgml'.
See language access `x-symbol-LANG-image-keywords'."
  :group 'x-symbol-sgml
  :group 'x-symbol-image-language
  :type 'x-symbol-image-keywords)

(defun x-symbol-sgml-image-file-truename (num)
  "Return true image file name for last match.
Return text matched by the NUMth regexp group of the corresponding
keyword regexp, after being processed according to
`x-symbol-sgml-image-file-truename-alist'."
  (x-symbol-match-in-alist (setq num (match-string num))
			   x-symbol-sgml-image-file-truename-alist
			   num t))


;;;===========================================================================
;;;  Super- and Subscripts
;;;===========================================================================

(defcustom x-symbol-sgml-subscript-matcher 'x-symbol-sgml-subscript-matcher
  "Function matching super-/subscripts for language `sgml'.
See language access `x-symbol-LANG-subscript-matcher'."
  :group 'x-symbol-sgml
  :type 'function)

(defcustom x-symbol-sgml-font-lock-regexp "<su[bp]>"
  "Regexp matching the start tag of SGML's super- and subscripts.
See also `x-symbol-sgml-font-lock-alist'."
  :group 'x-symbol-sgml
  :type 'regexp)

(defcustom x-symbol-sgml-font-lock-limit-regexp "\n\\|</?su[bp]>"
  "Regexp matching the end tag of SGML's super- and subscripts.
This regexp should match the end of line and the closing tags in
`x-symbol-sgml-font-lock-alist'."
  :group 'x-symbol-sgml
  :type 'regexp)

(defcustom x-symbol-sgml-font-lock-contents-regexp "[^ \t\n\240]"
  "*Regexp matching the super- and subscript contents.
This regexp should match the text between the opening and closing super-
or subscript tag."
  :group 'x-symbol-sgml
  :type 'regexp)

(defcustom x-symbol-sgml-font-lock-alist
  '(("<sub>" . "</sub>") ("<sup>" . "</sup>"))
  "Alist for correct tag pairs for HTML's super- and subscripts.
Each element looks like (OPEN . CLOSE).  All keys OPEN in this alist
should be matched by `x-symbol-sgml-font-lock-regexp', all CLOSEs should
be matched by `x-symbol-sgml-font-lock-limit-regexp'."
  :group 'x-symbol-sgml
  :type '(repeat (cons :format "%v"
		       (string :tag "Open tag")
		       (string :tag "Close tag"))))


;;;===========================================================================
;;;  The tables
;;;===========================================================================

(defun x-symbol-sgml-default-token-list (tokens)
  (mapcar #'list
	  (and (car tokens)
	       (memq x-symbol-sgml-token-list
		     '(x-symbol-sgml-token-list-name
		       x-symbol-sgml-token-list-code
		       x-symbol-sgml-token-list-netscape))
	       (if (or (eq x-symbol-sgml-token-list
			   'x-symbol-sgml-token-list-name)
		       (and (eq x-symbol-sgml-token-list
				'x-symbol-sgml-token-list-netscape)
			    (< (car tokens) 256)))
		   (append (cdr tokens) (list (format "&#%d;" (car tokens))))
		 (cons (format "&#%d;" (car tokens)) (cdr tokens))))))

;; http://www.w3.org/TR/REC-html40/sgml/entities.html
;; (query-replace-regexp "<!ENTITY[ \t]*\\([A-Za-z][A-Za-z0-9]*\\)[ \t]*CDATA[ \t]*\"&#\\([0-9]+\\);\"[ \t]*--\\(.+\\) -->[ \t]*.*$" " (\\1 () \\2 \"&\\1;\") ; \\3")

(defvar x-symbol-sgml-latin1-table
  '((nobreakspace () 160 "&nbsp;")
    (exclamdown () 161 "&iexcl;")
    (cent () 162 "&cent;")
    (sterling () 163 "&pound;")
    (currency () 164 "&curren;")
    (yen () 165 "&yen;")
    (brokenbar () 166 "&brvbar;" "&brkbar;")
    (section () 167 "&sect;")
    (diaeresis () 168 "&uml;" "&die;")
    (copyright () 169 "&copy;")
    (ordfeminine () 170 "&ordf;")
    (guillemotleft () 171 "&laquo;")
    (notsign () 172 "&not;")
    (hyphen () 173 "&shy;")
    (registered () 174 "&reg;")
    (macron () 175 "&macr;" "&hibar;")
    (degree () 176 "&deg;")
    (plusminus () 177 "&plusmn;")
    (twosuperior () 178 "&sup2;")
    (threesuperior () 179 "&sup3;")
    (acute () 180 "&acute;")
    (mu1 () 181 "&micro;")
    (paragraph () 182 "&para;")
    (periodcentered () 183 "&middot;")
    (cedilla () 184 "&cedil;")
    (onesuperior () 185 "&sup1;")
    (masculine () 186 "&ordm;")
    (guillemotright () 187 "&raquo;")
    (onequarter () 188 "&frac14;")
    (onehalf () 189 "&frac12;")
    (threequarters () 190 "&frac34;")
    (questiondown () 191 "&iquest;")
    (Agrave () 192 "&Agrave;")
    (Aacute () 193 "&Aacute;")
    (Acircumflex () 194 "&Acirc;")
    (Atilde () 195 "&Atilde;")
    (Adiaeresis () 196 "&Auml;")
    (Aring () 197 "&Aring;")
    (AE () 198 "&AElig;")
    (Ccedilla () 199 "&Ccedil;")
    (Egrave () 200 "&Egrave;")
    (Eacute () 201 "&Eacute;")
    (Ecircumflex () 202 "&Ecirc;")
    (Ediaeresis () 203 "&Euml;")
    (Igrave () 204 "&Igrave;")
    (Iacute () 205 "&Iacute;")
    (Icircumflex () 206 "&Icirc;")
    (Idiaeresis () 207 "&Iuml;")
    (ETH () 208 "&ETH;") ; "&Dstrok;" for Dbar (U0110) = latin2#208?
    (Ntilde () 209 "&Ntilde;")
    (Ograve () 210 "&Ograve;")
    (Oacute () 211 "&Oacute;")
    (Ocircumflex () 212 "&Ocirc;")
    (Otilde () 213 "&Otilde;")
    (Odiaeresis () 214 "&Ouml;")
    (multiply () 215 "&times;")
    (Ooblique () 216 "&Oslash;")
    (Ugrave () 217 "&Ugrave;")
    (Uacute () 218 "&Uacute;")
    (Ucircumflex () 219 "&Ucirc;")
    (Udiaeresis () 220 "&Uuml;")
    (Yacute () 221 "&Yacute;")
    (THORN () 222 "&THORN;")
    (ssharp () 223 "&szlig;")
    (agrave () 224 "&agrave;")
    (aacute () 225 "&aacute;")
    (acircumflex () 226 "&acirc;")
    (atilde () 227 "&atilde;")
    (adiaeresis () 228 "&auml;")
    (aring () 229 "&aring;")
    (ae () 230 "&aelig;")
    (ccedilla () 231 "&ccedil;")
    (egrave () 232 "&egrave;")
    (eacute () 233 "&eacute;")
    (ecircumflex () 234 "&ecirc;")
    (ediaeresis () 235 "&euml;")
    (igrave () 236 "&igrave;")
    (iacute () 237 "&iacute;")
    (icircumflex () 238 "&icirc;")
    (idiaeresis () 239 "&iuml;")
    (eth () 240 "&eth;")
    (ntilde () 241 "&ntilde;")
    (ograve () 242 "&ograve;")
    (oacute () 243 "&oacute;")
    (ocircumflex () 244 "&ocirc;")
    (otilde () 245 "&otilde;")
    (odiaeresis () 246 "&ouml;")
    (division () 247 "&divide;")
    (oslash () 248 "&oslash;")
    (ugrave () 249 "&ugrave;")
    (uacute () 250 "&uacute;")
    (ucircumflex () 251 "&ucirc;")
    (udiaeresis () 252 "&uuml;")
    (yacute () 253 "&yacute;")
    (thorn () 254 "&thorn;")
    (ydiaeresis () 255 "&yuml;"))
  "Table defining SGML entities, see `x-symbol-sgml-table'.")

(defvar x-symbol-sgml-latinN-table
  '((Aogonek (noname) 260)
    (breve (noname) 728)
    (Lslash (noname) 321)
    (Lcaron (noname) 317)
    (Sacute (noname) 346)
    (Scaron (symbol) 352 "&Scaron;")
    (Scedilla (noname) 350)
    (Tcaron (noname) 356)
    (Zacute (noname) 377)
    (Zcaron (noname) 381)
    (Zdotaccent (noname) 379)
    (aogonek (noname) 261)
    (ogonek (noname) 731)
    (lslash (noname) 322)
    (lcaron (noname) 318)
    (sacute (noname) 347)
    (caron (noname) 711)
    (scaron (symbol) 353 "&scaron;")
    (scedilla (noname) 351)
    (tcaron (noname) 357)
    (zacute (noname) 378)
    (hungarumlaut (noname) 733)
    (zcaron (noname) 382)
    (zdotaccent (noname) 380)
    (Racute (noname) 340)
    (Abreve (noname) 258)
    (Lacute (noname) 313)
    (Cacute (noname) 262)
    (Ccaron (noname) 268)
    (Eogonek (noname) 280)
    (Ecaron (noname) 282)
    (Dcaron (noname) 270)
    (Dbar (noname) 272)
    (Nacute (noname) 323)
    (Ncaron (noname) 327)
    (Ohungarumlaut (noname) 336)
    (Rcaron (noname) 344)
    (Uring (noname) 366)
    (Uhungarumlaut (noname) 368)
    (Tcedilla (noname) 354)
    (racute (noname) 341)
    (abreve (noname) 259)
    (lacute (noname) 314)
    (cacute (noname) 263)
    (ccaron (noname) 269)
    (eogonek (noname) 281)
    (ecaron (noname) 283)
    (dcaron (noname) 271)
    (dbar (noname) 273)
    (nacute (noname) 324)
    (ncaron (noname) 328)
    (ohungarumlaut (noname) 337)
    (rcaron (noname) 345)
    (uring (noname) 367)
    (uhungarumlaut (noname) 369)
    (tcedilla (noname) 355)
    (dotaccent (noname) 729)
    (Hbar (noname) 294)
    (Hcircumflex (noname) 292)
    (Idotaccent (noname) 304)
    (Gbreve (noname) 286)
    (Jcircumflex (noname) 308)
    (hbar (noname) 295)
    (hcircumflex (noname) 293)
    (dotlessi (noname) 305)
    (gbreve (noname) 287)
    (jcircumflex (noname) 309)
    (Cdotaccent (noname) 266)
    (Ccircumflex (noname) 264)
    (Gdotaccent (noname) 288)
    (Gcircumflex (noname) 284)
    (Ubreve (noname) 364)
    (Scircumflex (noname) 348)
    (cdotaccent (noname) 267)
    (ccircumflex (noname) 265)
    (gdotaccent (noname) 289)
    (gcircumflex (noname) 285)
    (ubreve (noname) 365)
    (scircumflex (noname) 349)
    (euro (symbol) 8364 "&euro;")
    (OE (symbol) 338 "&OElig;")
    (oe (symbol) 339 "&oelig;")
    (Ydiaeresis (symbol) 376 "&Yuml;"))
  "Table defining SGML entities, see `x-symbol-sgml-table'.")

(defvar x-symbol-sgml-xsymb0-table
  '((Delta (symbol) 916 "&Delta;")
    (Phi (symbol) 934 "&Phi;")
    (Gamma (symbol) 915 "&Gamma;")
    (theta1 (symbol) 977 "&thetasym;")
    (Lambda (symbol) 923 "&Lambda;")
    (Pi (symbol) 928 "&Pi;")
    (Theta (symbol) 920 "&Theta;")
    (Sigma (symbol) 931 "&Sigma;")
    (sigma1 (symbol) 962 "&sigmaf;")
    (Omega (symbol) 937 "&Omega;")
    (Xi (symbol) 926 "&Xi;")
    (Psi (symbol) 936 "&Psi;")
    (alpha (symbol) 945 "&alpha;")
    (beta (symbol) 946 "&beta;")
    (chi (symbol) 967 "&chi;")
    (delta (symbol) 948 "&delta;")
    (epsilon (symbol) 949 "&epsilon;")
    (phi (symbol) 966 "&phi;")
    (gamma (symbol) 947 "&gamma;")
    (eta (symbol) 951 "&eta;")
    (iota (symbol) 953 "&iota;")
    (kappa (symbol) 954 "&kappa;")
    (lambda (symbol) 955 "&lambda;")
    (mu (symbol) 956 "&mu;")
    (nu (symbol) 957 "&nu;")
    (pi (symbol) 960 "&pi;")
    (theta (symbol) 952 "&theta;")
    (rho (symbol) 961 "&rho;")
    (sigma (symbol) 963 "&sigma;")
    (tau (symbol) 964 "&tau;")
    (upsilon (symbol) 965 "&upsilon;")
    (omega1 (symbol) 982 "&piv;")
    (omega (symbol) 969 "&omega;")
    (xi (symbol) 958 "&xi;")
    (psi (symbol) 968 "&psi;")
    (zeta (symbol) 950 "&zeta;")
    (Upsilon1 (symbol) 978 "&upsih;")

    (florin (symbol) 402 "&fnof;")
    (bullet (symbol) 8226 "&bull;")
    (ellipsis (symbol) 8230 "&hellip;")
    (minute (symbol) 8242 "&prime;")
    (second (symbol) 8243 "&Prime;")
    (radicalex (symbol) 8254 "&oline;")
    (fraction (symbol) 8260 "&frasl;")
    (weierstrass (symbol) 8472 "&weierp;")
    (Ifraktur (symbol) 8465 "&image;")
    (Rfraktur (symbol) 8476 "&real;")
    (trademark (symbol) 8482 "&trade;")
    (aleph (symbol) 8501 "&alefsym;")
    (arrowleft (symbol) 8592 "&larr;")
    (arrowup (symbol) 8593 "&uarr;")
    (arrowright (symbol) 8594 "&rarr;")
    (arrowdown (symbol) 8595 "&darr;")
    (arrowboth (symbol) 8596 "&harr;")
    (carriagereturn (symbol) 8629 "&crarr;")
    (arrowdblleft (symbol) 8656 "&lArr;")
    (arrowdblup (symbol) 8657 "&uArr;")
    (arrowdblright (symbol) 8658 "&rArr;")
    (arrowdbldown (symbol) 8659 "&dArr;")
    (arrowdblboth (symbol) 8660 "&hArr;")

    (partialdiff (symbol) 8706 "&part;")
    (emptyset (symbol) 8709 "&empty;")
    (gradient (symbol) 8711 "&nabla;")
    (element (symbol) 8712 "&isin;")
    (notelement (symbol) 8713 "&notin;")
    (suchthat (symbol) 8715 "&ni;")
    (product (symbol) 8719 "&prod;")
    (summation (symbol) 8721 "&sum;")
    (minus1 (symbol) 8722 "&minus;")
    (asterisk1 (symbol) 8727 "&lowast;")
    (radical (symbol) 8730 "&radic;")
    (proportional (symbol) 8733 "&prop;")
    (infinity (symbol) 8734 "&infin;")
    (angle (symbol) 8736 "&ang;")
    (logicaland (symbol) 8743 "&and;")
    (logicalor (symbol) 8744 "&or;")
    (intersection (symbol) 8745 "&cap;")
    (union (symbol) 8746 "&cup;")
    (integral (symbol) 8747 "&int;")
    (similar (symbol) 8764 "&sim;")
    (congruent (symbol) 8773 "&cong;")
    (notequal (symbol) 8800 "&ne;")
    (equivalence (symbol) 8801 "&equiv;")
    (lessequal (symbol) 8804 "&le;")
    (greaterequal (symbol) 8805 "&ge;")
    (propersubset (symbol) 8834 "&sub;")
    (propersuperset (symbol) 8835 "&sup;")
    (notsubset (symbol) 8836 "&nsub;")
    (reflexsubset (symbol) 8838 "&sube;")
    (reflexsuperset (symbol) 8839 "&supe;")
    (circleplus (symbol) 8853 "&oplus;")
    (circlemultiply (symbol) 8855 "&otimes;")
    (perpendicular (symbol) 8869 "&perp;")
    (periodcentered1 (symbol) 8901 "&sdot;")
    (angleleft (symbol) 9001 "&lang;")
    (angleright (symbol) 9002 "&rang;")
    (lozenge (symbol) 9674 "&loz;")
    (spade (symbol) 9824 "&spades;")
    (club (symbol) 9827 "&clubs;")
    (heart (symbol) 9829 "&hearts;")
    (diamond (symbol) 9830 "&diams;"))
  "Table defining SGML entities, see `x-symbol-sgml-table'.")

(defvar x-symbol-sgml-xsymb1-table
  '((ampersand2 () 38 "&amp;")
    (quotedbl1 () 34 "&quot;")
    (less2 () 60 "&lt;")
    (greater2 () 62 "&gt;")
    (universal1 (symbol) 8704 "&forall;")
    (existential1 (symbol) 8707 "&exist;")
    (circumflex (symbol) 710 "&circ;")
    (tilde (symbol) 732 "&tilde;")
    ;;(ensp (symbol) 8194 "&ensp;") ;  en space, U+2002 ISOpub
    ;;(emsp (symbol) 8195 "&emsp;") ;  em space, U+2003 ISOpub
    ;;(thinsp (symbol) 8201 "&thinsp;") ;  thin space, U+2009 ISOpub
    ;;(zwnj (symbol) 8204 "&zwnj;") ;  zero width non-joiner, U+200C NEW RFC 2070
    ;;(zwj (symbol) 8205 "&zwj;") ;  zero width joiner, U+200D NEW RFC 2070
    ;;(lrm (symbol) 8206 "&lrm;") ;  left-to-right mark, U+200E NEW RFC 2070
    ;;(rlm (symbol) 8207 "&rlm;") ;  right-to-left mark, U+200F NEW RFC 2070
    (endash (symbol) 8211 "&ndash;")
    (emdash (symbol) 8212 "&mdash;")
    ;;(lsquo (symbol) 8216 "&lsquo;") ;  left single quotation mark, U+2018 ISOnum
    ;;(rsquo (symbol) 8217 "&rsquo;") ;  right single quotation mark, U+2019 ISOnum
    ;;(sbquo (symbol) 8218 "&sbquo;") ;  single low-9 quotation mark, U+201A NEW
    ;;(ldquo (symbol) 8220 "&ldquo;") ;  left double quotation mark, U+201C ISOnum
    ;;(rdquo (symbol) 8221 "&rdquo;") ;  right double quotation mark, U+201D ISOnum
    ;;(bdquo (symbol) 8222 "&bdquo;") ;  double low-9 quotation mark, U+201E NEW
    (dagger (symbol) 8224 "&dagger;")
    (daggerdbl (symbol) 8225 "&Dagger;")
    (perthousand (symbol) 8240 "&permil;")
    (guilsinglleft (symbol) 8249 "&lsaquo;")
    (guilsinglright (symbol) 8250 "&rsaquo;")
    (therefore1 (symbol) 8756 "&there4;")
    (ceilingleft (symbol) 8968 "&lceil;")
    (ceilingright (symbol) 8969 "&rceil;")
    (floorleft (symbol) 8970 "&lfloor;")
    (floorright (symbol) 8971 "&rfloor;")
    (asym (symbol) 8776 "&asymp;")
    )
  "Table defining SGML entities, see `x-symbol-sgml-table'.")

;; Should I add symbols from http://www.bbsinc.com/iso8859.html ?
(defvar x-symbol-sgml-table
  (append x-symbol-sgml-user-table
	  '(nil)
	  x-symbol-sgml-latin1-table
	  x-symbol-sgml-latinN-table
	  x-symbol-sgml-xsymb0-table
	  x-symbol-sgml-xsymb1-table)
  "Table defining `sgml' tokens for the characters.
See language access `x-symbol-LANG-table' and variable
`x-symbol-sgml-token-list'.  Use `x-symbol-sgml-user-table' to define
private SGML entities or shadow existing ones.")


;;;===========================================================================
;;;  Subscript functions
;;;===========================================================================

(defun x-symbol-sgml-subscript-matcher (limit)
  ;; checkdoc-params: (limit)
  "Match and skip over super- and subscripts.
Return nil if `x-symbol-mode' or `x-symbol-subscripts' is nil.  Uses
`x-symbol-sgml-font-lock-regexp'."
  (block nil
    (let (open-beg open-end close-end close-beg)
      (while (re-search-forward x-symbol-sgml-font-lock-regexp limit t)
	(setq open-beg (match-beginning 0)
	      open-end (match-end 0))
	(when (re-search-forward x-symbol-sgml-font-lock-limit-regexp
				 limit 'limit)
	  (setq close-beg (match-beginning 0)
		close-end (match-end 0))
	  (if (equal (cdr (assoc (downcase
				  (buffer-substring open-beg open-end))
				 x-symbol-sgml-font-lock-alist))
		     (downcase (buffer-substring close-beg close-end)))
	      (when
		  (save-excursion
		    (goto-char open-end)
		    (re-search-forward x-symbol-sgml-font-lock-contents-regexp
				       close-beg t))
		(store-match-data (list open-beg close-end
					open-beg open-end
					open-end close-beg
					close-beg close-end))
		(return (if (eq (char-after (+ 3 open-beg)) ?b)
			    'x-symbol-sub-face
			  'x-symbol-sup-face)))
	    (goto-char close-beg)))))))

;;; Local IspellPersDict: .ispell_xsymb
;;; x-symbol-sgml.el ends here
