;;; x-symbol-texi.el --- token language "TeXinfo command" for package x-symbol

;; Copyright (C) 2000, 2002, 2003 Free Software Foundation, Inc.
;;
;; Author: Christoph Wedler <wedler@users.sourceforge.net>
;; Maintainer: (Please use `M-x x-symbol-package-bug' to contact the maintainer)
;; Version: 4.5
;; Keywords: WYSIWYG, TeXinfo, wp, internationalization
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

(provide 'x-symbol-texi)


;;;===========================================================================
;;;  General language accesses, see `x-symbol-language-access-alist'
;;;===========================================================================

(defcustom x-symbol-texi-auto-style '(t nil nil nil nil nil)
  "Values for X-Symbol's buffer-local variables with language `texi'.
See language access `x-symbol-LANG-auto-style'."
  :group 'x-symbol-texi
  :group 'x-symbol-mode
  :type 'x-symbol-auto-style)

(defcustom x-symbol-texi-modeline-name "texi"
  "Modeline name of token language `texi'.
See language access `x-symbol-LANG-modeline-name'."
  :group 'x-symbol-texi
  :type 'string)

(defcustom x-symbol-texi-header-groups-alist
  '(("Symbol" bigop operator line relation arrow triangle shape white dots
     punctuation quote parenthesis symbol currency mathletter setsymbol)
    ("Misc. Letter" greek greek1 letter slash cedilla ogonek)
    ("Dotaccent, Ring" dotaccent ring)
    ("Tilde, Breve" tilde breve)
    ("Circumflex, Caron" circumflex caron)
    ("Diaeresis, Umlaut" diaeresis hungarumlaut)
    ("Acute, Grave" acute grave))
  "Header/submenu specification of the specific menu for language `texi'.
See language access `x-symbol-LANG-header-groups-alist'."
  :group 'x-symbol-texi
  :group 'x-symbol-input-init
  :type 'x-symbol-headers)

(defcustom x-symbol-texi-electric-ignore nil
  "Specification restricting input method ELECTRIC with language `texi'.
See language access `x-symbol-LANG-electric-ignore'."
  :group 'x-symbol-texi
  :group 'x-symbol-input-control
  :type 'x-symbol-function-or-regexp)

(defcustom x-symbol-texi-class-alist
  '((aletter "acc.letter" (x-symbol-info-face))
    (symbol "symbol" (x-symbol-info-face))
    (bullet "bullet" (x-symbol-info-face))
    (no-code "not as code" (x-symbol-emph-info-face))
    (VALID "unknown TeXinfo command" (x-symbol-emph-info-face))
    (INVALID "no TeXinfo command" (x-symbol-emph-info-face)))
  "Token classes displayed by info in echo area, for language `texi'.
See language access `x-symbol-LANG-class-alist'."
  :group 'x-symbol-texi
  :group 'x-symbol-info-strings
  :type 'x-symbol-class-info)

(defcustom x-symbol-texi-class-face-alist nil
  "Color scheme in language specific grid and info, for language `texi'.
See language access `x-symbol-LANG-class-face-alist'."
  :group 'x-symbol-texi
  :group 'x-symbol-input-init
  :group 'x-symbol-info-general
  :type 'x-symbol-class-faces)


(defvar x-symbol-texi-token-grammar
  '(x-symbol-make-grammar
    :encode-spec (?@)
    :decode-regexp
    "@\\(?:[A-Za-z]+{[A-Za-z]?}\\|[{}]\\|[~^\"'`][A-Za-z]\\|,{[A-Za-z]}\\)"
    :decode-spec (?@))
  "Grammar of token language `texi'.
See language access `x-symbol-LANG-token-grammar'.")

(defvar x-symbol-texi-user-table nil
  "User table defining TeXinfo commands, used in `x-symbol-texi-table'.")

(defvar x-symbol-texi-generated-data nil
  "Generated data for token language `texi'.
See language access `x-symbol-LANG-generated-data'.")


;;;===========================================================================
;;;  The tables
;;;===========================================================================

(defvar x-symbol-texi-latin1-table
  '(;;(nobreakspace () "\\nobreakspace")
    (exclamdown (symbol) "@exclamdown{}")
    ;;(cent () "\\textcent")
    (sterling (symbol) "@pounds{}")
    ;;(currency () "\\textcurrency")
    ;;(yen () "\\textyen")
    ;;(brokenbar () "\\textbrokenbar")
    ;;(section () "\\S")
    ;;(diaeresis () "@\"{}")
    (copyright (symbol) "@copyright{}")
    ;;(ordfeminine () "\\textordfeminine")
    ;;(guillemotleft () "\\guillemotleft")
    ;;(notsign () "\\lnot" "\\neg")
    ;;(hyphen () "\\-")
    ;;(registered () "\\textregistered")
    ;;(macron () "\\={}")
    ;;(degree () "\\textdegree")
    ;;(plusminus () "\\pm")
    ;;(twosuperior () "\\mathtwosuperior")
    ;;(threesuperior () "\\maththreesuperior")
    ;;(acute () "@'{}")
    ;;(mu1 () "\\mathmicro")
    ;;(paragraph () "\\P")
    ;;(periodcentered () "\\textperiodcentered")
    ;;(cedilla () "@,\\ ")
    ;;(onesuperior () "\\mathonesuperior")
    ;;(masculine () "\\textordmasculine")
    ;;(guillemotright () "\\guillemotright")
    ;;(onequarter () "\\textonequarter")
    ;;(onehalf () "\\textonehalf")
    ;;(threequarters () "\\textthreequarters")
    (questiondown (symbol) "@questiondown{}")
    (Agrave (aletter) "@`A")
    (Aacute (aletter) "@'A")
    (Acircumflex (aletter) "@^A")
    (Atilde (aletter) "@~A")
    (Adiaeresis (aletter) "@\"A")
    (Aring (aletter) "@AA{}")
    (AE (aletter) "@AE{}")
    (Ccedilla (aletter) "@,{C}")
    (Egrave (aletter) "@`E")
    (Eacute (aletter) "@'E")
    (Ecircumflex (aletter) "@^E")
    (Ediaeresis (aletter) "@\"E")
    (Igrave (aletter) "@`I")
    (Iacute (aletter) "@'I")
    (Icircumflex (aletter) "@^I")
    (Idiaeresis (aletter) "@\"I")
    ;;(ETH () "\\DH")
    (Ntilde (aletter) "@~N")
    (Ograve (aletter) "@`O")
    (Oacute (aletter) "@'O")
    (Ocircumflex (aletter) "@^O")
    (Otilde (aletter) "@~O")
    (Odiaeresis (aletter) "@\"O")
    ;;(multiply () "\\times")
    (Ooblique (aletter) "@O{}")
    (Ugrave (aletter) "@`U")
    (Uacute (aletter) "@'U")
    (Ucircumflex (aletter) "@^U")
    (Udiaeresis (aletter) "@\"U")
    (Yacute (aletter) "@'Y")
    ;;(THORN () "\\TH")
    (ssharp (aletter) "@ss{}")
    (agrave (aletter) "@`a")
    (aacute (aletter) "@'a")
    (acircumflex (aletter) "@^a")
    (atilde (aletter) "@~a")
    (adiaeresis (aletter) "@\"a")
    (aring (aletter) "@aa{}")
    (ae (aletter) "@ae{}")
    (ccedilla (aletter) "@,{c}")
    (egrave (aletter) "@`e")
    (eacute (aletter) "@'e")
    (ecircumflex (aletter) "@^e")
    (ediaeresis (aletter) "@\"e")
    (igrave (aletter) "@`i")
    (iacute (aletter) "@'i")
    (icircumflex (aletter) "@^i")
    (idiaeresis (aletter) "@\"i")	; TeX should used dotless-i
    ;;(eth () "\\dh")
    (ntilde (aletter) "@~n")
    (ograve (aletter) "@`o")
    (oacute (aletter) "@'o")
    (ocircumflex (aletter) "@^o")
    (otilde (aletter) "@~o")
    (odiaeresis (aletter) "@\"o")
    ;;(division () "\\div")
    (oslash (aletter) "@o{}")
    (ugrave (aletter) "@`u")
    (uacute (aletter) "@'u")
    (ucircumflex (aletter) "@^u")
    (udiaeresis (aletter) "@\"u")
    (yacute (aletter) "@'y")
    ;;(thorn () "\\th")
    (ydiaeresis (aletter) "@\"y"))
  "Table defining TeXinfo commands, see `x-symbol-texi-table'.")

(defvar x-symbol-texi-latinN-table
  '(;;(Aogonek () "\\k A")
    ;;(breve () "@u{}")
    (Lslash (aletter) "@L{}")
    (Lcaron (aletter) "@v{L}")		; TeX should use T1 fontenc
    (Sacute (aletter) "@'S")
    (Scaron (aletter) "@v{S}")
    (Scedilla (aletter) "@,{S}")
    (Tcaron (aletter) "@v{T}")
    (Zacute (aletter) "@'Z")
    (Zcaron (aletter) "@v{Z}")
    (Zdotaccent (aletter) "@dotaccent{Z}")
    ;;(aogonek () "\\k a")
    ;;(ogonek () "\\k\\ ")
    (lslash (aletter) "@l{}")
    (lcaron (aletter) "@v{l}")		; TeX should use T1 fontenc
    (sacute (aletter) "@'s")
    ;;(caron () "\\v{}")
    (scaron (aletter) "@v{s}")
    (scedilla (aletter) "@,{s}")
    (tcaron (aletter) "@v{t}")		; TeX should use T1 fontenc
    (zacute (aletter) "@'z")
    ;;(hungarumlaut () "@H{}")
    (zcaron (aletter) "@v{z}")
    (zdotaccent (aletter) "@dotaccent{z}")
    (Racute (aletter) "@'R")
    (Abreve (aletter) "@u{A}")
    (Lacute (aletter) "@'L")
    (Cacute (aletter) "@'C")
    (Ccaron (aletter) "@v{C}")
    ;;(Eogonek () "\\k E")
    (Ecaron (aletter) "@v{E}")
    (Dcaron (aletter) "@v{D}")
    ;;(Dbar () "\\DJ")
    (Nacute (aletter) "@'N")
    (Ncaron (aletter) "@v{N}")
    (Ohungarumlaut (aletter) "@H{O}")
    (Rcaron (aletter) "@v{R}")
    (Uring (aletter) "@ringaccent{U}")
    (Uhungarumlaut (aletter) "@H{U}")
    (Tcedilla (aletter) "@,{T}")
    (racute (aletter) "@'r")
    (abreve (aletter) "@u{a}")
    (lacute (aletter) "@'l")
    (cacute (aletter) "@'c")
    (ccaron (aletter) "@v{c}")
    ;;(eogonek () "\\k e")
    (ecaron (aletter) "@v{e}")
    (dcaron (aletter) "@v{d}")		; TeX should use T1 fontenc
    ;;(dbar () "\\dj")
    (nacute (aletter) "@'n")
    (ncaron (aletter) "@v{n}")
    (ohungarumlaut (aletter) "@H{o}")
    (rcaron (aletter) "@v{r}")
    (uring (aletter) "@ringaccent{u}")
    (uhungarumlaut (aletter) "@H{u}")
    (tcedilla (aletter) "@,{t}")
    ;;(dotaccent () "@dotaccent{}")
    ;;(Hbar () "\\textmalteseH")
    (Hcircumflex (aletter) "@^H")
    (Idotaccent (aletter) "@dotaccent{I}")
    (Gbreve (aletter) "@u{G}")
    (Jcircumflex (aletter) "@^J")
    ;;(hbar () "\\textmalteseh")
    (hcircumflex (aletter) "@^h")
    (dotlessi (aletter) "@dotless{i}")
    (gbreve (aletter) "@u{g}")
    (jcircumflex (aletter) "@^j")
    (Cdotaccent (aletter) "@dotaccent{C}")
    (Ccircumflex (aletter) "@^C")
    (Gdotaccent (aletter) "@dotaccent{G}")
    (Gcircumflex (aletter) "@^G")
    (Ubreve (aletter) "@u{U}")
    (Scircumflex (aletter) "@^S")
    (cdotaccent (aletter) "@dotaccent{c}")
    (ccircumflex (aletter) "@^c")
    (gdotaccent (aletter) "@dotaccent{g}")
    (gcircumflex (aletter) "@^g")
    (ubreve (aletter) "@u{u}")
    (scircumflex (aletter) "@^s")
    (OE (aletter) "@OE{}")
    (oe (aletter) "@oe{}")
    (Ydiaeresis (aletter) "@\"Y"))
  "Table defining TeXinfo commands, see `x-symbol-texi-table'.")

(defvar x-symbol-texi-xsymbX-table
  '((bullet (bullet) "@bullet{}")
    (equivalence (symbol) "@equiv{}")
    (ellipsis (symbol) "@dots{}")
    (arrowdblright (symbol) "@result{}")
    ;;(NG () "\\NG")
    (dotlessj (aletter) "@dotless{j}")
    ;;(ng () "\\ng")
    (star (symbol) "@point{}")
    (braceleft2 (symbol) "@{")
    (braceright2 (symbol) "@}")
    (mapsto (symbol) "@expansion{}")
    (dashbar (symbol) "@print{}")
    ;;(grave () "@`{}")
    ;;(circumflex () "@^{}")
    ;;(tilde () "@~{}")
    (endash (bullet no-code) "@minus{}")
    ;;(emdash () "\\textemdash")
    ;;(at2 () "@@")
    ;;(endellipsis () "enddots{}")
    ;;(error () "error{}")
    )
  "Table defining TeXinfo commands, see `x-symbol-texi-table'.")

(defvar x-symbol-texi-table
  (append x-symbol-texi-user-table
	  '(nil)
	  x-symbol-texi-latin1-table
	  x-symbol-texi-latinN-table
	  x-symbol-texi-xsymbX-table)
  "Table defining `texi' tokens for the characters.
See language access `x-symbol-LANG-table'.  Use
`x-symbol-texi-user-table' to define private TeXinfo commands or shadow
existing ones.")

;;; Local IspellPersDict: .ispell_xsymb
;;; x-symbol-texi.el ends here
