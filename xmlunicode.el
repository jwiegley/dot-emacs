;;; xmlunicode.el --- Unicode support for XML -*- coding: utf-8 -*-

;; $Id$

;; Copyright (C) 2003 Norman Walsh
;; Inspired in part by sgml-input, Copyright (C) 2001 Dave Love
;; Inspired in part by http://www.tbray.org/ongoing/When/200x/2003/09/27/UniEmacs

;; Author: Norman Walsh <ndw@nwalsh.com>
;; Maintainer: Norman Walsh <ndw@nwalsh.com>
;; Created: 2004-07-21
;; Version: 1.6
;; CVS ID: $Id$
;; Keywords: utf-8 unicode xml characters

;; This file is NOT part of GNU emacs.

;; This is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 2, or (at your option)
;; any later version.

;; This software is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with GNU Emacs; see the file COPYING.  If not, write to the
;; Free Software Foundation, Inc., 59 Temple Place - Suite 330,
;; Boston, MA 02111-1307, USA.

;;; Commentary

;; This file provides a suite of functions designed to make it easier
;; to enter Unicode into Emacs. It is not, in fact, particularly XML-specific though
;; it does define an 'xml input-mode and does support the ISO 8879 entity names.

;;; Usage

;; 1. Before loading this file, make sure that the variable unicode-character-list is
;;    defined. The unicode-character-list is a list of triples of the form:
;;
;;    (codepoint "unicode name" "iso name") ; iso name can be nil
;;
;;    e.g.:   (defvar unicode-character-list
;;             '(
;;               ;Codept   Unicode name                            ISO Name
;;               (#x000000 "NULL"                                   nil     )
;;               (#x000001 "START OF HEADING"                       nil     )
;;               ...
;;               (#x0000a0 "NO-BREAK SPACE"                         "nbsp"  )
;;               (#x0000a1 "INVERTED EXCLAMATION MARK"              "iexcl" )
;;               (#x0000a2 "CENT SIGN"                              "cent"  )
;;               ...))
;;
;;
;;    The easiest way to define this list is to load "unichars.el"
;;    which should be available where you got this file.
;;
;; 2. Bind the functions defined in this file to keys you find convenient.
;;
;;    The likely candidates are:
;;
;;    unicode-character-insert            insert a character by unicode name
;;                                        (with completion)
;;    iso8879-character-insert            insert a character by ISO entity name
;;                                        (with completion)
;;    unicode-smart-double-quote          inserts an appropriate double quote
;;    unicode-smart-single-quote          inserts an appropriate single quote
;;    unicode-character-menu-insert       choose special character from a popup menu
;;    unicode-character-shortcut-insert   enter a two-character shortcut for a
;;                                        unicode character
;;
;;    You can also create a standard Emacs menu for the character menu list
;;    (instead of, or in addition to, the popup). To do that:
;;
;;    (define-key APPROPRIATE-MAP [menu-bar unichar]
;;      (cons "UniChar" unicode-character-menu-map))
;;
;;    Where APPROPRIATE-MAP is the name of the emacs keymap to bind into
;;
;; 3. If you want to use the xml input-mode, which provides automatic replacement for the
;;    ISO entity names:
;;
;;    (set-input-method 'xml)
;;
;;    in the appropriate context. Unlike sgml-input, xml-input only inserts the
;;    characters for which you have glyphs. It inserts other characters as numeric
;;    character references. (If you want to insert a literal character even if
;;    you don't have it in your fonts, use unicode-character-insert or
;;    iso8879-character-insert with a prefix.)

;;; Changes

;; v1.7
;;   Require "cl" because, well, because it's required. Also fiddled with
;;   the way single quotes are handled; the apostrophe is now part of the
;;   cycle
;; v1.6
;;   Remove debugging code. Embarrassed again. :-(
;; v1.5
;;   Fixed bug in unicode-smart-single-quote. It wasn't cycling through all
;;   three quotes correctly because of a typo in the function definition.
;;   Make sure smart semicolon insertion only happens if we're right at the
;;   end of a numeric character reference.
;; v1.4
;;   Fixed bug in insert-smart-semicolon. It wasn't careful to tie the search
;;   to the most recent preceding ampersand.
;; v1.3
;;   Fixed bug in (in-comment)
;;   Added unicode-smart-semicolon as another convenience for entering Unicode chars
;;   Added show-unicode-character-list
;; v1.2
;;   Added unicode-smart-hyphen for easy insert of mdash and ndash
;;   Added unicode-smart-period for easy insert of hellip
;;   Fixed a bug in unicode-smart-single-quote
;; v1.1
;;   Fixed a few bugs with respect to how numeric character references are entered.
;;   Added xml-tag-search-limit and unicode-charref-format
;; v1.0
;;   First release. Nearly a complete rewrite from the former xmlchars.el file

;;; Code:

(require 'cl)

(defvar unicode-ldquo  (decode-char 'ucs #x00201c))
(defvar unicode-rdquo  (decode-char 'ucs #x00201d))
(defvar unicode-lsquo  (decode-char 'ucs #x002018))
(defvar unicode-rsquo  (decode-char 'ucs #x002019))
(defvar unicode-quot   (decode-char 'ucs #x000022))
(defvar unicode-apos   (decode-char 'ucs #x000027))
(defvar unicode-capos  (decode-char 'ucs #x0002bc))
(defvar unicode-ndash  (decode-char 'ucs #x002013))
(defvar unicode-mdash  (decode-char 'ucs #x002014))
(defvar unicode-hellip (decode-char 'ucs #x002026))

(defvar unicode-charref-format "&#x%x;"
  "The format for numeric character references")

(defvar xml-tag-search-limit 4096
  "Maximum distance to search from point for tag start characters")

(defvar unicode-character-list-file "/define/this/before/you/load/me"
  "The name of the file that contains your unicode-character-list. unichars.el should be available where you got this file.")

(if (not (boundp 'unicode-character-list))
    (load-file unicode-character-list-file))

(defvar unicode-character-alist '()
  "Mapping of Unicode character names to codepoints.")

(let ((ulist unicode-character-list))
  (setq unicode-character-alist
	(list (cons (cadr (car ulist)) (car (car ulist)))))
  (setq ulist (cdr ulist))
  (while ulist
    (nconc unicode-character-alist
	   (list (cons (cadr (car ulist)) (car (car ulist)))))
    (setq ulist (cdr ulist))))

(defvar iso8879-character-alist '()
  "Mapping of ISO 8879 entity names names to codepoints.")

(let ((ulist unicode-character-list))
  (while (and ulist (not (caddr (car ulist))))
    (setq ulist (cdr ulist)))
  (setq iso8879-character-alist
	(list (cons (caddr (car ulist)) (car (car ulist)))))
  (setq ulist (cdr ulist))
  (while ulist
    (if (caddr (car ulist))
	(nconc iso8879-character-alist
	       (list (cons (caddr (car ulist)) (car (car ulist))))))
    (setq ulist (cdr ulist))))

(defun iso8879-to-codepoints (&optional isolist)
  "Converts a list of ISO 8879 entity names to a list of codepoints. This is a convenience function for defining the glyph list."
  (let (codepoint-list)
    (setq codepoint-list (list 0))
    (while isolist
      (nconc codepoint-list
	     (list (cdr (assoc (car isolist) iso8879-character-alist))))
      (setq isolist (cdr isolist)))
    (cdr codepoint-list)))

(defun unicode-to-codepoints (&optional unilist)
  "Converts a list of Unicode character names to a list of codepoints. This is a convenience function for defining the glyph list."
  (let (codepoint-list)
    (setq codepoint-list (list 0))
    (while unilist
      (nconc codepoint-list
	     (list (cdr (assoc (car isolist) unicode-character-alist))))
      (setq unilist (cdr unilist)))
    (cdr codepoint-list)))

(defvar unicode-glyph-list
  (append
   '(?A ?B ?C ?D ?E ?F ?G ?H ?I ?J ?K ?L ?M
     ?N ?O ?P ?Q ?R ?S ?T ?U ?V ?W ?X ?Y ?Z
     ?a ?b ?c ?d ?e ?f ?g ?h ?i ?j ?k ?l ?m
     ?n ?o ?p ?q ?r ?s ?t ?u ?v ?w ?x ?y ?z
     ?0 ?1 ?2 ?3 ?4 ?5 ?6 ?7 ?8 ?9 ?! ?@ ?#
     ?$ ?% ?^ ?* ?( ?) ?- ?_ ?= ?+ ?\ ?|
     ?[ ?] ?{ ?} 59 ?: ?/ ?? ?. 44 96 126)
   (iso8879-to-codepoints
    '("AElig"  "Aacute" "Abreve" "Acirc"  "Agrave"  "Amacr"  "Aogon"
      "Aring"  "Atilde" "Auml"   "Cacute" "Ccaron"  "Ccedil" "Ccirc"
      "Cdot"   "Dagger" "Dcaron" "Dot"    "Dstrok"  "ENG"    "ETH"
      "Eacute" "Ecaron" "Ecirc"  "Edot"   "Egrave"  "Emacr"  "Eogon"
      "Euml"   "Gbreve" "Gcedil" "Gcirc"  "Gdot"    "Hcirc"
      "Hstrok" "IJlig"  "Iacute" "Icirc"  "Idot"    "Igrave"
      "Imacr"  "Iogon"  "Itilde" "Iuml"   "Jcirc"   "Kcedil"
      "Lacute" "Lcaron" "Lcedil" "Lmidot" "Lstrok"  "Nacute"
      "Ncaron" "Ncedil" "Ntilde" "OElig"  "Oacute"  "Ocirc"
      "Odblac" "Ograve" "Omacr"  "Oslash" "Otilde"  "Ouml"
      "Racute" "Rcaron" "Rcedil" "Sacute" "Scaron"  "Scedil"
      "Scirc"  "THORN"  "Tcaron" "Tcedil" "Tstrok"  "Uacute"
      "Ubreve" "Ucirc"  "Udblac" "Ugrave" "Umacr"   "Uogon"
      "Uring"  "Utilde" "Uuml"   "Wcirc"  "Yacute"  "Ycirc"
      "Yuml"   "Zacute" "Zcaron" "Zdot"   "aacute"  "abreve"
      "acirc"  "acute"  "aelig"  "agrave" "amacr"   "angst"
      "aogon"           "aring"  "ast"    "atilde"  "auml"
      "b.mu"   "bdquo"  "blank"  "blk12"  "blk14"   "blk34"
      "block"  "boxDL"  "boxDR"  "boxH"   "boxHD"   "boxHU"
      "boxUL"  "boxUR"  "boxV"   "boxVH"  "boxVL"   "boxVR"
      "boxVh"  "boxdl"  "boxdr"  "boxh"   "boxhd"   "boxhu"
      "boxul"  "boxur"  "boxv"   "boxvH"  "boxvh"   "boxvl"
      "boxvr"  "breve"  "brvbar" "bsol"   "bull"    "cacute"
      "caron"  "ccaron" "ccedil" "ccirc"  "cdot"    "cedil"
      "cent"   "circ"   "colon"  "comma"  "commat"  "copy"
      "curren" "dagger" "dash"   "dblac"  "dcaron"  "deg"
      "die"    "divide" "dollar" "dot"    "dstrok"  "eacute"
      "ecaron" "ecirc"  "edot"   "egrave" "emacr"   "emsp"
      "emsp13" "emsp14" "eng"    "ensp"   "eogon"   "equals"
      "equiv"  "eth"    "euml"   "excl"   "exist"   "fnof"
      "forall" "frac12" "frac14" "frac34" "frasl"   "gacute"
      "gbreve" "gcedil" "gcirc"  "gdot"   "ge"      "ges"
      "grave"           "hairsp" "half"   "hcirc"   "hellip"
      "horbar" "hstrok" "hyphen" "iacute" "icirc"   "iexcl"
      "igrave" "ijlig"  "imacr"  "inodot" "inodot"  "iogon"
      "iquest" "itilde" "iuml"   "jcirc"  "kcedil"  "kgreen"
      "lacute" "laquo"  "lcaron" "lcedil" "lcub"    "ldquo"
      "ldquor" "le"     "les"    "lhblk"  "lmidot"  "lowbar"
      "lpar"   "lsaquo" "lsqb"   "lsquo"  "lsquor"  "lstrok"
      "macr"   "mdash"  "mgr"    "micro"  "middot"  "minus"
      "mldr"   "mu"     "nacute" "napos"  "nbsp"    "ncaron"
      "ncedil" "ndash"  "ne"     "nequiv" "nexist"  "nge"
      "nges"   "ngt"    "nle"    "nles"   "nlt"     "not"
      "ntilde" "num"    "numsp"  "oacute" "ocirc"   "odblac"
      "oelig"  "ogon"   "ograve" "omacr"  "ordf"    "ordm"
      "oslash" "otilde" "ouml"   "para"   "percnt"  "period"
      "permil" "plus"   "plusmn" "pound"  "puncsp"  "quest"
               "racute" "raquo"  "rcaron" "rcedil"  "rcub"
      "rdquo"  "rdquor" "reg"    "ring"   "rpar"    "rsaquo"
      "rsqb"   "rsquo"  "rsquor" "sacute" "sbquo"   "sbsol"
      "scaron" "scedil" "scirc"  "sect"   "semi"    "shy"
      "sol"    "sup1"   "sup2"   "sup3"   "szlig"   "tcaron"
      "tcedil" "thinsp" "thorn"  "tilde"  "times"   "trade"
      "tstrok" "uacute" "ubreve" "ucirc"  "udblac"  "ugrave"
      "uhblk"  "umacr"  "uml"    "uogon"  "uring"   "utilde"
      "uuml"   "verbar" "wcirc"  "wedgeq" "yacute"  "ycirc"
      "yen"    "yuml"   "zacute" "zcaron" "zdot")))
  "A list of Unicode codepoints identifying the characters that display correctly in your Emacs with your fonts.")

;; Insert characters by Unicode name (with completion)

(defun unicode-character-insert (arg &optional argname)
  "Insert a Unicode character by character name. If a prefix is given, the character will be inserted regardless of whether or not it has a displayable glyph; otherwise, a numeric character reference is inserted if the codepoint is not in the unicode-glyph-list. If argname is given, it is used for the prompt. If argname uniquely identifies a character, that character is inserted without the prompt."
  (interactive "P")
  (let* ((completion-ignore-case t)
	 (uniname (if (stringp argname) argname ""))
	 (charname
	  (if (eq (try-completion uniname unicode-character-alist) t)
	      uniname
	    (completing-read
	     "Unicode name: "
	     unicode-character-alist
	     nil t uniname)))
	 codepoint glyph)
    (setq codepoint (cdr (assoc charname unicode-character-alist)))
    (xml-unicode-insert arg codepoint)))

;; Insert characters by iso8879 name

(defun iso8879-character-insert (arg &optional argname)
  "Insert a Unicode character by ISO 8879 entity name. If a prefix is given, the character will be inserted regardless of whether or not it has a displayable glyph; otherwise, a numeric character reference is inserted if the codepoint is not in the unicode-glyph-list. If argname is given, it is used for the prompt. If argname uniquely identifies a character, that character is inserted without the prompt."
  (interactive "P")
  (let* ((isoname (if (stringp argname) argname ""))
	 (charname
	  (if (eq (try-completion isoname iso8879-character-alist) t)
	      isoname
	    (completing-read
	     "ISO name: "
	     iso8879-character-alist
	     nil t isoname)))
	 codepoint glyph)
    (setq codepoint (cdr (assoc charname iso8879-character-alist)))
    (xml-unicode-insert arg codepoint)))

(defun xml-unicode-insert (arg codepoint)
  "Insert the Unicode character identified by codepoint taking into account available glyphs and XML predefined entities."
  (interactive "P")
  (let ((glyph (memq codepoint unicode-glyph-list)))
    (cond
     ((and (decode-char 'ucs codepoint) (or arg glyph))
      (ucs-insert codepoint))
     ((= codepoint 34)
      (insert "&quot;"))
     ((= codepoint 38)
      (insert "&amp;"))
     ((= codepoint 39)
      (insert "&apos;"))
     ((= codepoint 60)
      (insert "&lt;"))
     ((= codepoint 62)
      (insert "&gt;"))
     (t
      (insert (format unicode-charref-format codepoint))))))

;; Menus

(defvar unicode-character-menu-alist
  '(
    ("angst"     . #x212B)
    ("cent"      . #x00A2)
    ("copy"      . #x00A9)
    ("Dagger"    . #x2021)
    ("dagger"    . #x2020)
    ("deg"       . #x00B0)
    ("emsp"      . #x2003)
    ("ensp"      . #x2002)
    ("ETH"       . #x00D0)
    ("eth"       . #x00F0)
    ("euro"      . #x20AC)
    ("half"      . #x00BD)
    ("laquo"     . #x00AB)
    ("ldquo"     . #x201c)
    ("lsquo"     . #x2018)
    ("mdash"     . #x2014)
    ("micro"     . #x00B5)
    ("middot"    . #x00B7)
    ("nbsp"      . #x00A0)
    ("ndash"     . #x2013)
    ("not"       . #x00AC)
    ("numsp"     . #x2007)
    ("para"      . #x00B6)
    ("permil"    . #x2030)
    ("puncsp"    . #x2008)
    ("raquo"     . #x00BB)
    ("rdquo"     . #x201d)
    ("rsquo"     . #x2019)
    ("reg"       . #x00AE)
    ("sect"      . #x00A7)
    ("THORN"     . #x00DE)
    ("thorn"     . #x00FE)
    ("trade"     . #x2122)
    )
  "Mapping of names to codepoints for use in the popup or Emacs menu.")

(defun  unicode-character-menu-insert ()
  "Popup a menu for inserting unicode characters."
  (interactive)
  (let* ((xml-chars-menu
	  (list "Special char" (append (list "") unicode-character-menu-alist)))
	 (value (x-popup-menu t xml-chars-menu)))
    (if value (xml-unicode-insert nil value))))

(defvar unicode-character-menu-map (make-sparse-keymap "UniChar")
  "A menu map for inserting Unicode characters.")

(defun make-unicode-character-menu-bar ()
  "Builds the unicode-character-menu-map for the currently defined unicode-character-menu-alist."
  (let ((alist (reverse unicode-character-menu-alist))
	name codepoint)
    (setq unicode-character-menu-map (make-sparse-keymap "UniChar"))
    (while alist
      (setq name (car (car alist))
	    codepoint (cdr (car alist)))
      (define-key unicode-character-menu-map (vector (intern name))
	`(,name . (lambda () (interactive) (xml-unicode-insert nil ,codepoint))))
      (setq alist (cdr alist)))))

(make-unicode-character-menu-bar)

;; Simple XML tests

(defun in-start-tag ()
  "Crude test to see if point is inside an open start tag."
  (interactive)
  (let (slim here pgt plt)
    (setq here (point))
    (setq slim
	  (if (> here xml-tag-search-limit)
	      (- here xml-tag-search-limit)
	    0))
    (setq pgt (search-backward ">" slim t))
    (goto-char here)
    (setq plt (search-backward "<" slim t))
    (goto-char here)
    (if (and pgt plt)
	(> plt pgt)
      plt)))

(defun after-start-tag ()
  "Crude test to see if point is just after a start tag"
  (interactive)
  (if (and (char-before) (char-equal (char-before) ?>))
      (let (slim here plt psl)
	(setq here (point))
	(setq slim
	      (if (> here xml-tag-search-limit)
		  (- here xml-tag-search-limit)
		0))
	(setq plt (search-backward "<" slim t))
	(goto-char here)
	(setq psl (search-backward "/" slim t))
	(goto-char here)
	(or (and plt (not psl))
	    (and plt psl (< psl plt))))))

(defun in-comment ()
  "Crude test to see if point is inside a comment."
  (interactive)
  (let (slim here pgt pcmt)
    (setq here (point))
    (setq slim
	  (if (> here xml-tag-search-limit)
	      (- here xml-tag-search-limit)
	    0))
    (setq pgt (search-backward "-->" slim t))
    (goto-char here)
    (setq pcmt (search-backward "<!" slim t))
    (goto-char here)
    (if (and pgt pcmt)
	(> pcmt pgt)
      pcmt)))

;;stolen from hen.el which in turn claims to have stolen it from cxref
(defun unicode-looking-backward-at (regexp)
  "Return t if text before point matches regular expression REGEXP.
This function modifies the match data that `match-beginning',
`match-end' and `match-data' access; save and restore the match
data if you want to preserve them."
  (save-excursion
    (let ((here (point)))
      (if (re-search-backward regexp (point-min) t)
          (if (re-search-forward regexp here t)
              (= (point) here))))))

;; Smart quotes

(defun unicode-smart-double-quote ()
  "Insert a left or right double quote as appropriate. Left quotes are inserted after a space, newline, or start tag. Right quotes are inserted after any other character, except if the preceding character is a quote, in which case we cycle through the three quote styles."
  (interactive)
  (if (char-before)
      (let ((ch (char-before)))
	(cond
	 ((in-start-tag)
	  (insert "\""))
	 ((or
	   (after-start-tag)
	   (char-equal ch 40)  ; (
	   (char-equal ch 91)  ; [
	   (char-equal ch ?{)) ; {
	  (insert unicode-ldquo))
	 ((or
	   (char-equal ch ?>)  ; >
	   (char-equal ch 41)  ; )
	   (char-equal ch 93)  ; ]
	   (char-equal ch ?})) ; }
	  (insert unicode-rdquo))
	 ((or (char-equal ch 32)
	      (char-equal ch 10))
	  (insert unicode-ldquo))
	 ((char-equal ch unicode-ldquo)
	  (progn
	    (delete-backward-char 1)
	    (insert "\"")))
	 ((char-equal ch unicode-quot)
	  (progn
	    (delete-backward-char 1)
	    (insert unicode-rdquo)))
	 ((char-equal ch unicode-rdquo)
	  (progn
	    (delete-backward-char 1)
	    (insert unicode-ldquo)))
	 ((char-equal ch unicode-ldquo)
	  (progn
	    (delete-backward-char 1)
	    (insert unicode-rdquo)))
	 ((char-equal ch unicode-lsquo)
	  (insert unicode-ldquo))
	 (t (insert unicode-rdquo))))
    (insert unicode-ldquo)))

(defun unicode-smart-single-quote ()
  "Insert a left or right single quote, or an apostrophe, as appropriate. Left quotes are inserted after a space, newline, or start tag. An apostrophe is inserted after any other character, except if the preceding character is a quote or apostrophe, in which case we cycle through the styles."
  (interactive)
  (if (char-before)
      (let ((ch (char-before)))
	(cond
	 ((in-start-tag)
	  (insert "'"))
	 ((or
	   (after-start-tag)
	   (char-equal ch 40)  ; (
	   (char-equal ch 91)  ; [
	   (char-equal ch ?{)) ; {
	  (insert unicode-lsquo))
	 ((or
	   (char-equal ch ?>)  ; >
	   (char-equal ch 41)  ; )
	   (char-equal ch 93)  ; ]
	   (char-equal ch ?})) ; }
	  (insert unicode-rsquo))
	 ((or (char-equal ch 32)
	      (char-equal ch 10))
	  (insert unicode-lsquo))
	 ((char-equal ch unicode-apos)  ; ' -> rsquo
	  (progn
	    (delete-backward-char 1)
	    (insert unicode-rsquo)))
	 ((char-equal ch unicode-rsquo) ; rsquo -> lsquo
	  (progn
	    (delete-backward-char 1)
	    (insert unicode-lsquo)))
	 ((char-equal ch unicode-lsquo) ; lsquo -> '
	  (progn
	    (delete-backward-char 1)
	    (insert unicode-apos)))
	 (t (insert unicode-apos))))
    (insert unicode-lsquo)))

(defun unicode-smart-hyphen ()
  "Insert a hyphen, mdash, or ndash as appropriate. A hyphen, an mdash, and then an ndash is inserted."
  (interactive)
  (if (char-before)
      (let ((ch (char-before)))
	(cond
	 ((in-comment)
	  (insert "-"))
	 ((char-equal ch ?-)
	  (progn
	    (delete-backward-char 1)
	    (insert unicode-mdash)))
	 ((char-equal ch unicode-mdash)
	  (progn
	    (delete-backward-char 1)
	    (insert unicode-ndash)))
	 ((char-equal ch unicode-ndash)
	  (progn
	    (delete-backward-char 1)
	    (insert "-")))
	 (t (insert "-"))))
    (insert "-")))

(defun unicode-smart-period ()
  "Insert an hellipsis for three dots."
  (interactive)
  (if (> (point) 2)
      (let ((ch1 (char-before))
	    (ch2 (char-before (- (point) 1)))
	    (ch3 (char-before (- (point) 2))))
	(cond
	 ((in-comment)
	  (insert "."))
	 ((char-equal ch1 unicode-hellip)
	  (progn
	    (delete-backward-char 1)
	    (insert "....")))
	 ((and ch3 (char-equal ch1 ?.) (char-equal ch2 ?.) (char-equal ch3 ?.))
	  (insert "."))
	 ((and (char-equal ch1 ?.) (char-equal ch2 ?.))
	  (progn
	    (delete-backward-char 2)
	    (insert unicode-hellip)))
	 (t (insert "."))))
    (insert ".")))

(defun unicode-smart-semicolon ()
  "Detect numeric character references and replace them with the appropriate char."
  (interactive)
  (let ((pos (point))
	amppos codept)
    (search-backward "&" nil t nil)
    (setq amppos (point))
    (goto-char pos)
    (cond
     ((unicode-looking-backward-at "&#[xX][0-9a-fA-F]+")
      (progn
	(re-search-backward "&#[xX]\\([0-9a-fA-F]+\\)" nil t nil)
	(if (= amppos (point))
	    (progn
	      (setq codept (string-to-number (match-string 1) 16))
	      (if (memq codept unicode-glyph-list)
		  (replace-match (format "%c" (decode-char 'ucs codept)))
		(progn
		  (goto-char pos)
		  (insert ";"))))
	  (progn
	    (goto-char pos)
	    (insert ";")))))
     ((unicode-looking-backward-at "&#[0-9]+")
      (progn
	(re-search-backward "&#\\([0-9]+\\)" nil t nil)
	(if (= amppos (point))
	    (progn
	      (setq codept (string-to-number (match-string 1) 10))
	      (if (memq codept unicode-glyph-list)
		  (replace-match (format "%c" (decode-char 'ucs codept)))
		(progn
		  (goto-char pos)
		  (insert ";"))))
	  (progn
	    (goto-char pos)
	    (insert ";")))))
     (t
      (insert ";")))))

;; Setup quail for XML mode

(require 'quail)

(quail-define-package
 "xml" "UTF-8" "&" t
 "Unicode characters input method using ISO 8879 entitie names from the unicode-character-list"
 nil t nil nil nil nil nil nil nil nil t)

(defvar xml-quail-define-rules '()
  "The default xml-input rules. Built dynamically from the unicode-character-list and the unicode-glyph-list.")

(let ((ulist iso8879-character-alist)
      codepoint glyph entname)
  (setq xml-quail-define-rules (list 'quail-define-rules))
  (while ulist
    (setq codepoint (cdr (car ulist)))
    (setq glyph (memq codepoint unicode-glyph-list))
    (setq entname (concat "&" (car (car ulist)) ";"))
    (cond
     ((and glyph (decode-char 'ucs codepoint))
      (nconc xml-quail-define-rules
	     (list (list entname (decode-char 'ucs codepoint)))))
     ((= codepoint 34)
      (nconc xml-quail-define-rules
	     (list (list entname (vector "&quot;")))))
     ((= codepoint 38)
      (nconc xml-quail-define-rules
	     (list (list entname (vector "&amp;")))))
     ((= codepoint 39)
      (nconc xml-quail-define-rules
	     (list (list entname (vector "&apos;")))))
     ((= codepoint 60)
      (nconc xml-quail-define-rules
	     (list (list entname (vector "&lt;")))))
     ((= codepoint 62)
      (nconc xml-quail-define-rules
	     (list (list entname (vector "&gt;")))))
     (t
      (nconc xml-quail-define-rules
	     (list (list entname (vector (format unicode-charref-format codepoint)))))))
    (setq ulist (cdr ulist))))

(eval xml-quail-define-rules)

;; Read two keys

(defvar unicode-character-shortcut-alist
  (list
   (cons "AE"  (cdr (assoc "AElig"  iso8879-character-alist)))
   (cons "A'"  (cdr (assoc "Aacute" iso8879-character-alist)))
   (cons "A^"  (cdr (assoc "Acirc"  iso8879-character-alist)))
   (cons "A`"  (cdr (assoc "Agrave" iso8879-character-alist)))
   (cons "Ao"  (cdr (assoc "Aring"  iso8879-character-alist)))
   (cons "A~"  (cdr (assoc "Atilde" iso8879-character-alist)))
   (cons "A\"" (cdr (assoc "Auml"   iso8879-character-alist)))
   (cons "C,"  (cdr (assoc "Ccedil" iso8879-character-alist)))
   (cons "E'"  (cdr (assoc "Eacute" iso8879-character-alist)))
   (cons "E^"  (cdr (assoc "Ecirc"  iso8879-character-alist)))
   (cons "E`"  (cdr (assoc "Egrave" iso8879-character-alist)))
   (cons "E\"" (cdr (assoc "Euml"   iso8879-character-alist)))
   (cons "I'"  (cdr (assoc "Iacute" iso8879-character-alist)))
   (cons "I^"  (cdr (assoc "Icirc"  iso8879-character-alist)))
   (cons "I`"  (cdr (assoc "Igrave" iso8879-character-alist)))
   (cons "I\"" (cdr (assoc "Iuml"   iso8879-character-alist)))
   (cons "N~"  (cdr (assoc "Ntilde" iso8879-character-alist)))
   (cons "O'"  (cdr (assoc "Oacute" iso8879-character-alist)))
   (cons "O^"  (cdr (assoc "Ocirc"  iso8879-character-alist)))
   (cons "O`"  (cdr (assoc "Ograve" iso8879-character-alist)))
   (cons "O/"  (cdr (assoc "Oslash" iso8879-character-alist)))
   (cons "O~"  (cdr (assoc "Otilde" iso8879-character-alist)))
   (cons "O\"" (cdr (assoc "Ouml"   iso8879-character-alist)))
   (cons "U'"  (cdr (assoc "Uacute" iso8879-character-alist)))
   (cons "U^"  (cdr (assoc "Ucirc"  iso8879-character-alist)))
   (cons "U`"  (cdr (assoc "Ugrave" iso8879-character-alist)))
   (cons "U\"" (cdr (assoc "Uuml"   iso8879-character-alist)))
   (cons "Y'"  (cdr (assoc "Yacute" iso8879-character-alist)))
   (cons "a'"  (cdr (assoc "aacute" iso8879-character-alist)))
   (cons "a^"  (cdr (assoc "acirc"  iso8879-character-alist)))
   (cons "ae"  (cdr (assoc "aelig"  iso8879-character-alist)))
   (cons "a`"  (cdr (assoc  "agrave" iso8879-character-alist)))
   (cons "ao"  (cdr (assoc "aring"  iso8879-character-alist)))
   (cons "a~"  (cdr (assoc "atilde" iso8879-character-alist)))
   (cons "a\"" (cdr (assoc "auml"   iso8879-character-alist)))
   (cons "c,"  (cdr (assoc "ccedil" iso8879-character-alist)))
   (cons "e'"  (cdr (assoc "eacute" iso8879-character-alist)))
   (cons "e^"  (cdr (assoc "ecirc"  iso8879-character-alist)))
   (cons "e`"  (cdr (assoc "egrave" iso8879-character-alist)))
   (cons "e\"" (cdr (assoc "euml"   iso8879-character-alist)))
   (cons "i'"  (cdr (assoc "iacute" iso8879-character-alist)))
   (cons "i^"  (cdr (assoc "icirc"  iso8879-character-alist)))
   (cons "i`"  (cdr (assoc "igrave" iso8879-character-alist)))
   (cons "i\"" (cdr (assoc "iuml"   iso8879-character-alist)))
   (cons "n~"  (cdr (assoc "ntilde" iso8879-character-alist)))
   (cons "o'"  (cdr (assoc "oacute" iso8879-character-alist)))
   (cons "o^"  (cdr (assoc "ocirc"  iso8879-character-alist)))
   (cons "o`"  (cdr (assoc "ograve" iso8879-character-alist)))
   (cons "o-"  (cdr (assoc "omacr"  iso8879-character-alist)))
   (cons "o/"  (cdr (assoc "oslash" iso8879-character-alist)))
   (cons "o~"  (cdr (assoc "otilde" iso8879-character-alist)))
   (cons "o\"" (cdr (assoc "ouml"   iso8879-character-alist)))
   (cons "sz"  (cdr (assoc "szlig"  iso8879-character-alist)))
   (cons "u'"  (cdr (assoc "uacute" iso8879-character-alist)))
   (cons "u^"  (cdr (assoc "ucirc"  iso8879-character-alist)))
   (cons "u`"  (cdr (assoc "ugrave" iso8879-character-alist)))
   (cons "u\"" (cdr (assoc "uuml"   iso8879-character-alist)))
   (cons "y'"  (cdr (assoc "yacute" iso8879-character-alist)))
   (cons "y\"" (cdr (assoc "yuml"   iso8879-character-alist)))
   (cons "12"  (cdr (assoc "frac12" iso8879-character-alist)))
   (cons "13"  (cdr (assoc "frac13" iso8879-character-alist)))
   (cons "14"  (cdr (assoc "frac14" iso8879-character-alist)))
   (cons "15"  (cdr (assoc "frac15" iso8879-character-alist)))
   (cons "16"  (cdr (assoc "frac16" iso8879-character-alist)))
   (cons "18"  (cdr (assoc "frac18" iso8879-character-alist)))
   (cons "23"  (cdr (assoc "frac23" iso8879-character-alist)))
   (cons "25"  (cdr (assoc "frac25" iso8879-character-alist)))
   (cons "34"  (cdr (assoc "frac34" iso8879-character-alist)))
   (cons "35"  (cdr (assoc "frac35" iso8879-character-alist)))
   (cons "38"  (cdr (assoc "frac38" iso8879-character-alist)))
   (cons "45"  (cdr (assoc "frac45" iso8879-character-alist)))
   (cons "56"  (cdr (assoc "frac56" iso8879-character-alist)))
   (cons "58"  (cdr (assoc "frac58" iso8879-character-alist)))
   (cons "78"  (cdr (assoc "frac78" iso8879-character-alist)))
   (cons "<<"  (cdr (assoc "laquo"  iso8879-character-alist)))
   (cons ".."  (cdr (assoc "hellip" iso8879-character-alist)))
   (cons "!i"  (cdr (assoc "iexcl"  iso8879-character-alist)))
   (cons "?i"  (cdr (assoc "iquest" iso8879-character-alist)))
   (cons "  "  (cdr (assoc "nbsp"   iso8879-character-alist)))
   (cons "+-"  (cdr (assoc "plusmn" iso8879-character-alist)))
   (cons "--"  (cdr (assoc "mdash"  iso8879-character-alist)))
   (cons "$c"  (cdr (assoc "cent"   iso8879-character-alist)))
   (cons "$e"  (cdr (assoc "euro"   iso8879-character-alist)))
   (cons "$p"  (cdr (assoc "pound"  iso8879-character-alist)))
   (cons "$y"  (cdr (assoc "yen"    iso8879-character-alist))))
  "Defines a list of two-character shortcuts for keyboard entry of Unicode characters.")

(defun unicode-character-shortcut-insert ()
  "Read a (two-character) keyboard shortcut and insert the corresponding character."
  (interactive)
  (let* ((c1 (read-char))
	 (c2 (read-char))
	 (str (concat (char-to-string c1) (char-to-string c2))))
    (cond
     ((assoc str unicode-character-shortcut-alist)
      (xml-unicode-insert nil
			  (cdr (assoc str unicode-character-shortcut-alist))))
     (t (beep)))))

(defun show-unicode-character-list ()
  "Insert each Unicode character into a buffer. Let's you see which characters are available for literal display in your emacs font."
  (let ((chars unicode-character-list)
	char codept name)
    (while chars
      (setq char (car chars))
      (setq chars (cdr chars))
      (setq codept (car char))
      (setq name (cadr char))

      (if (< codept #xffff)
	  (progn
	    (insert (format "#x%06x " codept))
	    (ucs-insert codept)
	    (insert (format " %s\n" name)))))))

;; EOF
