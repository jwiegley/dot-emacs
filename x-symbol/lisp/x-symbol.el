;;; x-symbol.el --- semi WYSIWYG for LaTeX, HTML, etc using additional fonts

;; Copyright (C) 1995-2003 Free Software Foundation, Inc.
;;
;; Author: Christoph Wedler <wedler@users.sourceforge.net>
;; Maintainer: (Please use `M-x x-symbol-package-bug' to contact the maintainer)
;; Version: 4.4.X
;; Keywords: WYSIWYG, LaTeX, HTML, wp, math, internationalization
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

;; This is the main file of package X-Symbol.  It also defines charsets for the
;; basic fonts: latin1, latin2, latin3, latin5, xsymb0 and xsymb1.

;; This file does some initialization.  Thus, do not put any `defcustom'
;; commands into this file.  If you think some variables in this files should
;; be customized, move them to file `x-symbol-vars.el'.

;;; Code:

(provide 'x-symbol)
;;(require 'x-symbol-hooks)
(require 'x-symbol-vars)
(require (if (featurep 'mule) 'x-symbol-mule 'x-symbol-nomule))
(eval-when-compile (require 'x-symbol-macs))
(eval-when-compile (require 'cl))

(eval-when-compile
  (defvar font-lock-extra-managed-props) ; font-lock of Emacs-21.4
  (defvar reporter-prompt-for-summary-p))

;; CW: TODO
(defvar x-symbol-trace-invisible nil)
;; shows that invisible is reset but Emacs still shows it as invisible




;;;;##########################################################################
;;;;  General code, default values for `x-symbol-*-function'
;;;;##########################################################################


;;;===========================================================================
;;;  Token languages
;;;===========================================================================

(defconst x-symbol-language-access-alist
  `((x-symbol-auto-style "auto-style" t listp) ; redefinition, TODO: optional is just temporary
    (x-symbol-modeline-name "modeline-name" nil stringp)
    (x-symbol-required-fonts "required-fonts" t listp)
    (x-symbol-token-grammar "token-grammar" nil
			    ,(lambda (x)
			       (or (vectorp x)
				   (eq (car-safe x) 'x-symbol-make-grammar))))
    (x-symbol-input-token-grammar "input-token-grammar" nil consp)
    (x-symbol-table "table" nil consp)
    (x-symbol-generated-data "generated-data" nil null)
    ;; input methods
    (x-symbol-header-groups-alist "header-groups-alist" nil listp)
    (x-symbol-class-alist "class-alist" nil listp)
    (x-symbol-class-face-alist "class-face-alist" t listp)
    (x-symbol-electric-ignore "electric-ignore")
    (x-symbol-extra-menu-items "extra-menu-items" t listp)
    ;; super-/subscripts, images
    (x-symbol-subscript-matcher "subscript-matcher" t)
    (x-symbol-image-keywords "image-keywords" t listp)
    (x-symbol-master-directory "master-directory" x-symbol-image-keywords
			       functionp)
    (x-symbol-image-searchpath "image-searchpath" x-symbol-image-keywords
			       listp)
    (x-symbol-image-cached-dirs "image-cached-dirs" x-symbol-image-keywords
				listp))
  "Alist of token language dependent variable accesses.
Each element looks like (ACCESS . SUFFIX) or (ACCESS MULE . NOMULE).
With the first form, the symbol of the LANGUAGE dependent variable is
`FEATURE-SUFFIX' where FEATURE is the value of LANGUAGE's symbol
property `x-symbol-feature'.  With the second form, the symbol is
`FEATURE-MULE' when running under XEmacs/Mule or `FEATURE-NOMULE' when
running under XEmacs/no-Mule.  The symbol is stored as LANGUAGE's
property ACCESS.  To get a value of a language dependent variable, use
`x-symbol-language-value'.

The following language dependent access is defined after the language
has been registered, see `x-symbol-register-language':

 * `x-symbol-name': String naming the language when presented to the user.

The following language dependent accesses are defined after the language
has been initialized, see `x-symbol-init-language':

 * `x-symbol-modeline-name': String naming the language in the modeline.
 * `x-symbol-master-directory': Function returning the directory of the
   master file, see `x-symbol-image-parse-buffer'.
 * `x-symbol-image-searchpath': Search path used for implicitly relative
   image file names, see `x-symbol-image-use-remote'.
 * `x-symbol-image-cached-dirs': Directory parts of image file names
   stored in the memory cache, see `x-symbol-image-use-remote'.
 * `x-symbol-image-keywords': Keywords used to find image insertion
   commands, see `x-symbol-image-parse-buffer'.
 * `x-symbol-font-lock-keywords': font-lock keywords for super- and
   subscripts.

 * `x-symbol-header-groups-alist': If non-nil, used instead
   `x-symbol-header-groups-alist' in the language specific grid/menu.
 * `x-symbol-class-alist': Alist used for the info in the echo area, see
   `x-symbol-character-info'.  Each element looks like (CLASS . SPEC)
   where CLASS is a valid token class, see `x-symbol-init-language' and
   SPEC is used according to `x-symbol-fancy-string'.  You should define
   entries for the CLASSes `VALID' and `INVALID'.
 * `x-symbol-class-face-alist': Alist used for the color scheme in the
   language dependent grid and token info.  Each element looks like
   (CLASS FACE . FACE-SPECS) where CLASS is a valid token class, FACE is
   used for the character in the grid, and FACE-SPECS is used according
   to `x-symbol-fancy-string'.
 * `x-symbol-electric-ignore': Language dependent version of
   `x-symbol-electric-ignore', see variable `x-symbol-electric-input'.

 * `x-symbol-required-fonts': Features providing fonts.
 * `x-symbol-case-insensitive': If non-nil, tokens are case-insensitive.
   The non-nil value should be a function: `upcase' or `downcase'.
 * `x-symbol-token-shape': Used to (conditionally) prevent decoding
   tokens of the given shape.  Looks like
      (TOKEN-ESC TOKEN-REGEXP . LETTER-REGEXP)
   If TOKEN-ESC is non-nil, a token is not decoded if the character
   before token is TOKEN-ESC, TOKEN-ESC is allowed to appear exactly
   even times, though.  If non-nil, TOKEN-REGEXP matches tokens not to
   be decoded if LETTER-REGEXP matches the character after the token.
 * `x-symbol-table': Table defining the language, includes user table.
 * `x-symbol-token-list': The token specification in language tables are
   passed to this function, see `x-symbol-init-language'.
 * `x-symbol-input-token-ignore': Regexp or function used to \"hide\"
   some tokens from input method TOKEN.
 * `x-symbol-exec-specs': Specification used when building executables,
   t if no executables should be built, see `x-symbol-exec-create'.

The following internal language dependent accesses are defined after the
language has been initialized, see `x-symbol-init-language':

 * `x-symbol-menu-alist': Alist used for language dependent menu.
 * `x-symbol-grid-alist': Alist used for language dependent grid.
 * `x-symbol-decode-atree': Atree for used by `x-symbol-token-input'.
 * `x-symbol-decode-alist': Alist used during decoding.
 * `x-symbol-encode-alist': Alist used during encoding.
 * `x-symbol-decode-exec': File name of decode executable.  If this
   access is not present, no warning is issued, as opposed to value nil.
 * `x-symbol-encode-exec': File name of encode executable.  If this
   access is not present, no warning is issued, as opposed to value nil.")


;;;===========================================================================
;;;  Structure data types
;;;===========================================================================

(defstruct (x-symbol-generated (:type vector)
			       (:constructor x-symbol-make-generated-data)
			       (:copier nil))
  encode-table
  decode-obarray
  menu-alist
  grid-alist
  token-classes
  max-token-len)

(defstruct (x-symbol-grammar (:type vector)
			     (:constructor x-symbol-make-grammar)
			     (:copier nil))
  case-function
  encode-spec
  decode-regexp
  decode-spec
  token-list
  after-init)


;;;===========================================================================
;;;  Internal variables used throughout the package
;;;===========================================================================

(defvar x-symbol-map nil
  "Keymap for x-symbol key sequences starting with \\[x-symbol-map].
Set by `x-symbol-init-input'.")

(defvar x-symbol-unalias-alist nil
  "Internal.  Alist used to resolve character aliases.
See `x-symbol-unalias'.")

(defvar x-symbol-latin-decode-alists nil
  "Internal.  Alist used during decoding to handle different file codings.
Used if `x-symbol-coding' differs from `x-symbol-default-coding'.")

(defvar x-symbol-context-atree nil
  "Internal.  Atree used by input method context.
See `x-symbol-modify-key'.")

(defvar x-symbol-electric-atree nil
  "Internal.  Atree used by `x-symbol-electric-input'.")

(defvar x-symbol-grid-alist nil
  "Internal.  Alist containing the global grid.")

(defvar x-symbol-menu-alist nil
  "Internal.  Alist containing the global submenus for insert commands.")

(defvar x-symbol-all-charsyms nil
  "Internal.  List of all defined charsyms in order of definition.
Symbol property `x-symbol-decode-alist' is a cache {symbol-name->symbol}
used by `x-symbol-read-token'.")

(defvar x-symbol-fancy-value-cache nil
  "Internal.  Cache for `x-symbol-fancy-value'.")

;; encoding -> charsym-for-char-in-encoding-cset -> char-in-default-cset
(defvar x-symbol-fchar-tables nil)

;; encoding -> charsym-for-char-in-encoding-cset -> char-in-encoding-cset (string in nomule)
(defvar x-symbol-bchar-tables nil)

(defvar x-symbol-cstring-table nil)

(defvar x-symbol-fontified-cstring-table nil)

(defvar x-symbol-charsym-decode-obarray nil)


;;;===========================================================================
;;;  General functions
;;;===========================================================================

(defun x-symbol-set-variable (var value)
  "Set VAR's value to VALUE, using special set functions.
If VAR has a symbol property `x-symbol-set-function', use that function
instead `set' to set the value.  At the end, run each hook in the symbol
property `x-symbol-after-set-hook' of VAR."
  (if (get var 'x-symbol-set-function)
      (funcall (get var 'x-symbol-set-function) var value)
    (if (and (get var 'custom-type)
	     (null (local-variable-if-set-p var (current-buffer))))
	(customize-set-variable var value)
      (set var value)))
  (let ((hook (get var 'x-symbol-after-set-hook)))
    (while hook (funcall (pop hook)))))

(defun x-symbol-ensure-hashtable (symbol)
  "Make sure that SYMBOL's value is a hashtable.
The initial size of the key-weak hashtable is `x-symbol-cache-size'."
  (or (hash-table-p (symbol-value symbol))
      (set symbol (make-hash-table :size x-symbol-cache-size
				   :test 'eq :weakness 'key))))

(defun x-symbol-puthash (key val hashtable)
  "Hash KEY to VAL in HASHTABLE.  Return VAL.
Flush HASHTABLE, i.e., delete all entries before, if number of entries
would become larger than `x-symbol-cache-size'."
  (if (>= (hash-table-count hashtable) x-symbol-cache-size)
      (clrhash hashtable))
  (puthash key val hashtable))

(defun x-symbol-call-function-or-regexp (callee string &rest args)
  "Check STRING by calling function or matching a regexp.
If CALLEE is a function, call function with first argument STRING and
rest ARGS.  If it is a string, return index of start of first match for
CALLEE in STRING."
  (if (stringp callee)
      (string-match callee string)
    (if (fboundp callee) (apply callee string args))))

(defun x-symbol-match-in-alist (elem alist &optional result replacep)
  "Check ALIST for element whose car is a regexp matching elem.
Return cdr of matching element or RESULT if the cdr is nil.  If REPLACEP
is non-nil and the cdr is a string, replace text matched by the car with
the cdr and return result, see `replace-match' for details.  If REPLACEP
is non-nil and the cdr is a non-empty list, call the car of the cdr with
ELEM and the remaining arguments in the cdr of the cdr to get the
result."
  (let (match)
    (while alist
      (if (string-match (caar alist) elem)
	  (setq result (cdar alist)
		match t
		alist nil)
	(setq alist (cdr alist))))
    (if (and replacep match)
	(cond ((stringp result) (replace-match result t nil elem))
	      ((consp result) (apply (car result) elem (cdr result)))
	      (t result))
      result)))


;;;===========================================================================
;;;  Strings with properties (inclusive. caching)
;;;===========================================================================
;; both Emacs and XEmacs fail with properties & `format': XEmacs drops the
;; properties, Emacs does it wrong, i.e., keeps the original positions in the
;; format string

(defun x-symbol-fancy-string (spec)
  "Return a \"fancy\" string according to SPEC.
SPEC has the form (STRING FACE-SPEC...).  Return a copy of STRING
annotated with faces as duplicatable text properties.  FACE-SPEC has the
form ([START [END]] FACE...).  All characters between START and END are
attached with FACEs.  START and END can be positive numbers, denoting
string positions, negative numbers, denoting positions from the end, and
default to 0 or the end of the string, respectively."
  (if (cdr spec)
      (let* ((string (copy-sequence (pop spec)))
	     (len (length string))
	     faces start end)
	(while spec
	  (setq faces (pop spec))
	  (setq start (if (numberp (car faces)) (pop faces) 0)
		end (if (numberp (car faces)) (pop faces) len))
	  (put-text-property (if (natnump start) start (+ len start))
			     (if (natnump end) end (+ len end))
			     'face faces string))
	string)
    (car spec)))

(defun x-symbol-fancy-value (symbol &optional string-fn)
  "Return the \"fancy\" value of variable SYMBOL.
If the value is not cached in SYMBOL's property `x-symbol-fancy-value',
pass SYMBOL's value SPEC to `x-symbol-fancy-string', caching the result.
If STRING-FN is non-nil, the STRING part of SPEC is passed to function
STRING-FN before."
  (or (hash-table-p x-symbol-fancy-value-cache)
      (setq x-symbol-fancy-value-cache
	    (make-hash-table :size x-symbol-fancy-cache-size :test 'eq)))
  (or (gethash symbol x-symbol-fancy-value-cache)
      (puthash symbol
	       (let ((spec (symbol-value symbol)))
		 (x-symbol-fancy-string
		  (if string-fn
		      (cons (funcall string-fn (car spec)) (cdr spec))
		    spec)))
	       x-symbol-fancy-value-cache)))


(defun x-symbol-fancy-associations (symbols spec-alist pre sep post
					    &optional default)
  "Return all \"fancy\" associations for SYMBOLS in SPEC-ALIST.
SPEC-ALIST should have elements which look like (SYMBOL . SPEC).
Collect all SPECs whose SYMBOL is a element in SYMBOLS or is equal to
DEFAULT when no SPEC can be collected.

If SPECs is nil, concat the fancy value of PRE with all fancy strings of
SPECs separated by the fancy value of SEP, and the fancy value of POST,
see `x-symbol-fancy-string' and `x-symbol-fancy-value'."
  (let (spec result)
    (while symbols
      (and (setq spec (cdr (assq (pop symbols) spec-alist)))
	   (push spec result)))
    (and (null result)
	 (setq spec (cdr (assq default spec-alist)))
	 (setq result (list spec)))
    (when result
      (concat (x-symbol-fancy-value pre)
	      (mapconcat 'x-symbol-fancy-string
			 (nreverse result)
			 (x-symbol-fancy-value sep))
	      (x-symbol-fancy-value post)))))


;;;===========================================================================
;;;  Tiny x-symbol specific functions
;;;===========================================================================

(defun x-symbol-language-value (access &optional language)
  "Return value of language dependent variable accessed by ACCESS.
LANGUAGE defaults to `x-symbol-language'.  If necessary, load file
providing the token language and initialize language.  For supported
accesses, see `x-symbol-language-access-alist'."
  (or language (setq language x-symbol-language))
  (let ((symbol (get language access)))
    (if symbol (symbol-value symbol)
      (and language
	   (null (get language 'x-symbol-initialized))
	   (or (x-symbol-init-language language)
	       (warn "Illegal X-Symbol token language `%s'" language))
	   (symbol-value (get language access))))))

(defun x-symbol-charsym-face (charsym language)
  "Return face and face specs for CHARSYM in LANGUAGE.
The returned value is (FACE . FACE-SPECS) where FACE is used for the
grid and FACE-SPECS for the token in the info.  For the format of
FACE-SPECS, see `x-symbol-fancy-string'.  The value depends on the first
token class and the language access `x-symbol-class-face-alist'."
  (cdr (assq (car (gethash charsym
			   (x-symbol-generated-token-classes
			    (x-symbol-language-value
			     'x-symbol-generated-data language))))
	     (x-symbol-language-value 'x-symbol-class-face-alist language))))

(defun x-symbol-image-available-p ()
  "Non-nil, if `x-symbol-image' can be set in current file."
  (and (x-symbol-language-value 'x-symbol-image-keywords)
       (null (file-remote-p default-directory))))

(defun x-symbol-default-context-info-ignore (context charsym)
  "Non-nil, if no info in the echo area should be shown for CONTEXT.
The CONTEXT would be modified to the character represented by CHARSYM.
Return non-nil, if the group of CHARSYM is a member of
`x-symbol-context-info-ignore-groups' or the context is shorter than
`x-symbol-context-info-threshold' or the context is matched by
`x-symbol-context-info-ignore-regexp'.  This function is the default
value for `x-symbol-context-info-ignore'."
  (or (memq (car (get charsym 'x-symbol-grouping))
	    x-symbol-context-info-ignore-groups)
      (< (length context) x-symbol-context-info-threshold)
      (and x-symbol-context-info-ignore-regexp
	   (string-match x-symbol-context-info-ignore-regexp context))))

(defun x-symbol-default-info-keys-keymaps (&optional dummy)
  ;; checkdoc-params: (dummy)
  "Used in keys info for not showing the prefix \\[x-symbol-map].
Used as the default value for `x-symbol-info-keys-keymaps'."
  ;; probably just `x-symbol-map' with Emacs-20.4
  (list x-symbol-map))


;;;===========================================================================
;;;  Get Valid charsyms
;;;===========================================================================

(defun x-symbol-alias-charsym (pos+charsym)
  "Charsym of character alist, nil for other characters.
If the character after the `car' of POS+CHARSYM is a character alias,
return the `cdr' of POS+CHARSYM."
  (and (car pos+charsym)
       (not (eq (char-after (car pos+charsym))
		(aref (gethash (cdr pos+charsym) x-symbol-cstring-table) 0)))
       (cdr pos+charsym)))

(defun x-symbol-default-valid-charsym (charsym &optional language)
  "Non-nil, if CHARSYM is valid in LANGUAGE.
If LANGUAGE is non-nil or `x-symbol-mode' is on, CHARSYM must represent
a token in LANGUAGE which defaults to `x-symbol-language'.  Otherwise,
it should be a 8bit character according to `x-symbol-coding'.
If LANGUAGE is non-nil, the result looks like (TOKEN . MISC)."
  (if (or language (and x-symbol-mode x-symbol-language))
      (and (or language
	       (null x-symbol-coding)	; default coding
	       (assq x-symbol-coding x-symbol-fchar-tables) ; valid coding
	       (not (gethash charsym	; not a 8bit char in default coding
			     (cdr (assq (x-symbol-buffer-coding)
					x-symbol-fchar-tables)))))
	   (gethash charsym (x-symbol-generated-encode-table
			     (x-symbol-language-value
			      'x-symbol-generated-data
			      (or language x-symbol-language)))))
    (gethash charsym (cdr (assq (or (x-symbol-buffer-coding)
				    x-symbol-default-coding
				    'iso-8859-1)
				x-symbol-fchar-tables)))))

(defun x-symbol-next-valid-charsym (charsym direction &optional prop tried)
  "Return a valid charsym starting with CHARSYM.
Try CHARSYM first, if it is not valid, use CHARSYM's property PROP.  If
DIRECTION is not t, charsym must have a rotate aspect direction with
value DIRECTION.  Do not try to use charsyms in TRIED.  See
`x-symbol-valid-charsym-function'."
  (let ((line (and (consp charsym) (prog1 (cdr charsym)
				     (setq charsym (car charsym))))))
    (while (and charsym
		(if (memq charsym tried)
		    (setq charsym nil)
		  (push charsym tried))
		(not (and (gethash charsym x-symbol-cstring-table) ; CW: nec?
			  (funcall x-symbol-valid-charsym-function charsym)
			  (or (eq direction t)
			      (eq (plist-get
				   (cdr (get charsym 'x-symbol-rotate-aspects))
				   'direction)
				  direction)))))
      (if line
	  (setq charsym (car line)
		line (cdr line))
	(if (consp (setq charsym (get charsym prop)))
	    (setq line (cdr charsym)
		  charsym (car charsym)))))
    charsym))

(defun x-symbol-valid-context-charsym (atree &optional prop)
  "Return first valid charsym for longest context match before point.
Return (START . CHARSYM) where the buffer substring between START and
point is the key to the association VALUE in ATREE, see also
`x-symbol-match-before'.  CHARSYM is the VALUE or the next valid charsym
using PROP, see `x-symbol-next-valid-charsym'."
  (let* ((pos+charsym (x-symbol-match-before atree (point)))
	 (charsym (and (cdr pos+charsym)
		       (x-symbol-next-valid-charsym (cdr pos+charsym) t prop))))
    (and charsym (cons (car pos+charsym) charsym))))

(defun x-symbol-next-valid-charsym-before (prop1 prop2)
  "Return next valid charsym for character before point.
Return (POS . CHARSYM) where POS is usually the point position.  If
character is an character alias, resolve it.  Otherwise, try chain
according to PROP1, then use the OPPOSITE of the character, see
`x-symbol-init-cset', then try chain according to PROP2."
  (let* ((pos+charsym (x-symbol-charsym-after (1- (point))))
	 (charsym (cdr pos+charsym)))
    (and charsym
	 (setq charsym (or (x-symbol-alias-charsym pos+charsym)
			   (x-symbol-next-valid-charsym
			    (get charsym prop1) t prop1 (list charsym))
			   (x-symbol-next-valid-charsym
			    (caddr (get charsym 'x-symbol-grouping)) t
			    'x-symbol-modify-to (list charsym))
			   (x-symbol-next-valid-charsym
			    (get charsym prop2) t prop2 (list charsym))))
	 (cons (car pos+charsym) charsym))))


;;;===========================================================================
;;;  Text functions
;;;===========================================================================

(defun x-symbol-prefix-arg-texts (arg)
  "Return texts for prefix argument ARG."
  (if (consp arg)
      '("token" . "once")
    (cons (if (natnump (setq arg (prefix-numeric-value arg)))
	      "valid character"
	    "character")
	  (if (= (abs arg) 1) "once" (format "%d times" (abs arg))))))

(defun x-symbol-region-text (&optional long)
  "Return \"Region\", \"Buffer\" or \"Narrowed Part\".
When non-nil, use format string FORMAT."
  (cond ((region-active-p) "Region")
	((and (= (point-min) 1) (= (point-max) (1+ (buffer-size))))
	 "Buffer")
	(long "Buffer/narrowed")
	(t "Buffer/n")))

(defun x-symbol-language-text (&optional format language)
  "Return text for LANGUAGE, to be presented to the user.
LANGUAGE defaults to `x-symbol-language'.  If LANGUAGE is nil, return
`x-symbol-charsym-name'.  When non-nil, use format string FORMAT."
  (let ((text (or (x-symbol-language-value 'x-symbol-name language)
		  x-symbol-charsym-name)))
    (if format (format format text) text)))

(defun x-symbol-coding-text (coding &optional coding2 format)
  "Return text for coding, to be presented to the user.
Use association in `x-symbol-coding-name-alist' if `x-symbol-8bits' is
non-nil, \"Ascii\" otherwise.  If both CODING1 and CODING2 are provided
use format FORMAT with the associations for CODING1 and CODING2,
otherwise just return text for CODING1."
  (if format
      (if (or (null (and coding coding2)) (eq coding coding2))
	  ""
	(format format
		(x-symbol-coding-text coding)
		(x-symbol-coding-text coding2)))
    (or (cdr (assq (or coding (x-symbol-buffer-coding))
		   x-symbol-coding-name-alist))
	"Ascii")))

;;;(defvar x-symbol-unsupported-coding-modeline-alist nil)

(defun x-symbol-language-modeline-text (language)
  "Return text for LANGUAGE, to be presented in the modeline."
  (or (and (setq language (and (boundp language) (symbol-value language)))
	   (x-symbol-language-value 'x-symbol-modeline-name))
      x-symbol-modeline-name))

(defun x-symbol-coding-modeline-text (coding)
  "Return text for symbol value of CODING, to be used in the modeline.
Use association in `x-symbol-coding-modeline-alist' if value of CODING
differs from `x-symbol-default-coding', \"\" otherwise."
  (setq coding (and (boundp coding) (symbol-value coding)))
  (let ((buffer-coding (x-symbol-buffer-coding)))
    (cdr (assq (cond ((null buffer-coding)
		      (if x-symbol-8bits 'error (if coding 'info 'none)))
		     ((or (null coding) (eq coding buffer-coding))
		      (if (eq buffer-coding x-symbol-default-coding)
			  'same
			buffer-coding))
		     ((and (eq buffer-coding x-symbol-default-coding)
			   (assq coding x-symbol-fchar-tables))
		      coding)
		     (t
		      (if x-symbol-8bits 'error 'info)))
	       x-symbol-coding-modeline-alist))))
;;;  (and (setq coding (and (boundp coding) (symbol-value coding)))
;;;       (null (eq coding x-symbol-default-coding))
;;;       (let ((string (cdr (assq coding x-symbol-coding-modeline-alist))))
;;;	 (if (assq coding x-symbol-fchar-tables)
;;;	     string
;;;	   (format x-symbol-coding-modeline-warning-format (or string ""))))))

;;;       (let ((string (assq coding x-symbol-coding-modeline-alist)))
;;;	 (if (assq coding x-symbol-fchar-tables)
;;;	     (cdr string)
;;;	   (or string (setq coding 'error))
;;;	   (or (cdr (assq coding x-symbol-unsupported-coding-modeline-alist))
;;;	       (let ((fstring (copy-sequence
;;;			       (or (cdr (assq coding
;;;					      x-symbol-coding-modeline-alist))
;;;				   "-err"))))
;;;		 (put-text-property 0 (length fstring)
;;;				    'face 'x-symbol-modeline-warning-face
;;;				    fstring)
;;;		 (push (cons coding fstring)
;;;		       x-symbol-unsupported-coding-modeline-alist)
;;;		 fstring))))))


;;;===========================================================================
;;;  reftex support (could be useful otherwise, too)
;;;===========================================================================

;;;###autoload
(defun x-symbol-translate-to-ascii (string)
  "Translate STRING to an ascii string.
Non-ascii characters in STRING are converted to charsyms.  Their ascii
representation is determined by:

 * If CHARSYM is a key in `x-symbol-charsym-ascii-alist', use its ASCII.
 * Charsym is defined in the table to have an ascii representation, see
   ASCII in `x-symbol-init-cset'.
 * Compute ascii representation according to the CHARSYM's GROUP,
   SUBGROUP and `x-symbol-charsym-ascii-groups'.
 * Use \"\" otherwise."
  (mapconcat (lambda (item)
	       (if (characterp item)
		   (char-to-string item)
		 (let ((grouping (get item 'x-symbol-grouping)))
		   (or (cdr (assq item x-symbol-charsym-ascii-alist))
		       (cadddr grouping)
		       (and (memq (car grouping)
				  x-symbol-charsym-ascii-groups)
			    (cadr grouping))))))
	     (x-symbol-string-to-charsyms string)
	     ""))


;;;===========================================================================
;;;  Key bindings
;;;===========================================================================


;;;===========================================================================
;;;  Package info / bug report
;;;===========================================================================

;;;###autoload
(defun x-symbol-package-web ()
  "Ask a WWW browser to load URL `x-symbol-package-url'."
  (interactive)
  (browse-url x-symbol-package-url)
  (message "Sent URL of package x-symbol to your web browser"))

;;;###autoload
(defun x-symbol-package-info ()
  "Read documentation for package X-Symbol in the info system."
  (interactive)
  (Info-goto-node "(x-symbol)"))

;;;###autoload
(defun x-symbol-package-bug (&optional arg)
  "Send a bug/problem report to the maintainer of package X-Symbol.
Please try to contact person in `x-symbol-installer-address' first.
Normal reports are sent without prefix argument ARG.

If you are sure that the problem cannot be solved locally, e.g., by
contacting the person who has installed package X-Symbol, use prefix
argument 2 to send the message to `x-symbol-maintainer-address'.

If your message has nothing to do with a problem or a bug, use prefix 9
to send a short message to `x-symbol-maintainer-address'."
  (interactive "p")
  (or (= arg 9)
      (condition-case nil
	  (progn (Info-goto-node "(x-symbol)Bug Reports") t)
	(error (setq arg 1) x-symbol-installer-address))
      (with-output-to-temp-buffer "*Help*"
	(beep)
	(set-buffer "*Help*")
	(princ "\
The info files for package X-Symbol are not installed.

Please read the manual before contacting the maintainer of package
X-Symbol.  If you want to send a bug/problem report or a question,
please follow the instructions in the manual.

The manual is also available as an HTML document at the web page of
package X-Symbol:
   ")
	(princ x-symbol-package-url)
	nil)
      (null (y-or-n-p "Send URL of package X-Symbol to your web browser? "))
      (x-symbol-package-web))
  (require 'reporter)
  (let ((reporter-prompt-for-summary-p t)) ;# dynamic
    ;; For some reasons, the package version in the subject line, which I
    ;; definitely want, is only inserted with value t.  Thus, I ignore user
    ;; wishes here.
    (reporter-submit-bug-report
     (or (unless (or (= arg 9) (= arg 2)) x-symbol-installer-address)
	 x-symbol-maintainer-address)
     (concat "x-symbol " x-symbol-version)
     (unless (= arg 9)
       `(command-line-args x-symbol-auto-style-alist
			   x-symbol-default-coding
			   x-symbol-image-converter
			   ,@(and (featurep 'x-symbol-nomule)
				  '(x-symbol-nomule-leading-faces-alist))
			   features)))))

;;;###autoload
(defun x-symbol-package-reply-to-report ()
  "Reply to a bug/problem report not using \\[x-symbol-package-bug]."
  (interactive)
  (insert "\
Thank you for trying package X-Symbol.  If you have problems, please use
`M-x x-symbol-package-bug' to contact the maintainer.  Do not assume
that I remember the contents of your message (appended to this reply)...
er, I have actually deleted it.")
  (goto-char (point-max))
  (when (get-buffer " *gnus article copy*")
    (newline)
    (insert-buffer " *gnus article copy*")))



;;;;##########################################################################
;;;;  Conversion, Minor Mode Control, Menu
;;;;##########################################################################


(defvar x-symbol-encode-rchars 1
  "Internal variable.  Is always 1 with Mule support, 1 or 2 without.")


;;;===========================================================================
;;;  Conversion
;;;===========================================================================

(defun x-symbol-even-escapes-before-p (pos esc)
  (let ((even t))
    (while (eq (char-before pos) esc)
      (setq even (not even)
	    pos (1- pos)))
    even))

;;;###autoload
(defun x-symbol-decode-region (beg end)
  "Decode all tokens between BEG and END.
Make sure that X-Symbol characters are correctly displayed under
XEmacs/no-Mule even when font-lock is disabled."
  (save-restriction
    (narrow-to-region beg end)
    (x-symbol-decode-all)
    ;; Is the following really necessary?  Anyway, it doesn't hurt...
    (unless (featurep 'mule) (x-symbol-nomule-fontify-cstrings))
    ))

;;;###autoload
(defun x-symbol-decode-all ()
  "Decode all tokens in buffer to characters.
Use executables for decoding if buffer is larger than EXEC-THRESHOLD
which defaults to `x-symbol-exec-threshold'.  Before decoding, decode
8bit characters in CODING which defaults to `x-symbol-coding'."
  ;; Assumptions: ------------------------------------------------------------
  ;;  * Latin decode alists are ordered, see `x-symbol-init-latin-decoding'
  ;;  * No part of the association is a KEY in the conversion alists
  ;;  * Keys in conversion alists are ordered: long...short
  (let* ((grammar (x-symbol-language-value 'x-symbol-token-grammar))
	 (decode-obarray (if x-symbol-language
			     (x-symbol-generated-decode-obarray
			      (x-symbol-language-value
			       'x-symbol-generated-data))))
	 (buffer-coding (x-symbol-buffer-coding))
	 (unique (and x-symbol-unique t)))
    ;; TODO: recheck.  Decode uniquely and do not decode to 8bit if current
    ;; coding is unknown, otherwise we would wrongly use the same char for a
    ;; token and an 8bit char in the file.  E.g., with latin1 as default and we
    ;; visit a tex file with latin9 encoding where both the euro character and
    ;; \textcurrency is used.  If you use XEmacs on Windows, there is no latin9
    ;; font and therefore no recoding would take place, i.e., you would see the
    ;; euro character as the currency character (as you would w/o X-Symbol).
    ;; But then it would be very bad if \textcurrency would be decoded to the
    ;; currency character.
    (when buffer-coding
      (let ((fchar-table (assq (or x-symbol-coding buffer-coding)
			       x-symbol-fchar-tables)))
	(if (eq buffer-coding x-symbol-default-coding)
	    (let* ((case-fold-search nil)	;#dynamic
		   (coding-alist (cdr (assq x-symbol-coding x-symbol-latin-decode-alists)))
		   from to)
	      (while coding-alist
		(setq from (caar coding-alist)
		      to   (cdar coding-alist)
		      coding-alist (cdr coding-alist))
		(goto-char (point-min))
		(while (search-forward from nil 'limit)
		  (replace-match to t t))))
	  ;; TODO: unalias only with 8bit would be faster, but if done
	  ;; interactively?
	  (x-symbol-unalias nil nil buffer-coding)
	  (or (null x-symbol-coding) (eq x-symbol-coding buffer-coding)
	      (setq fchar-table nil)))
	(setq unique (if x-symbol-8bits
			 (if fchar-table
			     (and x-symbol-unique (cdr fchar-table))
			   ;; invalid coding w/ 8bit => unique
			   (cdr (assq buffer-coding x-symbol-fchar-tables)))
		       (and x-symbol-unique t)))))
    ;; the real decoding -----------------------------------------------------
    (when decode-obarray
      (let ((case-fold-search (x-symbol-grammar-case-function
			       grammar)) ;#dynamic
	    (decode-spec (x-symbol-grammar-decode-spec grammar))
	    (decode-regexp (x-symbol-grammar-decode-regexp grammar)))
	(goto-char (point-min))
	(if (functionp decode-spec)
	    (funcall decode-spec decode-regexp decode-obarray unique)
	  (x-symbol-decode-lisp decode-spec decode-regexp decode-obarray
				unique))))))

;;;###autoload
(defun x-symbol-decode-single-token (string)
  (when x-symbol-language
    (let ((token (symbol-value
		  (intern-soft string
			       (x-symbol-generated-decode-obarray
				(x-symbol-language-value
				 'x-symbol-generated-data))))))
      (if token (gethash (car token) x-symbol-cstring-table)))))

(defun x-symbol-decode-lisp (contexts decode-regexp decode-obarray unique)
  (let ((case-fn (if (functionp case-fold-search) case-fold-search))
	(before-context (car contexts))
	(after-context (cdr contexts))
	charsym esc-char shape bad-regexp)
    (when (characterp before-context)
      (or (memq before-context '(?\ ?\t ?\n ?\r nil)) ; or warning?
	  (setq esc-char before-context))
      (setq before-context nil))
    (or before-context after-context (setq contexts nil))
    ;; -----------------------------------------------------------------------
    (x-symbol-decode-for-charsym ((decode-regexp decode-obarray case-fn)
				  token beg end)
	nil
      (cond ((x-symbol-decode-unique-test token unique))
	    ((and esc-char (eq (char-before beg) esc-char)
		  (x-symbol-even-escapes-before-p (1- beg) esc-char)))
	    ((not (and contexts (setq shape (cadr token))))
	     (if (setq charsym (car token))
		 (replace-match (gethash charsym x-symbol-cstring-table) t t)))
	    ((and (setq bad-regexp (assq shape after-context))
		  (not (memq (char-after) '(?\ ?\t ?\n ?\r nil)))
		  (looking-at (cdr bad-regexp))))
	    ((and (setq bad-regexp (assq shape before-context))
		  (not (memq (char-before beg) '(?\ ?\t ?\n ?\r nil)))
		  (string-match (cdr bad-regexp)
				(char-to-string (char-before beg)))))
	    ((setq charsym (car token))
	     (insert-before-markers (gethash charsym x-symbol-cstring-table))
	     (delete-region beg end))))))

;;;###autoload
(defun x-symbol-encode-all (&optional buffer start end)
  "Encode all characters in buffer to tokens.
Use executables for decoding if buffer is larger than EXEC-THRESHOLD
which defaults to `x-symbol-exec-threshold'.  If CODING is non-nil, do
not encode 8bit characters in CODING.  Otherwise, do not encode 8bit
characters in `x-symbol-coding' or `x-symbol-default-coding' if
`x-symbol-8bits' is non-nil.  If BUFFER is non-nil, copy contexts
between START and END to BUFFER, make BUFFER current and do conversion
there.  If BUFFER is non-nil, START and END must be buffer positions or
START is a string, see kludgy feature of `write-region'."
  (let ((grammar (x-symbol-language-value 'x-symbol-token-grammar))
	(encode-table (x-symbol-generated-encode-table
		       (x-symbol-language-value
			'x-symbol-generated-data)))
	(buffer-coding (x-symbol-buffer-coding))
	(coding (if x-symbol-coding
		    (if (assq x-symbol-coding x-symbol-fchar-tables)
			x-symbol-coding
		      t)))
	(store8 x-symbol-8bits))
    (if buffer
	(if start
	    (let ((curr-buffer (current-buffer)))
	      (if (featurep 'mule)
		  (let ((coding-system buffer-file-coding-system))
		    (set-buffer buffer)
		    (setq buffer-file-coding-system coding-system))
		(set-buffer buffer))
	      (x-symbol-set-buffer-multibyte)
	      (if write-region-annotations-so-far
		  (format-insert-annotations write-region-annotations-so-far
					     start))
	      (if (stringp start)
		  (insert start)	; kludgy feature of `write-region'
		(insert-buffer-substring curr-buffer start end))
	      ;;(set-text-properties (point-min) (point-max) nil)
	      (map-extents (lambda (e dummy) (delete-extent e) nil)))
	  (if (featurep 'mule)		; TODO: should be done by format.el
	      (let ((coding-system buffer-file-coding-system))
		(set-buffer buffer)
		(setq buffer-file-coding-system coding-system))
	    (set-buffer buffer))))
    ;;    (set-buffer buffer)))
    ;; format.el should now set multibyte itself, we'll see
    ;;    (x-symbol-set-buffer-multibyte)))
    ;; the encoding ----------------------------------------------------------
    (let* ((case-fold-search (x-symbol-grammar-case-function grammar)) ;#dynamic
	   (encode-spec (x-symbol-grammar-encode-spec grammar))
	   (fchar-fb-table (cdr (if buffer-coding
				    (if (eq buffer-coding x-symbol-default-coding) ; should always be the case for non-mule
					(or (assq coding x-symbol-fchar-tables) ; valid specified coding
					    (assq buffer-coding x-symbol-fchar-tables)) ; invalid coding or not specified
				      (assq buffer-coding x-symbol-bchar-tables))
				  (assq (or x-symbol-default-coding 'iso-8859-1)
					x-symbol-fchar-tables))))
	   (fchar-table (if store8 fchar-fb-table)))
      (goto-char (point-min))
      (if (functionp encode-spec)
	  (funcall encode-spec encode-table fchar-table fchar-fb-table)
	(x-symbol-encode-lisp encode-spec encode-table
			      fchar-table fchar-fb-table)))))

(defun x-symbol-encode-lisp (contexts encode-table fchar-table fchar-fb-table)
  (let ((before-context (car contexts))
	(after-context (cdr contexts))
	esc-char shape bad-regexp)
    (when (characterp before-context)
      (or (memq before-context '(?\ ?\t ?\n ?\r nil)) ; or warning?
	  (setq esc-char before-context))
      (setq before-context nil))
    (or before-context after-context (setq contexts nil))
    
    (x-symbol-encode-for-charsym ((encode-table fchar-table fchar-fb-table)
				  token)
      (and esc-char (eq (char-before) esc-char)
	   (x-symbol-even-escapes-before-p (1- (point)) esc-char)
	   (insert ?\ ))
      (if (not (and contexts (setq shape (cdr token))))
	  (progn
	    (insert (car token))
	    (delete-char x-symbol-encode-rchars))
	(and (setq bad-regexp (assq shape before-context))
	     (not (memq (char-before) '(?\ ?\t ?\n ?\r nil)))
	     (string-match (cdr bad-regexp) (char-to-string (char-before)))
	     (insert ?\ ))
	(insert (car token))
	(delete-char x-symbol-encode-rchars)
	(and (setq bad-regexp (assq shape after-context))
	     (not (memq (char-after) '(?\ ?\t ?\n ?\r nil)))
	     (looking-at (cdr bad-regexp))
	     (insert-before-markers " "))))))


;;;===========================================================================
;;;  Interactive conversion
;;;===========================================================================

;;;###autoload
(defun x-symbol-decode-recode (&optional beg end interactive-flag)
  "Decode all tokens in active region or buffer to characters.
If called interactively and if the region is active, BEG and END are the
boundaries of the region.  BEG and END default to the buffer boundaries.
8bit characters are treated according to `x-symbol-coding'.  See also
commands `x-symbol-encode' and `x-symbol-mode'.

Note that in most token languages, different tokens might be decoded to
the same character, e.g., \\neq and \\ne in `tex', &Auml\; and &#196\;
in `sgml'!"
  (interactive (and (region-active-p) (list (region-beginning) (region-end))))
  (unless x-symbol-language
    (error "No token language which can be used for decoding"))
  (or beg (setq beg (point-min)))
  (or end (setq end (point-max)))
  (save-excursion
    (save-restriction
      (narrow-to-region beg end)
      (let ((first-change-hook nil) ; no `flyspell-mode' here
	    (after-change-functions nil)) ; no fontification!
	(x-symbol-decode-all))
      (if font-lock-mode (x-symbol-fontify (point-min) (point-max)))))
  (if (or interactive-flag (interactive-p))
      (message "%sDecoded %s to Character in %s"
	       (x-symbol-coding-text x-symbol-coding x-symbol-default-coding
				     "Recoded %s to %s, ")
	       (x-symbol-language-text)
	       (x-symbol-region-text t))))

;;;###autoload
(defun x-symbol-decode (&optional beg end)
  (interactive (and (region-active-p) (list (region-beginning) (region-end))))
  (if (or (null x-symbol-coding)
	  (eq x-symbol-coding x-symbol-default-coding))
      (x-symbol-decode-recode beg end t)
    (let ((x-symbol-coding (or x-symbol-default-coding t)))
      (x-symbol-decode-recode beg end t))))

;;;###autoload
(defun x-symbol-encode-recode (&optional beg end interactive-flag)
  "Encode all characters in active region or buffer to tokens.
If called interactively and if the region is active, BEG and END are the
boundaries of the region.  BEG and END default to the buffer boundaries.
Variables `x-symbol-8bits' and `x-symbol-coding' determine whether to
encode 8bit characters.  See also commands `x-symbol-decode' and
`x-symbol-mode'."
  (interactive (and (region-active-p) (list (region-beginning) (region-end))))
  (unless x-symbol-language
    (error "No token language which can be used for encoding"))
  (or beg (setq beg (point-min)))
  (or end (setq end (point-max)))
  (save-excursion
    (save-restriction
      (narrow-to-region beg end)
      (let ((first-change-hook nil)	; no `flyspell-mode' here
	    (after-change-functions nil)) ; no fontification!
	(x-symbol-encode-all))
      (if font-lock-mode (x-symbol-fontify (point-min) (point-max)))))
  (if (or interactive-flag (interactive-p))
      (message "Encoded Non-%s to %s in %s%s"
	       (x-symbol-coding-text x-symbol-coding)
	       (x-symbol-language-text)
	       (x-symbol-region-text t)
	       (x-symbol-coding-text x-symbol-coding x-symbol-default-coding
				     ", Recoded %s to %s"))))

;;;###autoload
(defun x-symbol-encode (&optional beg end)
;;  "Encode all characters in active region or buffer to tokens.
;;If called interactively and if the region is active, BEG and END are the
;;boundaries of the region.  BEG and END default to the buffer boundaries.
;;Always encode all 8bit characters, as opposed to \\[x-symbol-encode],
;;i.e., `x-symbol-8bits' is assumed to be nil here."
  (interactive (and (region-active-p) (list (region-beginning) (region-end))))
  (if (or (null x-symbol-coding)
	  (eq x-symbol-coding x-symbol-default-coding))
      (x-symbol-encode-recode beg end t)
    (let ((x-symbol-coding (or x-symbol-default-coding t))
	  (x-symbol-8bits nil))
      (x-symbol-encode-recode beg end t))))

;;;###autoload
(defun x-symbol-unalias (&optional beg end coding)
  ;; TODO: use char-tables, noe
  ;; checkdoc-params: (beg end)
  "Resolve all character aliases in active region or buffer.
A char alias is a character which is also a character in a font with
another registry, e.g., `adiaeresis' is defined in all supported latin
fonts.  XEmacs distinguish between these four characters.  In package
x-symbol, one of them, with `x-symbol-default-coding' if possible, is
supported by the input methods, the other ones are char aliases to the
supported one.  The character and all the aliases are represented by the
same charsym.  The info in the minibuffer displays char aliases, you can
resolve a single character before point with \\[x-symbol-modify-key].

8bit characters in files with a file coding `x-symbol-coding' other than
`x-symbol-default-coding' are converted to the \"normal\" form.  E.g.,
if you have a latin-1 font by default, the `adiaeresis' in a latin-2
encoded file is a latin-1 `adiaeresis' in the buffer.  When saving the
buffer, its is again the right 8bit character in the latin-2 encoded
file.  But note: CHAR ALIASES ARE NOT ENCODED WHEN SAVING THE FILE.
Invoke this command before, if your buffers have char aliases!  Seven
positions in latin-3 fonts are not used, the corresponding 8bit bytes in
latin-3 encoded files are not changed.

In normal cases, buffers do not have char aliases: in XEmacs/Mule, this
is only possible if you copy characters from buffers with characters
considered as char aliases by package x-symbol, e.g., from the Mule file
\"european.el\".  In XEmacs/no-Mule, this is only possible if you use
commands like `\\[universal-argument] 2 3 4'.

The reason why package x-symbol does not support all versions of
`adiaeresis'es:
 * It is confusing to the user to choose among four similar characters.
 * These four versions are not distinguished in Unicode.
 * There are not different tokens for them, neither in the token
   language \"TeX macro\", nor \"SGML entity\"."
  (interactive (and (region-active-p) (list (region-beginning) (region-end))))
  (or beg (setq beg (point-min)))
  (or end (setq end (point-max)))
  (and coding (featurep 'mule)
       (setq coding (cdr (assq coding
			       '((iso-8859-1 . latin-iso8859-1)
				 (iso-8859-2 . latin-iso8859-2)
				 (iso-8859-3 . latin-iso8859-3)
				 (iso-8859-9 . latin-iso8859-9)
				 (iso-8859-15 . latin-iso8859-15))))))
  (let ((alist x-symbol-unalias-alist)
	(case-fold-search nil)
	(count 0)
	from to)
    (save-excursion
      (save-restriction
	(narrow-to-region beg end)
	(while alist
	  (setq from (caar alist)
		to   (cdar alist)
		alist (cdr alist))
	  ;; with CODING: unalias just for chars with that coding
	  (when (or (null coding)
		    (eq (char-charset (aref from 0)) coding))
	    (goto-char (point-min))
	    (while (search-forward from nil 'limit)
	      (setq count (1+ count))
	      (replace-match to t t))))))
    (if (interactive-p)
	(message "Normalized %d Character Aliases in %s"
		 count (x-symbol-region-text t)))))

(defun x-symbol-copy-region-encoded (start end)
  ;; WARNING: args might change (for prefix arg: kill, append/prepend).  No,
  ;; this command does not append after a kill as `copy-region-as-kill' does.
  ;; I think it's quite strange to append after a kill, but not after another
  ;; copy...
  (interactive "r")
  (if x-symbol-language			; yes, not `x-symbol-mode'
      (kill-new
       (save-excursion
	 (let* ((x-symbol-8bits
		 ;; do not use 8bit chars if not default coding
		 (and (or (null x-symbol-coding)
			  (eq x-symbol-coding x-symbol-default-coding))
		      (eq (x-symbol-buffer-coding) x-symbol-default-coding)
		      x-symbol-8bits))
		;; if 8bit chars remain, do not recode, 8bit chars in the
		;; `kill-ring' always have default coding
		(x-symbol-coding (or x-symbol-default-coding t))
		(write-region-annotations-so-far nil)) ; safety
	   (x-symbol-encode-all (get-buffer-create " x-symbol conversion")
				start end)
	   (prog1 (buffer-substring (point-min) (point-max))
	     (kill-buffer (current-buffer))))))
    (copy-region-as-kill start end)))

(defun x-symbol-yank-decoded (&optional arg)
  ;; Can also be inserted+decoded directly.  But it would be much longer when
  ;; doing it right (`buffer-undo-list', disable font-lock, etc).
  (interactive "*P")
  (if x-symbol-mode			; yes, not `x-symbol-language'
      (let* ((orig-buffer (current-buffer))
	     (string
	      (save-excursion
		(set-buffer (get-buffer-create " x-symbol conversion"))
		(x-symbol-inherit-from-buffer orig-buffer)
		;; 8bit chars in the `kill-ring' always have default coding
		(setq x-symbol-coding (or x-symbol-default-coding t))
		(yank arg)
		(x-symbol-decode-all)
		(prog1 (buffer-substring (point-min) (point-max))
		  (kill-buffer (current-buffer))))))
	(insert string))
    (yank arg)))


;;;===========================================================================
;;;  Modeline
;;;===========================================================================

(defun x-symbol-update-modeline ()
  "Update modeline according to `x-symbol-modeline-state-list'."
  (let ((alist x-symbol-modeline-state-list)
	strings string sep)
    (while alist
      (cond ((stringp (car alist))
	     (or sep (setq sep (car alist))))
	    ((setq string (if (functionp (cdar alist))
			      (funcall (cdar alist) (caar alist))
			    (if (symbol-value (caar alist))
				(cadar alist)
			      (cddar alist))))
	     (when sep (push sep strings) (setq sep nil))
	     (push string strings)))
      (setq alist (cdr alist)))
    (setq x-symbol-modeline-string
	  (apply 'concat (nreverse strings))))
  (force-mode-line-update))


;;;===========================================================================
;;;  Minor mode control
;;;===========================================================================

;;;###autoload
(defun x-symbol-auto-coding-alist (alist &optional limit no-match)
  "Return first match for ALIST in buffer limited by LIMIT.
Each element in ALIST looks like
  (REGEXP . RESULT) or (REGEXP MATCH (KEY . RESULT)...)

Search forward from the start of the buffer for a match with REGEXP.
With the first form, return RESULT.  With the second form, return RESULT
where KEY is equal to the MATCH'th regexp group of the match."
  (or limit (setq limit x-symbol-auto-coding-search-limit))
  (if (eq limit 'point-max) (setq limit nil))
  (let ((lim (if limit
		 (if (eq limit 'point-max) nil limit)
	       x-symbol-auto-coding-search-limit))
	(alist-copy alist)
	regexp value result)
    (save-excursion
      (save-restriction
	(widen)
	(while alist
	  (setq regexp (caar alist)
		value  (cdar alist))
	  (goto-char (point-min))
	  (if (re-search-forward regexp lim t)
	      (setq alist nil
		    no-match nil
		    result (if (consp value)
			       (cdr (assoc (match-string (car value))
					   (cdr value)))
			     value))
	    (setq alist (cdr alist))))
	(if no-match
	    (funcall no-match alist-copy limit)
	  result)))))

;; TODO: quick hack
;;;###autoload
(defun x-symbol-auto-8bit-search (&optional limit)
  (or limit (setq limit x-symbol-auto-8bit-search-limit))
  (if (eq limit 'point-max) (setq limit nil))
  (let ((cs (if (featurep 'mule)
		(cdr (assq (x-symbol-buffer-coding)
			   '((iso-8859-1 . latin-iso8859-1)
			     (iso-8859-2 . latin-iso8859-2)
			     (iso-8859-3 . latin-iso8859-3)
			     (iso-8859-9 . latin-iso8859-9)
			     (iso-8859-15 . latin-iso8859-15))))
	      'latin-iso8859-1)))
    (when cs
      (save-excursion
	(save-restriction
	  (widen)
	  (and limit (< limit (point-max))
	       (narrow-to-region (point-min) limit))
	  (goto-char (point-min))
	  (if (eq cs 'latin-iso8859-1)
	      (progn (skip-chars-forward "^\200-\377" limit)
		     (and (< (point) (point-max)) 'buffer))
	    (when cs
	      (block nil
		(while (not (eobp))
		  (if (eq (char-charset (char-after)) cs) (return 'buffer))
		  (forward-char))))))))))

(defvar x-symbol-font-family-postfixes
  (if x-symbol-font-lock-with-extra-props '("" "" "") '("" "_sub" "_sup")))

(defvar x-symbol-font-lock-property-alist
  '((x-symbol-sub-face face x-symbol-sub-face display (raise -0.33))
    (x-symbol-sup-face face x-symbol-sub-face display (raise 0.5))))

(defvar x-symbol-font-lock-keywords
  `((x-symbol-font-lock-start)
    ,(if x-symbol-font-lock-with-extra-props
	 (if (eq x-symbol-font-lock-with-extra-props 'invisible)
	     '(x-symbol-match-subscript
	       (1 '(face x-symbol-revealed-face invisible t) prepend)
	       (2 (or (cdr (assq x-symbol-subscript-type
				 x-symbol-font-lock-property-alist))
		      x-symbol-subscript-type)
		  prepend)
	       (3 '(face x-symbol-revealed-face invisible t) prepend t))
	   '(x-symbol-match-subscript
	     (1 x-symbol-invisible-face t)
	     (2 (or (cdr (assq x-symbol-subscript-type
			       x-symbol-font-lock-property-alist))
		    x-symbol-subscript-type)
		prepend)
	     (3 x-symbol-invisible-face t t)))
       '(x-symbol-match-subscript
	 (1 x-symbol-invisible-face t)
	 (2 (progn x-symbol-subscript-type) prepend)
	 (3 x-symbol-invisible-face t t)))
    ,@(unless (featurep 'mule)
	'((x-symbol-nomule-match-cstring
	   (0 (progn x-symbol-nomule-font-lock-face) prepend)))))
  "TODO")

(defvar x-symbol-subscript-matcher nil
  "Internal")

(defvar x-symbol-subscript-type nil
  "Internal")

(defun x-symbol-subscripts-available-p ()
  "Non-nil, if KEYWORDS are a part of `font-lock-keywords'."
  (x-symbol-font-lock-start nil)
  (and x-symbol-subscript-matcher
       (assq 'x-symbol-match-subscript x-symbol-font-lock-keywords)))

(defun x-symbol-font-lock-start (limit)
  (setq x-symbol-subscript-matcher
	(and x-symbol-mode x-symbol-subscripts
	     (find-face 'x-symbol-sub-face) ; TODO: not if in Emacs-21.4
	     (find-face 'x-symbol-sup-face) ; ditto
	     (x-symbol-language-value 'x-symbol-subscript-matcher)))
  (if (eq x-symbol-subscript-matcher 'ignore)
      (setq x-symbol-subscript-matcher nil)))

(defun x-symbol-match-subscript (limit)
  (if x-symbol-subscript-matcher
      (setq x-symbol-subscript-type
	    (funcall x-symbol-subscript-matcher limit))))

(defun x-symbol-init-font-lock ()
  "Initialize all font-lock keywords for current `major-mode'.
The additional x-symbol keywords are determined by the language access
`x-symbol-font-lock-keywords' for `major-mode's symbol property
`x-symbol-font-lock-language' and the XEmacs/no-Mule cstring
fontification, if necessary.  The font-lock keywords variables are those
mentioned in `font-lock-defaults' or in the symbol property
`font-lock-defaults' of `major-mode'."
  (if (assq 'x-symbol-match-subscript x-symbol-font-lock-keywords)
      (let ((symbols (car (or font-lock-defaults
			      (if (fboundp 'font-lock-find-font-lock-defaults)
				  (font-lock-find-font-lock-defaults
				   major-mode))))))
	(dolist (symbol (if (listp symbols) symbols (list symbols)))
	  (or (assq 'x-symbol-match-subscript (symbol-value symbol))
	      (set symbol (append (symbol-value symbol)
				  x-symbol-font-lock-keywords))))
	(or (null font-lock-keywords)
	    (assq 'x-symbol-match-subscript font-lock-keywords)
	    (setq font-lock-keywords (append font-lock-keywords
					     x-symbol-font-lock-keywords)))
	(when x-symbol-font-lock-with-extra-props
	  (make-local-variable 'font-lock-extra-managed-props)
	  ;; see `x-symbol-font-lock-keywords':
	  (if (eq x-symbol-font-lock-with-extra-props 'invisible)
	      (pushnew 'invisible font-lock-extra-managed-props))
	  (pushnew 'display font-lock-extra-managed-props)))
    (when x-symbol-font-lock-keywords
      (lwarn 'x-symbol 'error
	"Additional font-lock keywords are invalid, set to nil")
      (setq x-symbol-font-lock-keywords nil))))

(defun x-symbol-set-image (dummy value)
  ;; checkdoc-params: (dummy)
  "Set function for buffer local variable `x-symbol-image'.
If VALUE is non-nil, call `x-symbol-image-parse-buffer', otherwise
delete existing x-symbol image extents in buffer."
  (if (and (setq x-symbol-image (and value (x-symbol-image-available-p)))
	   x-symbol-mode)
      (progn
	(make-local-hook 'after-change-functions)
	(x-symbol-image-parse-buffer)
	(add-hook 'after-change-functions
		  'x-symbol-image-after-change-function nil t))
    (if (local-variable-p 'x-symbol-image-buffer-extents (current-buffer))
	(x-symbol-image-delete-extents 1 (1+ (buffer-size))))
    (remove-hook 'after-change-functions 'x-symbol-image-after-change-function
		 t)))

;;;###autoload
(defun x-symbol-mode-internal (conversion)
  "Setup X-Symbol mode according to buffer-local variables.
If CONVERSION is non-nil, do conversion with EXEC-THRESHOLD.  See
command `x-symbol-mode' for details."
  (unless (featurep 'xemacs)
    (unless enable-multibyte-characters
      ;; Emacs: we need to convert the buffer from unibyte to multibyte
      ;; since we'll use multibyte support for the symbol charset.
      ;; TODO: try to do it less often
      (let ((modified (buffer-modified-p))
	    (inhibit-read-only t)
	    (inhibit-modification-hooks t))
	(unwind-protect
	    (progn
	      (decode-coding-region (point-min) (point-max) 'undecided)
	      (set-buffer-multibyte t))
	  (set-buffer-modified-p modified)))))
  (if conversion
      (let ((modified (buffer-modified-p))
	    (buffer-read-only nil)	; always allow conversion
	    (buffer-file-name nil)	; no file-locking, TODO: dangerous?
	    (inhibit-read-only t)
	    (first-change-hook nil)	; no `flyspell-mode' here
	    (after-change-functions nil) ; no fontification!
	    (no-undo (null buffer-undo-list)))
	(if no-undo (setq buffer-undo-list t))
	(save-excursion
	  (save-restriction
	    (if x-symbol-mode
		(let ((buffer-coding (x-symbol-buffer-coding)))
		  ;; cannot do this in `x-symbol-mode': `x-symbol-fchar-tables' might not be defined
		  (if buffer-coding
		      (or (null x-symbol-coding) ; no coding specified
			  (eq x-symbol-coding buffer-coding) ; specified = buffer-file-coding
			  (and (eq buffer-coding x-symbol-default-coding)
					; valid coding and buffer-fc = default
			       (assq x-symbol-coding x-symbol-fchar-tables))
			  (setq x-symbol-8bits
				(x-symbol-auto-8bit-search 'point-max)))
		    (setq x-symbol-8bits nil))
		  (x-symbol-decode-all))
	      (x-symbol-encode-all))
	    (if font-lock-mode (x-symbol-fontify (point-min) (point-max)))))
	(if no-undo (setq buffer-undo-list nil))
	(or modified (set-buffer-modified-p nil))))
  (x-symbol-set-image nil x-symbol-image)
  (if x-symbol-mode
      (progn
	;; set font-lock keywords
	(x-symbol-init-font-lock)
	(make-local-hook 'pre-command-hook)
	(make-local-hook 'post-command-hook)
	(add-hook 'pre-command-hook 'x-symbol-pre-command-hook nil t)
	(add-hook 'post-command-hook 'x-symbol-post-command-hook nil t)
	(if (assq 'x-symbol format-alist)
	    (pushnew 'x-symbol buffer-file-format))
	(easy-menu-add x-symbol-menu)
	(x-symbol-update-modeline))
    (remove-hook 'pre-command-hook 'x-symbol-pre-command-hook t)
    (remove-hook 'post-command-hook  'x-symbol-post-command-hook t)
    (setq buffer-file-format (delq 'x-symbol buffer-file-format))
    (if (local-variable-p 'current-menubar (current-buffer))
	;; XEmacs bug workaround
	(ignore-errors (easy-menu-remove x-symbol-menu)))))

(defun nuke-x-symbol ()
  "Turn off X-Symbol mode and make sure that tokens are encoded.
Used in `change-major-mode-hook'."
  (when x-symbol-mode
    (setq x-symbol-mode nil)
    (x-symbol-mode-internal x-symbol-language)))
(add-hook 'change-major-mode-hook 'nuke-x-symbol)


;;;===========================================================================
;;;  Menu filters
;;;===========================================================================

(defun x-symbol-options-filter (menu-items)
  (let (item menu var options)
    (while (setq item (pop menu-items))
      (push (if (not (and (vectorp item)
			  (= (length item) 3)
			  (setq var (aref item 1))
			  (symbolp var)
			  (setq options (get var 'x-symbol-options))))
		item
	      (let ((header (aref item 0))
		    (active (and (eval (aref item 2)) t))
		    (value (symbol-value var))
		    fallback submenu option)
		(if (functionp options) (setq options (funcall options)))
		(setq fallback (pop options))
		;; VARIABLE with VALUE, allowed OPTIONS with FALLBACK
		(if (null options)
		    (vector header
			    `(x-symbol-set-variable
			      (quote ,var) ,(if value nil `(quote ,fallback)))
			    :active active
			    :style 'toggle
			    :selected (and value t))
		  (or (assq value options) (setq value fallback))
		  (while (setq option (pop options))
		    (push (vector (cdr option)
				  `(x-symbol-set-variable
				    (quote ,var) (quote ,(car option)))
				  :active active
				  :style 'radio
				  :selected (eq (car option) value))
			  submenu))
		  (cons header (nreverse submenu)))))
	    menu))
    (nreverse menu)))

(defun x-symbol-extra-filter (menu-items)
  (let ((extra (assoc (aref (car menu-items) 0)
		      (x-symbol-language-value 'x-symbol-extra-menu-items))))
    (if extra
	(append (cdr menu-items) (cdr extra))
      (cdr menu-items))))

(defun x-symbol-menu-filter (menu-items)
  "Menu filter `x-symbol-menu'.
Append the global or token-language specific menu to MENU-ITEMS."
  (nconc (mapcar (lambda (item)
		   (if (and (consp item)
			    (eq (caddr item) 'x-symbol-extra-filter)
			    (aref (cadddr item) 2))
		       (cons (format (car item)
				     (funcall (aref (cadddr item) 2)))
			     (cdr item))
		     item))
		 menu-items)
	 (or (and x-symbol-local-menu
		  x-symbol-language
		  (x-symbol-generated-menu-alist
		   (x-symbol-language-value 'x-symbol-generated-data)))
	     x-symbol-menu-alist)))



;;;;##########################################################################
;;;;  Info, List-Mode
;;;;##########################################################################


(put 'x-symbol-list-mode 'mode-class 'special) ; where is it used?

(defvar x-symbol-list-mode-map
  (let ((map (make-sparse-keymap)))
    (define-key map " " 'x-symbol-list-selected)
    (define-key map "\C-m" 'x-symbol-list-selected)
    (define-key map "q" 'x-symbol-list-bury)
    (define-key map "?" 'x-symbol-list-info)
    (define-key map "i" 'x-symbol-list-info)
    (define-key map "h" 'x-symbol-list-info)
    ;; TODO: either XEmacs or Emacs bindings
    ;; Bindings for XEmacs.
    (when (lookup-key global-map [(button2)])
      (define-key map 'button2 'x-symbol-list-mouse-selected)
      (define-key map 'button2up 'undefined)
      (define-key map 'button3 'x-symbol-list-menu-selected)
      (define-key map 'button3up 'undefined))
    ;; Same bindings but for Emacs.
    (when (lookup-key global-map [(mouse-2)])
      (define-key map [mouse-2] 'x-symbol-list-mouse-selected)
      (define-key map [up-mouse-2] 'undefined)
      (define-key map [down-mouse-3] 'x-symbol-list-menu-selected)
      (define-key map [mouse-3] 'undefined)
      (define-key map [up-mouse-3] 'undefined))
    (set-keymap-parent map list-mode-map)
    map)
  "Mode map used in grid buffers and the key completion buffer.")

(defvar x-symbol-list-buffer nil
  "Internal.  Recently used list buffer.")
(defvar x-symbol-list-win-config nil
  "Internal buffer-local in list buffer.  Win-config before invocation.")
(defvar x-symbol-invisible-spec nil
  "Internal.  Used by `x-symbol-hide-revealed-at-point'.
Looks like (BUFFER START END . FACE-OR-FACES) or nil.")

(defvar x-symbol-itimer nil
  "Internal.  Used by `x-symbol-start-itimer-once'.")

(defvar x-symbol-invisible-display-table
  (let ((table (make-display-table))
	(i 0))
    (while (< i 256)
      (aset table i "")
      (setq i (1+ i)))
    table)
  "Internal variable.  Display table for `x-symbol-invisible-face'.")

(defvar x-symbol-invisible-font "-XSYMB-nil-*"
  ;; Note that the `nil' font uses a `fontspecific' encoding, so we need to go
  ;; through a fontset to convince Emacs to use this font when displaying ASCII
  ;; chars.
  "Internal variable.  Font to use for `x-symbol-invisible-face'.
It is not used if faces can have a property \"display table\", i.e., if
 `x-symbol-invisible-display-table' has a non-nil value.")

(make-face 'x-symbol-invisible-face
	   "*Face for displaying invisible things like \"_\" and \"^\" in TeX.")
(unless noninteractive			; CW: see noninteractive below
  (cond (x-symbol-invisible-display-table
	 (set-face-display-table 'x-symbol-invisible-face
				 x-symbol-invisible-display-table))
	((and (fboundp 'create-fontset-from-ascii-font)
	      x-symbol-invisible-font
	      (try-font-name x-symbol-invisible-font))
	 ;; This is a mean and ugly hack.  Since Emacs seems unable to create a
	 ;; face that makes text invisible, we simulate it by using a minuscule
	 ;; pseudo-font.
	 (set-face-font 'x-symbol-invisible-face
			(create-fontset-from-ascii-font
			 x-symbol-invisible-font)))))

(defvar x-symbol-charsym-info-cache nil
  "Internal.  Cache for `x-symbol-charsym-info'.")
(defvar x-symbol-language-info-caches nil
  "Internal.  Cache for `x-symbol-language-info'.")
(defvar x-symbol-coding-info-cache nil
  "Internal.  Cache for `x-symbol-coding-info'.")
(defvar x-symbol-keys-info-cache nil
  "Internal.  Cache for `x-symbol-keys-info'.")


;;;===========================================================================
;;;  X-Symbol List Mode (for GRID and KEYBOARD completion)
;;;===========================================================================

(defun x-symbol-list-bury ()
  "Bury current buffer while trying to use the old window configuration."
  (interactive)
  (setq x-symbol-list-buffer (current-buffer))
  (x-symbol-list-restore t))

(defun x-symbol-list-restore (&optional bury)
  "Restore window configuration used before invoking the list buffer.
If optional argument BURY is non-nil, bury current buffer if
configuration cannot be restored.  See `x-symbol-temp-grid' and
`x-symbol-temp-help'.  Used by `x-symbol-insert-command'."
  (and x-symbol-list-buffer
       (get-buffer-window x-symbol-list-buffer)
       (let ((orig (current-buffer))
	     reference win-config)
	 (set-buffer x-symbol-list-buffer)
	 (setq reference completion-reference-buffer)
	 ;; CW: a first try:
	 (or (and (buffer-live-p reference)
		  (get-buffer-window reference t)
		  (cond ((null x-symbol-use-refbuffer-once))
			((functionp x-symbol-use-refbuffer-once)
			 (not (funcall x-symbol-use-refbuffer-once
				       reference)))))
	     (setq completion-reference-buffer nil))
	 (setq win-config x-symbol-list-win-config
	       x-symbol-list-win-config nil)
	 (if (or (eq orig reference)
		 (and (eq orig x-symbol-list-buffer) (buffer-live-p reference)))
	     (if (window-configuration-p win-config)
		 (set-window-configuration win-config)
	       (pop-to-buffer reference))
	   (set-buffer orig)
	   (if bury (bury-buffer)))))
  (setq x-symbol-list-buffer nil))

(defun x-symbol-list-store (reference win-config)
  "Store window configuration WIN-CONFIG and reference buffer REFERENCE.
Used by `x-symbol-list-restore'."
  (setq x-symbol-list-buffer (and reference (current-buffer)))
  (make-local-variable 'completion-reference-buffer)
  (setq completion-reference-buffer reference)
  (make-local-variable 'x-symbol-list-win-config)
  (setq x-symbol-list-win-config win-config))

(defun x-symbol-list-mode (&optional language reference win-config)
  "Major mode for buffers containing x-symbol items.
Invoked for token language LANGUAGE form buffer REFERENCE.  WIN-CONFIG
is the window configuration before invoking the grid or key completion
buffer, used by `x-symbol-list-restore'.  Runs hook
`x-symbol-list-mode-hook'.

\\{x-symbol-list-mode-map}"
  (list-mode)
  (setq major-mode 'x-symbol-list-mode)
  (use-local-map x-symbol-list-mode-map)
  (setq mode-name "XS-List")
  (setq x-symbol-language language)
  (x-symbol-list-store reference win-config)
  (run-hooks 'x-symbol-list-mode-hook))


;;;===========================================================================
;;;  List Mode Selection
;;;===========================================================================

(defun x-symbol-list-scroll (pos buffer)
  "Scrolls BUFFER up/down according to POS.
In POS is in the upper half of the window, scroll down, otherwise,
scroll up."
  (let ((window (get-buffer-window buffer 'visible)))
    (if window
	(progn
	  (select-window window)
	  (set-buffer buffer))
      (pop-to-buffer buffer)))
  (let ((old-pos (point)))
    (move-to-window-line nil)
    (if (> (point) pos)
	(scroll-down)
      (scroll-up)
      (when (pos-visible-in-window-p (point-max))
	(goto-char (point-max))
	(recenter -1)))
    (if (pos-visible-in-window-p old-pos)
	(goto-char old-pos)
      (move-to-window-line nil))))

;;;###autoload
(defun x-symbol-init-language-interactive (language)
  "Initialize token language LANGUAGE.
See `x-symbol-init-language'."
  (interactive (list (x-symbol-read-language
		      "Initialize Token Language: " nil
		      (lambda (elem)
			(and (cdr elem)
			     (null (get (cdr elem) 'x-symbol-initialized)))))))
  (if language
      (if (get language 'x-symbol-initialized)
	  (message "Token language %S is already initialized"
		   (x-symbol-language-value 'x-symbol-name language))
	(if (x-symbol-init-language language)
	    (message "Token language %S has been initialized"
		     (x-symbol-language-value 'x-symbol-name language))
	  (error "Failed to initialize token language `%s'" language)))))

(defun x-symbol-list-menu (reference charsym)
  "Popup menu for the insertion of the character under mouse.
Insert character or one of its tokens, represented by CHARSYM into
buffer REFERENCE, see `x-symbol-insert-command'."
  (let ((keys (where-is-internal (get charsym 'x-symbol-insert-command)
				 nil t))
	(alist (cons (cons nil x-symbol-charsym-name)
		     x-symbol-language-alist))
	menu menu1
	language token)
    (while alist
      (if (or (null (car (setq language (pop alist))))
	      (get (car language) 'x-symbol-initialized))
	  (if (setq token (if (car language)
			      (car (gethash charsym
					    (x-symbol-generated-encode-table
					     (x-symbol-language-value
					      'x-symbol-generated-data
					      (car language)))))
			    (symbol-name charsym)))
	      (push (vector token
			    `(x-symbol-insert-command -1 (quote ,charsym)
						      ,token)
			    :keys (format (if (eq (car language)
						  x-symbol-language)
					      "(%s)*"
					    "(%s)")
					  (cdr language)))
		    menu))
	(push (vector "Initialize..." `(x-symbol-init-language-interactive
					(quote ,(car language)))
		      :keys (cdr language))
	      menu1)))
    (popup-menu
     (list* (if (symbol-value-in-buffer 'buffer-read-only reference)
		"Store in kill-ring as:"
	      (if (eq (current-buffer) reference)
		  "Insert as:"
		(format "Insert in \"%s\" as:" (buffer-name reference))))
	    (vector
	     "Character"
	     `(x-symbol-insert-command -1 (quote ,charsym) nil)
	     :active (gethash charsym x-symbol-cstring-table)
	     :keys (if keys
		       (if (funcall x-symbol-valid-charsym-function charsym)
			   (key-description keys)
			 (concat (key-description
				  (where-is-internal 'negative-argument nil t))
				 " "
				 (key-description keys)))))
	    "---"
	    (nconc (nreverse menu)
		   (and menu1 (cons "--:shadowDoubleEtchedIn"
				    (nreverse menu1))))))))

(defun x-symbol-list-selected (&optional arg pos buffer)
  "Handle selection of a x-symbol list item at POS in BUFFER.
When called interactively, insert character with prefix argument ARG for
list item at point, see `x-symbol-insert-command'.  Also called by
`x-symbol-list-menu-selected' and `x-symbol-list-mouse-selected'."
  (interactive "P")
  (or pos (setq pos (point)))
  ;; SM: we rely too much on list-mode's implementation (and properties).  CW:
  ;; I don't think so, at least these are XEmacs' documented properties...
  (let* ((extent (extent-at pos buffer 'list-mode-item)))
    (if extent
	(let ((charsym (extent-property extent 'list-mode-item-user-data))
	      (reference (or completion-reference-buffer (current-buffer))))
	  ;; current list buffer must be equal
	  (setq x-symbol-list-buffer (or buffer (current-buffer)))
	  (if (and buffer (consp arg))
	      (x-symbol-list-menu reference charsym)
	    (x-symbol-insert-command arg charsym)))
      (or buffer (error "Not over an x-symbol selection"))
      (if (consp arg)
	  (popup-menu x-symbol-menu)
	(let ((selected (selected-window)))
	  (unwind-protect
	      (x-symbol-list-scroll pos buffer)
	    (select-window selected)))))))

(defun x-symbol-list-menu-selected (event)
  ;; checkdoc-params: (event)
  "Popup menu for x-symbol list item under mouse.
If mouse is over a list item, popup menu for the insertion of the
corresponding character or one of its tokens, see
`x-symbol-insert-command'.  Otherwise, popup the X-Symbol menu."
  (interactive "e")
  ;;(run-hooks 'mouse-leave-buffer-hook)
  (x-symbol-list-selected '(4) (event-closest-point event)
			  (event-buffer event)))

(defun x-symbol-list-mouse-selected (arg event)
  ;; checkdoc-params: (arg event)
  "Select x-symbol list item under mouse.
If mouse is over a list item, insert the corresponding character, see
`x-symbol-insert-command'.  Otherwise, scroll the list buffer down, if
mouse is in the upper half of the window, scroll up, otherwise."
  (interactive "P\ne")
  ;;(run-hooks 'mouse-leave-buffer-hook)
  (x-symbol-list-selected arg (event-closest-point event)
			  (event-buffer event)))
(put 'x-symbol-list-mouse-selected 'isearch-command t)


;;;===========================================================================
;;;  Character Info Parts
;;;===========================================================================

(defun x-symbol-charsym-info (charsym)
  "Return info for CHARSYM describing the charsym."
  (x-symbol-ensure-hashtable 'x-symbol-charsym-info-cache)
  (or (gethash charsym x-symbol-charsym-info-cache)
      (x-symbol-puthash
       charsym
       (concat (x-symbol-fancy-string
		(cons (format (car x-symbol-info-token-charsym) charsym)
		      (cdr x-symbol-info-token-charsym)))
	       (x-symbol-fancy-value 'x-symbol-info-classes-pre)
	       (x-symbol-fancy-value 'x-symbol-info-classes-charsym)
	       (x-symbol-fancy-value 'x-symbol-info-classes-post))
       x-symbol-charsym-info-cache)))

(defun x-symbol-language-info (charsym language)
  "Return info for CHARSYM describing the token and classes in LANGUAGE."
  (let ((cache (plist-get x-symbol-language-info-caches language)))
    (unless cache
      (x-symbol-ensure-hashtable 'cache)
      (setq x-symbol-language-info-caches
	    (plist-put x-symbol-language-info-caches language cache)))
    (or (gethash charsym cache)
	(let* ((data (x-symbol-language-value
		      'x-symbol-generated-data language))
	       (token (gethash charsym
			       (x-symbol-generated-encode-table data))))
	  (x-symbol-puthash
	   charsym
	   (concat (if token
		       (x-symbol-fancy-string
			(cons (car token)
			      (cdr (x-symbol-charsym-face charsym language))))
		     (x-symbol-fancy-string
		      (cons (format (car x-symbol-info-token-charsym) charsym)
			    (cdr x-symbol-info-token-charsym))))
		   (x-symbol-fancy-associations
		    (gethash charsym
			     (x-symbol-generated-token-classes data))
		    (x-symbol-language-value 'x-symbol-class-alist language)
		    'x-symbol-info-classes-pre
		    'x-symbol-info-classes-sep
		    'x-symbol-info-classes-post
		    (if token 'VALID 'INVALID)))
	   cache)))))

(defun x-symbol-coding-info (charsym)
  "Return info for CHARSYM describing possible 8bit codings."
  (x-symbol-ensure-hashtable 'x-symbol-coding-info-cache)
  (or (gethash charsym x-symbol-coding-info-cache)
      (let ((tables x-symbol-info-coding-alist) coding table charsym-codings)
	(while tables
	  (setq coding (car (pop tables)))
	  (and (setq table (assq coding x-symbol-fchar-tables))
	       (gethash charsym (cdr table))
	       (push coding charsym-codings)))
	(x-symbol-puthash charsym
			  (or (x-symbol-fancy-associations
			       (nreverse charsym-codings)
			       x-symbol-info-coding-alist
			       'x-symbol-info-coding-pre
			       'x-symbol-info-coding-sep
			       'x-symbol-info-coding-post)
			      "")
			  x-symbol-coding-info-cache))))

(defun x-symbol-keys-info (charsym)
  "Return info for CHARSYM describing key bindings.
See `x-symbol-info-keys-keymaps'."
  (x-symbol-ensure-hashtable 'x-symbol-keys-info-cache)
  (or (gethash charsym x-symbol-keys-info-cache)
      ;;(if x-symbol-input-initialized
      (x-symbol-puthash
       charsym
       (concat (x-symbol-fancy-value 'x-symbol-info-keys-pre
				     'substitute-command-keys)
	       (sorted-key-descriptions
		(where-is-internal
		 (get charsym 'x-symbol-insert-command)
		 (and (functionp x-symbol-info-keys-keymaps)
		      (funcall x-symbol-info-keys-keymaps charsym)))
		(x-symbol-fancy-value 'x-symbol-info-keys-sep))
	       (x-symbol-fancy-value 'x-symbol-info-keys-post))
       x-symbol-keys-info-cache)))


;;;===========================================================================
;;;  Character Info
;;;===========================================================================

(defun x-symbol-info (charsym language long intro)
  "Return info for CHARSYM in LANGUAGE with introduction INTRO.
See `x-symbol-character-info'.  When LONG is nil, do not show info
describing key bindings."
  (concat intro
	  (gethash charsym x-symbol-fontified-cstring-table)
	  (x-symbol-fancy-value 'x-symbol-info-token-pre)
	  (if (get language 'x-symbol-name)
	      (x-symbol-language-info charsym language)
	    (x-symbol-charsym-info charsym))
	  (x-symbol-coding-info charsym)
	  (and long (x-symbol-keys-info charsym))))

(defun x-symbol-list-info ()
  "Display info for character under point in echo area."
  (interactive)
  ;; FIXME: we rely too much on list-mode's implementation (and properties).
  (let* ((extent (extent-at (point) nil 'list-mode-item))
	 (charsym (and extent
		       (extent-property extent 'list-mode-item-user-data))))
    (if charsym
	(display-message 'no-log
	  (x-symbol-info charsym x-symbol-language t
			 (x-symbol-fancy-value 'x-symbol-info-intro-list
					       'substitute-command-keys)))
      (error "No charsym selected"))))

(defun x-symbol-highlight-echo (extent &optional window pos)
  "Return info for character covered by EXTENT."
  ;; CW: check -- seems to work
  ;; Emacs-21 provides `window' but as the first argument.
  (if (windowp extent) (let ((w extent)) (setq extent window window w)))
  ;; FIXME: we rely too much on list-mode's implementation (and properties).
  (let ((charsym (extent-property extent 'list-mode-item-user-data)))
    (if charsym
	(x-symbol-info charsym x-symbol-language t
		       (x-symbol-fancy-value 'x-symbol-info-intro-highlight)))))

(defun x-symbol-point-info (after before)
  "Return info for characters around point.
See `x-symbol-character-info' and `x-symbol-context-info'.  AFTER and
BEFORE represent the characters after and before point.  They have the
same type as the return values of `x-symbol-charsym-after'."
  (let (charsym context pos)
    (cond ((and x-symbol-character-info (setq charsym (cdr after)))
	   (if (x-symbol-alias-charsym after)
	       (x-symbol-info
		charsym x-symbol-language nil
		(x-symbol-fancy-value 'x-symbol-info-alias-after
				      'substitute-command-keys))
	     (x-symbol-info
	      charsym x-symbol-language t
	      (x-symbol-fancy-value 'x-symbol-info-intro-after))))
	  ((and (eq x-symbol-character-info t) (setq charsym (cdr before)))
	   (if (x-symbol-alias-charsym before)
	       (x-symbol-info
		charsym x-symbol-language nil
		(x-symbol-fancy-value 'x-symbol-info-alias-before
				      'substitute-command-keys))
	     (x-symbol-info
	      charsym x-symbol-language t
	      (x-symbol-fancy-value 'x-symbol-info-intro-before))))
	  ((and x-symbol-context-info
		(setq pos (or (car after) (point)))
		(setq before (x-symbol-match-before x-symbol-context-atree pos))
		(setq charsym (x-symbol-next-valid-charsym
			       (cdr before) t 'x-symbol-modify-to))
		(null (x-symbol-call-function-or-regexp
		       x-symbol-context-info-ignore
		       (setq context (buffer-substring (car before) pos))
		       charsym)))
	   (x-symbol-info
	    charsym x-symbol-language t
	    ;; no fancy context (too fancy, would break no-Mule cstrings)
	    (concat (x-symbol-fancy-value 'x-symbol-info-context-pre
					  'substitute-command-keys)
		    context
		    (x-symbol-fancy-value 'x-symbol-info-context-post)))))))


;;;===========================================================================
;;;  Hide & Reveal Invisible
;;;===========================================================================

(defun x-symbol-hide-revealed-at-point ()
  "Hide characters at point revealed by `x-symbol-reveal-invisible'.
Used by `x-symbol-pre-command-hook'.  To avoid flickering, commands
which do not change the buffer contents and just move point by a
predictable number of characters right or left should have a function
MOVE as the symbol property `x-symbol-point-function'.  MOVE is called
with argument `point' and should return the position of `point' after
the execution of the command.  E.g., `forward-char' uses `1+'."
  (when x-symbol-invisible-spec
    (unless (let (fun pos)
	      (and (symbolp this-command)
		   (functionp (setq fun (get this-command
					     'x-symbol-point-function)))
		   (setq pos (funcall fun (point)))
		   (<= (cadr x-symbol-invisible-spec) pos)
		   (if (eq x-symbol-reveal-invisible t)
		       (>= (caddr x-symbol-invisible-spec) pos)
		     (> (caddr x-symbol-invisible-spec) pos))))
      (x-symbol-ignore-property-changes
	(if (eq x-symbol-font-lock-with-extra-props 'invisible)
	    (progn
	      (put-text-property (cadr x-symbol-invisible-spec)
				 (caddr x-symbol-invisible-spec)
				 'invisible 'hide)
	      (unless (eq this-command 'eval-expression)
		(setq x-symbol-trace-invisible
		      (text-properties-at (cadr x-symbol-invisible-spec)))))
	  (funcall (if (consp (cdddr x-symbol-invisible-spec))
		       'put-text-property
		     'put-nonduplicable-text-property)
		   (cadr x-symbol-invisible-spec)
		   (caddr x-symbol-invisible-spec)
		   'face (cdddr x-symbol-invisible-spec)
		   (car x-symbol-invisible-spec)))
	(setq x-symbol-invisible-spec nil)))))

(defun x-symbol-reveal-invisible (after before)
  "Reveal invisible characters around point.
See `x-symbol-reveal-invisible'.  AFTER and BEFORE represent the
characters after and before point.  They have the same type as the
return values of `x-symbol-charsym-after'.  The characters are hidden
with `x-symbol-hide-revealed-at-point'."
  (let ((faces (and after (get-text-property after 'face)))
	(iface (if (eq x-symbol-font-lock-with-extra-props 'invisible)
		   'x-symbol-revealed-face
		 'x-symbol-invisible-face)))
    (when (setq x-symbol-invisible-spec
		(or (if (consp faces)
			(memq iface faces)
		      (eq faces iface))
		    (and (eq x-symbol-reveal-invisible t)
			 (setq after before)
			 (setq faces (get-text-property after 'face))
			 (if (consp faces)
			     (memq iface faces)
			   (eq faces iface)))))
      (let ((start (previous-single-property-change (1+ after) 'face nil
						    (point-at-bol)))
	    (end (next-single-property-change after 'face nil
					      (point-at-eol))))
	(setq x-symbol-invisible-spec
	      (list* (current-buffer) start end faces))
	(x-symbol-ignore-property-changes
	  (if (eq x-symbol-font-lock-with-extra-props 'invisible)
	      (progn (remove-text-properties start end '(invisible nil))
		     (setq x-symbol-trace-invisible (text-properties-at start)))
	    (put-nonduplicable-text-property
	     start end 'face (if (consp faces)
				 (cons 'x-symbol-revealed-face
				       (delq 'x-symbol-invisible-face
					     (copy-sequence faces)))
			       'x-symbol-revealed-face))))))))


;;;===========================================================================
;;;  Entry Points
;;;===========================================================================

(defun x-symbol-show-info-and-invisible ()
  "Reveal invisible characters and show info in echo area.
See `x-symbol-reveal-invisible', `x-symbol-character-info' and
`x-symbol-context-info'.  Expiry function for itimer started with
`x-symbol-start-itimer-once'."
  (when x-symbol-mode
    (let* ((after (x-symbol-charsym-after))
	   (pos (1- (or (car after) (point))))
	   (before (and (null (eq (char-after pos) ?\n))
			(x-symbol-charsym-after pos)))
	   info)
      (and x-symbol-reveal-invisible
	   (null x-symbol-invisible-spec)
	   (x-symbol-reveal-invisible (car after) (car before)))
      (and (null message-stack)		; no message in echo area
	   (not (eq (selected-window) (minibuffer-window)))
	   ;; Quail:
	   (not (and (local-variable-p 'quail-guidance-buf (current-buffer))
		     (buffer-live-p quail-guidance-buf)
		     (> (buffer-size quail-guidance-buf) 0)))
;;	   (not (and (local-variable-p 'current-input-method (current-buffer))
;;		     current-input-method
;;		     (fboundp 'quail-point-in-conversion-region)
;;		     (boundp 'quail-conv-overlay)
;;		     (setq cw quail-overlay)
;;		     (overlayp quail-overlay) ; ehem, this test should be in that function
;;		     (setq cw2 quail-overlay)))
;;		     ;;(quail-point-in-conversion-region)))
	   (setq info (x-symbol-point-info after before))
	   (display-message 'no-log info)))))

(defun x-symbol-start-itimer-once ()
  "Start idle timer for function `x-symbol-show-info-and-invisible'.
Used in `x-symbol-post-command-hook.'"
  (if (and (numberp x-symbol-idle-delay) (> x-symbol-idle-delay 0))
      (unless (itimer-live-p x-symbol-itimer)
	(setq x-symbol-itimer
	      (start-itimer "X-Symbol Idle Timer"
			    'x-symbol-show-info-and-invisible
			    x-symbol-idle-delay nil t)))
    (x-symbol-show-info-and-invisible)))


;;;===========================================================================
;;;  Minibuffer Setup
;;;===========================================================================

(defun x-symbol-setup-minibuffer ()
  "Inherit buffer-local x-symbol variables for minibuffer."
  (let (mode language)
    (save-excursion
      (set-buffer (window-buffer minibuffer-scroll-window))
      (setq mode x-symbol-mode
	    language x-symbol-language))
    (setq x-symbol-mode mode
	  x-symbol-language language)))
(add-hook 'minibuffer-setup-hook 'x-symbol-setup-minibuffer)



;;;;##########################################################################
;;;;  Input Methods
;;;;##########################################################################


(defvar x-symbol-language-history nil
  "History of token languages, long form, see access `x-symbol-name'.")
(defvar x-symbol-token-history nil
  "History of tokens of any language.")

(defvar x-symbol-last-abbrev ""
  "Internal.  Used by input methods CONTEXT, ELECTRIC, TOKEN.")
(defvar x-symbol-electric-pos nil
  "Internal.  Used by input method ELECTRIC.")

(defvar x-symbol-command-keys nil
  "Internal.  Key sequence set and used by `x-symbol-help'.
Also used by temporary functions.")

(defvar x-symbol-help-keys nil
  "Internal.  Key description used by `x-symbol-help-mapper'.")
(defvar x-symbol-help-language nil
  "Internal.  Token language used for `x-symbol-help-mapper'.")
(defvar x-symbol-help-completions nil
  "Internal.  Characters displayed prior to others.")
(defvar x-symbol-help-completions1 nil
  "Internal.  Characters displayed late.")


;;;===========================================================================
;;;  Miscellaneous key functions
;;;===========================================================================

(defun x-symbol-map-default-binding (&optional arg)
  ;; checkdoc-params: (arg)
  "Default binding in X-Symbol key map.
Check `x-symbol-map-default-keys-alist' for commands to execute.
Otherwise signal error `undefined-keystroke-sequence'."
  (interactive "P")
  (let* ((this (this-command-keys))
	 (last (aref this (1- (length this))))
	 (alist x-symbol-map-default-keys-alist)
	 definition)
    (while alist
      (if (x-symbol-event-matches-key-specifier-p last (caar alist))
	  (setq definition (car alist)
		alist nil)
	(setq alist (cdr alist))))
    (if definition
	(let ((cmd (or (cadr definition) (key-binding (vector last)))))
	  (if (caddr definition)
	      (progn
		(command-execute cmd)
		(setq prefix-arg arg)
		(setq unread-command-events x-symbol-command-keys))
	    (setq prefix-arg arg)
	    (command-execute cmd)))
      (signal-error 'undefined-keystroke-sequence (list this)))))


;;;===========================================================================
;;;  self-insert
;;;===========================================================================

(defun x-symbol-read-charsym-token (charsym)
  "Read one of the languages for defined tokens of CHARSYM."
  (let* ((token (if x-symbol-language
		    (car (gethash charsym (x-symbol-generated-encode-table
					   (x-symbol-language-value
					    'x-symbol-generated-data))))))
	 (language (x-symbol-read-language 
		    (format "Insert %s in token language (default %s): "
			    charsym
			    (if token
				(x-symbol-language-text)
			      x-symbol-charsym-name))
		    (if token x-symbol-language)
		    (lambda (lang)
		      (or (null (setq lang (cdr lang)))
			  (gethash charsym (x-symbol-generated-encode-table
					    (x-symbol-language-value
					     'x-symbol-generated-data
					     lang))))))))
    (or (if language
	    (car (gethash charsym (x-symbol-generated-encode-table
				   (x-symbol-language-value
				    'x-symbol-generated-data
				    language)))))
	(symbol-name charsym))))

(defun x-symbol-insert-command (arg &optional charsym cstring)
  "Insert character for CHARSYM.
If ARG is a cons, e.g., when the current command is preceded by one or
more \\[universal-argument]'s with no digits, select initialized
language in minibuffer for token to insert.  Otherwise insert character
abs(ARG) times.  If ARG is negative, do not barf if character is not
valid, see `x-symbol-valid-charsym-function'.

Restore window configuration if necessary, see `x-symbol-list-restore'.
If buffer is read-only, store in `kill-ring'.  If optional argument
CSTRING is non-nil, insert that string instead the character.  Optional
CHARSYM defaults to `this-command's symbol property `x-symbol-charsym'."
  (interactive "P")
  (x-symbol-list-restore)
  (or charsym (setq charsym (get this-command 'x-symbol-charsym)))
  (if cstring
      (setq charsym nil)
    (if (consp arg)
	(setq cstring (x-symbol-read-charsym-token charsym)
	      charsym nil
	      arg -1)
      (setq cstring (gethash charsym x-symbol-cstring-table))))
  (cond (isearch-mode
	 (if cstring (isearch-process-search-string cstring cstring)))
	((null cstring)
	 (error "Charsym %s has no character" charsym))
	(buffer-read-only
	 (kill-new cstring)
	 (display-message 'message
	   (if charsym
	       (x-symbol-info charsym x-symbol-language nil
			      (x-symbol-fancy-value 'x-symbol-info-intro-yank
						    'substitute-command-keys))
	     (concat (x-symbol-fancy-value 'x-symbol-info-intro-yank
					   'substitute-command-keys)
		     cstring))))
	(t
	 (if (natnump (setq arg (prefix-numeric-value arg)))
	     (or buffer-read-only
		 (null charsym)
		 (funcall x-symbol-valid-charsym-function charsym)
		 (error "Charsym %s not valid in current buffer" charsym))
	   (setq arg (- arg)))
	 (while (>= (decf arg) 0) (insert cstring)))))


;;;===========================================================================
;;;  Read token
;;;===========================================================================

;;;###autoload
(defun x-symbol-read-language (prompt default &optional predicate)
  "Read token language in the minibuffer with completion.
Use PROMPT in minibuffer.  If the inserted string is empty, use DEFAULT
as return value.  If PREDICATE non-nil, only match languages if
PREDICATE with argument (NAME . LANGUAGE) returns non-nil."
  (let* ((languages (cons (cons x-symbol-charsym-name nil)
			  (mapcar (lambda (x) (cons (cdr x) (car x)))
				  x-symbol-language-alist)))
	 (completion-ignore-case t)
	 (language (completing-read prompt languages predicate t nil
				    'x-symbol-language-history)))
    (if (string-equal language "")
	default
      (cdr (assoc language languages)))))

(defun x-symbol-read-token (&optional arg currentp)
  "Select language and token to insert a character.
Use `x-symbol-language' if optional CURRENTP is non-nil.  If a number or
nil, argument ARG is passed to `x-symbol-insert-command'."
  (interactive "P")
  (let* ((arg-strings (x-symbol-prefix-arg-texts arg))
	 (language (if currentp
		       x-symbol-language
		     (x-symbol-read-language
		      (format "Select %s by token language (current %s): "
			      (car arg-strings) (x-symbol-language-text))
		      x-symbol-language)))
	 (decode-obarray (if language
			     (x-symbol-generated-decode-obarray
			      (x-symbol-language-value
			       'x-symbol-generated-data language))
			   x-symbol-charsym-decode-obarray))
	 (completion (try-completion "" decode-obarray))
	 (completion-ignore-case (if language
				     (x-symbol-grammar-case-function
				      (x-symbol-language-value
				       'x-symbol-token-grammar language))))
	 (cstring (completing-read
		   (format "Insert %s %s: " (car arg-strings) (cdr arg-strings))
		   decode-obarray
		   (and (or (null arg) (natnump arg))
			(lambda (x)
			  (funcall x-symbol-valid-charsym-function
				   (car (symbol-value x)))))
		   t
		   (and (stringp completion) completion)
		   'x-symbol-token-history)))
    (if (string-equal cstring "")
	(error "No token entered")
      (if (consp arg)
	  (x-symbol-insert-command -1 nil cstring)
	(x-symbol-insert-command
	 arg (car (symbol-value (intern-soft cstring decode-obarray))))))))

(defun x-symbol-read-token-direct (&optional arg)
  "Select token in current language to insert a character.
Argument ARG is passed to `x-symbol-insert-command'."
  (interactive "P")
  (x-symbol-read-token arg t))


;;;===========================================================================
;;;  GRID
;;;===========================================================================

;;;###autoload
(defun x-symbol-grid (&optional arg)
  "Displays characters in a grid-like fashion for mouse selection.
Display global or language dependent grid, see `x-symbol-local-grid'.
See `x-symbol-list-mode' for key and mouse bindings.  Without optional
argument ARG and non-nil `x-symbol-grid-reuse', just popup old grid
buffer if it already exists, but is not displayed.  Store window
configuration current before the invocation if `x-symbol-temp-grid' is
non-nil, see `x-symbol-list-restore'."
  (interactive "P")
  (let* ((grid-alist (and x-symbol-local-grid
			  x-symbol-language
			  (x-symbol-generated-grid-alist
			   (x-symbol-language-value
			    'x-symbol-generated-data))))
	 (language (and grid-alist x-symbol-language))
	 (win-config (and x-symbol-temp-grid (current-window-configuration)))
	 ;;(ref-buffer (and x-symbol-temp-grid (current-buffer)))
	 (ref-buffer (current-buffer))
	 (default-enable-multibyte-characters t)
	 (buffer (x-symbol-language-text x-symbol-grid-buffer-format))
	 (font (and (fboundp 'face-font-instance)
		    (face-font-instance 'x-symbol-heading-face))))
    (x-symbol-init-input)
    (or grid-alist (setq grid-alist x-symbol-grid-alist))
    (and (null arg)
	 (get-buffer buffer)
	 (not (get-buffer-window buffer 'visible)) ; CW: new `visible'
	 (save-excursion
	   (set-buffer buffer)
	   ;; CW: in XEmacs, `pop-up-frames'=t seems to be broken.
	   (x-symbol-list-store ref-buffer win-config)
	   (funcall (or temp-buffer-show-function 'display-buffer) buffer)
	   (setq grid-alist nil)))	; exit
    (when grid-alist
      (save-excursion
	(ignore-errors
	  ;; CW: in XEmacs, `pop-up-frames'=t seems to be broken, ignore error
	  (with-output-to-temp-buffer buffer))
	(set-buffer buffer)
	(if (featurep 'scrollbar)
	    (set-specifier scrollbar-height 0 (current-buffer)))
	(setq truncate-lines t)
	(and font (featurep 'xemacs)
	     (set-face-font 'default font (current-buffer)))
	(setq tab-width x-symbol-grid-tab-width)
	(let ((max (- (x-symbol-window-width
		       (get-buffer-window buffer 'visible))
		      x-symbol-grid-tab-width))
	      charsyms charsym pos extent face
	      (inhibit-read-only t))
	  (while grid-alist
	    (setq extent (insert-face (concat (caar grid-alist) ": ")
				      'x-symbol-heading-face))
	    (set-extent-end-glyph extent x-symbol-heading-strut-glyph)
	    
	    (set-extent-property extent 'help-echo
				 (x-symbol-fancy-value
				  'x-symbol-grid-header-echo))
	    (insert "\t")
	    (setq charsyms (cdar grid-alist)
		  grid-alist (cdr grid-alist))
	    (while charsyms
	      (unless (memq (setq charsym (pop charsyms))
			    x-symbol-grid-ignore-charsyms)
		(if (>= (current-column) max) (insert "\n\t"))
		(setq pos (point))
		(insert (gethash charsym x-symbol-fontified-cstring-table)
			"\t")
		(setq extent (add-list-mode-item pos (point) nil t charsym))
		;; for no-Mule -- CW: cannot be avoided, in x-symbol-nomule?
		(if (fboundp 'set-extent-priority)
		    (set-extent-priority extent -10))
		(set-extent-property extent 'help-echo 'x-symbol-highlight-echo)
		(and language
		     (setq face (car (x-symbol-charsym-face charsym language)))
		     (set-extent-face extent face))))
	    (if grid-alist (insert "\n"))))
	(set-buffer-modified-p nil)
	(x-symbol-list-mode language ref-buffer win-config)
	(setq tab-width x-symbol-grid-tab-width)
	(and font (featurep 'xemacs)
	     (set-face-font 'default font (current-buffer)))))))


;;;===========================================================================
;;;  General Insertion
;;;===========================================================================

(defun x-symbol-replace-from (from cstring &optional ignore)
  "Replace buffer contents between FROM and `point' by CSTRING.
If IGNORE is non-nil, the current command, which should be a
self-inserting character, is ignored by providing a zero prefix
argument.  Also prepare the use of `undo' and `unexpand-abbrev'."
  (or (stringp cstring)
      (setq cstring (gethash cstring x-symbol-cstring-table)))
  (when cstring
    (and ignore
	 (null prefix-arg)
	 (self-insert-command 1))
    (undo-boundary)
    (let ((pos (point)))
      (if (listp buffer-undo-list)	; put point position on undo-list...
	  (push pos buffer-undo-list))	; ...necessary for aggressive CONTEXT
      (setq x-symbol-last-abbrev cstring ; allow use of `unexpand-abbrev'
	    last-abbrev-location from
	    last-abbrev 'x-symbol-last-abbrev
	    last-abbrev-text (buffer-substring from pos))
      ;; `replace-region': first insert, then delete (reason: markers)
      (insert-before-markers cstring)
      (delete-region from pos)
      (if ignore (setq prefix-arg 0))
      (setq abbrev-start-location pos	; this hack stops expand-abbrev
	    abbrev-start-location-buffer (current-buffer)))
    (undo-boundary)
    t))


;;;===========================================================================
;;;  Input method TOKEN
;;;===========================================================================

;; Hint: if you trace one of these function in XEmacs, you break the handling
;; of consecutive `self-insert-command's...

(defvar x-symbol-token-search-prelude-size 10)

(defun x-symbol-replace-token (&optional command-char)
  "Replace token by corresponding character.
If COMMAND-STRING is non-nil, check token shape."
  (let* ((grammar (x-symbol-language-value 'x-symbol-input-token-grammar))
	 (generated (x-symbol-language-value 'x-symbol-generated-data))
	 (decode-obarray (x-symbol-generated-decode-obarray generated))
	 (case-fold-search (x-symbol-grammar-case-function ;#dynamic
			    (x-symbol-language-value 'x-symbol-token-grammar)))
	 (input-regexp (car grammar))
	 (input-spec (cdr grammar))
	 (beg (- (point) (x-symbol-generated-max-token-len generated)
		 x-symbol-token-search-prelude-size))
	 (res (save-excursion
		(save-restriction
		  (narrow-to-region (max beg (point-at-bol)) (point))
		  (if (functionp input-spec)
		      (funcall input-spec input-regexp decode-obarray
			       command-char)
		    (x-symbol-match-token-before input-spec
						 (list input-regexp)
						 decode-obarray
						 command-char))))))
    (if res (x-symbol-replace-from (car res) (cadr res)))))

(defun x-symbol-match-token-before (contexts token-regexps decode-obarray
					     command-char)
  (let ((case-fn (if (functionp case-fold-search) case-fold-search))
	(before-context (car contexts))
	(after-context (cdr contexts))
	token charsym beg esc-char shape bad-regexp)
    (when (characterp before-context)
      (or (memq before-context '(?\ ?\t ?\n ?\r nil)) ; or warning?
	  (setq esc-char before-context))
      (setq before-context nil))
    (or before-context after-context (setq contexts nil))

    (while token-regexps
      (goto-char (point-min))
      (and (re-search-forward (pop token-regexps) nil t)
	   (setq beg (match-beginning 0))
	   (eobp)			; regexp should always end with \\'
	   (setq token
		 (symbol-value
		  (intern-soft
		   (if case-fn
		       (funcall case-fn (buffer-substring beg (point-max)))
		     (buffer-substring beg (point-max)))
		   decode-obarray)))
	   (cond ((and esc-char (eq (char-before beg) esc-char)
		       (x-symbol-even-escapes-before-p (1- beg) esc-char)))
		 ((not (and contexts (setq shape (cadr token))))
		  (if (setq charsym (car token)) (setq token-regexps nil)))
		 ((and (setq bad-regexp (assq shape after-context))
		       (not (memq command-char '(?\ ?\t ?\n ?\r nil)))
		       (string-match (cdr bad-regexp)
				     (char-to-string command-char))))
		 ((and (setq bad-regexp (assq shape before-context))
		       (not (memq (char-before beg) '(?\ ?\t ?\n ?\r nil)))
		       (string-match (cdr bad-regexp)
				     (char-to-string (char-before beg)))))
		 ((setq charsym (car token))
		  (setq token-regexps nil)))))
    (and charsym
	 (not (and x-symbol-unique (cddr token)))
	 (funcall x-symbol-valid-charsym-function charsym)
	 (cons beg token))))

(defun x-symbol-token-input ()
  "Provide input method TOKEN.
Called in `x-symbol-pre-command-hook', see `x-symbol-token-input'."
  (cond ((not (and x-symbol-language x-symbol-token-input)))
	((and prefix-arg (not (zerop (prefix-numeric-value prefix-arg)))))
	((and (symbolp this-command)
	      (fboundp this-command)
	      (or (get this-command 'x-symbol-input)
		  (and (symbolp (symbol-function this-command))
		       (get (symbol-function this-command) 'x-symbol-input))))
	 (x-symbol-replace-token))
	((not (eq this-command 'self-insert-command)))
	(t
	 (x-symbol-replace-token (if prefix-arg nil last-command-char)))))


;;;===========================================================================
;;;  Input method context
;;;===========================================================================

;;;###autoload
(defun x-symbol-modify-key (&optional beg end)
  "Modify key for input method CONTEXT.
If character before point is a char alias, resolve alias, see
\\[x-symbol-unalias].  If character before point is a character
supported by package x-symbol, replace it by the next valid character in
the modify-to chain.

Otherwise replace longest context before point by a character which
looks similar to it.  See also \\[x-symbol-rotate-key] and
`x-symbol-electric-input'.  If called interactively and if the region is
active, restrict context to the region between BEG and END."
  (interactive (and (region-active-p)
		    (list (region-beginning) (region-end))))
  (if (and beg end)
      (save-excursion
	(save-restriction
	  (narrow-to-region beg end)
	  (goto-char (point-max))
	  (x-symbol-modify-key)))
    (x-symbol-init-input)
    (let ((pos+charsym (or (x-symbol-valid-context-charsym
			    x-symbol-context-atree 'x-symbol-modify-to)
			   (x-symbol-next-valid-charsym-before
			    'x-symbol-modify-to 'x-symbol-rotate-to))))
      (if (and pos+charsym
	       (null (x-symbol-call-function-or-regexp
		      x-symbol-context-ignore
		      (buffer-substring (car pos+charsym) (point))
		      (cdr pos+charsym))))
	  (x-symbol-replace-from (car pos+charsym) (cdr pos+charsym))
	(error "Nothing to modify")))))

;;;###autoload
(defun x-symbol-rotate-key (&optional arg beg end)
  "Rotate key for input method CONTEXT.
If character before point is a char alias, resolve alias, see
\\[x-symbol-unalias].  If character before point is a character
supported by package x-symbol, replace it by the next valid character in
the rotate-to chain.  With optional prefix argument ARG, the
\"direction\" of the new character should be according to ARG and
`x-symbol-rotate-prefix-alist'.

Otherwise replace longest context before point by a character which
looks similar to it, assuming an additional context suffix
`x-symbol-rotate-suffix-char'.  See also \\[x-symbol-modify-key] and
`x-symbol-electric-input'.  If called interactively and if the region is
active, restrict context to the region between BEG and END."
  (interactive (cons current-prefix-arg
		     (and (region-active-p)
			  (list (region-beginning) (region-end)))))
  (if (and beg end)
      (save-excursion
	(save-restriction
	  (narrow-to-region beg end)
	  (goto-char (point-max))
	  (x-symbol-rotate-key arg)))
    (x-symbol-init-input)
    (if arg
	(let* ((pos+charsym (x-symbol-charsym-after (1- (point))))
	       (charsym (cdr pos+charsym))
	       (direction (assq (prefix-numeric-value arg)
				x-symbol-rotate-prefix-alist)))
	  (if charsym
	      (if direction
		  (if (setq charsym
			    (x-symbol-next-valid-charsym
			     charsym (cdr direction) 'x-symbol-rotate-to))
		      (x-symbol-replace-from (car pos+charsym) charsym)
		    (error "Cannot rotate %s to direction %s"
			   (cdr pos+charsym) (cdr direction)))
		(error "Prefix argument %s does not represent a valid direction"
		       arg))
	    (error "Nothing to rotate")))
      (let ((pos+charsym (or (x-symbol-valid-context-charsym
			      (assq x-symbol-rotate-suffix-char
				    x-symbol-context-atree)
			      'x-symbol-modify-to)
			     (x-symbol-next-valid-charsym-before
			      'x-symbol-rotate-to 'x-symbol-modify-to))))
	(if (and pos+charsym
		 (null (x-symbol-call-function-or-regexp
			x-symbol-context-ignore
			(buffer-substring (car pos+charsym) (point))
			(cdr pos+charsym))))
	    (x-symbol-replace-from (car pos+charsym) (cdr pos+charsym))
	  (error "Nothing to rotate"))))))

(defun x-symbol-electric-input ()
  "Provide input method ELECTRIC.
Called in `x-symbol-post-command-hook', see `x-symbol-electric-input'."
  (setq x-symbol-electric-pos
	(and x-symbol-electric-input
	     x-symbol-mode
	     (symbolp this-command)
	     (fboundp this-command)
	     (or (eq this-command 'self-insert-command)
		 (get this-command 'x-symbol-input)
		 (and (symbolp (symbol-function this-command))
		      (get (symbol-function this-command) 'x-symbol-input)))
	     (null current-prefix-arg)
	     (not (and (local-variable-p 'current-input-method (current-buffer))
		       (equal current-input-method "x-symbol")))
	     (or x-symbol-electric-pos (1- (point)))))
  (if x-symbol-electric-pos
      (let ((pos+charsym (x-symbol-valid-context-charsym
			  x-symbol-electric-atree))
	    context)
	(and pos+charsym
	     (>= (car pos+charsym) x-symbol-electric-pos)
	     (setq context (buffer-substring (car pos+charsym) (point)))
	     (or (let ((pos+charsym2 (x-symbol-valid-context-charsym
				      x-symbol-context-atree)))
		   (and pos+charsym2
			(> (car pos+charsym) (car pos+charsym2)))) ; suffix
		 (x-symbol-call-function-or-regexp
		  x-symbol-context-ignore context (cdr pos+charsym))
		 (x-symbol-call-function-or-regexp
		  x-symbol-electric-ignore context (cdr pos+charsym))
		 (x-symbol-call-function-or-regexp
		  (x-symbol-language-value 'x-symbol-electric-ignore)
		  context (cdr pos+charsym))
		 (x-symbol-replace-from (car pos+charsym)
					(cdr pos+charsym)))))))


;;;===========================================================================
;;;  Keyboard Completion Help
;;;===========================================================================

(defun x-symbol-help-mapper (key binding)
  "Collect help for specific KEY with BINDING."
  (let ((x-symbol-help-keys (cons (single-key-description key)
				  x-symbol-help-keys))
	charsym)
    (if (keymapp binding)
	(map-keymap #'x-symbol-help-mapper binding t)
      (and (commandp binding)
	   (symbolp binding)
	   (setq charsym (get binding 'x-symbol-charsym))
	   (or (eq x-symbol-help-language t)
	       (funcall x-symbol-valid-charsym-function charsym
			x-symbol-help-language))
	   (if (or (cdr x-symbol-help-keys)
		   (null (member (car x-symbol-help-keys)
				 (eval-when-compile
				   (mapcar 'single-key-description
					   (append "1234567890" nil))))))
	       (push (cons x-symbol-help-keys charsym)
		     x-symbol-help-completions)
	     (push (cons x-symbol-help-keys charsym)
		   x-symbol-help-completions1))))))

(defun x-symbol-help-output (arg keys)
  "Popup completions buffer for KEYS with prefix argument ARG."
  (let ((win-config (and x-symbol-temp-help (current-window-configuration)))
	(ref-buffer (current-buffer))
	(read-only buffer-read-only)
	(mode-on x-symbol-mode)
	(language x-symbol-language)
	(default-enable-multibyte-characters t)
	(arg-texts (x-symbol-prefix-arg-texts arg)))
    (with-output-to-temp-buffer x-symbol-completions-buffer
      (save-excursion
	(set-buffer x-symbol-completions-buffer)
	(message "Working...")
	(setq ctl-arrow 'ts)		; non-t-non-nil
	(insert "You are typing a x-symbol key sequence to insert a "
		(car arg-texts) " " (cdr arg-texts)
		(if read-only "\ninto read-only buffer \"" "\ninto buffer \"")
		(buffer-name ref-buffer)
		(if language
		    (x-symbol-language-text
		     (if mode-on "\" (%s)" "\" (%s, turned-off)")
		     language)
		  "\"")
		".\nSo far you have typed \""
		(key-description keys)
		"\".  "
		(if (eq x-symbol-help-language t)
		    "Completions from here are:\n"
		  "Valid completions from here are:\n"))
	(while x-symbol-help-completions
	  (insert "\n")
	  (let ((completion (pop x-symbol-help-completions))
		(start (point)))
	    (when completion
	      (insert (mapconcat #'identity (reverse (car completion)) " "))
	      ;; no nreverse!
	      (indent-to 16)
	      (insert (x-symbol-info (cdr completion) language nil ""))
	      (set-extent-property
	       (add-list-mode-item start (point) nil t (cdr completion))
	       'help-echo 'x-symbol-highlight-echo))))
	(x-symbol-list-mode language ref-buffer win-config)))))

(defun x-symbol-help (&optional arg)
  ;; checkdoc-params: (arg)
  "Display some help during a x-symbol key sequence.
Displays some info for all characters which can be inserted by a key
sequence starting with the current one.  See `x-symbol-temp-help'."
  (interactive "P")
  (setq x-symbol-command-keys
	(or (nbutlast (append (this-command-keys) nil))
	    x-symbol-command-keys))
  (setq x-symbol-help-language
	(or (consp arg) (< (prefix-numeric-value arg) 0)
	    (and x-symbol-mode x-symbol-language)))
  (let* ((keys (apply 'vector x-symbol-command-keys))
	 (map (key-binding keys)))
    (while (and x-symbol-command-keys (not (keymapp map)))
      (setq x-symbol-command-keys (cdr x-symbol-command-keys)
	    keys (apply 'vector x-symbol-command-keys)
	    map (key-binding keys)))
    (or x-symbol-command-keys
	(error "Can't find map?  %s" (this-command-keys)))
    (setq x-symbol-help-completions nil
	  x-symbol-help-completions1 nil)
    (map-keymap #'x-symbol-help-mapper map t)
    (setq x-symbol-help-completions
	  (if x-symbol-help-completions1
	      (nconc (nreverse x-symbol-help-completions1)
		     (list nil)	; not! '(nil)
		     (nreverse x-symbol-help-completions))
	    (nreverse x-symbol-help-completions))
	  x-symbol-help-completions1 nil)
    (if x-symbol-help-completions
	(progn
	  (x-symbol-help-output arg keys)
	  ;; the code in x11/x-compose doesn't work here, this is easier anyway
	  (setq prefix-arg arg)
	  (setq unread-command-events x-symbol-command-keys))
      (ding)   ; CW: was (ding nil 'no-completion), not that important...
      (message (if (eq x-symbol-help-language t)
		   "%s [No completions]"
		 "%s [No valid completions]")
	       (key-description keys))
      ;; don't remember key sequence prefix until now
      (setq x-symbol-command-keys nil
	    unread-command-events nil))))
      ;;;(x-symbol-shrink-grid-buffer display))



;;;;##########################################################################
;;;;  Init code
;;;;##########################################################################


(defvar x-symbol-face-docstrings
   '("Face used for normal characters."
     "Face used for subscripts."
     "Face used for superscripts.")
   "Docstrings for special x-symbol faces.")

(defvar x-symbol-all-key-prefixes nil
  "Internal.  Key prefixes not shorter than `x-symbol-key-min-length'.")
(defvar x-symbol-all-key-chain-alist nil
  "Internal.  Alist with elements (CONTEXT CHARSYM...).")
(defvar x-symbol-all-horizontal-chain-alist nil
  "Internal.  Alist with elements (MODIFY-CONTEXT CHARSYM...).")
(defvar x-symbol-all-chain-subchains-alist nil
  "Internal.  Alist with elements (CHAIN-REP (FIRST . LAST)...).")
(defvar x-symbol-all-exclusive-context-alist nil
  "Internal.  Alist with elements (MODIFY-CONTEXT . CHAIN-REP).")


;;;===========================================================================
;;;  Tiny functions
;;;===========================================================================

(defalias 'x-symbol-table-grouping 'car)
(defalias 'x-symbol-table-aspects 'cadr)
(defalias 'x-symbol-table-score 'caddr)
(defalias 'x-symbol-table-input 'cadddr)
(defsubst x-symbol-table-prefixes (xs) (nth 4 xs))
(defsubst x-symbol-table-junk (xs) (nthcdr 5 xs))

(defsubst x-symbol-charsym-defined-p (charsym)
  (get charsym 'x-symbol-score))


;;;===========================================================================
;;;  Init code per cset, called from x-symbol-{mule/nomule}
;;;===========================================================================

(defun x-symbol-try-font-name-0 (font raise)
  (let ((sizes x-symbol-font-sizes)
	(idx 0)
	size args)
    (while sizes
      (if (string-match (caar sizes) font)
	  (setq size (cdar sizes)
		sizes nil)
	(setq sizes (cdr sizes))))
    (setq size (or (nth raise size) (car (last size))
		   (if (zerop raise) 14 12)))
    (while (string-match "%d" font idx)
      (push size args)
      (setq idx (match-end 0)))
    (when (string-match "%s" font)
      (push (nth raise x-symbol-font-family-postfixes) args))
    (if args (apply 'format font args) font)))

(defun x-symbol-try-font-name (fonts &optional raise)
  "Return name of first valid font in FONTS."
  (when fonts
    (let ((fonts1 fonts) result)
      (while fonts1
	(if (setq result (try-font-name
			  (x-symbol-try-font-name-0 (car fonts1) (or raise 0))))
	    (setq fonts1 nil)
	  (setq fonts1 (cdr fonts1))))
      (unless (or result (null raise))
	(lwarn 'x-symbol 'warning
	  "Cannot find font in %s"
	  (mapconcat (lambda (f) (x-symbol-try-font-name-0 f raise))
		     fonts
		     ", ")))
      result)))

(defun x-symbol-set-cstrings (charsym coding cstring fchar face)
  "Set cstrings of CHARSYM to CSTRING.
Set string with duplicatable text property FACE.  Also set file and buffer
cstrings if CODING is non-nil.  File cstrings are the representation as
8bit characters in file with encoding CODING.  Buffer cstrings are the
representation in the buffer.  Prefer using the buffer-cstring in
`x-symbol-default-coding' as the default cstring, all other cstrings
will be considered as char aliases, see \\[x-symbol-unalias]."
  (unless (and coding
	       (let ((fchar-table (cdr (assq coding x-symbol-fchar-tables)))
		     (bchar-table (cdr (assq coding x-symbol-bchar-tables))))
		 (unless fchar-table	; for 96 chars
		   (setq fchar-table
			 ;; Emacs uses :size directly, XEmacs uses higher prime
			 (make-hash-table :size 113 :test 'eq)) ; (primep 113)
		   (setq x-symbol-fchar-tables
			 (nconc x-symbol-fchar-tables
				(list (cons coding fchar-table)))))
		 (puthash charsym fchar fchar-table)
		 
		 (unless bchar-table	; for 96 chars
		   (setq bchar-table
			 ;; Emacs uses :size directly, XEmacs uses higher prime
			 (make-hash-table :size 113 :test 'eq)) ; (primep 113)
		   (setq x-symbol-bchar-tables
			 (nconc x-symbol-bchar-tables
				(list (cons coding bchar-table)))))
		 (puthash charsym cstring bchar-table)
		 (not (eq coding (or x-symbol-default-coding 'iso-8859-1))))
	       (gethash charsym x-symbol-cstring-table))
    (or (stringp cstring) (setq cstring (char-to-string cstring)))
    (puthash charsym cstring x-symbol-cstring-table)
    (puthash charsym
	     (if face
		 (let ((copy (copy-sequence cstring)))
		   (put-text-property 0 (length copy) 'face face copy)
		   copy)
	       cstring)
	     x-symbol-fontified-cstring-table)))


;;;===========================================================================
;;;  Init code per cset, MAIN: `x-symbol-init-cset'
;;;===========================================================================

(defun x-symbol-init-charsym-command (charsym)
  "Init self insert command for CHARSYM.  See `x-symbol-insert-command'."
  (let ((command (intern (format "x-symbol-INSERT-%s" charsym))))
    (fset command 'x-symbol-insert-command)
    (put charsym 'x-symbol-insert-command command)
    (put command 'isearch-command t)
    (put command 'x-symbol-charsym charsym)))

(defun x-symbol-init-charsym-input (charsym grouping score cset-score input
					    prefixes)
  "Check and init input definitions for CHARSYM.
Set GROUPING, SCORE, CSET-SCORE, INPUT, PREFIXES according to
`x-symbol-init-cset'."
  (let* ((group (car grouping))
	 (ginput (cdr (assq group x-symbol-group-input-alist)))
	 (subgroup (cadr grouping))
	 (opposite (caddr grouping))
	 (ascii (cadddr grouping))
	 (syntax (cdr (assq group x-symbol-group-syntax-alist)))
	 (syntax-special (assq subgroup (cdr syntax)))
	 context-strings electric-strings electric-ok
	 (case-fold-search nil))
    (unless ginput
      (warn "X-Symbol charsym %s: undefined group %S" charsym group)
      (setq group nil
	    ginput '(0)))
    (and subgroup (symbolp subgroup)
	 (setq subgroup (cdr (assq subgroup x-symbol-subgroup-string-alist))))
    (unless (or (stringp subgroup) (null subgroup))
      (warn "X-Symbol charsym %s: illegal subgroup %S" charsym (cadr grouping))
      (setq subgroup nil))
    (unless (symbolp opposite)
      (warn "X-Symbol charsym %s: illegal opposite %S" charsym opposite)
      (setq opposite nil))
    (unless (or (stringp ascii) (null ascii))
      (warn "X-Symbol charsym %s: illegal Ascii representation %S"
	    charsym ascii)
      (setq ascii nil))
    (if (numberp score)
	(setq score (+ score (car ginput)))
      (if score (warn "X-Symbol charsym %s: illegal score %S" charsym score))
      (setq score (car ginput)))
    (and (null input)
	 (stringp subgroup)
	 (progn
	   (setq input (mapcar (lambda (x)
				 (if (stringp x) (format x subgroup) x))
			       (cdr ginput)))
	   ;; accents: not only use "' " and " '", use "'" also
	   (and (string-equal subgroup " ")
		(progn
		  (while (eq (car (setq ginput (cdr ginput))) t))
		  (stringp (car ginput)))
		(push (format (car ginput) "") input))))
    (dolist (context (reverse input))
      (cond ((stringp context)
	     (push context context-strings)
	     (setq electric-ok t))
	    ((not (eq context t))
	     (warn "X-Symbol charsym %s: illegal input element %S"
		   charsym context))
	    (electric-ok
	     (push (car context-strings) electric-strings)
	     (setq electric-ok nil))
	    (t
	     (warn "X-Symbol charsym %s: misuse of input tag `t'" charsym))))
    (put charsym 'x-symbol-grouping
	 (and group (list group subgroup opposite ascii)))
    (put charsym 'x-symbol-syntax
	 (and syntax (cons (car syntax)
			   (and syntax-special opposite
				(cons (cdr syntax-special) opposite)))))
    (put charsym 'x-symbol-score (+ cset-score score))
    (put charsym 'x-symbol-context-strings context-strings)
    (put charsym 'x-symbol-electric-strings electric-strings)
    (put charsym 'x-symbol-electric-prefixes prefixes)))

(defun x-symbol-init-charsym-aspects (charsym aspects)
  "Check and init ASPECTS of CHARSYM.  See `x-symbol-init-cset'."
  (let (modify-aspects
	rotate-aspects
	aspect value type)
    (while (consp aspects)
      (setq aspect (pop aspects)
	    value (and (consp aspects) (pop aspects)))
      (cond ((setq type (assq aspect x-symbol-modify-aspects-alist))
	     (if (assq value (cdr type))
		 (setq modify-aspects (plist-put modify-aspects aspect value))
	       (warn "X-Symbol charsym %s: illegal modify aspect %s:%s"
		     charsym aspect value)))
	    ((setq type (assq aspect x-symbol-rotate-aspects-alist))
	     (if (assq value (cdr type))
		 (setq rotate-aspects (plist-put rotate-aspects aspect value))
	       (warn "X-Symbol charsym %s: illegal rotate aspect %s:%s"
		     charsym aspect value)))
	    (t
	     (warn "X-Symbol charsym %s: illegal aspect %s:%s"
		   charsym aspect value))))
    (unless (symbolp aspects)
      (warn "X-Symbol charsym %s: illegal parent %S" charsym aspects)
      (setq aspects nil))
    (put charsym 'x-symbol-modify-aspects (cons nil modify-aspects))
    (put charsym 'x-symbol-rotate-aspects (cons nil rotate-aspects))
    (put charsym 'x-symbol-parent (or aspects charsym))))

(eval-when-compile (defvar x-symbol-no-of-charsyms))

(defun x-symbol-init-cset (cset fonts table)
  "Define and initialize a new character set.
CSET looks like
  (((REGISTRY . CODING) LEADING CSET-SCORE) MULE-LEFT . MULE-RIGHT)

REGISTRY is the charset registry of the fonts in FONTS.  If CODING is
non-nil, characters defined in TABLE are considered to be 8bit
characters if `x-symbol-coding' has value CODING.  CSET-SCORE is the
base score for characters defined in TABLE, see below.

Under XEmacs/no-Mule, cstrings for characters defined in TABLE consist
of the character LEADING and the octet ENCODING, explained below, if
CODING is different to `x-symbol-default-coding'.  LEADING should be in
the range \\200-\\237.

Under XEmacs/Mule, MULE-LEFT and MULE-RIGHT are used.  They look like
  nil or (NAME) or (NAME DOCSTRING CHARS FINAL)
With the first form, no charset is used in that half of the font.  With
the second form, it is assumed that there exists a charset NAME.  The
third forms defines a new charset with name NAME, docstring DOCSTRING
and the charset properties CHARS and FINAL, see `make-charset' for
details.

FONTS look like (NORMAL-FONT SUBSCRIPT-FONT SUPERSCRIPT-FONT) where each
FONT is a list of fonts.  They are tried until the first which is
installed on your system, see `try-font-name'.

Each element of TABLE looks like:
  (CHARSYM ENCODING GROUPING ASPECTS SCORE INPUT PREFIXES) or
  (CHARSYM ENCODING . t)
Its character descriptions, not the ENCODING, can be shadowed by
elements in `x-symbol-user-table'.

Define a character with \"descriptions\" in current cset with encoding
ENCODING.  It is represented by the symbol CHARSYM.  If CHARSYM already
represents another character, the second form is used.  This is only
useful if both definitions were defined for csets with non-nil CODING.
In this case, only one of the characters are normally used, the others
are char aliases, see \\[x-symbol-unalias].

GROUPING = (GROUP SUBGROUP OPPOSITE ASCII).  GROUP defines the grid and
submenu headers of the character, see `x-symbol-header-groups-alist'.
SUBGROUP with `x-symbol-subgroup-string-alist' defines some order in the
grid.  OPPOSITE is used for \\[x-symbol-rotate-key] if no other
character in the rotate chain has been defined.  ASCII is the ascii
representation, see `x-symbol-translate-to-ascii'.

GROUP and SUBGROUP define the default INPUT and SCORE, see below and
`x-symbol-group-input-alist', and default ascii representations, see
`x-symbol-charsym-ascii-groups'.  GROUP, SUBGROUP and OPPOSITE define
the char syntax under XEmacs/Mule, see `x-symbol-group-syntax-alist'.

ASPECTS = PARENT | (ASPECT VALUE . PARENT).  Define modify and rotate
aspects with corresponding values, see `x-symbol-modify-aspects-alist'
and `x-symbol-rotate-aspects-alist'.  If PARENT is non-nil, CHARSYM and
PARENT are in the same component and CHARSYM inherits all remaining
aspects from PARENT which should be defined in the same or earlier csets
as the original definition of CHARSYM.  See `x-symbol-init-input'.

The charsym score is the addition of SCORE, or 0 if nil, the GROUP
SCORE, see `x-symbol-group-input-alist', and CSET-SCORE, see above.

INPUT = nil | (CONTEXT . INPUT) | (t CONTEXT . INPUT).  Contexts
defining key bindings and contexts for input method context.  If CONTEXT
is prefixed by t, it is also a context for input method electric.  The
first CONTEXT is called modify context and determines the modify-to
chain.  If INPUT is nil, use INPUT from `x-symbol-group-input-alist'
with substitutions SUBGROUP/%s.  See `x-symbol-init-input' for details.

PREFIXES are charsyms which are considered prefixes for input method
electric.  Default prefixes are provided, though."
  (let ((size (if (featurep 'xemacs)
		  x-symbol-no-of-charsyms
		(x-symbol-get-prime-for x-symbol-no-of-charsyms))))
    (unless x-symbol-cstring-table
      (setq x-symbol-cstring-table
	    (make-hash-table :size size :test 'eq)))
    (unless x-symbol-fontified-cstring-table
      (setq x-symbol-fontified-cstring-table
	    (make-hash-table :size size :test 'eq)))
    (unless x-symbol-charsym-decode-obarray
      (setq x-symbol-charsym-decode-obarray
	    (make-vector (x-symbol-get-prime-for x-symbol-no-of-charsyms) 0))))
  ;;--------------------------------------------------------------------------
  (setq x-symbol-input-initialized nil)
  (let* ((faces (x-symbol-make-cset cset
				    (if (stringp (car fonts))
					(list fonts fonts fonts)
				      fonts)))
	 (cset-score (x-symbol-cset-score cset))
	 (coding (x-symbol-cset-coding cset))
	 (force-use (or x-symbol-latin-force-use
			(eq (or x-symbol-default-coding 'iso-8859-1) coding)))
	 new-charsyms)
    (unless faces
      (when fonts
	(warn (if (and coding force-use)
		  "X-Symbol characters with registry %S will look strange"
		"X-Symbol characters with registry %S are not used")
	      (x-symbol-cset-registry cset))))
    (dolist (entry table)
      (let ((charsym (car entry))
	    definition)
	(if (or faces (and coding force-use))
	    (x-symbol-make-char cset (cadr entry) charsym (car faces) coding))
	(set (intern (symbol-name charsym) x-symbol-charsym-decode-obarray)
	     (list charsym))
	(if (memq (cddr entry) '(t unused))
	    (if coding
		(if (x-symbol-charsym-defined-p charsym)
		    (if (eq (cddr entry) 'unused)
			(warn "X-Symbol charsym %s: redefinition as unused"
			      charsym))
		  (if (eq (cddr entry) 'unused)
		      (push charsym new-charsyms)
		    (warn "X-Symbol charsym %s: alias without definition"
			  charsym)))
	      (warn "X-Symbol charsym %s: alias or unused without coding system"
		    charsym))
	  (if (x-symbol-charsym-defined-p charsym)
	      (progn
		(warn "X-Symbol charsym %s: redefinition (not used)" charsym)
		(or (assq charsym new-charsyms)
		    (assq charsym x-symbol-all-charsyms)
		    (push charsym new-charsyms))) ; ie, re-run
	    (push charsym new-charsyms)
	    (setq definition (cddr (or (assq charsym x-symbol-user-table)
				       entry)))
	    (when (x-symbol-table-junk definition)
	      (warn "X-Symbol charsym %s: unused elements in definition"
		    charsym))
	    (x-symbol-init-charsym-command charsym)
	    (x-symbol-init-charsym-input charsym
					 (x-symbol-table-grouping definition)
					 (x-symbol-table-score definition)
					 cset-score
					 (x-symbol-table-input definition)
					 (x-symbol-table-prefixes definition))
	    (x-symbol-init-charsym-aspects charsym
					   (x-symbol-table-aspects
					    definition))))))
    (x-symbol-init-charsym-syntax new-charsyms)	; after all (reason: opposite)
    (setq x-symbol-all-charsyms		; cosmetic reverse
	  (nconc x-symbol-all-charsyms (nreverse new-charsyms)))))


;;;===========================================================================
;;;  New data-type atree
;;;===========================================================================

(defun x-symbol-make-atree ()
  "Create a new association tree."
  (list nil))

(defun x-symbol-atree-push (value key atree)
  "Insert VALUE as the association for KEY in ATREE.
KEY should be a string, VALUE is typically recovered by calling
`x-symbol-match-before'."
  (let ((path (nreverse (append key nil)))
	branch)
    (while path
      (if (setq branch (assoc (car path) (cdr atree)))
	  (setq atree (cdr branch))
	(setq branch (list (car path) nil))
	(setcdr atree (cons branch (cdr atree)))
	(setq atree (cdr branch)))
      (setq path (cdr path)))
    (setcar atree value)))


;;;===========================================================================
;;;  Charsym components
;;;===========================================================================

(defun x-symbol-component-root-p (node)
  "Non-nil, if NODE is the root of a symbol component."
  (listp (get node 'x-symbol-component)))

(defun x-symbol-component-elements (node)
  "Return all elements in symbol component of NODE."
  (or (listp (get node 'x-symbol-component))
      (setq node (get node 'x-symbol-component)))
  (or (get node 'x-symbol-component)
      (list node)))

(defun x-symbol-component-merge (node1 node2)
  "Merge components of NODE1 and NODE2, return root of merged component."
  (or (listp (get node1 'x-symbol-component))
      (setq node1 (get node1 'x-symbol-component)))
  (or (eq node1 node2)
      (eq node1 (get node2 'x-symbol-component))
      (let ((elements2 (x-symbol-component-elements node2)))
	(when node1
	  (put node1 'x-symbol-component
	       (nconc (x-symbol-component-elements node1) elements2))
	  (while elements2
	    (put (pop elements2) 'x-symbol-component node1)))))
  node1)

(defun x-symbol-component-space (root prop)
  "Classify component of ROOT according to symbol property PROP.
Return an alist with elements (PROP-VALUE NODE...) where `cdr' of the
symbol property PROP of all NODEs are `equal' to PROP-VALUE."
  (let (space)
    (dolist (charsym (x-symbol-component-elements root))
      (x-symbol-push-assoc charsym (cdr (get charsym prop)) space))
    space))


;;;===========================================================================
;;;  Code for charsym aspects
;;;===========================================================================

(defun x-symbol-modify-less-than (charsym1 charsym2)
  "Non-nil, if CHARSYM1 has a lower modify score than CHARSYM2."
  (< (car (get charsym1 'x-symbol-modify-aspects))
     (car (get charsym2 'x-symbol-modify-aspects))))

(defun x-symbol-inherit-aspects (charsym prop parent)
  "CHARSYM inherits all aspects in `cdr' of property PROP from PARENT.
The `cdr' of properties PROP of CHARSYM and PARENT should be plists."
  (let ((aspects (cdr (get charsym prop))))
    (x-symbol-do-plist (aspect value (cdr (get parent prop)))
      (or (plist-member aspects aspect)
	  (setq aspects (plist-put aspects aspect value))))
    (put charsym prop (cons nil aspects))))

(defun x-symbol-compute-aspects (charsym prop score-alists score)
  "Compute CHARSYM's aspects stored in PROP with their scores.
Each element of SCORE-ALISTS looks like (ASPECT (VALUE . VSCORE)...).
Order aspects according to SCORE-ALISTS.  For all ASPECTs with their
VALUEs, add corresponding VSCOREs to SCORE.  Finally, set car of PROP to
the sum."
  (let* ((aspect-plist (cdr (get charsym prop)))
	 (aspect-alist
	  (mapcar (lambda (elem)
		    (let ((type (assq (plist-get aspect-plist (car elem))
				      (cdr elem))))
		      (if type (setq score (+ score (cdr type))))
		      (cons (car elem) (car type))))
		  score-alists)))
    (put charsym prop (cons score (destructive-alist-to-plist aspect-alist)))))

(defun x-symbol-init-aspects ()
  "Initialize the aspects of all currently defined charsyms.
This includes component merging, inheritance and aspect scores."
  (let (parent)
    ;; Check parents ---------------------------------------------------------
    (dolist (charsym x-symbol-all-charsyms)
      (when (setq parent (get charsym 'x-symbol-parent))
	(put charsym 'x-symbol-component nil)
	(if (eq charsym parent)
	    (remprop charsym 'x-symbol-parent)
	  (unless (x-symbol-charsym-defined-p parent)
	    (warn "X-Symbol charsym %s: undefined parent %s" charsym parent)
	    (remprop charsym 'x-symbol-parent)))))
    ;; Aspects inheritance, component building -------------------------------
    (dolist (charsym
	     ;; Maximum path length is small enough => fast enough
	     (x-symbol-dolist-delaying (charsym x-symbol-all-charsyms)
		 (and (setq parent (get charsym 'x-symbol-parent))
		      (get parent 'x-symbol-parent))
	       (when parent
		 (x-symbol-inherit-aspects charsym 'x-symbol-modify-aspects
					   parent)
		 (x-symbol-inherit-aspects charsym 'x-symbol-rotate-aspects
					   parent)
		 (x-symbol-component-merge parent charsym)
		 (remprop charsym 'x-symbol-parent))))
      (warn "X-Symbol charsym %s: circular inheritance %s"
	    charsym (get charsym 'x-symbol-parent))))
  ;; Compute aspects scores --------------------------------------------------
  (dolist (charsym x-symbol-all-charsyms)
    (when (get charsym 'x-symbol-insert-command)
      (x-symbol-compute-aspects charsym 'x-symbol-modify-aspects
				x-symbol-modify-aspects-alist
				(get charsym 'x-symbol-score))
      (x-symbol-compute-aspects charsym 'x-symbol-rotate-aspects
				x-symbol-rotate-aspects-alist 0)
      (remprop charsym 'x-symbol-parent)
      (remprop charsym 'x-symbol-modify-to)
      (remprop charsym 'x-symbol-rotate-to))))


;;;===========================================================================
;;;  Init global modify chain/subchain alists
;;;===========================================================================

(defun x-symbol-sort-modify-chain (chain)
  "Sort charsyms in CHAIN according to modify score.
Issue warning of two charsyms have the same score."
  (setq chain (sort chain 'x-symbol-modify-less-than))
  (let (score previous-score previous-charsym)
    (dolist (charsym chain)
      (setq score (car (get charsym 'x-symbol-modify-aspects)))
      (and previous-charsym
	   (= previous-score score)
	   (warn "X-Symbol charsyms %s and %s: same modify score %d"
		 previous-charsym charsym score))
      (setq previous-score score
	    previous-charsym charsym)))
  chain)

(defun x-symbol-init-horizontal/key-alist (chain contexts)
  "Create horizontal and key chains for all charsyms in CHAIN.
Do it for all contexts in CHAIN starting with CONTEXTS.  The first
context in CONTEXTS is the modify context.  Also set key prefixes."
  (dolist (charsym chain)
    (setq contexts (or (get charsym 'x-symbol-context-strings)
		       contexts))
    (x-symbol-push-assoc charsym (car contexts)
			 x-symbol-all-horizontal-chain-alist)
    (dolist (key contexts)
      (unless (x-symbol-push-assoc charsym key x-symbol-all-key-chain-alist)
	(while (and (> (length key) x-symbol-key-min-length)
		    (null (member (setq key (substring key 0 -1))
				  x-symbol-all-key-prefixes)))
	  (push key x-symbol-all-key-prefixes))))))

(defun x-symbol-init-exclusive-alist (chain context)
  "Check whether CHAIN uses its CONTEXT exclusively.
If so, store all subchains in `x-symbol-all-chain-subchains-alist', in
reverse order.  If not, delete previously stored subchains for CONTEXT."
  (let ((chain-rep (car chain))
	subchain-beg subchain-end subchains
	(exclusive t)
	charsym next-context temp)
    (while chain
      (setq subchain-beg (pop chain)
	    subchain-end subchain-beg)
      (while (and (setq charsym (car chain))
		  (or (null (setq next-context
				  (car (get charsym
					    'x-symbol-context-strings))))
		      (string-equal next-context context)))
	(setq subchain-end charsym)
	(setq chain (cdr chain)))
      (push (cons subchain-beg subchain-end) subchains)
      ;; Delete subchains for chain which previously used the same context
      ;; exclusively.
      (if (setq temp (assoc context x-symbol-all-exclusive-context-alist))
	  (progn
	    (setq exclusive nil)
	    (x-symbol-set-assq nil (cdr temp)
			       x-symbol-all-chain-subchains-alist)
	    (setcdr temp nil))		; for debugging
	(push (cons context chain-rep) x-symbol-all-exclusive-context-alist))
      (setq context next-context))
    ;; Store begin and end of subchains, if all contexts were used exclusively.
    (x-symbol-set-assq (and exclusive subchains) chain-rep
		       x-symbol-all-chain-subchains-alist)))


;;;===========================================================================
;;;  Init modify and rotate chains, context and electric atrees, keys
;;;===========================================================================

(defun x-symbol-init-horizontal-chain (chain previous)
  "Set modify-to behavior for all charsyms in CHAIN.
PREVIOUS modifies to the first charsym in CHAIN."
  ;; Warning about same scores will appear when defining key bindings
  (dolist (charsym chain)
    (put previous 'x-symbol-modify-to charsym)
    (setq previous charsym)))

(defun x-symbol-init-exclusive-chain (subchains previous)
  "Connect SUBCHAINS since all their contexts are used exclusively.
PREVIOUS should be the first charsym of the chain."
  (dolist (subchain subchains)		; subchains are reversed
    (put (cdr subchain) 'x-symbol-modify-to previous)
    (setq previous (car subchain))))

(defun x-symbol-init-rotate-chain (chain)
  "Set rotate-to behavior for all charsyms in CHAIN.
Divide CHAIN in blocks containing charsyms with the same rotate score
which are sorted according to their modify score.  The blocks are sorted
according to their rotate score.  All charsyms in a block rotate to the
first charsym in the next block."
  (let (blocks)
    (dolist (charsym chain)
      (x-symbol-push-assq charsym
			  (car (get charsym 'x-symbol-rotate-aspects))
			  blocks))
    (setq blocks (mapcar (lambda (block)
			   (sort (cdr block) 'x-symbol-modify-less-than))
			 (sort blocks 'car-less-than-car)))
    ;; For each CHARSYM in a BLOCK, set `rotate-to' to (circular) next BLOCK.
    (let ((last-block (car (last blocks))))
      (dolist (block blocks)
	(dolist (charsym last-block)
	  (put charsym 'x-symbol-rotate-to block))
	(setq last-block block)))))

(defun x-symbol-init-context-atree (context chain)
  "Init atrees for input method CONTEXT and ELECTRIC for CONTEXT.
\\[x-symbol-modify-key] modifies CONTEXT to the first charsym in CHAIN.
Prefixes of CONTEXT could have been already converted to x-symbol
characters.  Contexts with these prefixes being replaced by the
corresponding cstring of the x-symbol character are also considered."
  (let ((charsym (car chain)))	; lowest score
    (x-symbol-atree-push charsym context x-symbol-context-atree)
    (if (member context (get charsym 'x-symbol-electric-strings))
	(x-symbol-atree-push charsym context x-symbol-electric-atree)))
  (let ((len (length context))
	prefix-chain prefix-cstring)
    (while (> (decf len) 0)
      (when (setq prefix-chain (assoc (substring context 0 len)
				      x-symbol-all-key-chain-alist))
	(dolist (prefix (cdr prefix-chain))
	  (catch 'x-symbol-init-context-atree
	    (or (setq prefix-cstring (gethash prefix x-symbol-cstring-table))
		(throw 'x-symbol-init-context-atree t))
	    (let ((context1 (concat prefix-cstring (substring context len))))
	      ;; If any of the charsyms defines PREFIX as an electric prefix,
	      ;; use that one as the target.
	      (dolist (charsym chain)
		(when (memq prefix (get charsym 'x-symbol-electric-prefixes))
		  (x-symbol-atree-push charsym context1 x-symbol-context-atree)
		  (x-symbol-atree-push charsym context1 x-symbol-electric-atree)
		  (throw 'x-symbol-init-context-atree t)))
	      ;; Otherwise, use charsym with same aspects as target.
	      (dolist (charsym chain)
		(when (and (plists-eq
			    (cdr (get charsym 'x-symbol-modify-aspects))
			    (cdr (get prefix 'x-symbol-modify-aspects)))
			   (plists-eq
			    (cdr (get charsym 'x-symbol-rotate-aspects))
			    (cdr (get prefix 'x-symbol-rotate-aspects))))
		  (x-symbol-atree-push charsym context1 x-symbol-context-atree)
		  (if (member context (get charsym 'x-symbol-electric-strings))
		      (x-symbol-atree-push charsym context1
					   x-symbol-electric-atree))
		  (throw 'x-symbol-init-context-atree t)))
	      ;; Otherwise, use first charsym in chain (the one with the
	      ;; lowest score), but never for input method ELECTRIC.
	      (x-symbol-atree-push (car chain) context1
				   x-symbol-context-atree))))))))

(defun x-symbol-init-key-bindings (context chain)
  "Define key bindings for all charsyms in key chain CHAIN.
The key bindings use CONTEXT and, if necessary, a digit."
  (if (or (cdr chain)		; more than one charsym
	  (< (length context) x-symbol-key-min-length)
	  (member context x-symbol-all-key-prefixes))
      (let ((suffix (eval-when-compile
		      (mapcar 'char-to-string (append "1234567890" nil)))))
	(dolist (charsym chain)
	  (if suffix
	      (define-key x-symbol-map
		(concat context (pop suffix))
		(get charsym 'x-symbol-insert-command))
	    (warn "X-Symbol charsym %s: more than 10 bindings for key prefix %S"
		  charsym context))))
    (define-key x-symbol-map context
      (get (car chain) 'x-symbol-insert-command))))


;;;===========================================================================
;;;  Grid and Menu
;;;===========================================================================

(defun x-symbol-rotate-modify-less-than (charsym1 charsym2)
  "Non-nil, if the scores of CHARSYM1 are lower than those in CHARSYM2.
The rotate score is more important than the modify score."
  (let ((diff (- (car (get charsym1 'x-symbol-rotate-aspects))
		 (car (get charsym2 'x-symbol-rotate-aspects)))))
    (or (< diff 0)
	(and (zerop diff) (x-symbol-modify-less-than charsym1 charsym2)))))

(defun x-symbol-subgroup-less-than (charsym1 charsym2)
  "Non-nil, if subgroup string of CHARSYM1 is less than that of CHARSYM2."
  (string-lessp (or (cadr (get charsym1 'x-symbol-grouping)) "\377")
		(or (cadr (get charsym2 'x-symbol-grouping)) "\377")))

(defun x-symbol-header-charsyms (&optional language)
  "Return an alists with headers and their charsyms.
If optional argument LANGUAGE is non-nil, only collect valid charsym in
that language.  Used for menu and grid.  See variable and language
access `x-symbol-header-groups-alist'."
  (let (group-alist)
    (dolist (charsym x-symbol-all-charsyms)
      (when (or (null language)
		;; This is part of the initialization, we rely on the semantics
		;; => no (funcall x-symbol-valid-charsym-function ...)
		(x-symbol-default-valid-charsym charsym language))
	(x-symbol-push-assq charsym (car (get charsym 'x-symbol-grouping))
			    group-alist)))
    (mapcar (lambda (header-groups)
	      (cons (car header-groups)
		    (apply #'nconc
			   (mapcar (lambda (group)
				     (sort (nreverse
					    (cdr (assq group group-alist)))
					   #'x-symbol-subgroup-less-than))
				   (cdr header-groups)))))
	    (or (and language
		     (symbol-value
		      (get language 'x-symbol-header-groups-alist)))
		x-symbol-header-groups-alist))))

(defun x-symbol-init-grid/menu (&optional language)
  "Initialize the grid and the menu.
If optional argument LANGUAGE is non-nil, init local grid/menu for that
language."
  (let (grid-alist menu-alist)
    (dolist (header-charsyms (x-symbol-header-charsyms language))
      (when (cdr header-charsyms)
	(let ((header (car header-charsyms))
	      (charsyms (cdr header-charsyms)))
	  ;; Grid ------------------------------------------------------------
	  (let (charsyms1 charsyms2)
	    (dolist (charsym charsyms)
	      (unless (memq charsym charsyms1)
		(setq charsyms1
		      (nconc charsyms1
			     (sort (intersection
				    (x-symbol-component-elements charsym)
				    charsyms)
				   'x-symbol-rotate-modify-less-than)))))
	    (dolist (charsym charsyms1)
	      (if (gethash charsym x-symbol-cstring-table)
		  (push charsym charsyms2)))
	    (if charsyms2
		(push (cons header (nreverse charsyms2)) grid-alist)))
	  ;; Menu ------------------------------------------------------------
	  (setq charsyms
		(sort (mapcar
		       (lambda (charsym)
			 (vector (if language
				     (car (x-symbol-default-valid-charsym
					   charsym language))
				   (symbol-name charsym))
				 (get charsym 'x-symbol-insert-command)
				 t))
		       charsyms)
		      (lambda (a b) (string-lessp (aref a 0) (aref b 0)))))
	  (if (<= (length charsyms) x-symbol-menu-max-items)
	      (push (cons header charsyms) menu-alist)
	    (let* ((len (length charsyms))
		   (submenus (1+ (/ (1- len) x-symbol-menu-max-items)))
		   (items (/ len submenus))
		   (submenus (% len items))
		   (number 0)
		   charsyms1 i)
	      (while charsyms
		(if (= submenus number) (decf items))
		(setq charsyms1 nil
		      i items)
		(while (>= i 0)
		  (decf i)
		  (push (pop charsyms) charsyms1))
		(push (cons (format "%s %d" header (incf number))
			    (nreverse charsyms1))
		      menu-alist)))))))
    ;; Set alists ------------------------------------------------------------
    (setq grid-alist (nreverse grid-alist)
	  menu-alist (nreverse menu-alist))
    (if language
	(let ((generated (symbol-value
			  (get language 'x-symbol-generated-data))))
	  (setf (x-symbol-generated-menu-alist generated) menu-alist)
	  (setf (x-symbol-generated-grid-alist generated) grid-alist))
      (setq x-symbol-menu-alist menu-alist
	    x-symbol-grid-alist grid-alist))))


;;;===========================================================================
;;;  Init code for all charsyms.  MAIN: `x-symbol-init-input'
;;;===========================================================================

;;;###autoload
(defun x-symbol-init-input ()
  "Initialize all input methods for all charsyms defined so far.
Run `x-symbol-after-init-input-hook' afterwards.  This function should
be called if new charsyms have been added, but not too often since it
takes some time to complete.  Input methods TOKEN and READ-TOKEN are
defined with `x-symbol-init-language'.

As explained in the docstring of `x-symbol-init-cset', charsyms are
defined with \"character descriptions\" which consist of different
\"aspects\" and \"contexts\", which can also be inherited from a
\"parent\" character.  All characters which are connected with parents,
form a \"component\".  Aspects and contexts are used to determine the
Modify-to and Rotate-to chain for characters, the contexts for input
method CONTEXT and ELECTRIC, the key bindings, and the position in the
MENU and the GRID.

If a table entry of a charsym does not define its own contexts, they are
the same as the contexts of the charsym in an earlier position in the
\"modify chain\" (see below), or the contexts of the first charsym with
defined contexts in the modify chain.  The modify context of a charsym
is the first context.

Characters in the same component whose aspects only differ by their
\"direction\" (east,...), a key in `x-symbol-rotate-aspects-alist', are
circularly connected by \"rotate-to\".  The sequence in the \"rotate
chain\" is determined by rotate scores depending on the values in the
rotate aspects.  Charsyms with the same \"rotate-aspects\" are not
connected (charsyms with the smallest modify scores are preferred).

Characters in the same components whose aspects only differ by their
\"size\" (big,...), \"shape\" (round, square,...) and/or \"shift\" (up,
down,...), keys in `x-symbol-modify-aspects-alist', are circularly
connected by \"modify-to\", if all their modify contexts are used
exclusively, i.e., no other modify chain uses any of them.  The sequence
in the \"modify chain\" is determined by modify scores depending on the
values in the modify aspects and the charsym score.

Otherwise, the \"modify chain\" is divided into modify subchains, which
are those charsyms sharing the same modify context.  All modify
subchains using the same modify context, build a \"horizontal chain\"
whose charsyms are circularly connected by \"modify-to\".

We build a \"key chain\" for all contexts (not just modify contexts),
consisting of all charsyms (sorted according to modify scores) having
the context.  Input method CONTEXT modifies the context to the first
charsym in the \"key chain\".

If there is only one charsym in the key chain, `x-symbol-compose-key'
plus the context inserts the charsym.  Otherwise, we use a digit \(1..9,
0\) as a suffix for each charsym in the key chain.
`x-symbol-compose-key' plus the context plus the optional suffix inserts
the charsym."
  (unless x-symbol-input-initialized
    (let ((gc-cons-threshold most-positive-fixnum)
	  (quail-ignore (regexp-quote x-symbol-quail-suffix-string)))
      (setq x-symbol-input-initialized t)
      (x-symbol-init-aspects)
      (setq x-symbol-all-key-prefixes nil)
      (setq x-symbol-all-key-chain-alist nil)
      (setq x-symbol-all-horizontal-chain-alist nil)
      (setq x-symbol-all-chain-subchains-alist nil)
      (setq x-symbol-all-exclusive-context-alist nil)
      (dolist (root x-symbol-all-charsyms)
	(when (and (get root 'x-symbol-insert-command)
		   (x-symbol-component-root-p root))
	  (dolist (chain (x-symbol-component-space root
						   'x-symbol-modify-aspects))
	    (x-symbol-init-rotate-chain (cdr chain)))
	  (dolist (chain (x-symbol-component-space root
						   'x-symbol-rotate-aspects))
	    (setq chain (x-symbol-sort-modify-chain (cdr chain)))
	    (let ((input (some (lambda (charsym)
				 (get charsym 'x-symbol-context-strings))
			       chain)))
	      (if input
		  (progn
		    (x-symbol-init-horizontal/key-alist chain input)
		    (x-symbol-init-exclusive-alist chain (car input)))
		(dolist (charsym chain)
		  (warn "X-Symbol charsym %s: no input" charsym)))))))
      (dolist (chain x-symbol-all-horizontal-chain-alist)
	;; Do not use `x-symbol-sort-modify-chain', since same warnings will
	;; appear later again.
	(setq chain (setcdr chain	; do not destroy horizontal chain
			    (sort (cdr chain) 'x-symbol-modify-less-than)))
	(x-symbol-init-horizontal-chain chain (car (last chain))))
      (dolist (entry x-symbol-all-chain-subchains-alist)
	(x-symbol-init-exclusive-chain (cdr entry) (car entry)))
      (setq x-symbol-context-atree (x-symbol-make-atree)
	    x-symbol-electric-atree (x-symbol-make-atree))
      (setq x-symbol-map (make-keymap))
      (dolist (entry x-symbol-all-key-chain-alist) ; first sort
	(setcdr entry (x-symbol-sort-modify-chain (cdr entry))))
      (if x-symbol-define-input-method-quail
	  (x-symbol-init-quail-bindings nil nil))
      (dolist (entry x-symbol-all-key-chain-alist) ; then use
	(let ((context (car entry))
	      (chain (cdr entry)))
	  (or (and x-symbol-context-init-ignore
		   (string-match x-symbol-context-init-ignore context))
	      (x-symbol-init-context-atree context chain))
	  (unless (string-match "[0-9]" context 1) ; no digit from 2nd char on
	    (or (null x-symbol-define-input-method-quail)
		(string-match quail-ignore context 1) ; no semi from 2nd char
		(and x-symbol-quail-init-ignore
		     (string-match x-symbol-quail-init-ignore context))
		(x-symbol-init-quail-bindings context chain))
	    (or (and x-symbol-key-init-ignore
		     (string-match x-symbol-key-init-ignore context))
		(x-symbol-init-key-bindings context chain))))))
    (or (featurep 'xemacs)		; CW: is OK in XEmacs, but slow
	(dolist (m (mapcar 'cdr (accessible-keymaps x-symbol-map)))
	  (set-keymap-default-binding m 'x-symbol-map-default-binding)))
    (defalias 'x-symbol-map x-symbol-map)
    (x-symbol-init-grid/menu)
    (substitute-key-definition 'x-symbol-map-autoload 'x-symbol-map global-map)
    (dolist (binding x-symbol-map-default-bindings)
      (define-key x-symbol-map
	(or (car binding) (vector x-symbol-compose-key))
	(cadr binding)))
    ;; always set the following (or only if `x-symbol-map-default-keys-alist'
    ;; is non-nil?):
    (set-keymap-default-binding x-symbol-map 'x-symbol-map-default-binding)
    (run-hooks 'x-symbol-after-init-input-hook)))


;;;===========================================================================
;;;  Latin recoding
;;;===========================================================================

(defun x-symbol-init-latin-decoding ()
  "Init alists for latin decoding and \\[x-symbol-unalias].
This function should be run after all csets with CODING have been
defined, see `x-symbol-init-cset'."
  (let (normalize-alist decode-alists)
    ;; set alists ------------------------------------------------------------
    (dolist (charsym (reverse x-symbol-all-charsyms)) ; rev cosmetic
      (let ((cstring (gethash charsym x-symbol-cstring-table)) bfstring)
	(dolist (table x-symbol-bchar-tables)
	  (and (setq bfstring (gethash charsym (cdr table)))
	       (not (equal (if (stringp bfstring)
			       bfstring
			     (setq bfstring (char-to-string bfstring)))
			   cstring))
	       (push (cons bfstring cstring) normalize-alist)))
	(dolist (table x-symbol-fchar-tables)
	  (and (setq bfstring (gethash charsym (cdr table)))
	       (not (equal (setq bfstring (char-to-string bfstring)) cstring))
	       (x-symbol-push-assq (cons bfstring cstring) (car table)
				   decode-alists)))))
    (setq x-symbol-unalias-alist (nreverse normalize-alist))
					; rev cosmetic
    ;; order recodings in decoding -------------------------------------------
    (setq x-symbol-latin-decode-alists nil)
    (dolist (coding+alist decode-alists)
      (let (decode-alist)
	(when (x-symbol-dolist-delaying
		  (decode-elem (nreverse (cdr coding+alist)) working delayed)
		  (let ((octet (substring (cdr decode-elem) -1)))
		    (or (assoc octet (cdr working)) (assoc octet delayed)))
		(push decode-elem decode-alist))
	  (error "Circular recoding between latin characters"))
	(push (cons (car coding+alist)
		    (nreverse decode-alist)) ; rev important
	      x-symbol-latin-decode-alists)))))


;;;===========================================================================
;;;  Token languages
;;;===========================================================================

(defun x-symbol-get-prime-for (size)
  (setq size (/ (* size 5) 4))
  ;; not all primes
  (let ((primes '(127 149 173 197 223 251 283 317 359 409 463 523 599 683 773
		      883 1009 1151 1307 1493 1709 1951 2341 2819 3389 4073))
	result)
    (while (and (setq result (pop primes)) (< result size)))
    (or result size)))

(defun x-symbol-alist-to-obarray (alist)
  (let ((ob-array (make-vector (x-symbol-get-prime-for (length alist)) 0)))
    (dolist (elt alist)
      (set (intern (car elt) ob-array) (cdr elt)))
    ob-array))

(defun x-symbol-alist-to-hash-table (alist)
  (let ((hash-table (make-hash-table
		     :size (if (featurep 'xemacs)
			       (length alist) ; does already use higher prime
			     (x-symbol-get-prime-for (length alist)))
		     :test 'eq)))
    (dolist (elt alist)
      (puthash (car elt) (cdr elt) hash-table))
    hash-table))

(defun x-symbol-init-language (language)
  "Load and init token language LANGUAGE.
Set language dependent accesses in `x-symbol-language-access-alist'.
Set conversion alists according to table and initialize executables, see
`x-symbol-init-executables'.  Initialize all input methods, see
`x-symbol-init-input'.  LANGUAGE should have been registered with
`x-symbol-register-language' before.

Each element in TABLE, the language access `x-symbol-table', looks like
  (CHARSYM CLASSES . TOKEN-SPEC) or nil.

With the first form, pass TOKEN-SPEC to the language aspect
`x-symbol-token-list' to get a list of TOKENs.  Decoding converts all
TOKENs to the cstring of CHARSYM, encoding converts the cstring to the
first TOKEN.

IF CHARSYM or the first TOKEN is used a second time in the table, issue
a warning and do not define entries for decoding and encoding.  If any
TOKEN appears a second time, do not define the corresponding entry for
decoding.  If the third form nil has appeared in TABLE, do not issue a
warning for the next entries in TABLE.

CLASSES are a list of symbols which are used for the character info in
the echo are, see `x-symbol-character-info', the grid coloring scheme,
and probably by the token language dependent control of input method
ELECTRIC, see `x-symbol-electric-input'.  They are used by the language
accesses `x-symbol-class-alist' and `x-symbol-class-face-alist'.

If non-nil, the language aspect `x-symbol-input-token-ignore' \"hides\"
some tokens from input method token.  `x-symbol-call-function-or-regexp'
uses it with TOKEN and CHARSYM."
  (when (get language 'x-symbol-feature)
    (require (get language 'x-symbol-feature))
    (x-symbol-init-language-accesses language x-symbol-language-access-alist)
    (put language 'x-symbol-initialized t)
    (dolist (feature (x-symbol-language-value 'x-symbol-required-fonts
					      language))
      (require feature))
    (x-symbol-init-input)
    (let ((grammar (x-symbol-language-value 'x-symbol-token-grammar language)))
      (when (eq (car-safe grammar) 'x-symbol-make-grammar)
	(setq grammar (apply 'x-symbol-make-grammar (cdr grammar)))
	(set (get language 'x-symbol-token-grammar) grammar))
      (let ((token-list (x-symbol-grammar-token-list grammar))
	    (after-init (x-symbol-grammar-after-init grammar))
	    (class-alist (x-symbol-language-value 'x-symbol-class-alist
						  language))
	    decode-alist encode-alist classes-alist
	    (warn-double t)
	    used-charsyms used-tokens secondary
	    (max-token-len 0) tlen)
	(dolist (entry (x-symbol-language-value 'x-symbol-table language))
	  (if (null entry)
	      (setq warn-double nil)
	    (let* ((charsym (car entry))
		   (classes (cadr entry))
		   (tokens (if token-list
			       (funcall token-list (cddr entry))
			     (mapcar #'list (cddr entry)))))
	      ;; Check entries, set charsym properties -----------------------
	      (cond ((null charsym))
		    ((memq charsym used-charsyms)
		     (if warn-double
			 (warn "X-Symbol charsym %s: used twice in language %s"
			       charsym language))
		     (setq charsym nil))
		    ((memq charsym x-symbol-all-charsyms)
		     (push charsym used-charsyms))
		    (t
		     (warn "X-Symbol: used undefined charsym %s in language %s"
			   charsym language)))
	      (dolist (class classes)
		(unless (assq class class-alist)
		  (warn "X-Symbol charsym %s: undefined %s class %s"
			(car entry) language class)))
	      (and charsym
		   (or (null tokens)
		       (member (caar tokens) used-tokens)
		       (not (gethash charsym x-symbol-cstring-table)))
		   (setq charsym nil))
	      ;;--------------------------------------------------------------
	      ;; TODO: allow (nil nil TOKEN...) to shadow tokens
	      (when charsym
		(push (cons charsym classes) classes-alist)
		(push (cons charsym (car tokens)) encode-alist)
		(setq secondary nil)
		(dolist (token tokens)
		  (if (member (car token) used-tokens)
		      (if warn-double
			  (warn "X-Symbol charsym %s: used %s token %S twice"
				(car entry) language (car token)))
		    (push (car token) used-tokens)
		    (push (list* (car token) charsym (cdr token) secondary)
			  decode-alist)
		    (if (> (setq tlen (length (car token))) max-token-len)
			(setq max-token-len tlen))
		    (setq secondary t)))))))
	;; set vars ----------------------------------------------------------
	(set (get language 'x-symbol-generated-data)
	     (x-symbol-make-generated-data
	      :encode-table (x-symbol-alist-to-hash-table encode-alist)
	      :decode-obarray (x-symbol-alist-to-obarray decode-alist)
	      :token-classes (x-symbol-alist-to-hash-table classes-alist)
	      :max-token-len max-token-len))
	(if (functionp after-init) (funcall after-init))))
    (x-symbol-init-grid/menu language)
    t))



;;;;##########################################################################
;;;;  The Tables
;;;;##########################################################################

;; ISO 2022/2375 final char/byte (for charset extension/switching): 0x30-0x3F
;; are reserved as user-defined.  Emacs keeps 0x3A-0x3F [:;<=>?] free for
;; users, although XEmacs defines the charset `thai-xtis' with final ??...

(defvar x-symbol-latin1-cset
  '((("iso8859-1" . iso-8859-1) ?\237 -3750)
    nil .
    (latin-iso8859-1))
  "Cset with registry \"iso8859-1\", see `x-symbol-init-cset'.")

(defvar x-symbol-latin2-cset
  '((("iso8859-2" . iso-8859-2) ?\236 -3750)
    nil .
    (latin-iso8859-2))
  "Cset with registry \"iso8859-2\", see `x-symbol-init-cset'.")

(defvar x-symbol-latin3-cset
  '((("iso8859-3" . iso-8859-3) ?\235 -3750)
    nil .
    (latin-iso8859-3))
  "Cset with registry \"iso8859-3\", see `x-symbol-init-cset'.")

(defvar x-symbol-latin5-cset
  '((("iso8859-9". iso-8859-9) ?\234 -3750)
    nil .
    (latin-iso8859-9))
  "Cset with registry \"iso8859-9\", see `x-symbol-init-cset'.")

(defvar x-symbol-latin9-cset
  '((("iso8859-15". iso-8859-15) ?\231 -3750)
    nil .
    (latin-iso8859-15 "ISO8859-15 (Latin-9)" 96 ?b) )
  "Cset with registry \"iso8859-15\", see `x-symbol-init-cset'.")

(defvar x-symbol-xsymb0-cset
  '((("adobe-fontspecific") ?\233 -3600)
    (xsymb0-left  "X-Symbol characters 0, left"  94 ?:) .
    (xsymb0-right "X-Symbol characters 0, right" 94 ?\;))
  "Cset with registry \"fontspecific\", see `x-symbol-init-cset'.")

(defvar x-symbol-xsymb1-cset
  '((("xsymb-xsymb1") ?\232 -3500)
    (xsymb1-left  "X-Symbol characters 1, left"  94 ?<) .
    (xsymb1-right "X-Symbol characters 1, right" 96 ?=))
  "Cset with registry \"xsymb1\", see `x-symbol-init-cset'.")

(defvar x-symbol-latin1-table
  '((nobreakspace 160 (white) nil nil (" "))
    (exclamdown 161 (punctuation) nil nil ("!"))
    (cent 162 (currency "c") nil nil ("C|" "|C"))
    (sterling 163 (currency "L") nil nil ("L-" "-L"))
    (currency 164 (currency "x") nil nil ("ox" "xo"))
    (yen 165 (currency "Y") nil nil ("Y=" "=Y"))
    (brokenbar 166 (line) nil nil ("!!"))
    (section 167 (symbol) nil nil ("SS"))
    (diaeresis 168 (diaeresis accent))
    (copyright 169 (symbol "C") nil nil ("CO" "cO"))
    (ordfeminine 170 (symbol "a") (shift up) nil ("a_" "_a"))
    (guillemotleft 171 (quote open guillemotright)
		   (direction west . guillemotright) nil (t "<<"))
    (notsign 172 (symbol) nil nil ("-,"))
    (hyphen 173 (line) (size sml) nil ("-"))
    (registered 174 (symbol "R") nil nil ("RO"))
    (macron 175 (line) (shift up) nil ("-"))
    (degree 176 (symbol "0") (shift up) nil ("o^" "^o"))
    (plusminus 177 (operator) (direction north) nil (t "+-" t "+_"))
    (twosuperior 178 (symbol "2") (shift up) nil ("2^" "^2"))
    (threesuperior 179 (symbol "3") (shift up) nil ("3^" "^3"))
    (acute 180 (acute accent))
    (mu1 181 (greek1 "m" nil "mu"))
    (paragraph 182 (symbol "P") nil nil ("q|"))
    (periodcentered 183 (dots) (shift up) nil ("." ".^" t "^."))
    (cedilla 184 (cedilla accent))
    (onesuperior 185 (symbol "1") (shift up) nil ("1^" "^1"))
    (masculine 186 (symbol "o") (shift up) nil ("o_" "_o"))
    (guillemotright 187 (quote close guillemotleft) (direction east) nil
		    (t ">>"))
    (onequarter 188 (symbol "1") nil nil ("1Q" "1/4"))
    (onehalf 189 (symbol "2") nil nil ("1H" "1/2"))
    (threequarters 190 (symbol "3") nil nil ("3Q" "3/4"))
    (questiondown 191 (punctuation) nil nil ("?"))
    (Agrave 192 (grave "A" agrave))
    (Aacute 193 (acute "A" aacute))
    (Acircumflex 194 (circumflex "A" acircumflex))
    (Atilde 195 (tilde "A" atilde))
    (Adiaeresis 196 (diaeresis "A" adiaeresis))
    (Aring 197 (ring "A" aring))
    (AE 198 (letter "AE" ae))
    (Ccedilla 199 (cedilla "C" ccedilla))
    (Egrave 200 (grave "E" egrave))
    (Eacute 201 (acute "E" eacute))
    (Ecircumflex 202 (circumflex "E" ecircumflex))
    (Ediaeresis 203 (diaeresis "E" ediaeresis))
    (Igrave 204 (grave "I" igrave))
    (Iacute 205 (acute "I" iacute))
    (Icircumflex 206 (circumflex "I" icircumflex))
    (Idiaeresis 207 (diaeresis "I" idiaeresis))
    (ETH 208 (slash "D" eth) nil 120)
    (Ntilde 209 (tilde "N" ntilde))
    (Ograve 210 (grave "O" ograve))
    (Oacute 211 (acute "O" oacute))
    (Ocircumflex 212 (circumflex "O" ocircumflex))
    (Otilde 213 (tilde "O" otilde))
    (Odiaeresis 214 (diaeresis "O" odiaeresis))
    (multiply 215 (operator) (shift up) nil ("x"))
    (Ooblique 216 (slash "O" oslash))
    (Ugrave 217 (grave "U" ugrave))
    (Uacute 218 (acute "U" uacute))
    (Ucircumflex 219 (circumflex "U" ucircumflex))
    (Udiaeresis 220 (diaeresis "U" udiaeresis))
    (Yacute 221 (acute "Y" yacute))
    (THORN 222 (letter "TH" thorn))
    (ssharp 223 (letter "ss" nil))
    (agrave 224 (grave "a" Agrave))
    (aacute 225 (acute "a" Aacute))
    (acircumflex 226 (circumflex "a" Acircumflex))
    (atilde 227 (tilde "a" Atilde))
    (adiaeresis 228 (diaeresis "a" Adiaeresis))
    (aring 229 (ring "a" Aring))
    (ae 230 (letter "ae" AE))
    (ccedilla 231 (cedilla "c" Ccedilla))
    (egrave 232 (grave "e" Egrave))
    (eacute 233 (acute "e" Eacute))
    (ecircumflex 234 (circumflex "e" Ecircumflex))
    (ediaeresis 235 (diaeresis "e" Ediaeresis))
    (igrave 236 (grave "i" Igrave))
    (iacute 237 (acute "i" Iacute))
    (icircumflex 238 (circumflex "i" Icircumflex))
    (idiaeresis 239 (diaeresis "i" Idiaeresis))
    (eth 240 (slash "d" ETH) nil 120)
    (ntilde 241 (tilde "n" Ntilde))
    (ograve 242 (grave "o" Ograve))
    (oacute 243 (acute "o" Oacute))
    (ocircumflex 244 (circumflex "o" Ocircumflex))
    (otilde 245 (tilde "o" Otilde))
    (odiaeresis 246 (diaeresis "o" Odiaeresis))
    (division 247 (operator) nil nil (":-" "-:"))
    (oslash 248 (slash "o" Ooblique))
    (ugrave 249 (grave "u" Ugrave))
    (uacute 250 (acute "u" Uacute))
    (ucircumflex 251 (circumflex "u" Ucircumflex))
    (udiaeresis 252 (diaeresis "u" Udiaeresis))
    (yacute 253 (acute "y" Yacute))
    (thorn 254 (letter "th" THORN))
    (ydiaeresis 255 (diaeresis "y" Ydiaeresis)))
  "Table for registry \"iso8859-1\", see `x-symbol-init-cset'.")

(defvar x-symbol-latin2-table
  '((nobreakspace 160 . t)
    (Aogonek 161 (ogonek "A" aogonek))
    (breve 162 (breve accent))
    (Lslash 163 (slash "L" lslash))
    (currency 164 . t)
    (Lcaron 165 (caron "L" lcaron))
    (Sacute 166 (acute "S" sacute))
    (section 167 . t)
    (diaeresis 168 . t)
    (Scaron 169 (caron "S" scaron))
    (Scedilla 170 (cedilla "S" scedilla))
    (Tcaron 171 (caron "T" tcaron))
    (Zacute 172 (acute "Z" zacute))
    (hyphen 173 . t)
    (Zcaron 174 (caron "Z" zcaron))
    (Zdotaccent 175 (dotaccent "Z" zdotaccent))
    (degree 176 . t)
    (aogonek 177 (ogonek "a" Aogonek))
    (ogonek 178 (ogonek accent))
    (lslash 179 (slash "l" Lslash))
    (acute 180 . t)
    (lcaron 181 (caron "l" Lcaron))
    (sacute 182 (acute "s" Sacute))
    (caron 183 (caron accent) (shift up))
    (cedilla 184 . t)
    (scaron 185 (caron "s" Scaron))
    (scedilla 186 (cedilla "s" Scedilla))
    (tcaron 187 (caron "t" Tcaron))
    (zacute 188 (acute "z" Zacute))
    (hungarumlaut 189 (hungarumlaut accent))
    (zcaron 190 (caron "z" Zcaron))
    (zdotaccent 191 (dotaccent "z" Zdotaccent))
    (Racute 192 (acute "R" racute))
    (Aacute 193 . t)
    (Acircumflex 194 . t)
    (Abreve 195 (breve "A" abreve))
    (Adiaeresis 196 . t)
    (Lacute 197 (acute "L" lacute))
    (Cacute 198 (acute "C" cacute))
    (Ccedilla 199 . t)
    (Ccaron 200 (caron "C" ccaron))
    (Eacute 201 . t)
    (Eogonek 202 (ogonek "E" eogonek))
    (Ediaeresis 203 . t)
    (Ecaron 204 (caron "E" ecaron))
    (Iacute 205 . t)
    (Icircumflex 206 . t)
    (Dcaron 207 (caron "D" dcaron))
    (Dbar 208 (slash "D" dbar))
    (Nacute 209 (acute "N" nacute))
    (Ncaron 210 (caron "N" ncaron))
    (Oacute 211 . t)
    (Ocircumflex 212 . t)
    (Ohungarumlaut 213 (hungarumlaut "O" ohungarumlaut))
    (Odiaeresis 214 . t)
    (multiply 215 . t)
    (Rcaron 216 (caron "R" rcaron))
    (Uring 217 (ring "U" uring))
    (Uacute 218 . t)
    (Uhungarumlaut 219 (hungarumlaut "U" uhungarumlaut))
    (Udiaeresis 220 . t)
    (Yacute 221 . t)
    (Tcedilla 222 (cedilla "T" tcedilla))
    (ssharp 223 . t)
    (racute 224 (acute "r" Racute))
    (aacute 225 . t)
    (acircumflex 226 . t)
    (abreve 227 (breve "a" Abreve))
    (adiaeresis 228 . t)
    (lacute 229 (acute "l" Lacute))
    (cacute 230 (acute "c" Cacute))
    (ccedilla 231 . t)
    (ccaron 232 (caron "c" Ccaron))
    (eacute 233 . t)
    (eogonek 234 (ogonek "e" Eogonek))
    (ediaeresis 235 . t)
    (ecaron 236 (caron "e" Ecaron))
    (iacute 237 . t)
    (icircumflex 238 . t)
    (dcaron 239 (caron "d" Dcaron))
    (dbar 240 (slash "d" Dbar))
    (nacute 241 (acute "n" Nacute))
    (ncaron 242 (caron "n" Ncaron))
    (oacute 243 . t)
    (ocircumflex 244 . t)
    (ohungarumlaut 245 (hungarumlaut "o" Ohungarumlaut))
    (odiaeresis 246 . t)
    (division 247 . t)
    (rcaron 248 (caron "r" Rcaron))
    (uring 249 (ring "u" Uring))
    (uacute 250 . t)
    (uhungarumlaut 251 (hungarumlaut "u" Uhungarumlaut))
    (udiaeresis 252 . t)
    (yacute 253 . t)
    (tcedilla 254 (cedilla "t" Tcedilla))
    (dotaccent 255 (dotaccent accent) (shift up)))
  "Table for registry \"iso8859-2\", see `x-symbol-init-cset'.")

(defvar x-symbol-latin3-table
  '((nobreakspace 160 . t)
    (Hbar 161 (slash "H" hbar))
    (breve 162 . t)
    (sterling 163 . t)
    (currency 164 . t)
    (unused-l3/165 165 . unused)
    (Hcircumflex 166 (circumflex "H" hcircumflex))
    (section 167 . t)
    (diaeresis 168 . t)
    (Idotaccent 169 (dotaccent "I" dotlessi))
    (Scedilla 170 . t)
    (Gbreve 171 (breve "G" gbreve))
    (Jcircumflex 172 (circumflex "J" jcircumflex))
    (hyphen 173 . t)
    (unused-l3/174 174 . unused)
    (Zdotaccent 175 . t)
    (degree 176 . t)
    (hbar 177 (slash "h" Hbar))
    (twosuperior 178 . t)
    (threesuperior 179 . t)
    (acute 180 . t)
    (mu1 181 . t)
    (hcircumflex 182 (circumflex "h" hcircumflex))
    (periodcentered 183 . t)
    (cedilla 184 . t)
    (dotlessi 185 (dotaccent "i" Idotaccent))
    (scedilla 186 . t)
    (gbreve 187 (breve "g" Gbreve))
    (jcircumflex 188 (circumflex "j" Jcircumflex))
    (onehalf 189 . t)
    (unused-l3/190 190 . unused)
    (zdotaccent 191 . t)
    (Agrave 192 . t)
    (Aacute 193 . t)
    (Acircumflex 194 . t)
    (unused-l3/195 195 . unused)
    (Adiaeresis 196 . t)
    (Cdotaccent 197 (dotaccent "C" cdotaccent))
    (Ccircumflex 198 (circumflex "C" ccircumflex))
    (Ccedilla 199 . t)
    (Egrave 200 . t)
    (Eacute 201 . t)
    (Ecircumflex 202 . t)
    (Ediaeresis 203 . t)
    (Igrave 204 . t)
    (Iacute 205 . t)
    (Icircumflex 206 . t)
    (Idiaeresis 207 . t)
    (unused-l3/208 208 . unused)
    (Ntilde 209 . t)
    (Ograve 210 . t)
    (Oacute 211 . t)
    (Ocircumflex 212 . t)
    (Gdotaccent 213 (dotaccent "G" gdotaccent))
    (Odiaeresis 214 . t)
    (multiply 215 . t)
    (Gcircumflex 216 (circumflex "G" gcircumflex))
    (Ugrave 217 . t)
    (Uacute 218 . t)
    (Ucircumflex 219 . t)
    (Udiaeresis 220 . t)
    (Ubreve 221 (breve "U" ubreve))
    (Scircumflex 222 (circumflex "S" scircumflex))
    (ssharp 223 . t)
    (agrave 224 . t)
    (aacute 225 . t)
    (acircumflex 226 . t)
    (unused-l3/227 227 . unused)
    (adiaeresis 228 . t)
    (cdotaccent 229 (dotaccent "c" Cdotaccent))
    (ccircumflex 230 (circumflex "c" Ccircumflex))
    (ccedilla 231 . t)
    (egrave 232 . t)
    (eacute 233 . t)
    (ecircumflex 234 . t)
    (ediaeresis 235 . t)
    (igrave 236 . t)
    (iacute 237 . t)
    (icircumflex 238 . t)
    (idiaeresis 239 . t)
    (unused-l3/240 240 . unused)
    (ntilde 241 . t)
    (ograve 242 . t)
    (oacute 243 . t)
    (ocircumflex 244 . t)
    (gdotaccent 245 (dotaccent "g" Gdotaccent))
    (odiaeresis 246 . t)
    (division 247 . t)
    (gcircumflex 248 (circumflex "g" Gcircumflex))
    (ugrave 249 . t)
    (uacute 250 . t)
    (ucircumflex 251 . t)
    (udiaeresis 252 . t)
    (ubreve 253 (breve "u" Ubreve))
    (scircumflex 254 (circumflex "s" Scircumflex))
    (dotaccent 255 . t))
  "Table for registry \"iso8859-3\", see `x-symbol-init-cset'.")

(defvar x-symbol-latin5-table
  '((nobreakspace 160 . t)
    (exclamdown 161 . t)
    (cent 162 . t)
    (sterling 163 . t)
    (currency 164 . t)
    (yen 165 . t)
    (brokenbar 166 . t)
    (section 167 . t)
    (diaeresis 168 . t)
    (copyright 169 . t)
    (ordfeminine 170 . t)
    (guillemotleft 171 . t)
    (notsign 172 . t)
    (hyphen 173 . t)
    (registered 174 . t)
    (macron 175 . t)
    (degree 176 . t)
    (plusminus 177 . t)
    (twosuperior 178 . t)
    (threesuperior 179 . t)
    (acute 180 . t)
    (mu1 181 . t)
    (paragraph 182 . t)
    (periodcentered 183 . t)
    (cedilla 184 . t)
    (onesuperior 185 . t)
    (masculine 186 . t)
    (guillemotright 187 . t)
    (onequarter 188 . t)
    (onehalf 189 . t)
    (threequarters 190 . t)
    (questiondown 191 . t)
    (Agrave 192 . t)
    (Aacute 193 . t)
    (Acircumflex 194 . t)
    (Atilde 195 . t)
    (Adiaeresis 196 . t)
    (Aring 197 . t)
    (AE 198 . t)
    (Ccedilla 199 . t)
    (Egrave 200 . t)
    (Eacute 201 . t)
    (Ecircumflex 202 . t)
    (Ediaeresis 203 . t)
    (Igrave 204 . t)
    (Iacute 205 . t)
    (Icircumflex 206 . t)
    (Idiaeresis 207 . t)
    (Gbreve 208 . t)
    (Ntilde 209 . t)
    (Ograve 210 . t)
    (Oacute 211 . t)
    (Ocircumflex 212 . t)
    (Otilde 213 . t)
    (Odiaeresis 214 . t)
    (multiply 215 . t)
    (Ooblique 216 . t)
    (Ugrave 217 . t)
    (Uacute 218 . t)
    (Ucircumflex 219 . t)
    (Udiaeresis 220 . t)
    (Idotaccent 221 . t)
    (Scedilla 222 . t)
    (ssharp 223 . t)
    (agrave 224 . t)
    (aacute 225 . t)
    (acircumflex 226 . t)
    (atilde 227 . t)
    (adiaeresis 228 . t)
    (aring 229 . t)
    (ae 230 . t)
    (ccedilla 231 . t)
    (egrave 232 . t)
    (eacute 233 . t)
    (ecircumflex 234 . t)
    (ediaeresis 235 . t)
    (igrave 236 . t)
    (iacute 237 . t)
    (icircumflex 238 . t)
    (idiaeresis 239 . t)
    (gbreve 240 . t)
    (ntilde 241 . t)
    (ograve 242 . t)
    (oacute 243 . t)
    (ocircumflex 244 . t)
    (otilde 245 . t)
    (odiaeresis 246 . t)
    (division 247 . t)
    (oslash 248 . t)
    (ugrave 249 . t)
    (uacute 250 . t)
    (ucircumflex 251 . t)
    (udiaeresis 252 . t)
    (dotlessi 253 . t)
    (scedilla 254 . t)
    (ydiaeresis 255 . t))
  "Table for registry \"iso8859-9\", see `x-symbol-init-cset'.")

(defvar x-symbol-latin9-table
  '((nobreakspace 160 . t)
    (exclamdown 161 . t)
    (cent 162 . t)
    (sterling 163 . t)
    (euro 164 (currency "C") nil nil ("C="))
    (yen 165 . t)
    (Scaron 166 . t)			; latin-2
    (section 167 . t)
    (scaron 168 . t)			; latin-2
    (copyright 169 . t)
    (ordfeminine 170 . t)
    (guillemotleft 171 . t)
    (notsign 172 . t)
    (hyphen 173 . t)
    (registered 174 . t)
    (macron 175 . t)
    (degree 176 . t)
    (plusminus 177 . t)
    (twosuperior 178 . t)
    (threesuperior 179 . t)
    (Zcaron 180 . t)			; latin-2
    (mu1 181 . t)
    (paragraph 182 . t)
    (periodcentered 183 . t)
    (zcaron 184 . t)			; latin-2
    (onesuperior 185 . t)
    (masculine 186 . t)
    (guillemotright 187 . t)
    (OE 188 (letter "OE" oe))
    (oe 189 (letter "oe" OE))
    (Ydiaeresis 190 (diaeresis "Y" ydiaeresis))
    (questiondown 191 . t)
    (Agrave 192 . t)
    (Aacute 193 . t)
    (Acircumflex 194 . t)
    (Atilde 195 . t)
    (Adiaeresis 196 . t)
    (Aring 197 . t)
    (AE 198 . t)
    (Ccedilla 199 . t)
    (Egrave 200 . t)
    (Eacute 201 . t)
    (Ecircumflex 202 . t)
    (Ediaeresis 203 . t)
    (Igrave 204 . t)
    (Iacute 205 . t)
    (Icircumflex 206 . t)
    (Idiaeresis 207 . t)
    (ETH 208 . t)
    (Ntilde 209 . t)
    (Ograve 210 . t)
    (Oacute 211 . t)
    (Ocircumflex 212 . t)
    (Otilde 213 . t)
    (Odiaeresis 214 . t)
    (multiply 215 . t)
    (Ooblique 216 . t)
    (Ugrave 217 . t)
    (Uacute 218 . t)
    (Ucircumflex 219 . t)
    (Udiaeresis 220 . t)
    (Yacute 221 . t)
    (THORN 222 . t)
    (ssharp 223 . t)
    (agrave 224 . t)
    (aacute 225 . t)
    (acircumflex 226 . t)
    (atilde 227 . t)
    (adiaeresis 228 . t)
    (aring 229 . t)
    (ae 230 . t)
    (ccedilla 231 . t)
    (egrave 232 . t)
    (eacute 233 . t)
    (ecircumflex 234 . t)
    (ediaeresis 235 . t)
    (igrave 236 . t)
    (iacute 237 . t)
    (icircumflex 238 . t)
    (idiaeresis 239 . t)
    (eth 240 . t)
    (ntilde 241 . t)
    (ograve 242 . t)
    (oacute 243 . t)
    (ocircumflex 244 . t)
    (otilde 245 . t)
    (odiaeresis 246 . t)
    (division 247 . t)
    (oslash 248 . t)
    (ugrave 249 . t)
    (uacute 250 . t)
    (ucircumflex 251 . t)
    (udiaeresis 252 . t)
    (yacute 253 . t)
    (thorn 254 . t)
    (ydiaeresis 255 . t))
  "Table for registry \"iso8859-15\", see `x-symbol-init-cset'.")

(defvar x-symbol-xsymb0-table
  '(;;(exclam1 33)			; Adobe:exclam
    ;;(universal 34 (symbol) nil nil ("A"))
    (numbersign1 35 (symbol) nil nil ("#")) ; Adobe:numbersign, TeX
    ;;(existential 36 (symbol) nil nil ("E"))
    ;;(percent1 37 (symbol) nil nil ("%"))	; Adobe:percent
    ;;(ampersand1 38 (symbol) nil nil ("&"))
    (suchthat 39 (relation) (direction east . element) nil ("-)"))
    ;;(parenleft1 40)			; Adobe:parenleft
    ;;(parenright1 41)			; Adobe:parenright
    (asterisk1 42 (operator) nil nil ("*")) ; Adobe:asteriskmath
    ;;(plus1 43)				; Adobe:plus
    ;;(comma1 44 (quote) nil (","))	; Adobe:comma
    (minus1 45 (operator) nil nil ("-"))	; Adobe:minus
    (period1 46 (dots) nil nil ("."))	; Adobe:period
    ;;(slash1 47)				; Adobe:slash
    ;; 48..57 = ascii 0-9
    (colon1 58 (dots) nil nil (":"))	; Adobe:colon, TeX
    ;;(semicolon1 59)			; Adobe:semicolon
    ;;(less1 60 (relation) (direction west . greater1) nil ("<"))
    ;;(equal1 61)				; Adobe:equal
    ;;(greater1 62 (relation) (direction east) nil (">"))
    ;;(question1 63)			; Adobe:question
    (congruent 64 (relation) nil nil (t "~="))
    (Delta 68 (greek "D" delta "Delta"))
    (Phi 70 (greek "F" phi "Phi"))
    (Gamma 71 (greek "G" gamma "Gamma"))
    (theta1 74 (greek1 "q" Theta "theta"))
    (Lambda 76 (greek "L" lambda "Lambda"))
    (Pi 80 (greek "P" pi "Pi"))
    (Theta 81 (greek "Q" theta "Theta"))
    (Sigma 83 (greek "S" sigma "Sigma"))
    (sigma1 86 (greek1 "s" Sigma "sigma"))
    (Omega 87 (greek "W" omega "Omega"))
    (Xi 88 (greek "X" xi "Xi"))
    (Psi 89 (greek "Y" psi "Psi"))
    ;;(bracketleft1 91)			; Adobe:bracketleft
    ;;(therefore 92 (dots) (direction nil . ellipsis) nil (".:"))
    ;;(bracketright1 93)			; Adobe:bracketright
    (perpendicular 94 (arrow) (direction north) nil (t "_|_")) ; (TeX)
    (underscore1 95 (line) nil nil ("_"))	; Adobe:underscore, TeX
    (radicalex 96 (line) (shift up) nil ("-^" "^-"))
    (alpha 97 (greek "a" nil "alpha"))
    (beta 98 (greek "b" nil "beta"))
    (chi 99 (greek "c" nil "chi"))
    (delta 100 (greek "d" Delta "delta"))
    (epsilon 101 (greek "e" nil "epsilon"))
    (phi 102 (greek "f" Phi "phi"))
    (gamma 103 (greek "g" Gamma "gamma"))
    (eta 104 (greek "h" nil "eta"))
    (iota 105 (greek "i" nil "iota"))
    (phi1 106 (greek1 "f" Phi "phi"))
    (kappa 107 (greek "k" nil "kappa"))
    (lambda 108 (greek "l" Lambda "lambda"))
    (mu 109 (greek "m" nil "mu"))
    (nu 110 (greek "n" nil "nu"))
    (pi 112 (greek "p" Pi "pi"))
    (theta 113 (greek "q" Theta "theta"))
    (rho 114 (greek "r" nil "rho"))
    (sigma 115 (greek "s" Sigma "sigma"))
    (tau 116 (greek "t" nil "tau"))
    (upsilon 117 (greek "u" Upsilon1 "upsilon"))
    (omega1 118 (greek1 "w" Omega "omega"))
    (omega 119 (greek "w" Omega "omega"))
    (xi 120 (greek "x" Xi "xi"))
    (psi 121 (greek "y" Psi "psi"))
    (zeta 122 (greek "z" nil "zeta"))
;;;    (braceleft1 123 (parenthesis open braceright1)
;;;		(direction west . braceright1) nil ("{"))
    (bar1 124 (line) brokenbar 120 ("|"))	; Adobe:bar, TeX
;;;    (braceright1 125 (parenthesis close braceleft1) (direction east) nil ("}"))
    (similar 126 (relation) nil nil ("~"))
    (Upsilon1 161 (greek1 "U" upsilon "Upsilon"))
    (minute 162 (symbol) nil nil ("'"))
    (lessequal 163 (relation) (direction west . greaterequal) nil (t "<_"))
    (fraction 164 (operator) nil nil ("/"))
    (infinity 165 (symbol) nil nil ("oo"))
    (florin 166 (currency "f") nil nil ("f"))
    (club 167 (shape) (direction north . diamond) nil ("{#}"))
    (diamond 168 (shape) (direction east . lozenge) nil ("<#>"))
    (heart 169 (shape) (direction south . diamond) nil ("(#)"))
    (spade 170 (shape) (direction west . diamond) nil ("/#\\"))
    (arrowboth 171 (arrow) (direction horizontal . arrowright) nil
	       (t "<->") (arrowleft))
    (arrowleft 172 (arrow) (direction west . arrowright) nil (t "<-"))
    (arrowup 173 (arrow) (direction north . arrowright) nil ("|^"))
    (arrowright 174 (arrow) (direction east) nil (t "->"))
    (arrowdown 175 (arrow) (direction south . arrowright) nil ("|v"))
    (ring 176 (ring accent))		; Adobe:degree, TeX
    ;;(plusminus1 177)			; Adobe:plusminus
    (second 178 (symbol) nil nil ("''"))		; NEW
    (greaterequal 179 (relation) (direction east) nil (t ">_"))
    ;;(times1 180)				; Adobe:times
    (proportional 181 (relation) nil nil ("oc"))
    (partialdiff 182 (mathletter "d"))
    (bullet 183 (operator) nil 240 ("*"))
    ;;(divide1 184)			; Adobe:divide
    (notequal 185 (relation) nil nil (t "=/"))
    (equivalence 186 (relation) nil nil (t "=_"))
    (approxequal 187 (relation) nil nil (t "~~"))
    (ellipsis 188 (dots) (direction east) nil (t "..."))
    ;;(arrowhorizex 190 (line) (size big) nil ("-"))
    (carriagereturn 191 (arrow) (direction west) nil ("<-|"))	; NEW
    (aleph 192 (mathletter "N"))
    (Ifraktur 193 (mathletter "I"))
    (Rfraktur 194 (mathletter "R"))
    (weierstrass 195 (mathletter "P"))
    (circlemultiply 196 (operator) nil nil (t "xO") (multiply))
    (circleplus 197 (operator) nil nil (t "+O"))
    (emptyset 198 (shape) nil nil ("0/" "O/"))
    (intersection 199 (operator) (shape round . logicaland))
    (union 200 (operator) (shape round . logicalor))
    (propersuperset 201 (relation) (direction east . union) nil (">"))
    (reflexsuperset 202 (relation) (shape round . greaterequal) nil
		    nil (propersuperset))
    (notsubset 203 (relation) (shape round direction west) nil
	       ("</") (propersubset))
    (propersubset 204 (relation) (direction west . propersuperset) nil ("<"))
    (reflexsubset 205 (relation) (shape round . lessequal) nil
		  nil (propersubset))
    (element 206 (relation) (direction west) nil ("(-"))
    (notelement 207 (relation) (direction west) nil (t "(-/") (element))
    (angle 208 (symbol) nil nil ("/_"))
    (gradient 209 (triangle) (direction south . Delta) nil (t "\\-/"))
    ;;(register1 210)			; Adobe:registerserif
    ;;(copyright1 211)			; Adobe:copyrightserif
    ;;(trademark1 212)			; Adobe:trademarkserif
    (product 213 (bigop) (size big . Pi) nil ("TT"))
    (radical 214 (symbol) nil nil ("v/"))
    (periodcentered1 215 (dots) periodcentered 120) ; Adobe:dotmath, (TeX)
    ;;(logicalnot1 216)			; Adobe:logicalnot
    (logicaland 217 (operator) (direction north . logicalor) nil (t "/\\"))
    (logicalor 218 (operator) (direction south) nil (t "\\/"))
    (arrowdblboth 219 (arrow) (direction horizontal . arrowdblright) nil
		  (t "<=>") (arrowdblleft))
    (arrowdblleft 220 (arrow) (direction west . arrowdblright) nil (t "<="))
    (arrowdblup 221 (arrow) (direction north . arrowdblright) nil ("||^"))
    (arrowdblright 222 (arrow) (direction east) nil (t "=>"))
    (arrowdbldown 223 (arrow) (direction south . arrowdblright) nil ("||v"))
    (lozenge 224 (shape) nil nil ("<>"))
    (angleleft 225 (parenthesis open angleright)
	       (direction west . angleright) 120 ("{"))
    ;;(registered2 226)			; Adobe:registersans
    ;;(copyright2 227)			; Adobe:copyrightsans
    (trademark 228 (symbol "T") nil nil ("TM"))	; Adobe:trademarksans
    (summation 229 (bigop) (size big . Sigma))
    (angleright 241 (parenthesis close angleleft) (direction east) 120 ("}"))
    (integral 242 (bigop) (size big) nil (t "|'")))
  "Table for registry \"fontspecific\", see `x-symbol-init-cset'.")

(defvar x-symbol-xsymb1-table
  '((verticaldots 33 (dots) (direction north . ellipsis) nil (":."))
    (backslash1 34 (line) nil nil ("\\"))
    (dagger 35 (symbol) (direction north) nil ("|+"))
    ;;(unused36 36)
    ;;(unused36 37)
    (percent2 38 (symbol) nil nil ("%"))
    (guilsinglright 39 (quote close guilsinglleft) (direction east) 3000 (">"))
					; should be after the relations
    (NG 40 (letter "NG" ng))
    ;;(OE 41 (letter "OE" oe)) ; now latin-9
    (dotlessj 42 (dotaccent "j" nil))
    (ng 43 (letter "ng" NG))
    ;;(oe 44 (letter "oe" OE)) ; now latin-9
    (sharp 45 (symbol) nil nil ("#"))
    (ceilingleft 46 (parenthesis open ceilingright) (shift up . floorleft)
		 nil ("["))
    (ceilingright 47 (parenthesis close ceilingleft) (shift up . floorright)
		  nil ("]"))
    (zero1 48 (digit1 "0"))
    (one1 49 (digit1 "1"))
    (two1 50 (digit1 "2"))
    (three1 51 (digit1 "3"))
    (four1 52 (digit1 "4"))
    (five1 53 (digit1 "5"))
    (six1 54 (digit1 "6"))
    (seven1 55 (digit1 "7"))
    (eight1 56 (digit1 "8"))
    (nine1 57 (digit1 "9"))
    (star 58 (operator) nil nil ("*"))
    (lozenge1 59 (shape) lozenge -240 ("<>"))
    (braceleft2 60 (parenthesis open braceright2)
		(direction west . braceright2) nil ("{"))
    (circleslash 61 (operator) nil nil ("/O"))
    (braceright2 62 (parenthesis close braceleft2) (direction east) nil ("}"))
    (triangle1 63 (triangle) triangle 120)
    (smltriangleright 64 (triangle) (size sml . triangleright))
    (triangleleft 65 (triangle) (direction west . gradient) nil ("<|"))
    (triangle 66 (triangle) (direction north . gradient) nil (t "/_\\"))
    (triangleright 67 (triangle) (direction east . gradient) nil ("|>"))
    (trianglelefteq 68 (triangle) (direction west . trianglerighteq) nil
		    ("<|_") (triangleleft))
    (trianglerighteq 69 (triangle) (direction east) nil ("|>_") (triangleright))
    (periodcentered2 70 (dots) periodcentered 240)
    (dotequal 71 (relation) nil nil ("=."))
    (wrong 72 (relation) (direction south . similar) 1500 ("~"))
    (natural 73 (symbol) nil 120 ("#"))
    (flat 74 (symbol) nil nil ("b"))
    (epsilon1 75 (greek1 "e" nil "epsilon"))
    (hbarmath 76 (mathletter "h"))
    (imath 77 (mathletter "i"))
    (kappa1 78 (greek1 "k" nil "kappa"))
    (jmath 79 (mathletter "j"))
    (ell 80 (mathletter "l"))
    (amalg 81 (bigop) (size sml . coproduct))
    (rho1 82 (greek1 "r" nil "rho"))
    (top 83 (arrow) (direction south . perpendicular) nil ("T"))
    (Mho 84 (greek1 "M" nil  "Mho") (direction south . Omega))
    (floorleft 85 (parenthesis open floorright) (direction west . floorright)
	       nil ("["))
    (floorright 86 (parenthesis close floorleft) (direction east) nil ("]"))
    (perpendicular1 87 (arrow) perpendicular 120)
    (box 88 (shape) nil nil ("[]"))
    (asciicircum1 89 (symbol) nil nil ("^"))
    (asciitilde1 90 (symbol) nil nil ("~"))
    (leadsto 91 (arrow) (direction east) nil ("~>"))
    (quotedbl1 92 (quote) nil nil ("\""))
    (longarrowleft 93 (arrow) (size big . arrowleft) nil
		   ("<-" t "<--") (arrowleft))
    (arrowupdown 94 (arrow) (direction vertical . arrowright) nil
		 ("|v^" "|^v") (arrowup arrowdown))
    (longarrowright 95 (arrow) (size big . arrowright) nil
		    ("->" t "-->") (emdash))
    (longmapsto 96 (arrow) (size big . mapsto) nil ("|->" t "|-->"))
    (longarrowdblboth 97 (arrow) (size big . arrowdblboth) nil ("<=>" t "<==>")
		      (longarrowdblleft))
    (longarrowdblleft 98 (arrow) (size big . arrowdblleft) nil ("<=" t "<==")
		      (arrowdblleft))
    (arrowdblupdown 99 (arrow) (direction vertical . arrowdblright) nil
		    ("||v^" "||^v") (arrowdblup arrowdbldown))
    (longarrowdblright 100 (arrow) (size big . arrowdblright) nil
		       ("=>" t "==>"))
    (mapsto 101 (arrow) (direction east) nil (t "|->"))
    (iff 102 (arrow) longarrowdblboth 120)
    (hookleftarrow 103 (arrow) (direction west . hookrightarrow) nil
		   ("<-`") (leftarrow))
    (hookrightarrow 104 (arrow) (direction east) nil ("'->") (leftharpoonup))
    (arrownortheast 105 (arrow) (direction north-east . arrowright) nil ("/>"))
    (arrowsoutheast 106 (arrow) (direction south-east . arrowright) nil ("\\>"))
    (arrownorthwest 107 (arrow) (direction north-west . arrowright) nil ("\\<"))
    (arrowsouthwest 108 (arrow) (direction south-west . arrowright) nil ("/<"))
    (rightleftharpoons 109 (arrow) (direction horizontal . rightharpoonup) nil
		       (",=`"))
    (leftharpoondown 110 (arrow) (direction south-west . rightharpoondown) nil
		     (",-"))
    (rightharpoondown 111 (arrow) (direction south-east . rightharpoonup) nil
		      ("-,"))
    (leftharpoonup 112 (arrow) (direction north-west . rightharpoonup) nil
		   ("'-"))
    (rightharpoonup 113 (arrow) (direction north-east) nil ("-`"))
    (bardbl 114 (line) (direction east) nil (t "||"))
    (bardbl1 115 (line) bardbl 120 nil (bar1))
    (backslash2 116 (line) nil 240 ("\\"))
    (backslash3 117 (line) nil 120 ("\\"))
    (diagonaldots 118 (dots) (direction south-east . ellipsis) 300 (":."))
    (simequal 119 (relation) nil nil (t "~_") (similar))
    (digamma 120 (mathletter "F"))
    (asym 121 (relation) (direction vertical . smile) nil (">=<"))
    (minusplus 122 (operator) (direction south . plusminus) nil (t "-+"))
    (less2 123 (relation) (direction west . greater2) nil ("<")) ; SGML
    (bowtie 124 (triangle) (direction horizontal . triangle) nil ("|X|"))
    (greater2 125 (relation) (direction east) nil (">")) ; SGML
    (centraldots 126 (dots) (shift up . ellipsis))
    (visiblespace 160 (white) nil nil ("_" ",_," " "))
    (dagger1 161 (symbol) dagger 120)
    (circledot 162 (operator) nil nil (t ".O") (periodcentered))
    (propersqsuperset 163 (relation) (shape square . propersuperset))
    (reflexsqsuperset 164 (relation) (shape square . reflexsuperset) nil
		      nil (propersuperset))
    (gradient1 165 (triangle) gradient 120)
    (propersqsubset 166 (relation) (shape square . propersubset) nil ("<"))
    (reflexsqsubset 167 (relation) (shape square . reflexsubset) nil
		    nil (propersqsubset))
    (smllozenge 168 (shape) (size sml . lozenge))
    (lessless 169 (relation) (direction west . greatergreater) nil ("<<"))
    (greatergreater 170 (relation) (direction east) nil (">>"))
    (unionplus 171 (operator) (shape round direction south) nil
	       (t "\\/+") (union))
    (sqintersection 172 (operator) (shape square . logicaland))
    (squnion 173 (operator) (shape square . logicalor))
    (frown 174 (relation) (direction north . smile) nil (",-,"))
    (smile 175 (relation) (direction south) nil ("`-'"))
    (reflexprec 176 (relation) (shape curly . lessequal) nil nil (properprec))
    (reflexsucc 177 (relation) (shape curly . greaterequal) nil nil
		(propersucc))
    (properprec 178 (relation) (shape curly . propersubset))
    (propersucc 179 (relation) (shape curly . propersuperset))
    (bardash 180 (arrow) (direction east . perpendicular) nil ("|-"))
    (dashbar 181 (arrow) (direction west . perpendicular) nil ("-|"))
    (bardashdbl 182 (arrow) (direction east) nil ("|="))
    (smlintegral 183 (bigop) (size sml . integral))
    (circleintegral 184 (bigop) (size big) nil (t "|'O") (integral))
    (coproduct 185 (bigop) (direction south . product) nil (t "|_|"))
    (bigcircledot 186 (bigop) (size big . circledot))
    (bigcirclemultiply 187 (bigop) (size big . circlemultiply))
    (bigcircleplus 188 (bigop) (size big . circleplus))
    (biglogicaland 189 (bigop) (size big . logicaland))
    (biglogicalor 190 (bigop) (size big . logicalor))
    (bigintersection 191 (bigop) (size big . intersection))
    (bigunion 192 (bigop) (size big . union))
    (bigunionplus 193 (bigop) (size big . unionplus) nil nil (bigunion))
    (bigsqunion 194 (bigop) (size big . squnion))
    (bigcircle 195 (operator) (size big . circ) nil ("O"))
;;;    (quotedblbase 196 (quote) (shift down) nil ("\""))
;;;    (quotedblleft 197 (quote open quotedblright)
;;;		  (direction west . quotedblright) nil ("``"))
;;;    (quotedblright 198 (quote close quotedblleft) (direction east) nil ("''"))
    (guilsinglleft 196 (quote open guilsinglright)
		   (direction west . guilsinglright) nil ("<"))
    (circleminus 197 (operator) Theta 120 ("-O"))
    (smltriangleleft 198 (triangle) (size sml . triangleleft))
    (perthousand 199 (symbol) nil nil ("%."))
    (existential1 200 (symbol) nil nil ("E"))
    (daggerdbl1 201 (symbol) daggerdbl 120 nil (dagger1))
    (daggerdbl 202 (symbol) (direction vertical . dagger) nil
	       (t "|++") (dagger))
    (bigbowtie 203 (triangle) (size big . bowtie))
    (circ 204 (operator) (shift up) nil ("o"))
    (grave 205 (grave accent))
    (circumflex 206 (circumflex accent))
    (tilde 207 (tilde accent))
    (longarrowboth 208 (arrow) (size big . arrowboth) nil ("<->" t "<-->")
		   (longarrowleft))
    (endash 209 (line) nil nil ("-" "--"))	; TeX
    (emdash 210 (line) (size big) nil ("-" "--" "---")) ; TeX
    ;;(Ydiaeresis 211 (diaeresis "Y" ydiaeresis)) ; now latin-9
    (ampersand2 212 (symbol) nil nil ("&"))	; TeX, SGML
    (universal1 213 (symbol) nil nil ("A"))
    (booleans 214 (setsymbol "B"))
    (complexnums 215 (setsymbol "C"))
    (natnums 216 (setsymbol "N"))
    (rationalnums 217 (setsymbol "Q"))
    (realnums 218 (setsymbol "R"))
    (integers 219 (setsymbol "Z"))
    (lesssim 220 (relation) (direction west . greatersim) nil (t "<~"))
    (greatersim 221 (relation) (direction east) nil (t ">~"))
    (lessapprox 222 (relation) (direction west . greaterapprox) nil (t "<~~"))
    (greaterapprox 223 (relation) (direction east) nil (t ">~~"))
    (definedas 224 (relation) nil nil (t "/_\\=" "^=") (triangle))
    (circleminus1 225 (operator) circleminus 240)
    (circleasterisk 226 (operator) nil nil ("*O") (asterisk1))
    (circlecirc 227 (operator) nil nil ("oO") (circ))
    (dollar1 228 (currency "$") nil nil ("$"))
    ;;(euro 229 (currency "C") nil nil ("C=")) ; now latin-9
    (therefore1 230 (dots) (direction nil . ellipsis) nil (".:"))
    (coloncolon 231 (dots) nil nil ("::"))
    (bigsqintersection 232 (bigop) (size big . sqintersection))
    (semanticsleft 233 (parenthesis open semanticsright)
		   (direction west . semanticsright) nil ("[[" t "[|"))
    (semanticsright 234 (parenthesis close semanticsleft)
		    (direction east) nil ("]]" t "|]"))
    (cataleft 235 (parenthesis open cataright)
	      (direction west . cataright) nil (t "(|"))
    (cataright 236 (parenthesis close cataleft)
	       (direction east) nil (t "|)"))
    )
  "Table for registry \"xsymb1\", see `x-symbol-init-cset'.")

(defvar x-symbol-no-of-charsyms (+ 179 274)) ; latin{1,2,3,5,9}, xsymb{0,1}


;;;===========================================================================
;;;  Calling the init code
;;;===========================================================================

(unless noninteractive
  ;; necessary for batch compilation of x-symbol-image.el etc.  CW: maybe
  ;; calling the init code here isn't that good after all (see info node
  ;; "Miscellaneous Questions"), we'll see later...
  (x-symbol-initialize)
  (setq x-symbol-all-charsyms nil)

  ;; temp hack for console.  TODO: find better ways to prevent warnings etc
  (unless (console-type)
    (unless x-symbol-default-coding
      (warn "X-Symbol: only limited support on a console"))
    (unless (eq x-symbol-latin-force-use 'console-user)
      (setq x-symbol-latin1-fonts nil)
      (setq x-symbol-latin2-fonts nil)
      (setq x-symbol-latin3-fonts nil)
      (setq x-symbol-latin5-fonts nil)
      (setq x-symbol-latin9-fonts nil)
      (setq x-symbol-xsymb0-fonts nil)
      (setq x-symbol-xsymb1-fonts nil)))
  
  (x-symbol-init-cset x-symbol-latin1-cset x-symbol-latin1-fonts
		      x-symbol-latin1-table)
  (x-symbol-init-cset x-symbol-latin2-cset x-symbol-latin2-fonts
		      x-symbol-latin2-table)
  (x-symbol-init-cset x-symbol-latin3-cset x-symbol-latin3-fonts
		      x-symbol-latin3-table)
  (x-symbol-init-cset x-symbol-latin5-cset x-symbol-latin5-fonts
		      x-symbol-latin5-table)
  (x-symbol-init-cset x-symbol-latin9-cset x-symbol-latin9-fonts
		      x-symbol-latin9-table)
  (x-symbol-init-latin-decoding)

  (x-symbol-init-cset x-symbol-xsymb0-cset x-symbol-xsymb0-fonts
		      x-symbol-xsymb0-table)
  (x-symbol-init-cset x-symbol-xsymb1-cset x-symbol-xsymb1-fonts
		      x-symbol-xsymb1-table))

;; (when x-symbol-mule-change-default-face
;;   (set-face-font 'default (face-attribute 'x-symbol-face :font)))

(easy-menu-define x-symbol-menu-map x-symbol-mode-map
		  "X-Symbol menu." x-symbol-menu)


;;; Local IspellPersDict: .ispell_xsymb
;;; x-symbol.el ends here
