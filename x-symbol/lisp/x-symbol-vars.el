;;; x-symbol-vars.el --- customizable variables for package x-symbol

;; Copyright (C) 1995-1999, 2001-2002 Free Software Foundation, Inc.
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

;; This file contains all customizable variables, except token language
;; specific ones.  It avoids loading the main file when browsing the customize
;; menus.

;;; Code:

(provide 'x-symbol-vars)
(require 'x-symbol-hooks)
(eval-when-compile (require 'cl))

(defconst x-symbol-version "4.4.5"
  "Current development version of package X-Symbol.
Check <http://x-symbol.sourceforge.net/> for the newest.")


;;;===========================================================================
;;;  Custom groups
;;;===========================================================================

(defgroup x-symbol nil
  "Semi WYSIWYG for LaTeX, HTML, etc using additional fonts."
  :group 'wp
  :link '(info-link "(x-symbol)")
  :link '(url-link "http://x-symbol.sourceforge.net/")
  :prefix "x-symbol-")

(defgroup x-symbol-mode nil
  "Controlling whether and how to turn on X-Symbol mode."
  :group 'x-symbol
  :prefix "x-symbol-")

(defgroup x-symbol-input-init nil
  "Initialization of input methods supported by X-Symbol."
  :group 'x-symbol
  :prefix "x-symbol-")

(defgroup x-symbol-input-control nil
  "Control if input methods supported by X-Symbol."
  :group 'x-symbol
  :prefix "x-symbol-")

(defgroup x-symbol-info-general nil
  "General customization of X-Symbol info in echo area."
  :group 'x-symbol
  :prefix "x-symbol-")

(defgroup x-symbol-info-strings nil
  "Customization of X-Symbol info strings in echo area."
  :group 'x-symbol
  :prefix "x-symbol-")

(defgroup x-symbol-miscellaneous nil
  "Miscellaneous customization for X-Symbol."
  :group 'x-symbol
  :prefix "x-symbol-")

(defgroup x-symbol-image-general nil
  "General customization of images in X-Symbol buffers."
  :group 'x-symbol
  :prefix "x-symbol-")			; not "x-symbol-image-" !

(defgroup x-symbol-image-language nil
  "Language dependent customization of images in X-Symbol buffers."
  :group 'x-symbol
  :prefix "x-symbol-")			; not "x-symbol-image-" !

;;; language specific groups =================================================
;; they should not be defined in the x-symbol-LANG.el because this would
;; require the custom commands to load all languages when customizing the top
;; group `x-symbol'.

(defgroup x-symbol-tex nil
  "X-Symbol token language \"TeX macro\"."
  :group 'x-symbol
  :group 'tex
  :prefix "x-symbol-tex-")

(defgroup x-symbol-sgml nil
  "X-Symbol token language \"SGML entity\"."
  :group 'x-symbol
  :group 'sgml
  :prefix "x-symbol-sgml-")

(defgroup x-symbol-bib nil
  "X-Symbol token language \"BibTeX macro\"."
  :group 'x-symbol
  :group 'tex
  :prefix "x-symbol-bib-")

(defgroup x-symbol-texi nil
  "X-Symbol token language \"TeXinfo command\"."
  :group 'x-symbol
  :group 'tex
  :group 'docs
  :prefix "x-symbol-texi-")


;;;===========================================================================
;;;  Custom widgets
;;;===========================================================================

;; Shouldn't this be a generally useful widget type?
(define-widget 'x-symbol-key 'sexp
  "A key or mouse stroke."
  :tag "Key/Mouse stroke")

(define-widget 'x-symbol-auto-style 'list
  "Auto-mode setup."
  ;; Also allows=matches (t) as (t nil nil nil nil nil).  In older XEmacsen,
  ;; this was not possible and we had to use an "option-group-inline chain".
  ;; Drop support for all XEmacsen where this is still necessary:
  ;;  * (group foo bar ...)
  ;;  * (group foo (option (group :inline t :extra-offset -4 bar (...))))
  :args '((sexp :tag "Turn on if (eval'd)")
	  (sexp :tag "Coding (eval'd)")
	  (sexp :tag "Save 8bits (eval'd)")
	  (sexp :tag "Unique decoding (eval'd)")
	  (sexp :tag "Super/subscripts (eval'd)")
	  (sexp :tag "Show images (eval'd)")))

(defvar x-symbol-auto-style nil
  "Variable used to document the auto-style language accesses.
For each token language LANG, `x-symbol-LANG-auto-style' determines how
to set X-Symbol specific buffer-local variables if these variables do
not already have a buffer-local value.

A value of such a language access looks like
  (MODE-ON CODING 8BITS UNIQUE SUBSCRIPTS IMAGE)

If `x-symbol-mode' is not already buffer-local, MODE-ON determines
whether to turn the mode on if \\[x-symbol-mode] is called with a cons
as prefix argument.  LANGUAGE, CODING, 8BITS, UNIQUE, SUBSCRIPTS and
IMAGE are used to set `x-symbol-language', `x-symbol-coding',
`x-symbol-8bits', `x-symbol-unique', `x-symbol-subscripts' and
`x-symbol-image' if these values are not already buffer-local.

During evaluation, a non-nil `buffer-file-name' is sans backup versions
or strings, and without suffixes in `x-symbol-auto-mode-suffixes', and
`x-symbol-mode' is bound to the `eval'ed MODE-ON.  Then, the above
mentioned variables are set to the `eval'ed LANGUAGE, CODING, 8BITS,
UNIQUE, SUBSCRIPTS and IMAGE in that order, if the variables is not
already buffer-local.  If CODING evaluates to nil, `x-symbol-coding' is
set according to `x-symbol-auto-8bit-search-limit', if CODING evaluates
to `null', `x-symbol-coding' is set to nil.

Users might prefer to customize `x-symbol-auto-style-alist' instead.")

;;	  :value (nil nil nil nil nil nil)))
;;(define-widget 'x-symbol-auto-style 'checklist
;;  "Auto-mode setup."
;;  :args '((group
;;	   :inline t :extra-offset -4
;;	   (sexp :tag "Turn on if (eval'd)")
;;	   (option
;;	    (group
;;	     :inline t :extra-offset -4
;;	     (sexp :tag "Coding (eval'd)")
;;	     (option
;;	      (group
;;	       :inline t :extra-offset -4
;;	       (sexp :tag "Save 8bit (eval'd)")
;;	       (option
;;		(group
;;		 :inline t :extra-offset -4
;;		 (sexp :tag "Unique decoding (eval'd)")
;;		 (option
;;		  (group
;;		   :inline t :extra-offset -4
;;		   (sexp :tag "Super/subscripts (eval'd)")
;;		   (option
;;		    (group
;;		     :inline t :extra-offset -4
;;		     (sexp :tag "Show images (eval'd)"))))))))))))))


;;;===========================================================================
;;;  Custom widgets, general
;;;===========================================================================

;; Shouldn't this be generally a useful widget type?
(define-widget 'x-symbol-command 'function
  "A lisp command."
  :prompt-match 'commandp
  :tag "Command")

(define-widget 'x-symbol-charsym 'symbol
  "X-Symbol charsym."
  :tag "X-Symbol charsym")

(define-widget 'x-symbol-group 'symbol
  "X-Symbol charsym group."
  :tag "Charsym group")

(define-widget 'x-symbol-coding 'choice
  "X-Symbol 8bit character coding."
  :tag "8bit coding"
  :args '((const iso-8859-1)
	  (const iso-8859-2)
	  (const iso-8859-3)
	  (const iso-8859-9)
	  (const iso-8859-15)))

(define-widget 'x-symbol-function-or-regexp 'choice
  "Function or regexp, see `x-symbol-call-function-or-regexp'."
  :args '((const :tag "None" nil) regexp function))

(define-widget 'x-symbol-fancy-spec 'repeat
  "X-Symbol specification for fancy strings, without string."
  :args '((group :value (0 -1 x-symbol-info-face)
		 (option (group :inline t :extra-offset -4
				:value (0 -1)
				(integer :tag "From")
				(option (integer :tag "To" :value -1))))
		 (repeat :tag "Faces" :inline t (face :tag "Face")))))

(define-widget 'x-symbol-fancy 'cons
  "X-Symbol specification for fancy strings, with string."
  :args '(string (x-symbol-fancy-spec :tag "Face specifications")))


;;;===========================================================================
;;;  Custom simple, special
;;;===========================================================================

(define-widget 'x-symbol-auto-coding 'repeat
  "X-Symbol automatic coding control."
  :args '((cons :format "%v"
		regexp
		(choice x-symbol-coding
			(cons :tag "Depending on"
			      (integer :tag "Match")
			      (repeat (cons :format "%v"
					    (string :tag "Key")
					    x-symbol-coding)))))))

(define-widget 'x-symbol-headers 'repeat
  "Headers for grid and menu."
  :args '((cons :format "%v"
		(string :tag "Header")
		(repeat x-symbol-group))))

(define-widget 'x-symbol-class-info 'repeat
  "Definitions for X-Symbol token language classes."
  :args '((cons :format "%v"
		(symbol :tag "Token class" :value VALID)
		(choice (const :tag "No info" nil)
			(x-symbol-fancy :tag "Info")))))

(define-widget 'x-symbol-class-faces 'repeat
  "Definitions for X-Symbol token language classes."
  :args '((list :format "%v"
		(symbol :tag "Token class")
		(face :tag "Face in grid" :value default)
		(x-symbol-fancy-spec :inline t
				     :tag "Faces for tokens in info"))))

(define-widget 'x-symbol-image-keywords 'cons
  "Format of image keywords"
  :args '((regexp :tag "Regexp matching all image files")
	  (repeat
	   (list :format "%v"
		 :value ("IMAGE \"\\([A-Za-z0-9]\\)\"" 1)
		 regexp
		 (option (function :match (lambda (widget arg)
					    (and arg (symbolp arg)))
				   :value x-symbol-image-default-file-name))
		 (repeat :inline t :tag "Arguments" sexp)))))


;;;===========================================================================
;;;  custom set function
;;;===========================================================================

(defconst x-symbol-cache-variables '(x-symbol-fancy-value-cache
				     x-symbol-charsym-info-cache
				     x-symbol-charsym-info-cache
				     x-symbol-language-info-caches
				     x-symbol-coding-info-cache
				     x-symbol-keys-info-cache)
  "Internal.  Cache variables.")

;; TODO: not used anymore (would prevent files to be compilable w/o X-Symbol
(defun x-symbol-set-cache-variable (var value)
  "Set VAR's value to VALUE.
Custom set function of variables for fancy strings."
  (set var value)
  (dolist (cache x-symbol-cache-variables)
    (and (boundp cache) (set cache nil))))


;;;===========================================================================
;;;  Identity
;;;===========================================================================

(defvar x-symbol-package-url "http://x-symbol.sourceforge.net/index.html"
  "URL used by \\[x-symbol-package-web].
If you have a local copy, you might want to change the value.  The
default is \"http://x-symbol.sourceforge.net/index.html\".")

(defconst x-symbol-maintainer-address "wedler@users.sourceforge.net"
  "E-mail address of maintainer, used by \\[x-symbol-package-bug].")

(defvar x-symbol-installer-address nil
  "E-mail address of person who has installed package X-Symbol system-wide.
Used for normal reports by \\[x-symbol-package-bug].  If nil, normal
reports are sent to `x-symbol-maintainer-address'.")


;;;===========================================================================
;;;  General Options (appear in the menu)
;;;===========================================================================

(defcustom x-symbol-token-input t
  "*If non-nil, enable input method TOKEN.
With input method TOKEN, and if the characters before point represent a
token, an insertion command after a completed token forces Emacs to
replace the token before point by the corresponding character.  Use
\"\\[universal-argument] 0 space\" to just replace the token.  Use
\\[undo] or \\[unexpand-abbrev] to undo the replacement.

A command is considered to be a insertion command if it is a self-insert
command or has a non-nil symbol property `x-symbol-input'."
  :group 'x-symbol-input-control
  :type 'boolean)

(x-symbol-define-user-options 'x-symbol-token-input '(t))

(defcustom x-symbol-electric-input t
  "*If non-nil, enable input method ELECTRIC.
With this features, some contexts of input method CONTEXTS are
automatically replaced with the corresponding character, i.e., you do
not have to invoke \\[x-symbol-modify-key].  Use \\[undo] or
\\[unexpand-abbrev] to undo the replacement.

Because an unwanted replacement of a context with a character can be
quite annoying, the following conditions must be fulfilled:

 * The context must have been defined as an electric context for the
   character, see `x-symbol-init-cset'.
 * The character must be valid, i.e., represent a token of the current
   token language, see `x-symbol-valid-charsym-function'.
 * All characters of the context have been typed without any other
   command in between, e.g., with language \"TeX macro\", \"- >\" inserts
   \\to, \"- \\[backward-char] \\[forward-char] >\" simply inserts \"->\".
 * No prefix argument has been used for any character in the context.
 * The electric context must not be a suffix of a longer valid context
   for another character.  E.g., \"''o\" is not changed to \"'\"+`oacute'
   because \"''o\" is the context for `ohungarumlaut'.
 * Contexts matched by a global or a token language dependent regexp are
   not replaced.  Functions can also be used to prevent a context to be
   replaced by a character.  E.g., with language \"TeX macro\", only
   replace \"->\" by \\to if we are in TeX's math mode (using library
   texmathp by Carsten Dominik).  See `x-symbol-context-ignore' and
   `x-symbol-electric-ignore'."
  :group 'x-symbol-input-control
  :type 'boolean)

(x-symbol-define-user-options 'x-symbol-electric-input '(t))

(defcustom x-symbol-local-menu t
  "*If non-nil, provide a token language specific menu.
In a language specific menu, only insertion commands for valid
characters appear.  The entries are mentioned and sorted according to
the token."
  :group 'x-symbol-input-control
  :type 'boolean)

(x-symbol-define-user-options 'x-symbol-local-menu '(t))

(defcustom x-symbol-local-grid t
  "*If non-nil, provide a token language specific grid.
See `x-symbol-grid'.  In a language specific grid, only valid characters
appear.  They may be also colored according to some language specific
token class coloring scheme.  E.g., with language \"TeX macro\", purple
character can only be used in TeX's math mode, blue character can only
be used in TeX's text mode, see `x-symbol-charsym-face'."
  :group 'x-symbol-input-control
  :type 'boolean)

(x-symbol-define-user-options 'x-symbol-local-grid '(t))

(defcustom x-symbol-temp-grid nil
  "*If non-nil, the X-Symbol grid buffer only appears temporarily.
If a temporary grid is still visible, the first insertion of an X-Symbol
characters restores the window configuration current before the
invocation of `x-symbol-grid'."
  :group 'x-symbol-input-control
  :type 'boolean)

(x-symbol-define-user-options 'x-symbol-temp-grid '(t))

(defcustom x-symbol-temp-help t
  "*If non-nil, the key completion buffer only appears temporarily.
If the temporary key completions buffer is still visible, the first
insertion of an X-Symbol characters restores the window configuration
current before the invocation of `x-symbol-help'."
  :group 'x-symbol-input-control
  :type 'boolean)

(x-symbol-define-user-options 'x-symbol-temp-help '(t))

(defvar x-symbol-use-refbuffer-once 'get-buffer-window
  ;; TODO: customize (probably)
  ;; `pop-up-frames'=t seems to be broken in XEmacs and I don't like
  ;; multi-frames anyway, so I cannot say how it is supposed to work whether
  ;; this really works
  "*Use reference buffer just once when selecting a X-Symbol character.
For both the GRID and the Help buffer.  TODO: more...  A function means,
just once if function returns non-nil.  Function is called with the
reference buffer and called from within the list buffer.

E.g. `get-buffer-window' means: just once only if reference and list
buffer is on same frame.")
;;;  :group 'x-symbol-input-control
;;;  :type 'boolean) ; no, nil or function or sexp=t

;;;(x-symbol-define-user-options 'x-symbol-use-reference-buffer-once '(t))

(defcustom x-symbol-reveal-invisible t
  "*If non-nil, reveal invisible characters at point.
Usually, with a non-nil `x-symbol-subscripts', some parts of the text
might be invisible.  With this feature and if point is in such an area,
all the text in the area is revealed and displayed with
`x-symbol-revealed-face'.  With value t, also reveal if point is
directly after such an area.  See function `x-symbol-reveal-invisible'."
  :group 'x-symbol-info-general
  :group 'x-symbol-miscellaneous
  :type '(radio (const :tag "No" nil)
		(const :tag "Characters Around Point" t)
		(sexp :tag "Character After Point" :format "%t" :value after)))

(x-symbol-define-user-options 'x-symbol-reveal-invisible
    '(after
      (nil . "No")
      (after . "Character After Point")
      (t . "Characters Around Point")))

(defcustom x-symbol-character-info t
  "*If non-nil, display info for characters at point in echo area.
The info for the character after point includes the character itself,
the token of the current language, eventually colored according to some
coloring scheme, the token specific classes, the codings in which the
characters is considered to be a 8bit character and the key bindings.
With value t and no info for the character after point, show info for
character before point instead.  See also `x-symbol-context-info'."
  :group 'x-symbol-info-general
  :type '(radio (const :tag "None" nil)
		(const :tag "Characters Around Point" t)
		(sexp :tag "Character After Point" :format "%t" :value after)))

(x-symbol-define-user-options 'x-symbol-character-info
    '(after
      (nil . "None")
      (after . "Character After Point")
      (t . "Characters Around Point")))

(defcustom x-symbol-context-info t
  "*If non-nil, display info for context before point in echo area.
If enabled and no info for characters at point, display the info for
the character to which \\[x-symbol-modify-key] would replace the context
before point.  See also `x-symbol-character-info'."
  :group 'x-symbol-info-general
  :type 'boolean)

(x-symbol-define-user-options 'x-symbol-context-info '(t))


;;;===========================================================================
;;;  Texts, Modeline appearance
;;;===========================================================================

(defcustom x-symbol-modeline-name "none"
  "*String naming the pseudo language \"x-symbol charsym\" in the modeline."
  :group 'x-symbol-miscellaneous
  :type 'string)

(defcustom x-symbol-coding-name-alist
  '((iso-8859-1 . "Latin-1")
    (iso-8859-2 . "Latin-2")
    (iso-8859-3 . "Latin-3")
    (iso-8859-9 . "Latin-5")
    (iso-8859-15 . "Latin-9"))
  "*Alist of codings with their names presented to the user.
The elements look like (CODING . NAME) where CODING is a valid value for
`x-symbol-coding' and NAME is the NAME used in the menu."
  :group 'x-symbol-miscellaneous
  :type '(repeat (cons :format "%v" x-symbol-coding string)))

;;;(defface x-symbol-modeline-warning-face
;;;  `((((class color) (background light))
;;;     (:foreground "red4")))
;;;  "*TODO"
;;;  :group 'x-symbol-mode)

;;(defcustom x-symbol-coding-modeline-warning-format "%s-err"
;;  "*Format used to display coding which is not supported.
;;See `x-symbol-coding-modeline-text'."
;;  ;; using text properties with faces for the modeline string doesn't work on
;;  ;; XEmacs-21.4.5...
;;  :group 'x-symbol-mode
;;  :type 'string)

(defcustom x-symbol-coding-modeline-alist
  '((iso-8859-1 . "-l1")
    (iso-8859-2 . "-l2")
    (iso-8859-3 . "-l3")
    (iso-8859-9 . "-l5")
    (iso-8859-15 . "-l9")
    (info . "-i")
    (error . "-err"))
  "*Alist of codings with their names in the modeline.
The elements look like (CODING . NAME) where CODING is a valid value for
`x-symbol-coding' and NAME is used by `x-symbol-coding-modeline-text'."
  :group 'x-symbol-mode
  :type '(repeat (cons :format "%v" x-symbol-coding string)))

(defcustom x-symbol-modeline-state-list
  '(" XS:"
    (x-symbol-modeline-name . x-symbol-language-modeline-text)
    (x-symbol-8bits "8")
    (x-symbol-unique "*")
    (x-symbol-coding . x-symbol-coding-modeline-text)
    "/"
    (x-symbol-subscripts "s")
    (x-symbol-image "i"))
  "*Alist used by `x-symbol-update-modeline' to construct the modeline.
This function constructs `x-symbol-modeline-string' by concatenating the
result from the elements in this list.  Each element looks like
  SEPARATOR or
  (VARIABLE NON-NIL . NIL) or
  (ARG . FUNCTION)

SEPARATOR is a string and is used directly, only use the first from two
consecutive SEPARATORs.  If VARIABLE is non-nil, use NON-NIL, otherwise
NIL, both NON-NIL and NIL should be strings or nil.  FUNCTION is called
with argument ARG and should return a string or nil.  Two SEPARATORs
where all the elements in between return nil, are considered to be
consecutive."
  :group 'x-symbol-mode
  :type '(repeat (choice (string :tag "Separator")
			 (cons :tag "Depending on variable"
			       variable
			       (cons :format "%v"
				     (choice :tag "Non-nil"
					     (const :tag "Nothing" nil) string)
				     (choice :tag "Nil"
					     (const :tag "Nothing" nil)
					     string)))
			 (cons :tag "Calling function"
			       (sexp :tag "With argument")
			       function))))


;;;===========================================================================
;;;  Minor mode control
;;;===========================================================================

(defcustom x-symbol-auto-coding-search-limit 10000
  "*Limits searching for coding strings in the file.
Used in variable `x-symbol-auto-mode-alist' when finding an appropriate
value for `x-symbol-coding'."
  :group 'x-symbol-mode
  :type '(choice (const :tag "No limit" nil) (integer :tag "Limit")))


;;;===========================================================================
;;;  Misc
;;;===========================================================================

(defcustom x-symbol-charsym-ascii-alist nil
  "Alist of charsyms and their Ascii representation.
Each element looks like (CHARSYM . ASCII) where CHARSYM is a x-symbol
charsym and ASCII is a string.  Used by `x-symbol-translate-to-ascii'.

E.g., if you prefer the German way to Asciify accented characters, use
  (setq x-symbol-charsym-ascii-alist
	'((adiaeresis . \"ae\") (Adiaeresis . \"Ae\")
	  (odiaeresis . \"oe\") (Odiaeresis . \"Oe\")
	  (udiaeresis . \"ue\") (Udiaeresis . \"Ue\")))"
  :group 'x-symbol-miscellaneous
  :type '(repeat (cons :format "%v" x-symbol-charsym string)))

(defcustom x-symbol-charsym-ascii-groups
  '(digit1
    letter slash cedilla ogonek dotaccent ring tilde breve
    circumflex caron diaeresis hungarumlaut acute grave)
  "Charsym groups with default ascii representations.
Charsyms with a group in this list use their subgroup string as the last
possibility as the ascii representation.  See `x-symbol-init-cset' for
details.  Used by `x-symbol-translate-to-ascii'."
  :group 'x-symbol-miscellaneous
  :type '(repeat x-symbol-group))

(defcustom x-symbol-valid-charsym-function 'x-symbol-default-valid-charsym
  "Function which should return non-nil if a charsym is valid.
Function is called with the charsym and optional language."
  :group 'x-symbol-input-control
  :type 'function)

(defvar x-symbol-user-table nil
  "List of character definitions: groups, aspects, input.
Used to shadow default elements with key CHARSYM in the default tables.
The elements have the following form, as explained in
`x-symbol-init-cset', DUMMY is not used:
  (CHARSYM DUMMY GROUPING ASPECTS SCORE INPUT PREFIXES)

E.g., if you prefer charsym `epsilon1' over `epsilon', you might want to
copy the table element from `x-symbol-xsymb1-table' and change its score:
use the following element in this table:
  (epsilon1 t (greek1 \"e\" nil \"epsilon\") nil -3000)")

(defvar x-symbol-mule-change-default-face nil
  "If non-nil, change font of default face for existing charsets.
The default face is never changed for the charset registry corresponding
to `x-symbol-default-coding'.  It is always set for new charsets.
Otherwise, this value determines whether it is changed.")


;;;===========================================================================
;;;  Commands in X-Symbol map
;;;===========================================================================

(defcustom x-symbol-map-default-keys-alist
  '((help x-symbol-help)
    ((control ?h) x-symbol-help)
    (button1)
    (button2)
    (button3)
    (down-mouse-1 ignore)
    (down-mouse-2 ignore)
    (down-mouse-3 ignore)
    (mouse-1)
    (mouse-2)
    (mouse-3)
    ((meta home) beginning-of-buffer-other-window t)
    ((meta end) end-of-buffer-other-window t)
    ((meta prior) scroll-other-window-down t)
    ((meta next) scroll-other-window t))
  "Alist used by `x-symbol-map-default-binding'.
Each element looks like (KEY COMMAND TEMPORARYP).

If the last event in the undefined X-Symbol key sequence matches KEY,
see `events-to-keys', COMMAND is executed.  If COMMAND is nil, execute
command which has binding KEY without prefix of the X-Symbol key
sequence.  IF TEMPORARYP is non-nil, use key prefix and the prefix
argument for the following command."
  :group 'x-symbol-input-control
  :type '(repeat (group x-symbol-key
			(choice (const :tag "Usual command" nil)
				x-symbol-command)
			(boolean :tag "Temporary"))))

(defcustom x-symbol-map-default-bindings
  '(("\C-i"    x-symbol-read-token-direct)
    ("\C-m"    x-symbol-read-token)
    (nil       x-symbol-grid)
    ([(left)]  x-symbol-modify-key)
    ([(right)] x-symbol-modify-key)
    ([(up)]    x-symbol-rotate-key)
    ([(down)]  x-symbol-rotate-key))
  "TODO.  nil = (vector x-symbol-compose-key)"
  :group 'x-symbol-input-control
  :type '(repeat (group (sexp :tag "Key sequence" nil)
			x-symbol-command)))

(defvar x-symbol-after-init-input-hook nil
  "Hook run after the initialization of all input methods.
See `x-symbol-init-input'.  If you want define key bindings starting
with \\[x-symbol-map], do it here.  It is a bad idea to use this for
additional self insert commands, use \"character descriptions\" in
`x-symbol-user-table' instead.")


;;;===========================================================================
;;;  Menu (option part)
;;;===========================================================================

;; As long as custom does not offer a widget for menu entries...no defcustom
;; WARNING: XEmacs-20.4 :suffix STRING
(defvar x-symbol-menu
  '("X-Symbol" :filter x-symbol-menu-filter
    ("Conversion in %s" :filter x-symbol-extra-filter
     ["Conversion" nil x-symbol-region-text] ; pseudo entry
     ["Encode Characters" x-symbol-encode
      :active (and x-symbol-language (not buffer-read-only))]
     ["Encode & Recode" x-symbol-encode-recode
      :active (and x-symbol-coding
		   (not (eq x-symbol-coding x-symbol-default-coding))
		   x-symbol-language (not buffer-read-only))]
     ["Decode Tokens" x-symbol-decode
      :active (and x-symbol-language (not buffer-read-only))]
     ["Recode & Decode" x-symbol-decode-recode
      :active (and x-symbol-coding
		   (not (eq x-symbol-coding x-symbol-default-coding))
		   x-symbol-language (not buffer-read-only))]
     ["Replace Char Aliases" x-symbol-unalias
      :active (not buffer-read-only)])
    ;;
    ("Other Commands" :filter x-symbol-extra-filter
     ["Other Commands" nil nil]		; pseudo entry
     ["Copy Encoded" x-symbol-copy-region-encoded
      ;;(x-symbol-copy-region-encoded (region-beginning) (region-end))
      :active (and x-symbol-language (region-active-p))]
     ["Paste Decoded" x-symbol-yank-decoded
      :active (and x-symbol-mode (not buffer-read-only))]
     "---"
     ["GRID Of Characters" x-symbol-grid t]
     ["READ Token Character" x-symbol-read-token (not buffer-read-only)]
     "---"
     ["Modify CONTEXT" x-symbol-modify-key (not buffer-read-only)]
     ["Rotate CONTEXT" x-symbol-rotate-key (not buffer-read-only)]
     "---"
     ["Info Page" x-symbol-package-info t]
     ["Web Page" x-symbol-package-web t]
     ["Send Bug/Problem Report" x-symbol-package-bug t])
    ;;
    ("Buffer/File Options" :filter x-symbol-options-filter
     ["X-Symbol Mode" x-symbol-mode t]
     "---"
     ["Token Language:" x-symbol-language t]
     ["8bit Char Encoding:" x-symbol-coding t]
     ["Store 8bit In File" x-symbol-8bits t]
     ["Unique Decoding" x-symbol-unique t]
     "---"
     ["Super-/Subscripts" x-symbol-subscripts
      (x-symbol-subscripts-available-p)]
     ["Show Images" x-symbol-image (x-symbol-image-available-p)])
    ;;
    ("General Options" :filter x-symbol-options-filter
     ["Input Method TOKEN" x-symbol-token-input t]
     ["Input Method ELECTRIC" x-symbol-electric-input t]
     "---"
     ["Language Specific GRID" x-symbol-local-grid t]
     ["Language Specific MENU" x-symbol-local-menu t]
     "---"
     ["Temporary GRID" x-symbol-temp-grid t]
     ["Temporary Key Completions" x-symbol-temp-help t]
     "---"
     ["Reveal Invisible" x-symbol-reveal-invisible t]
     ["Display Character Info" x-symbol-character-info t]
     ["Display Context Info" x-symbol-context-info t]
     "---"
     ["Browse Customization" (customize-browse 'x-symbol) t])
    "---")
  "First entries of the x-symbol menu, language specific or not.
The next items are submenus with commands to insert x-symbol characters.
See also `x-symbol-header-groups-alist'.")


;;;===========================================================================
;;;  Menu (insert commands part), Grid
;;;===========================================================================

(defcustom x-symbol-menu-max-items 30
  "*Maximum number of entries in submenus of the x-symbol menu.
If the number of character input commands in a submenu exceed this
value, use more than one submenu for the same header.  These submenus
have nearly the same length.  See also `x-symbol-header-groups-alist'."
  :group 'x-symbol-input-init
  :type 'integer)

(defcustom x-symbol-header-groups-alist
  '(("Operator" bigop operator)
    ("Relation" relation)
    ("Arrow" arrow)
    ("Shaped" triangle shape)
    ("Punctuation" white line dots punctuation quote parenthesis)
    ("Symbol" symbol currency)
    ("Math Letter" mathletter setsymbol)
    ("Greek Letter" greek greek1)
    ("Misc. Letter" letter slash)
    ("Cedilla, Ogonek" cedilla ogonek)
    ("Dotaccent, Ring" dotaccent ring)
    ("Tilde, Breve" tilde breve)
    ("Circumflex, Caron" circumflex caron)
    ("Diaeresis, Umlaut" diaeresis hungarumlaut)
    ("Acute, Grave" acute grave))
  "Alist to determine the header/submenu for characters.
Each element looks like (HEADER GROUP...) where HEADER is a string and
GROUP is the group of a character as explained in `x-symbol-init-cset'.
This alist is used for `x-symbol-grid' and the `x-symbol-menu'.
Token languages might define their own alist."
;; TODO: mention: before init
  :group 'x-symbol-input-init
  :type 'x-symbol-headers)

(defcustom x-symbol-completions-buffer "*X-Symbol Key Completions*"
  "Buffer name for key completions buffer.
Used by `x-symbol-help', i.e., when pressing Help during a x-symbol
key sequence."
  :group 'x-symbol-input-init
  :type 'string)

(defcustom x-symbol-grid-buffer-format "*X-Symbol Grid (%s)*"
  "Buffer name format for grid buffers.
Used with substitution `x-symbol-charsym-name'/%s when invoked from a
buffer without a valid token language or if `x-symbol-local-grid' has
value nil.  Otherwise, used with substitution NAME/%s where NAME is the
name of `x-symbol-language'."
  :group 'x-symbol-input-init
  :type 'string)

(defcustom x-symbol-grid-reuse t
  "If non-nil, \\[x-symbol-grid] reuses old grid buffers.
If non-nil, avoid unnecessary computations.  You should probably set
this to nil, if you use side-by-side buffers with different width."
  :group 'x-symbol-input-control
  :type 'boolean)

(defcustom x-symbol-grid-header-echo
  '("button2 scrolls up/down, button3 pops up X-Symbol menu  (all non-highlighted parts)"
    (8 24 x-symbol-info-face) (33 54 x-symbol-info-face)
    (56 x-symbol-info-face))
  "Text used for the echo are if mouse if over a heading.
See `x-symbol-fancy-value' for the value type."
  :group 'x-symbol-input-init
  :group 'x-symbol-info-strings
  :set 'x-symbol-set-cache-variable
  :type 'x-symbol-fancy)

(defcustom x-symbol-grid-ignore-charsyms '(nobreakspace)
  "Charsyms not being displayed in the grid, see `x-symbol-grid'."
  :group 'x-symbol-input-control
  :type '(repeat x-symbol-charsym))
;; problems with var-space fonts

(defcustom x-symbol-grid-tab-width 4	; TODO Emacs better?  3 too small
  "Tab width in the grid between characters, see `x-symbol-grid'.
The widest character should not be wider than the tab width if the
default face has font of `x-symbol-heading-face'."
  :group 'x-symbol-input-init
  :type 'number)

(defface x-symbol-heading-face
  `((((class color) (background light))
     (:foreground "green4"
		  :bold t :family "Helvetica"
		  ,@(if (featurep 'xemacs) '(:size "12pt"))
		   :underline t)))	; underline must be last...
  ;;(:foreground "green4" :underline t)))
  "Face used for headers in the grid buffers.
The defined font is used as default font and influences the correct
value of `x-symbol-grid-tab-width'."
  :group 'x-symbol-input-init)

(defvar x-symbol-heading-strut-glyph
  (make-glyph (eval-when-compile
		`(((x) . [xbm :data (6 20 ,(make-string 20 0))])
		  ((mswindows) . [xbm :data (6 20 ,(make-string 20 0))])
		  ((tty) . [string :data " "]))))
  "Glyph at the end of headers in grid buffers, see `x-symbol-grid'.
Allows to have a larger interline spacing when the line starts with a
header.")


;;;===========================================================================
;;;  Other input methods
;;;===========================================================================

(defvar x-symbol-key-init-ignore nil
  "Regexp matching contexts not being used by input method QUAIL.")
;; TODO: just regexp, more text

(defvar x-symbol-quail-init-ignore " "
  "Regexp matching contexts not being used by input method QUAIL.")
;; TODO: just regexp, more text

(defvar x-symbol-context-init-ignore " "
  "Regexp matching contexts not being used by input method CONTEXT.
As opposed to `x-symbol-context-ignore', this is already used during
initialization.  It also allows the input method CONTEXT to consider the
next shorter context.")
;; just regexp

(defcustom x-symbol-context-ignore nil
  "Regexp matching contexts not to be replaced by input method CONTEXT.
You may also use a function instead of a regexp, see
`x-symbol-call-function-or-regexp'."
  :group 'x-symbol-input-control
  :type 'x-symbol-function-or-regexp)
;; TODO: mention that fn is called with CONTEXT CHARSYM

(defcustom x-symbol-electric-ignore "[ \t]\\|'[ls]"
  "Regexp matching contexts not to be replaced by input method ELECTRIC.
A language dependent regexp is also checked before a context is
replaced, see `x-symbol-electric-input' for details.  You may also use a
function instead of a regexp, see `x-symbol-call-function-or-regexp'."
  :group 'x-symbol-input-control
  :type 'x-symbol-function-or-regexp)

(defcustom x-symbol-rotate-suffix-char ?\#
  "Additional suffix character usually used to simulate Greekifying.
\\[x-symbol-modify-key] modifies the longest context before point
whereas \\[x-symbol-rotate-key] appends this character to the context to
determine the correct target character for the context.  The value is
typically a suffix being defined in `x-symbol-group-input-alist'."
  :group 'x-symbol-input-control
  :type 'character)

(defcustom x-symbol-rotate-prefix-alist
  '((8 . north)
    (7 . north-west)
    (4 . west)
    (1 . south-west)
    (2 . south)
    (28 . vertical)
    (82 . vertical)
    (3 . south-east)
    (6 . east)
    (64 . horizontal)
    (46 . horizontal)
    (9 . north-east)
    (5 . nil))
  "Alist used if `x-symbol-rotate-key' is called with a prefix arg.
Each element looks like (NUMBER . DIRECTION) where NUMBER is the numeric
value of the prefix argument and DIRECTION is a valid direction in
`x-symbol-rotate-aspects-alist'."
  :group 'x-symbol-input-control
  :type '(repeat (cons :format "%v"
		       (integer :tag "Numeric Prefix Arg")
		       (symbol :tag "Direction"))))

(defvar x-symbol-list-mode-hook nil
  "Hook run at the end of `x-symbol-list-mode'.")

;;;  Before init-input: ======================================================

(defvar x-symbol-key-min-length 2
  "Minimum number of key strokes in a x-symbol key sequence.
If the key context is shorter than this value, use \"1\" as an
additional key suffix.  See `x-symbol-init-input' for details.")

(defvar x-symbol-quail-suffix-string ";"
  "TODO")

(defvar x-symbol-define-input-method-quail (featurep 'mule))


;;;===========================================================================
;;;  Invisible and Info (part 1)
;;;===========================================================================

(defcustom x-symbol-idle-delay 0.5
  "*Time in seconds of idle time before showing info in the echo area.
Also used as idle time before revealing invisible characters.  See
`x-symbol-character-info', `x-symbol-context-info' and
`x-symbol-reveal-invisible'.  See also `x-symbol-start-itimer-once'."
  :group 'x-symbol-miscellaneous
 :type 'number)

(defface x-symbol-revealed-face
  '((((class color) (background light))
     (:background "pink")))
  "Face used when revealing invisible characters.
Used instead `x-symbol-invisible-face'.  See `x-symbol-reveal-invisible'."
  :group 'x-symbol-info-general
  :group 'x-symbol-miscellaneous)

(defcustom x-symbol-context-info-ignore 'x-symbol-default-context-info-ignore
  "Regexp matching contexts not used to display a context info for.
See `x-symbol-context-info'.  You may also use a function instead of a
regexp, see `x-symbol-call-function-or-regexp'."
;; TODO: mention that fn is called with CONTEXT CHARSYM
  :group 'x-symbol-info-general
  :type 'x-symbol-function-or-regexp)

(defcustom x-symbol-context-info-threshold 2
  "Minimum length of contexts to display a context info for.
Used by `x-symbol-default-context-info-ignore'."
  :group 'x-symbol-info-general
  :type 'integer)

(defcustom x-symbol-context-info-ignore-regexp "\\`[A-Za-z]+\\'"
  "Regexp matching contexts not to display a context info for.
Used by `x-symbol-default-context-info-ignore'."
  :group 'x-symbol-info-general
  :type 'regexp)

(defcustom x-symbol-context-info-ignore-groups
  '(letter
    slash cedilla ogonek dotaccent ring tilde breve
    circumflex caron diaeresis hungarumlaut acute grave)
  "Groups of characters not to display a context info for.
Used by `x-symbol-default-context-info-ignore'."
  :group 'x-symbol-info-general
  :type '(repeat x-symbol-group))


;;;===========================================================================
;;;  Character Info
;;;===========================================================================

(defface x-symbol-info-face
  (eval-when-compile
    `((((class color) (background light))
       (:foreground "green4" :family "Helvetica"
		    ;; :size necessary with XEmacs, I get huge fonts otherwise,
		    ;; at least if x-symbol is enabled from a buffer with a
		    ;; nonstandard default font...
		    ,@(if (featurep 'xemacs) '(:size "12pt"))))))
  "Face normally used for the info in the echo area."
  :group 'x-symbol-info-strings)

(defface x-symbol-emph-info-face
  (eval-when-compile
    `((((class color) (background light))
       (:foreground "red4" :family "Helvetica"
		    ,@(if (featurep 'xemacs) '(:size "12pt"))))))
  "Face used for the emphasized info in the echo area."
  :group 'x-symbol-info-strings)

(defcustom x-symbol-info-intro-after
  '("AFTER:  " (0 -2 x-symbol-info-face))
  "Intro spec of info for the character after point.
See `x-symbol-character-info'.  See `x-symbol-fancy-value' for the value
type."
  :group 'x-symbol-info-strings
  :set 'x-symbol-set-cache-variable
  :type 'x-symbol-fancy)

(defcustom x-symbol-info-intro-before
  '("BEFORE:  " (0 -2 x-symbol-info-face))
  "Intro spec of info for character before point.
See `x-symbol-character-info'.  See `x-symbol-fancy-value' for the value
type."
  :group 'x-symbol-info-strings
  :set 'x-symbol-set-cache-variable
  :type 'x-symbol-fancy)

(defcustom x-symbol-info-intro-highlight
  '("button2 inserts:  " (-10 -2 x-symbol-info-face))
  "Intro spec of the info character in grid under mouse.
See `x-symbol-fancy-value' for the value type, STRING is passed to
`substitute-command-keys'."
  :group 'x-symbol-info-strings
  :set 'x-symbol-set-cache-variable
  :type 'x-symbol-fancy)

(defcustom x-symbol-info-intro-list
  '("\\[x-symbol-list-selected] inserts:  " (-10 -2 x-symbol-info-face))
  "Intro spec of the info character in grid under point.
Used by \\[x-symbol-list-info].  See `x-symbol-fancy-value' for the
value type, STRING is passed to `substitute-command-keys'."
  :group 'x-symbol-info-strings
  :set 'x-symbol-set-cache-variable
  :type 'x-symbol-fancy)

(defcustom x-symbol-info-intro-yank
  '("\\[yank] inserts:  " (-10 -2 x-symbol-info-face))
  "Intro spec of info for the character inserted in read-only buffer.
See `x-symbol-insert-command'.  See `x-symbol-fancy-value' for the value
type, STRING is passed to `substitute-command-keys'."
  :group 'x-symbol-info-strings
  :set 'x-symbol-set-cache-variable
  :type 'x-symbol-fancy)

(defcustom x-symbol-info-alias-after
  '("\\[forward-char] \\[x-symbol-modify-key] replaces char alias with:  "
    (-27 -2 x-symbol-emph-info-face))
  "Intro spec of short info for character alias after point.
See `x-symbol-character-info'.  See `x-symbol-fancy-value' for the value
type, STRING is passed to `substitute-command-keys'."
  :group 'x-symbol-info-strings
  :set 'x-symbol-set-cache-variable
  :type 'x-symbol-fancy)

(defcustom x-symbol-info-alias-before
  '("\\[x-symbol-modify-key] replaces char alias with:  "
    (-27 -2 x-symbol-emph-info-face))
  "Intro spec of short info for character alias before point.
See `x-symbol-character-info'.  See `x-symbol-fancy-value' for the value
type, STRING is passed to `substitute-command-keys'."
  :group 'x-symbol-info-strings
  :set 'x-symbol-set-cache-variable
  :type 'x-symbol-fancy)

(defcustom x-symbol-info-context-pre
  '("\\[x-symbol-modify-key] replaces " (-9 -1 x-symbol-info-face))
  "Spec of text before context in info for context before point.
See `x-symbol-context-info'.  See `x-symbol-fancy-value' for the value
type, STRING is passed to `substitute-command-keys'."
  :group 'x-symbol-info-strings
  :set 'x-symbol-set-cache-variable
  :type 'x-symbol-fancy)

(defcustom x-symbol-info-context-post
  '(" with:  " (1 -2 x-symbol-info-face))
  "Spec of text after context in info for context before point.
See `x-symbol-context-info'.  See `x-symbol-fancy-value' for the value
type."
  :group 'x-symbol-info-strings
  :set 'x-symbol-set-cache-variable
  :type 'x-symbol-fancy)

(defcustom x-symbol-info-token-pre '(" = " (x-symbol-info-face))
  "Spec of text between character and token in info.
See `x-symbol-fancy-value' for the value type."
  :group 'x-symbol-info-strings
  :set 'x-symbol-set-cache-variable
  :type 'x-symbol-fancy)

(defcustom x-symbol-info-token-charsym
  '("<%s>" (0 1 x-symbol-info-face) (-1 x-symbol-info-face))
  "Spec with format for x-symbol charsym in info.
See `x-symbol-fancy-string' for the value type, the format with
substitution CHARSYM/%s is the STRING."
  :group 'x-symbol-info-strings
  :set 'x-symbol-set-cache-variable
  :type 'x-symbol-fancy)

(defcustom x-symbol-info-classes-pre '(" (" (1 x-symbol-info-face))
  "Spec of text before token classes in info.
See `x-symbol-fancy-associations' for details."
  :group 'x-symbol-info-strings
  :set 'x-symbol-set-cache-variable
  :type 'x-symbol-fancy)

(defcustom x-symbol-info-classes-sep '(", " (x-symbol-info-face))
  "Spec of text between token classes in info.
See `x-symbol-fancy-associations' for details."
  :group 'x-symbol-info-strings
  :set 'x-symbol-set-cache-variable
  :type 'x-symbol-fancy)

(defcustom x-symbol-info-classes-post '(")" (x-symbol-info-face))
  "Spec of text before after token classes in info.
See `x-symbol-fancy-associations' for details."
  :group 'x-symbol-info-strings
  :set 'x-symbol-set-cache-variable
  :type 'x-symbol-fancy)

(defcustom x-symbol-info-classes-charsym '("charsym" (x-symbol-info-face))
  "Spec of token class string for x-symbol charsyms in info.
See `x-symbol-fancy-value' for the value type."
  :group 'x-symbol-info-strings
  :set 'x-symbol-set-cache-variable
  :type 'x-symbol-fancy)

(defcustom x-symbol-info-coding-pre '("." (x-symbol-info-face))
  "Spec of text before codings in info.
See `x-symbol-fancy-associations' for details."
  :group 'x-symbol-info-strings
  :set 'x-symbol-set-cache-variable
  :type 'x-symbol-fancy)

(defcustom x-symbol-info-coding-sep '("." (x-symbol-info-face))
  "Spec of text between codings in info.
See `x-symbol-fancy-associations' for details."
  :group 'x-symbol-info-strings
  :set 'x-symbol-set-cache-variable
  :type 'x-symbol-fancy)

(defcustom x-symbol-info-coding-post '("")
  "Spec of text after codings in info.
See `x-symbol-fancy-associations' for details."
  :group 'x-symbol-info-strings
  :set 'x-symbol-set-cache-variable
  :type 'x-symbol-fancy)

(defcustom x-symbol-info-coding-alist
  '((iso-8859-1 "l1" (x-symbol-info-face))
    (iso-8859-2 "l2" (x-symbol-info-face))
    (iso-8859-3 "l3" (x-symbol-info-face))
    (iso-8859-9 "l5" (x-symbol-info-face))
    (iso-8859-15 "l9" (x-symbol-info-face)))
  "Specs for coding info.
Each element looks like (CODING . SPEC).  Characters which are defined
to be 8bit characters with CODING, are displayed with SPEC in the info.
See `x-symbol-fancy-associations' for details."
  :group 'x-symbol-info-strings
  :type '(repeat (group x-symbol-coding
			string
			(x-symbol-fancy-spec :inline t
					     :tag "Face specifications"))))

(defcustom x-symbol-info-keys-keymaps 'x-symbol-default-info-keys-keymaps
  "Function returning the root keymaps for the key info.
If non-nil, called with the current charsym as argument, the result is
the second argument to `where-is-internal'.  See also
`x-symbol-info-keys-pre'."
  :group 'x-symbol-info-strings
  :type '(choice (const :tag "Current maps" nil) function))

(defcustom x-symbol-info-keys-pre
  '("   \\[x-symbol-map] +: " (-4 -1 x-symbol-info-face))
  "Spec of text before key bindings in info.
See `x-symbol-fancy-associations' for details, STRING is passed to
`substitute-command-keys'.  See also `x-symbol-info-keys-keymaps'."
  :group 'x-symbol-info-strings
  :set 'x-symbol-set-cache-variable
  :type 'x-symbol-fancy)
  
(defcustom x-symbol-info-keys-sep '(" , " (0 -1 x-symbol-info-face))
  "Spec of text between key bindings in info.
See `x-symbol-fancy-associations' for details."
  :group 'x-symbol-info-strings
  :set 'x-symbol-set-cache-variable
  :type 'x-symbol-fancy)

(defcustom x-symbol-info-keys-post '("")
  "Spec of text after key bindings in info.
See `x-symbol-fancy-associations' for details."
  :group 'x-symbol-info-strings
  :set 'x-symbol-set-cache-variable
  :type 'x-symbol-fancy)

(defconst x-symbol-fancy-cache-size 25
  "Internal.  Number of variables whose fancy values are cached.")

(defvar x-symbol-cache-size 100
  "*Size of caches for fancy strings.
See `x-symbol-ensure-hashtable' and `x-symbol-puthash'.")


;;;===========================================================================
;;;  Init: aspects, default input
;;;===========================================================================

(defvar x-symbol-modify-aspects-alist
  '((shift     (nil . 0) (up . 300) (down . 600))
    (shape     (nil . 0) (round . 1000) (square . 2000) (curly . 3000))
    (size      (nil . 0) (big . 5000) (sml . 9000)))
  "Alist of modify aspects with their values and scores.
Each element looks like (ASPECT (VALUE . SCORE)...) where ASPECT is a
modify aspect.  It is a good idea to have a value nil with score 0 in
the alist of all aspects.

The aspect value must be equal to one VALUE, the modify score is
incremented by the corresponding SCORE.  A higher modify score makes a
character likely to appear late in the modify-to chain.  See
`x-symbol-init-cset' and `x-symbol-init-input'.")

(defvar x-symbol-rotate-aspects-alist
  '((direction (north . -5000) (north-west . -4500) (west . -4000)
	       (south-west . -3500) (south . -3000) (vertical . -2500)
	       (south-east . -2000) (east . -1500)
	       (horizontal . -1000) (north-east . -500) (nil . 0)))
  "Alist of rotate aspects with their values and scores.
Each element looks like (ASPECT (VALUE . SCORE)...) where ASPECT is a
rotate aspect.  It is a good idea to have a value nil with score 0 in
the alist of all aspects.  Aspect `direction' is also used by
`x-symbol-rotate-prefix-alist'.

The aspect value must be equal to one VALUE, the rotate score is
incremented by the corresponding SCORE.  A higher rotate score makes a
character likely to appear late in the rotate-to chain.  See
`x-symbol-init-cset' and `x-symbol-init-input'.")

(defvar x-symbol-group-input-alist
  '((bigop      0)
    (operator	-120)
    (relation	-120)
    (arrow   	0)
    (triangle	0)
    (shape	0)
    (white   	1500)
    (line    	0)
    (dots    	0)
    (punctuation 0)
    (quote  	0)
    (parenthesis 0)
    (symbol  	0)
    (currency  	0)
    (digit1     0 "%sd")
    (mathletter 500 "%s")
    (setsymbol  120 "%s")
    (greek1     1500 "%s#" "#%s")
    (greek      0 "%s#" "#%s")
    (letter	0 "%s")
    (slash	120 "%s/" "/%s")
    (ogonek	250 "%s," ",%s")
    (cedilla	120 "%s," ",%s")
    (dotaccent	250 "%s." ".%s")
    (ring	250 "%s*" "*%s")
    (breve	250 "%sv" "v%s")
    (caron	120 "%sv" "v%s")
    (circumflex	120 "%s^" "^%s")
    (tilde	120 t "%s~" "~%s")
    (hungarumlaut 250 "''%s")
    (diaeresis	120 "%s:" t ":%s" "%s\"" "\"%s")
    (grave	120 t "%s`" "`%s")
    (acute	120 "%s'" t "'%s"))
  "Alist of character groups with their scores and default input formats.
Each element looks like (GROUP GROUP-SCORE . INPUT).  If the group of a
charsym is equal to GROUP, its score is incremented by GROUP-SCORE, see
`x-symbol-init-cset'.

INPUT = nil | (FORMAT . INPUT) | (t FORMAT . INPUT).  It is used if the
charsym has no input definitions, but a SUBGROUP which might have been
processed using `x-symbol-subgroup-string-alist'.  In that case, the
FORMATs with substitutions SUBGROUP/%s are the CONTEXTs as described in
`x-symbol-init-cset'.")


;;;===========================================================================
;;;  Init: char syntax
;;;===========================================================================

(defvar x-symbol-group-syntax-alist
  '((bigop   	"_")
    (operator	"_")
    (relation	"_")
    (arrow   	"_")
    (triangle	"_")
    (shape	"_")
    (white   	" ")
    (line    	".")
    (dots    	".")
    (punctuation ".")
    (quote  	 "." (open . "(%s") (close . ")%s"))
    (parenthesis "." (open . "(%s") (close . ")%s"))
    (symbol  	"_")
    (currency  	"_")
    (digit1     "_")
    (mathletter "w")
    (setsymbol  "w")
    (greek      "w")
    (greek1     "w")
    (letter	"w")
    (slash	"w")
    (cedilla	"w")
    (ogonek	"w")
    (dotaccent	"w")
    (ring	"w")
    (tilde	"w")
    (breve	"w")
    (circumflex	"w")
    (caron	"w")
    (diaeresis	"w")
    (hungarumlaut "w")
    (acute	"w")
    (grave	"w"))
  "Alist of groups with their syntax designators used in XEmacs/Mule.
Each element looks like (GROUP SYNTAX (RAW-SUBGROUP . FORMAT)...).  A
charsym with group GROUP has normally the syntax designator SYNTAX.  If
its raw subgroup, i.e., a symbol, is equal to a RAW-SUBGROUP and the
OPPOSITE of the charsym is defined in the same or previous csets, FORMAT
with substitution CSTRING/%s is used as the syntax designator where
CSTRING is the cstring of OPPOSITE.  See `x-symbol-init-cset' and
`x-symbol-subgroup-string-alist'.")

(defvar x-symbol-subgroup-string-alist
  '((accent . " ")
    (open . "(")
    (close . ")"))
  "Alist of subgroup symbols with their string representation.
Each element looks like (RAW . STRING) where RAW is a symbol used in the
SUBGROUP position of entries in cset tables, see `x-symbol-init-cset'
and STRING is its string representation.")


;;;===========================================================================
;;;  Fonts
;;;===========================================================================

(defvar x-symbol-latin-force-use nil
  "If non-nil, define latin characters even when fonts are missing.
If nil, it is a bad idea to decode a file when its `x-symbol-coding'
corresponds to a missing font, i.e., 8bit characters are assumed to have
encoding `x-symbol-default-coding' in this case.  If nil, tokens are not
decoded if they require the missing font.  Values other than nil are
safe, but latin characters without correct fonts will look strange.")

(defvar x-symbol-font-sizes '(("\\`-etl-" 16 14) ("" 14 12)))
;;  '(14 ("\\`-etl-.+_su[bp]-" . 14) ("\\`-etl-" . 16) ("_su[bp]-" . 12)))

(defvar x-symbol-font-lock-with-extra-props
  (and (boundp 'x-symbol-emacs-has-font-lock-with-props)
       x-symbol-emacs-has-font-lock-with-props))

(defvar x-symbol-latin1-fonts
  '("-adobe-helvetica%s-medium-r-normal-*-%d-*-*-*-*-*-iso8859-1")
  "Fonts with registry/encoding \"iso8859-1\".
See `x-symbol-latin1-cset' and `x-symbol-init-cset'.")

(defvar x-symbol-latin2-fonts
  '("-adobe-helvetica%s-medium-r-normal-*-%d-*-*-*-*-*-iso8859-2"
    "-etl-fixed%s-medium-r-normal--%d-%d0-72-72-c-*-iso8859-2")
  "Fonts with registry/encoding \"iso8859-2\".
See `x-symbol-latin2-cset' and `x-symbol-init-cset'.")

(defvar x-symbol-latin3-fonts
  '("-adobe-helvetica%s-medium-r-normal-*-%d-*-*-*-*-*-iso8859-3"
    "-etl-fixed%s-medium-r-normal--%d-%d0-72-72-c-*-iso8859-3")
  "Fonts with registry/encoding \"iso8859-3\".
See `x-symbol-latin3-cset' and `x-symbol-init-cset'.")

(defvar x-symbol-latin5-fonts
  '("-etl-fixed%s-medium-r-normal--%d-%d0-72-72-c-*-iso8859-9")
  "Fonts with registry/encoding \"iso8859-9\".
See `x-symbol-latin5-cset' and `x-symbol-init-cset'.")

;; for some reason, the font foundry and family name have been renamed, it is
;; the normal helvetica font...
(defvar x-symbol-latin9-fonts
  '("-vh-herilane%s-medium-r-normal-*-%d-*-*-*-*-*-iso8859-15")
  "Fonts with registry/encoding \"iso8859-1\".
See `x-symbol-latin9-cset' and `x-symbol-init-cset'.")

(defvar x-symbol-xsymb0-fonts
  '("-xsymb-xsymb0%s-medium-r-normal--%d-%d0-75-75-p-*-adobe-fontspecific"
    "-adobe-symbol%s-medium-r-normal-*-*-%d0-*-*-*-*-adobe-fontspecific")
  "Fonts with registry/encoding \"adobe-fontspecific\".
See `x-symbol-xsymb0-cset' and `x-symbol-init-cset'.")

(defvar x-symbol-xsymb1-fonts
  '("-xsymb-xsymb1%s-medium-r-normal--%d-%d0-75-75-p-*-xsymb-xsymb1")
  "Fonts with registry/encoding \"xsymb-xsymb1\".
See `x-symbol-xsymb1-cset' and `x-symbol-init-cset'.")


;;;===========================================================================
;;;  X-Symbol Image: general
;;;===========================================================================

(defcustom x-symbol-image-max-width 120
  "*Maximum width of glyphs."
  :group 'x-symbol-image-general
  :type 'integer)

(defcustom x-symbol-image-max-height 80
  "*Maximum height of glyphs."
  :group 'x-symbol-image-general
  :type 'integer)

(defcustom x-symbol-image-update-cache 'old
  "*If non-nil, automatically update the image cache file.
With value nil, only create an image cache file if it does not exist.
With value t, always produce a new cache file.  With any other value,
only produce a cache file if it does not exist or is older than the
corresponding image file.  This variable has no influence if a glyph
having used the image cache file in question is stored in the buffer
local memory cache, see `x-symbol-image-memory-cache'.

See `x-symbol-image-cache-directories' for the file name of the
cached image.  See also `x-symbol-image-special-glyphs'."
  :group 'x-symbol-image-general
  :type '(radio (const :tag "No" nil)
		(const :tag "Always" t)
		(sexp :tag "Old" :format "%t" :value old)))

(defcustom x-symbol-image-use-remote nil
  "*If nil, only show glyphs which can be stored in the memory cache.
The memory cache stores glyphs for file names without directory part or
a directory part in the language access `x-symbol-image-cached-dirs',
e.g., it should contain \"images\", if \"images/mail.png\" should be
stored in the memory cache.

If this variable is nil, use `x-symbol-image-remote-glyph' for image
files not in the memory cache.  If it is non-nil, try to find the image
file during editing, ignoring the searchpath, for speed, though.
Editing lines with image files not in the memory cache will be slow,
since file accesses are necessary for every command.

When searching for the images file, all file names, including
directories in a search path, are relative to the return value of the
function in language access `x-symbol-master-directory', value nil means
function `default-directory'.

Implicitly relative file names, i.e., those which are neither absolute
nor are matched by `x-symbol-image-explicitly-relative-regexp', are
searched in the directories of language access
`x-symbol-image-searchpath'."
  :group 'x-symbol-image-general
  :type 'boolean)

(defcustom x-symbol-image-current-marker " *"
  "*Marker to indicate the directory of the image file.
Marker used in `x-symbol-image-menu' to indicate directories in the
image search path containing the image file.  The first marked directory
is used by button2 over an image insertion command."
  :group 'x-symbol-image-general
  :type 'string)

(defcustom x-symbol-image-scale-method "\\.[0-9][0-9]\\'"
  "*Regexp matching the scale factor in the image file name.
If non-nil and this regexp matches the image file name without its final
extension, only the part up to the beginning of the match is used to
determine the name of the image cache file and the design file if it
differs from the image file, see `x-symbol-image-editor-alist'.

Example: with the default values, for the image and image design file
\"file.70.jpeg\", the image cache file is \"file.png\", for the image
file \"file.70.eps\", the image cache file is \"file.png\", the image
design file is \"file.fig\"."
  :group 'x-symbol-image-general
  :type '(choice (const :tag "No scale method" nil) regexp))

(defcustom x-symbol-image-explicitly-relative-regexp "\\`\\.\\.?/"
  "Regexp matching files considered to be explicitly relative."
  :group 'x-symbol-image-general
  :type 'regexp)

(defcustom x-symbol-image-searchpath-follow-symlink nil
  "*Non-nil, if recursive searching for dirs should follow symbolic links.
Directories in the image search path ending with \"//\" are recursively
inserted.  With value nil, do not include subdirectories which are
symbolic links.  Directories which are directly specified in the image
searchpath are always included."
  :group 'x-symbol-image-general
  :type 'boolean)


;;;===========================================================================
;;;  Configuration: Image file cache
;;;===========================================================================

;; Influenced by `fast-lock-cache-directories' but different semantics!
(defcustom x-symbol-image-cache-directories
  `((,(concat "\\`" (regexp-quote (file-truename "~/"))) . "~/.images/")
    ("." . t))
  "List of directories for image cache files.
Each element should be of the form:
  (REGEXP) or
  (REGEXP . t) or
  (REGEXP . NEWDIR) or
  (REGEXP FUNCTION ARG...)

Used by `x-symbol-image-cache-name' to determine the directory where to
store the image cache files.  The elements in this list are processed
until REGEXP matches the directory part INDIR of the fully expanded
image file name, see `file-truename'.

With the first form, no image cache file will be produced and
`x-symbol-image-junk-glyph' represents the image file.  With the second
form, the image cache file is just produced temporary and is stored in
`x-symbol-image-temp-name'+SUFFIX.  If the glyph for the image file is
not stored in `x-symbol-image-memory-cache', the second form is an alias
for the first form.

With the third form, the match by REGEXP in INDIR is replaced with
NEWDIR, see `replace-match'.  With the fourth from, FUNCTION is called
with INDIR and arguments ARGs.  In both cases, the result is expanded
with INDIR to get the directory for the image cache file.

Example: if we have the value
  ((\"\\\\`/home/user/junk/\")
   (\"\\\\`/home/user/tmp/.*\" . \".images/\")
   (\"\\\\`/home/user/\" . \"~/.images/\")
   (\".\" . t)
and the following image files, we get:
  /home/user/junk/stupid.eps is not cached, a recycle sign is shown
  /home/user/tmp/tmp1/image.eps is cached in /home/user/tmp/tmp1/.images/
  /home/user/d1/d2/image.eps is cached in /home/user/.images/d1/d2/
  /usr/local/image.eps is temporary cached in file /tmp/xsi-a006JH.SUFFIX"
  :group 'x-symbol-image-general
  :type '(repeat (cons :format "%v"
		       :value (".")
		       regexp
		       (choice
			(const :tag "Junk" nil)
			(const :tag "Temporary" t)
			(string :tag "Replace match with")
			(cons :tag "Call"
			      function
			      (repeat :tag "With arguments" sexp))))))

(defvar x-symbol-image-temp-name
  (and (featurep 'xemacs)		; temp image files don't work in Emacs
       (if (fboundp 'make-temp-file)
	   (make-temp-file "xsi-")		; Emacs
	 (expand-file-name (make-temp-name "xsi-") (temp-directory))))
  "Name without suffix of the temporary image cache file.
This should be a unique, at best generated with `make-temp-name'.  See
`x-symbol-image-cache-directories' for details.")

(defcustom x-symbol-image-convert-mono-regexp
  (and x-symbol-image-temp-name (regexp-quote x-symbol-image-temp-name))
  "Regexp matching image cache file names not using a colormap.
Used by `x-symbol-image-start-convert-colormap' to determine monochrome
image cache files.  This regexp should match temporary image cache files
since \"convert\" is slow when using a colormap."
  :group 'x-symbol-image-general
  :type '(choice (const :tag "None" nil) regexp))


;;;===========================================================================
;;;  Configuration: highlighting image insertion commands, editor
;;;===========================================================================

(defcustom x-symbol-image-help-echo
  '("button2 runs: %S , button3 pops up menu"
    (8 13 x-symbol-info-face) (-23 -21 x-symbol-info-face)
    (-12 x-symbol-info-face))
  "Format string for info when the mouse is over image insertion commands.
Used with substitution COMMAND/%S, where COMMAND describes the
invocation of the image editor, see `x-symbol-image-editor-alist'."
  :group 'x-symbol-image-general
  :group 'x-symbol-info-strings
  :set 'x-symbol-set-cache-variable
  :type 'x-symbol-fancy)

(defcustom x-symbol-image-editor-alist
  '(("\\.\\(eps\\|ps\\(tex\\)?\\)\\'" "xfig %s &" ".fig")
    ("." "display %s &"))
  "Alist of image editors used by `x-symbol-image-editor'.
Each element looks like (REGEXP . EDITOR-SPEC) where EDITOR-SPEC looks
like (SHELL-COMMAND-FORMAT [EXT]) or (FUNCTION ARG...).

If REGEXP matches the image file, EDITOR-SPEC is used.  With the first
form, a shell command SHELL-COMMAND-FORMAT with substitution FILE/%s is
invoked where the image design file FILE is the image file, if used
without optional EXT or EXT with value nil, or the result of
`x-symbol-image-file-name' otherwise, called with arguments image file
name and EXT.

With the second form, calling (FUNCTION FILE nil ARG...) should return a
string describing the editor, used by function
`x-symbol-image-help-echo' and the title of `x-symbol-image-menu'.
Calling (FUNCTION FILE BUFFER ARG...)  should invoke the image editor.
FILE is the image file, BUFFER is the buffer in which the image is
used."
  :group 'x-symbol-image-general
  :type '(repeat
	  (cons :format "%v"
		:value ("." "display %s &")
		regexp
		(choice (list :tag "Shell command"
			      string
			      (choice (const :tag "Unchanged filename" nil)
				      (string :tag "Abstract extension")))
			(cons :tag "Call"
			      function
			      (repeat :tag "With arguments" sexp))))))

(defvar x-symbol-image-menu
  '("Run %S in"
    "--:shadowDoubleEtchedIn"
    ["Rescan buffer" (x-symbol-image-parse-buffer 'OTHER)
     :active (x-symbol-event-in-current-buffer)]
    ["Update file cache" (x-symbol-image-parse-buffer t)
     :active (x-symbol-event-in-current-buffer)])
  "Definition for the popup menu over image insertion commands.
It has the form (HEADER LAST-ITEM...).  The menu title is TITLE with
substitution COMMAND/%S, where COMMAND describes the invocation of the
image editor, see `x-symbol-image-editor-alist'.  The next menu items
are the directories in the image search path, see
`x-symbol-image-use-remote'.  If a image file is found in a
directory, it is marked with `x-symbol-image-current-marker'.")


;;;===========================================================================
;;;  Configuration: special-purpose images/glyphs and conversion program
;;;===========================================================================

;; `defcustom' with set function
(defvar x-symbol-image-data-directory x-symbol-data-directory
  "Configuration variable.  Directory of special purpose images.
See `x-symbol-image-special-glyphs'.")

(defvar x-symbol-image-special-glyphs
  '(("RIP.xbm" . xbm) ("hourglass.xbm" . xbm) ("drawing.xbm" . xbm)
    ("termlock.xbm" . xbm) ("escherknot.xbm" . xbm) ("recycle.xbm" . xbm))
  ;;'(("splat.xbm" . xbm) ("abacus.xbm" . xbm) ("scroll2.xbm" . xbm)
  ;;  ("stopsign.xbm" . xbm) ("filing.xbm" . xbm))
  "Special images used for recognized image insertion commands.
The value looks like (BROKEN CREATE DESIGN LOCKED REMOTE JUNK).  Each
element looks like (FILE . IMAGE-FORMAT) where FILE is a file name,
expanded with `x-symbol-image-data-directory' and IMAGE-FORMAT is a
image format compiled into your XEmacs.

They are used to initialize variables containing images/glyphs:
 * BROKEN for `x-symbol-image-broken-image',
 * CREATE for `x-symbol-image-create-image',
 * DESIGN for `x-symbol-image-design-glyph',
 * LOCKED for `x-symbol-image-locked-glyph',
 * REMOTE for `x-symbol-image-remote-glyph' and
 * JUNK for `x-symbol-image-junk-glyph'.

Special images are used in the following situations: REMOTE represents
images in a file, if the file is remote or if the image name prohibits
the use of the memory cache as specified by `x-symbol-image-use-remote'.
JUNK is used if `x-symbol-image-converter' is nil, if no image should be
created as specified by `x-symbol-image-cache-directories' or if the
image cache file cannot be written.

LOCKED represents existent image files which cannot be read or
non-existent image files which cannot be created.  DESIGN represents
non-existent image files which could be created.  CREATE is used during
the creation of the image cache file, an old image cache is used instead
if it exists.  BROKEN is used if the creation of the image cache file
failed.")

(defcustom x-symbol-image-convert-file-alist
  '(("\\.pstex\\'" . "ps:"))
  "Alist to determine a prefix for the INFILE passed to \"convert\".
Each element looks like (REGEXP . PREFIX).  If REGEXP matches INFILE,
INFILE is prefixed by PREFIX for the invocation of \"convert\".  If no
REGEXP matches, no prefix is used.  See `x-symbol-image-convert-file'."
  :group 'x-symbol-image-general
  :type '(repeat (cons :format "%v"
		       regexp (string :tag "Prefix"))))

(defcustom x-symbol-image-convert-program
  (if (eq system-type 'windows-nt) "C:\\ImageMagick\\convert" "convert")
  "*Name of the program used in `x-symbol-image-converter'."
  :group 'x-symbol-image-general
  :type 'string)

(defcustom x-symbol-image-converter
  (when (console-type)
    (save-excursion
      (set-buffer (get-buffer-create " *x-symbol-image command*"))
      (erase-buffer)
      (call-process shell-file-name nil t nil shell-command-switch
		    (concat x-symbol-image-convert-program " -list Format"))
      (call-process shell-file-name nil t nil shell-command-switch
		    (concat x-symbol-image-convert-program " -h"))
      (let (iformat)
	(cond ((when (featurep 'png)
		 (goto-char (point-min))
		 (re-search-forward "^[ \t]*[pP][nN][gG]" nil t))
	       (setq iformat 'png))
	      ((when (featurep 'gif)
		 (goto-char (point-min))
		 (re-search-forward "^[ \t]*[gG][iI][fF]" nil t))
	       (setq iformat 'gif))
	      (t
	       (setq iformat (cond ((featurep 'png) 'png)
				   ((featurep 'gif) 'gif)))
	       (unless iformat
		 (warn "x-symbol-image: your Emacs neither supports png nor gif"))
	       (goto-char (point-min))
	       (if (re-search-forward "ImageMagick" nil t)
		   (if iformat (warn "x-symbol-image: \"convert\" doesn't list recognized formats, I'll try %S" iformat))
		 (warn "x-symbol-image: no valid image converter")
		 (setq iformat nil))))
	(kill-buffer (current-buffer))
	(when iformat
	  (list* iformat
		 (cdr (assq iformat '((png . ".png") (gif . ".gif"))))
		 (if (and (boundp 'system-type) (eq system-type 'windows-nt))
		     'x-symbol-image-start-convert-mswindows
		   (let ((colors (if (featurep 'xemacs)
				     (or (device-color-cells) 2)
				   (if (display-color-p) 256 2))))
		     (cond ((< colors 32) 'x-symbol-image-start-convert-mono)
			   ((> colors 767)
			    'x-symbol-image-start-convert-truecolor)
			   (x-symbol-image-convert-colormap
			    'x-symbol-image-start-convert-colormap)
			   (t 'x-symbol-image-start-convert-color)))))))))
  "Converter to produce the image cache file from the image file.
This definition has the form (IMAGE-FORMAT EXTENSION . COMMAND).
IMAGE-FORMAT is a image format compiled into your XEmacs.  EXTENSION is
the extension used for image cache file names.

COMMAND, called with arguments INFILE and OUTFILE should start and
return the process which creates the image cache file OUTFILE from the
image file INFILE.  COMMAND should also use `x-symbol-image-max-width'
and `x-symbol-image-max-height'.  Value nil means, use
`x-symbol-image-junk-glyph' instead creating a glyph from IMAGE.

Predefined COMMANDS start \"convert\" from ImageMagick with different
options according to the number of colors in your device:
`x-symbol-image-start-convert-truecolor',
`x-symbol-image-start-convert-color' and
`x-symbol-image-start-convert-mono'."
  :group 'x-symbol-image-general
  :type '(choice
	  (const :tag "No image converter" nil)
	  (cons :tag "Converter"
		(symbol :tag "Image format")
		(cons :format "%v"
		      (string :tag "File extension")
		      (choice
		       :tag "Convert function"
		       (function-item :tag "To monochrome"
				      x-symbol-image-start-convert-mono)
		       (function-item :tag "To color, restricted"
				      x-symbol-image-start-convert-color)
		       (function-item :tag "To color, colormap"
				      x-symbol-image-start-convert-colormap)
		       (function-item :tag "To color, unrestricted"
				      x-symbol-image-start-convert-truecolor)
		       (function :tag "Other function"))))))


;;;===========================================================================
;;;  Package Integration
;;;===========================================================================

(put 'x-symbol-insert-command 'x-symbol-input t)
(put 'newline 'x-symbol-input t)
(put 'newline-and-indent 'x-symbol-input t)
(put 'reindent-then-newline-and-indent 'x-symbol-input t)
(put 'tex-insert-quote 'x-symbol-input t)
(put 'TeX-insert-quote 'x-symbol-input t)
(put 'TeX-insert-punctuation 'x-symbol-input t)
(put 'TeX-insert-dollar 'x-symbol-input t)
(put 'sgml-close-angle 'x-symbol-input t)
(put 'sgml-slash 'x-symbol-input t)
(put 'completion-separator-self-insert-command 'x-symbol-input t)
(put 'completion-separator-self-insert-autofilling 'x-symbol-input t)

(put 'forward-char 'x-symbol-point-function '1+)
(put 'backward-char 'x-symbol-point-function '1-)
(put 'forward-char-command 'x-symbol-point-function '1+)
(put 'backward-char-command 'x-symbol-point-function '1-)


;;;===========================================================================
;;;  For `set-variable'
;;;===========================================================================

;;;###autoload
(defun x-symbol-variable-interactive (var)
  "Provide interactive specification for `set-variable'.
VAR's options has been defined with `x-symbol-define-user-options'."
  (let* ((options (if (functionp (get var 'x-symbol-options))
		      (funcall (get var 'x-symbol-options))
		    (get var 'x-symbol-options)))
	 (alist (mapcar (lambda (x) (cons (symbol-name (car x)) (car x)))
			(or (cdr options) (list '(nil) options))))
	 (val (completing-read (format "Set `%s' to symbol (default %s): "
				       var (symbol-value var))
			       alist nil t)))
    (list (if (equal val "")
	      (symbol-value var)
	    (cdr (assoc val alist))))))

;;; Local IspellPersDict: .ispell_xsymb
;;; x-symbol-vars.el ends here
