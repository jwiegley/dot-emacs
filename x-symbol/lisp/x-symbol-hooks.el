;;; x-symbol-hooks.el --- pre-loaded stuff for package x-symbol

;; Copyright (C) 1996-1999, 2001-2003 Free Software Foundation, Inc.
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

;; This file provides `autoload's for package x-symbol, adds functions to hooks
;; for the automatic conversion and defines variables which control the
;; conversion.

;;; Code:

(provide 'x-symbol-hooks)
(require 'font-lock)
(eval-when-compile (require 'cl))
(eval-when-compile
  (defvar x-symbol-coding-name-alist)	; in "x-symbol-vars"
  (defvar x-symbol-image-colormap-allocation) ; here
  (defvar x-symbol-image-convert-colormap) ; here
  (defvar x-symbol-cstring-table)	; in x-symbol.el, only needed if loaded
  )
(eval-when-compile
  (defvar lazy-shot-minimum-size)
  (defvar comint-input-sender)
  (defvar comint-last-input-end)
  (defvar comint-last-output-start)
  (defvar fast-lock-save-faces)
  (defvar latex-mode-hook)
  (defvar LaTeX-mode-hook)
  (defvar LaTeX-math-insert-function)
  (defvar orig-buffer)
  (defvar reftex-translate-to-ascii-function)
)

(put 'x-symbol-define-user-options 'lisp-indent-function 2)
(put 'x-symbol-dolist-delaying 'lisp-indent-function 2)
(put 'x-symbol-do-plist 'lisp-indent-function 1)
(put 'x-symbol-while-charsym 'lisp-indent-function 1)
(put 'x-symbol-encode-for-charsym 'lisp-indent-function 1)
(put 'x-symbol-decode-for-charsym 'lisp-indent-function 2)
(put 'x-symbol-ignore-property-changes 'lisp-indent-function 0)

(defvar x-symbol-warn-of-old-emacs t
  "If non-nil, issue warning when using a old/buggy XEmacs.
XEmacs-21.0 to XEmacs-21.1.8 has been reported to core when using input
method token.")

;; CW: if possible, back to x-symbol.el, do not load too many files at init
(require (if (featurep 'xemacs) 'x-symbol-xmacs 'x-symbol-emacs))



;;;;##########################################################################
;;;;  Variables
;;;;##########################################################################


(defvar x-symbol-data-directory
  (or (locate-data-directory "x-symbol")
      (progn (warn "X-Symbol is not installed at the proper place")
	     nil))
  "Directory of data files that come with package X-Symbol.")

(defvar x-symbol-font-directory
  (and x-symbol-data-directory
       (expand-file-name "pcf/" x-symbol-data-directory))
  "Directory for additional X-Symbol fonts.
If non-nil, used in function `x-symbol-initialize'.")


;;;===========================================================================
;;;  Functions to set user options
;;;===========================================================================

(defun x-symbol-define-user-options (var options &optional after-set set-fn)
  "Define options and setting behavior for user option VAR.
OPTIONS has the form (FALLBACK . ALIST) where ALIST has elements of the
form (OPTION . MENU-TEXT).  If ALIST is non-nil, one OPTION should be
equal to FALLBACK, its MENU-TEXT is used for any values not being keys
in ALIST.  OPTIONS can also be a function which should return the form
mention above.

If ALIST is nil, `x-symbol-submenu-filter', which is used by
`x-symbol-menu', uses a toggle button with FALLBACK as the non-nil value
and \\[set-variable] offers completion with matches nil and FALLBACK.
Otherwise, the menu uses radio buttons for all OPTIONs, where MENU-TEXT
is the name of the menu item, and \\[set-variable] offers completion
over all OPTIONs.

`x-symbol-set-variable', which is invoked by the menu callbacks, uses
SET-FN instead `set' to set the value of VAR if SET-FN is non-nil.
Otherwise, all functions in AFTER-SET are invoked after `set'ting VAR."
  (put var 'x-symbol-options options)
  (put var 'variable-interactive
       (list 'x-symbol-variable-interactive (list 'quote var)))
  (while after-set
    (pushnew (pop after-set) (get var 'x-symbol-after-set-hook) :test 'equal))
  (if set-fn (put var 'x-symbol-set-function set-fn)))

;; CW: autoload important if var `x-symbol-auto-mode-suffixes' is saved by
;; custom
;;;###autoload
(defun x-symbol-auto-mode-suffixes (&optional suffixes)
  "Return REGEXPs of three-value elements in `auto-mode-alist'.
These REGEXPs are added to SUFFIXES."
  (setq suffixes (reverse suffixes))
  (let ((alist auto-mode-alist))
    (while alist
      (and (consp (cdar alist))
	   (null (member (caar alist) suffixes))
	   (push (caar alist) suffixes))
      (setq alist (cdr alist)))
    (nreverse suffixes)))


;;;===========================================================================
;;;  Initialization
;;;===========================================================================

(defcustom x-symbol-initialize t
  "Whether to do an extended initialization of package X-Symbol.
If t, do full initialization.  Otherwise, the value should be a list
with element.  To enable, include

 * `languages' to register all supported token languages,
 * `global' to turn on X-Symbol's global mode, i.e., as files are
   loaded, execute `turn-on-x-symbol-conditionally',
 * `keys' to set up the usual X-Symbol key bindings in `global-map',
 * `font-path' to add `x-symbol-font-directory' to the font-path,
 * `comint' to make X-Symbol work with comint,
 * `fast-lock' to make X-Symbol work with fast-lock,
 * `auctex' to make X-Symbol optimally work with AucTeX 9.8a+, it
   changes AucTeX's `TeX-region-hook', `TeX-translate-location-hook',
   and `LaTeX-math-insert-function',
 * `reftex' to make X-Symbol optimally work with RefTeX 3.26+,
 * `bib-cite' to make X-Symbol not overwriting bib-cite's highlighting.

You do not have to install the packages whose initialization is
enabled."
  :group 'x-symbol-mode
  :type '(choice (const :tag "All" t)
		 (set :value (languages global keys font-path comint
					fast-lock auctex reftex bib-cite)
		      (const :tag "Token languages" languages)
		      (const :tag "Global mode" global)
		      (const :tag "Key bindings" keys)
		      (const :tag "Font path" font-path)
		      (const :tag "Package comint" comint)
		      (const :tag "Package fast-lock" fast-lock)
		      (const :tag "Package AucTeX" auctex)
		      (const :tag "Package RefTeX" reftex)
		      (const :tag "Package bib-cite" bib-cite))))

(defvar x-symbol-orig-comint-input-sender 'comint-simple-send
  "Original function which sends a string to the comint process.")


;;;===========================================================================
;;;  Determine Locale
;;;===========================================================================

(defun x-symbol-coding-system-from-locale ()
  ;; See also EMACS/lisp/international/mule-cmds.el, `set-locale-environment'.
  "Get value for `x-symbol-default-coding' from locale.
Use \"locale -ck code_set_name charmap\" and search for the value of
\"code_set_name\" or \"charmap\"."
  (save-excursion
    (set-buffer (get-buffer-create " *x-symbol-coding-system-from-locale*"))
    (erase-buffer)
    (call-process shell-file-name nil t nil shell-command-switch
		  "locale -ck code_set_name charmap")
    (goto-char (point-min))

    (let* ((case-fold-search t)
	   ;; The GNU recode manual (www-find "recode charset iso646"), lists a
	   ;; lot of aliases, there are a bit less on
	   ;; http://mail.nl.linux.org/linux-utf8/2001-10/msg00072.html, I
	   ;; added some.  But this function shouldn't exceed 40 lines...
	   (map '((iso-8859-1
		   "iso-8859-1" "iso8859-1" "iso88591" ; HP: iso88591
		   ;; vendor-specific, supersets of ascii
		   ;; "roman8"		; HP: roman8 is not latin1
		   ;; ascii
		   "ascii" "us-ascii" "ansi_x3.4-1968" "646" "iso646"
		   "iso_646.irv")
		  (iso-8859-2
		   "iso-8859-2" "iso8859-2" "iso88592") ; HP: iso88592
		  (iso-8859-3
		   "iso-8859-3" "iso8859-3" "iso88593") ; HP: iso88593
		  (iso-8859-9
		   "iso-8859-9" "iso8859-9" "iso88599")
		  (iso-8859-15
		   "iso-8859-15" "iso8859-15" "iso885915"))) ; HP: iso885915
	   (charmap (and (re-search-forward "^[ \t]*\\(code_set_name\\|charmap\\)[ \t]*=[ \t]*\"\\([^\n\"]+\\)\"" nil t)
			 (find (downcase (match-string 2)) map
			       :test 'member))))
      (kill-buffer (current-buffer))
      (car charmap))))

(defun x-symbol-buffer-coding (&optional system)
  ;; nil = unknown, iso-8859-N otherwise
  (let (name)
    (if (featurep 'xemacs)
	(if (featurep 'mule)
	    (let* ((sy (or system buffer-file-coding-system))
		   (cs (if (symbolp sy) (find-coding-system sy) sy)))
	      (when (coding-system-p cs)
		(setq name (cdr (assq (coding-system-name
				       (coding-system-base cs))
				      '((raw-text . iso-8859-1)
					(binary . iso-8859-1)
					(escape-quoted . iso-8859-1)
					(iso-2022-8 . iso-8859-1)
					(iso-2022-8bit-ss2 . iso-8859-1)
					(iso-2022-lock . iso-8859-1)
					(iso-8859-2 . iso-8859-2)
					(iso-8859-3 . iso-8859-3)
					(iso-8859-9 . iso-8859-9)
					(iso-8859-15 . iso-8859-15)
					(ctext . iso-8859-1)))))))
	  (setq name x-symbol-default-coding))
      (let ((cs (or system buffer-file-coding-system 'no-conversion)))
	(when (coding-system-p cs)
	  (setq name (cdr (assq (coding-system-base cs)
				'((raw-text . iso-8859-1) ; console
				  (iso-latin-1 . iso-8859-1)
				  (iso-latin-1-with-esc . iso-8859-1)
				  (iso-latin-2 . iso-8859-2)
				  (iso-latin-2-with-esc . iso-8859-2)
				  (iso-latin-3 . iso-8859-3)
				  (iso-latin-3-with-esc . iso-8859-3)
				  (iso-latin-9 . iso-8859-9)
				  (iso-latin-9-with-esc . iso-8859-9)
				  (iso-latin-15 . iso-8859-15)
				  (iso-latin-15-with-esc . iso-8859-15)
				  (compound-text . iso-8859-1))))))))
    (if (or (null (boundp 'x-symbol-fchar-tables))
	    (assq name x-symbol-fchar-tables))
	name)))

(unless window-system
  (warn "X-Symbol: only limited support on a character terminal")
  (unless (and (boundp 'x-symbol-latin-force-use)
	       (eq x-symbol-latin-force-use 'console-user))
    (setq x-symbol-latin1-fonts nil)
    (setq x-symbol-latin2-fonts nil)
    (setq x-symbol-latin3-fonts nil)
    (setq x-symbol-latin5-fonts nil)
    (setq x-symbol-latin9-fonts nil)
    (setq x-symbol-xsymb0-fonts nil)
    (setq x-symbol-xsymb1-fonts nil)))

(defvar x-symbol-default-coding
  ;; TODO: make much nicer (do not use `x-symbol-buffer-coding' directly)
  (cond (noninteractive 'iso-8859-1)
	((featurep 'mule)
	 (let* ((cs (default-value 'buffer-file-coding-system))
		(val (cond (cs
			    (x-symbol-buffer-coding cs))
			   ((equal current-language-environment "English")
			    'iso-8859-1)))
		(loc (x-symbol-coding-system-from-locale)))
	   (and loc
		(not (eq loc val))
		(warn "X-Symbol: Emacs language environment and system locale specify different encoding, I'll assume `%s'" val))
	   val))
	((x-symbol-coding-system-from-locale))
	(t
	 (warn "X-Symbol: cannot deduce default encoding, I'll assume `iso-8859-1'")
	 'iso-8859-1))
  "Coding used for 8bit characters in buffers.
Also used for a 8bit file codings where `x-symbol-coding' has value nil.
Supported values are `iso-8859-1', `iso-8859-2', `iso-8859-3' and
`iso-8859-9', it should correspond to the normal charset registry of
your `default' face.

WARNING: Under XEmacs/Mule, package x-symbol is only tested with value
`iso-8859-1'!  It is assumed that you have not changed any of the
various Mule codings-system variables, i.e., it assumes iso-8859-1.  Use
\\[x-symbol-package-bug] to give the author some advice on Mule.")

(unless (or (memq x-symbol-default-coding
		  '(nil iso-8859-1 iso-8859-2 iso-8859-3 iso-8859-9))
	    (and (eq x-symbol-default-coding 'iso-8859-15)
		 (or (not (featurep 'xemacs))
		     (not (featurep 'mule))
		     (fboundp 'emacs-version>=) (emacs-version>= 21 5))))
  (warn "X-Symbol: illegal `x-symbol-default-coding', I'll use nil")
  (setq x-symbol-default-coding nil))


;;;===========================================================================
;;;  General Configuration
;;;===========================================================================

(defcustom x-symbol-compose-key '(control ?\=)
  "Key used to access command `x-symbol-map'.
By default, pressing this key twice invokes the GRID: \\[x-symbol-grid].
This is a list, no vector!"
  :group 'x-symbol-input-init
  :type '(x-symbol-key :tag "Prefix key"))

(defcustom x-symbol-auto-key-autoload t
  "*If non-nil, pressing `x-symbol-compose-key' initialize x-symbol.
The binding of `x-symbol-compose-key' is redefined after initialization.
With value nil, you must provide a prefix argument to initialize package
X-Symbol."
  :group 'x-symbol-input-init
  :type 'boolean)

(defvar x-symbol-auto-conversion-method 'auto-slow
  ;;(if (featurep 'crypt) 'slow 'fast)
  "Non-nil means, set up hooks for auto conversion.
Fast methods are used if this variable has value `fast'.  Otherwise,
slower methods are used and \\[vc-register] or \\[vc-next-action] will
fail to decode the buffer contents.

You should set this variable to value `slowest' if, for example, the
symbol for \\alpha looks like \\233a after \\[save-buffer] (this happens
on some systems).  Value `fast' should not be used, if some other
package, e.g., crypt, adds a function to `write-file-hooks' which does
not inspect the remaining functions in this hook.

Default value `auto-slow' is set to `fast' after the initialization of
XEmacs if package crypt has not been loaded by then.")


;;;===========================================================================
;;;  Known Token Languages
;;;===========================================================================

(defvar x-symbol-language-alist nil
  "Alist of currently registered token languages.
Elements look like (LANGUAGE . NAME) where LANGUAGE is the symbol
representing and NAME is the name normally presented to the user,
see `x-symbol-language-text'.

You should not set this variable directly, use
`x-symbol-register-language' instead!")

(defcustom x-symbol-charsym-name "x-symbol charsym"
  "Name of the pseudo token language x-symbol charsym.
This pseudo language corresponds to `x-symbol-language' having value nil
and is used for input methods, not for decoding and encoding.  See
`x-symbol-language-text'."
  :group 'x-symbol-miscellaneous
  :type 'string)

(defcustom x-symbol-tex-name "TeX macro"
  "Name of token language `tex'.  See `x-symbol-register-language'."
  :group 'x-symbol-tex
  :type 'string)

(defcustom x-symbol-tex-modes
  '(tex-mode latex-mode plain-tex-mode noweb-mode)
  "Major modes using language `tex'.  See `x-symbol-register-language'."
  :group 'x-symbol-tex
  :group 'x-symbol-mode
  :type '(repeat function))

(defcustom x-symbol-sgml-name "SGML entity"
  "Name of token language `sgml'.  See `x-symbol-register-language'."
  :group 'x-symbol-sgml
  :type 'string)

(defcustom x-symbol-sgml-modes
  ;;'(sgml-mode xml-mode html-mode hm--html-mode html-helper-mode)
  '(html-mode hm--html-mode html-helper-mode)
  "Major modes using language `sgml'.  See `x-symbol-register-language'."
  :group 'x-symbol-sgml
  :group 'x-symbol-mode
  :type '(repeat function))

(defcustom x-symbol-bib-name "BibTeX macro"
  "Name of token language `bib'.  See `x-symbol-register-language'."
  :group 'x-symbol-bib
  :type 'string)

(defcustom x-symbol-bib-modes '(bibtex-mode)
  "Major modes using language `bib'.  See `x-symbol-register-language'."
  :group 'x-symbol-bib
  :group 'x-symbol-mode
  :type '(repeat function))

(defcustom x-symbol-texi-name "TeXinfo command"
  "Name of token language `tex'.  See `x-symbol-register-language'."
  :group 'x-symbol-texi
  :type 'string)

(defcustom x-symbol-texi-modes '(texinfo-mode)
  "Major modes using language `texi'.  See `x-symbol-register-language'."
  :group 'x-symbol-texi
  :group 'x-symbol-mode
  :type '(repeat function))


;;;===========================================================================
;;;  Buffer-locals
;;;===========================================================================

(defvar x-symbol-mode nil
  "Non-nil if X-Symbol minor mode is enabled.")

(make-variable-buffer-local 'x-symbol-mode)
(x-symbol-define-user-options 'x-symbol-mode '(t)
  nil (lambda (dummy arg) (x-symbol-mode (if arg 1 0))))

(defvar x-symbol-language nil
  "*Token language used in current buffer.
A valid value is required to turn on `x-symbol-mode' which also sets
this variable to a reasonable value if the variable is not yet
buffer-local.  The value influences the conversion, i.e., decoding and
encoding of X-Symbol characters, input methods TOKEN and READ-TOKEN,
fontification of super- and subscripts, image command recognition, the
info in the echo area, etc.")

(make-variable-buffer-local 'x-symbol-language)
(put 'x-symbol-language 'permanent-local t)
(x-symbol-define-user-options 'x-symbol-language
    (lambda () (list* nil '(nil . "None") x-symbol-language-alist))
  '(x-symbol-update-modeline))

(defvar x-symbol-coding nil
  "*Coding of 8bit characters in a file.
Supported values are `iso-8859-1', `iso-8859-2', `iso-8859-3' and
`iso-8859-9', value nil means the value of `x-symbol-default-coding'.
Determines which characters are considered to be 8bit characters for
file operations.  Function `x-symbol-mode' sets this variable to a
reasonable value if the variable is not yet buffer-local.

During decoding, e.g., when visiting a file, the value is always
important for the interpretation of 8bit characters, an invalid value is
considered to be equivalent to value nil.  During encoding, e.g., when
saving a buffer, 8bit characters are not encoded to tokens if the value
is valid and `x-symbol-8bits' is non-nil.")

(make-variable-buffer-local 'x-symbol-coding)
(put 'x-symbol-coding 'permanent-local t)
(x-symbol-define-user-options 'x-symbol-coding
    (lambda () (cons x-symbol-default-coding x-symbol-coding-name-alist))
  '(x-symbol-update-modeline))

(defvar x-symbol-8bits nil
  "*If non-nil, do not encode 8bit characters.
Variable `x-symbol-coding' determines which characters are assumed to be
8bit characters.  Note that tokens representing 8bit characters are
always decoded.  Function `x-symbol-mode' sets this variable to a
reasonable value if the variable is not yet buffer-local.")
;; TODO: link to `x-symbol-unique'

(make-variable-buffer-local 'x-symbol-8bits)
(put 'x-symbol-8bits 'permanent-local t)
(x-symbol-define-user-options 'x-symbol-8bits '(t)
  '(x-symbol-update-modeline))

(defvar x-symbol-unique nil
  "*If non-nil, only decode canonical tokens.")
;; TODO: link to `x-symbol-8bits'

(make-variable-buffer-local 'x-symbol-unique)
(put 'x-symbol-unique 'permanent-local t)
(x-symbol-define-user-options 'x-symbol-unique '(t)
  '(x-symbol-update-modeline))

(defvar x-symbol-subscripts nil
  "*If non-nil, use special fonts to display super- and subscripts.
This feature must be supported by the token language dependent font-lock
keywords.  Function `x-symbol-mode' sets this variable to a reasonable
value if the variable is not yet buffer-local.  Some parts of the text
might be invisible, see also variable `x-symbol-reveal-invisible'.")

(make-variable-buffer-local 'x-symbol-subscripts)
(x-symbol-define-user-options 'x-symbol-subscripts '(t)
  '(x-symbol-update-modeline x-symbol-fontify))

(defvar x-symbol-image nil
  "*If non-nil, show little glyphs after image insertion commands.
This feature must be supported by the token language dependent image
keywords, see `x-symbol-image-parse-buffer'.  Function `x-symbol-mode'
sets this variable to a reasonable value if the variable is not yet
buffer-local.")

(make-variable-buffer-local 'x-symbol-image)
(x-symbol-define-user-options 'x-symbol-image '(t)
  '(x-symbol-update-modeline) 'x-symbol-set-image)


;;;===========================================================================
;;;  Minor mode control
;;;===========================================================================

(defcustom x-symbol-auto-mode-suffixes (x-symbol-auto-mode-suffixes)
  "*Regexps matching file suffixes not to be considered.
All suffixes from a file name matching these regexps are deleted before
the file name is used for `x-symbol-auto-mode-alist'.  The default value
includes the REGEXP in all three-valued elements of `auto-mode-alist',
at definition time, of course."
  :group 'x-symbol-mode
  :type '(repeat regexp))

(defcustom x-symbol-auto-8bit-search-limit nil
  "*Limits search for 8bit characters in the file.
Used when finding an appropriate value for `x-symbol-8bits'.  See also
`x-symbol-mode'."
  :group 'x-symbol-mode
  :type '(choice (const :tag "No limit" nil) (integer :tag "Limit")))

(defcustom x-symbol-auto-style-alist nil
  ;; TODO: docstring outdated
  "*Alist to setup X-Symbol values for buffers visiting files.
Elements look like
  (MATCH LANGUAGE MODE-ON CODING 8BITS UNIQUE SUBSCRIPTS IMAGE)
If MATCH matches a buffer in which command `x-symbol-mode' is invoked,
the rest of the element is used to setup some buffer-local x-symbol
specific variables.  If no element matches, set `x-symbol-language' to
the symbol property `x-symbol-language' of the major mode symbol if the
variable is not already buffer-local.

If `x-symbol-mode' is not already buffer-local, MODE-ON determines
whether to turn the mode on if `x-symbol-mode' is called with a cons as
prefix argument.  LANGUAGE, CODING, 8BITS, UNIQUE, SUBSCRIPTS and IMAGE
are used to set `x-symbol-language', `x-symbol-coding',
`x-symbol-8bits', `x-symbol-unique', `x-symbol-subscripts' and
`x-symbol-image' if these values are not already buffer-local.

MATCH is either a list of major modes which must include the mode of the
current buffer or a regexp matching the file name ignoring some
suffixes, see `x-symbol-auto-mode-suffixes', or a value used directly.
MODE-ON, LANGUAGE, CODING, 8BITS, UNIQUE, SUBSCRIPTS and IMAGE are
`eval'ed in that order.  During the evaluation, `x-symbol-mode' is
non-nil according to MODE-ON.

See the documentation of `x-symbol-auto-style' for the auto-style
language accesses."
  :group 'x-symbol-mode
  :type '(repeat (cons :format "%v"
		       (choice (repeat :tag "In major modes"
				       :menu-tag "In major modes"
				       (function :value text-mode))
			       (regexp :tag "When matched by")
			       (function :tag "Predicate"))
		       (cons :format "%v"
			     (symbol :tag "Token language")
			     ;;(x-symbol-auto-style :inline t))))
			     (choice (x-symbol-auto-style 
				      :menu-tag "Values"
				      :format "\n%v")
				     (variable :tag "Like variable"))))))

(defvar x-symbol-mode-disable-alist nil)
;; just a `defvar' people should know what they are doing...


;;;===========================================================================
;;;  Images
;;;===========================================================================

(defun x-symbol-image-set-colormap (var value)
  "Set VAR's value to VALUE.
Custom set function of `x-symbol-image-colormap-allocation' and
`x-symbol-image-convert-colormap'."
  (if var (set var value))
  (if (boundp 'x-symbol-image-convert-colormap)
      (put 'x-symbol-image-convert-colormap 'x-symbol-image-instance
	   (and (boundp 'x-symbol-image-colormap-allocation)
		x-symbol-image-colormap-allocation
		x-symbol-image-convert-colormap
		(if (featurep 'xemacs)
		    (make-image-instance
		     (vector x-symbol-image-colormap-allocation
			     :file x-symbol-image-convert-colormap)
		     nil nil t)
		  (create-image x-symbol-image-convert-colormap
				x-symbol-image-colormap-allocation))))))

(defcustom x-symbol-image-colormap-allocation 'xpm
  "If non-nil, prevent colors in colormap to be de-allocated.
The non-nil value should be an image format.  See
`x-symbol-image-convert-colormap'."
  :group 'x-symbol-image-general
  :initialize 'custom-initialize-default
  :set 'x-symbol-image-set-colormap
  :type '(choice (const :tag "Colors can be de-allocated" nil)
		 (const :tag "Colormap is xpm file" xpm)
		 (symbol :tag "Other image format")))

(defcustom x-symbol-image-convert-colormap
  (and x-symbol-data-directory
       (expand-file-name "colormap138.xpm" x-symbol-data-directory))
  "File name of colormap files.
Used by `x-symbol-image-start-convert-colormap' for image cache file
names not matched by `x-symbol-image-convert-mono-regexp'.  See also
`x-symbol-image-colormap-allocation'."
  :group 'x-symbol-image-general
  :initialize 'custom-initialize-default
  :set 'x-symbol-image-set-colormap
  :type '(choice (const :tag "No map" nil) file))



;;;;##########################################################################
;;;;  Code
;;;;##########################################################################


(defalias 'x-symbol-cset-registry 'caaar)
(defalias 'x-symbol-cset-coding 'cdaar)
(defalias 'x-symbol-cset-leading 'cadar)
(defalias 'x-symbol-cset-score 'caddar)
(defalias 'x-symbol-cset-left 'cadr)
(defalias 'x-symbol-cset-right 'cddr)

(defvar x-symbol-input-initialized nil
  "Internal.  If non-nil, the input methods are initialized.")


;;;===========================================================================
;;;  Key autoload
;;;===========================================================================

;;;###autoload
(defun x-symbol-key-autoload (&optional arg)
  "Initialize package x-symbol and use the keys for this command again.
Package x-symbol and the functions in `x-symbol-load-hook' should
re-bind all key-sequence which invoke this command.  You should provide
a prefix argument ARG to this command if `x-symbol-auto-key-autoload' is
nil."
  (interactive "P")
  (when x-symbol-input-initialized
    (error "%s should be rebound in `x-symbol-init-input-hook'"
	   (key-description (this-command-keys))))
  (unless (or arg x-symbol-auto-key-autoload)
    (error "Use %s with prefix argument to initialize the input methods"
	   (key-description (this-command-keys))))
  (let ((this (append (this-command-keys) nil)))
    ;; for some reason this loop is necessary...
    (while (and this (null (eq (key-binding (vector (car this))) this-command)))
      (setq this (cdr this)))
    (setq prefix-arg arg)
    (setq unread-command-events this))
  (x-symbol-init-input))

;;;###autoload
(defalias 'x-symbol-map-autoload 'x-symbol-key-autoload)


;;;===========================================================================
;;;  Minor mode, fontification
;;;===========================================================================

(defun x-symbol-buffer-file-name ()
  (when buffer-file-name
    (let ((name (file-name-sans-versions buffer-file-name))
	  (case-fold-search (eq system-type 'vax-vms))
	  (suffixes x-symbol-auto-mode-suffixes))
      (while suffixes
	(and (string-match (pop suffixes) name)
	     (< (match-beginning 0) (length name))
					; protect against stupid regexp
	     (setq name (substring name 0 (match-beginning 0))
		   suffixes x-symbol-auto-mode-suffixes)))
      name)))

(defun x-symbol-auto-set-variable (symbol form)
  "Set SYMBOL's value to evaluated FORM if SYMBOL is not buffer-local."
  (or (local-variable-p symbol (current-buffer))
      (set symbol (eval form))))

;;;###autoload
(defun x-symbol-mode (&optional arg special)
  "Toggle X-Symbol mode.
If ARG is a cons, e.g., when \\[x-symbol-mode] is preceded by one or
more \\[universal-argument]'s with no digits, turn on X-Symbol mode
conditionally, see MODE-ON in `x-symbol-auto-mode-alist'.  Otherwise,
turn X-Symbol mode on if ARG is positive, else turn it off.  If some
X-Symbol specific local variables are not buffer-local, set them to
reasonable values according to `x-symbol-buffer-mode-alist' and
`x-symbol-auto-mode-alist'.

Turning X-Symbol mode on requires a valid `x-symbol-language' and also
decodes tokens if the mode was turned off before, see
\\[x-symbol-decode].  Turning X-Symbol mode off also encodes x-symbol
characters if the mode was turned on before, see \\[x-symbol-encode].
If argument INIT is non-nil, the old mode status is assumed to be off."
  (interactive (list current-prefix-arg 'interactive))
  (if (eq special 'init) (setq x-symbol-mode nil))
  (let* ((old-mode (if (eq special 'init) nil x-symbol-mode))
	 (new-mode (if arg
		       (> (prefix-numeric-value arg) 0)
		     (not x-symbol-mode)))
	 (disabled0 (assq major-mode x-symbol-mode-disable-alist))
	 (disabled1 (if disabled0
			(cdr disabled0)
		      (get major-mode 'x-symbol-mode-disable)))
	 (disabled (cond (old-mode nil)
			 ((null new-mode) nil)
			 ((null disabled1)
			  (and buffer-file-name (get major-mode 'mode-class) t))
			 ((eq disabled1 'error))
			 ((stringp disabled1) disabled1)
			 ((functionp disabled1) (funcall disabled1)))))
    (setq x-symbol-mode nil)
    (when disabled
      (if (and (eq special 'interactive)
	       arg
	       (yes-or-no-p
		(format "Cannot use X-Symbol with %s Mode.  Turn on anyway? "
			mode-name)))
	  (setq disabled nil)
	(or (stringp disabled)
	    (setq disabled (format "%s Mode does not allow to turn on X-Symbol"
				   mode-name)))
	(setq new-mode nil)))
    (when new-mode
      (let* ((buffer-file-name (x-symbol-buffer-file-name))
	     (buffer-name (or buffer-file-name (buffer-name)))
	     (alist x-symbol-auto-style-alist)
	     (style (get major-mode 'x-symbol-style))
	     ;; WARNING: `values' is a global variable which is set during GC
	     ;; (and we have dynamic scoping)!  major-modes can set a specific
	     ;; language
	     matcher)
	(while alist
	  (setq matcher (caar alist))
	  (if (cond ((stringp matcher) (string-match matcher buffer-name))
		    ((consp matcher) (memq major-mode matcher))
		    ((functionp matcher) (funcall matcher)))
	      (setq style (cdar alist)
		    alist nil)
	    (setq alist (cdr alist))))
	(unless style
	  (let ((langs x-symbol-language-alist))
	    (while langs
	      (if (memq major-mode
			(symbol-value (get (caar langs) 'x-symbol-modes)))
		  (setq style (cons (caar langs) t)
			langs nil)
		(setq langs (cdr langs))))))
	(if (car style)
	    (or (local-variable-p 'x-symbol-language (current-buffer))
		(setq x-symbol-language (car style))))
	;; check language ----------------------------------------------------
	(if (and x-symbol-language
		 (symbolp x-symbol-language)
		 (get x-symbol-language 'x-symbol-feature))
	    (when (and (eq special 'interactive) (consp arg))
	      (setq x-symbol-language
		    (x-symbol-read-language
		     (format "Token Language for X-Symbol mode (default %s): "
			     (x-symbol-language-text))
		     x-symbol-language 'cdr)))
	  (if (eq special 'interactive)
	      (or (setq x-symbol-language
			(x-symbol-read-language
			 "Token Language for X-Symbol mode: " nil 'cdr))
		  (setq disabled
			"A valid token language is required to turn on X-Symbol"))
	    ;; no simple `setq': prevent making `x-symbol-language' buffer-local
	    (if x-symbol-language (setq x-symbol-language nil)))
	  (setq style nil))
	(when x-symbol-language
	  (require (get x-symbol-language 'x-symbol-feature))
	  (setq style
		(cond ((or (null style) (eq (cdr style) t)
			   (not (eq (car style) x-symbol-language)))
		       (symbol-value (get x-symbol-language
					  'x-symbol-auto-style)))
		      ((and (symbolp (cdr style)) (boundp (cdr style)))
		       (symbol-value (cdr style)))
		      (t
		       (cdr style))))
	  (setq x-symbol-mode (eval (car style)))
	  (x-symbol-auto-set-variable 'x-symbol-coding (cadr style))
	  (or (local-variable-p 'x-symbol-8bits (current-buffer))
	      (setq x-symbol-8bits (or (eval (caddr style))
				       (x-symbol-auto-8bit-search))
		    ;; use value `null' to disable 8bit char search
		    x-symbol-8bits (and (not (eq x-symbol-8bits 'null))
					x-symbol-8bits)))
	  (x-symbol-auto-set-variable 'x-symbol-unique (cadddr style))
	  (x-symbol-auto-set-variable 'x-symbol-subscripts (nth 4 style))
	  (x-symbol-auto-set-variable 'x-symbol-image (nth 5 style))
	  (or (and (eq special 'init) (null arg))
	      (setq x-symbol-mode new-mode)))))
    (if (eq special 'init)
	(if x-symbol-mode (x-symbol-mode-internal t))
      (x-symbol-mode-internal (and x-symbol-language
				   (eq (null old-mode) (and x-symbol-mode t))))
      (and disabled
	   (eq special 'interactive)
	   (error (if (stringp disabled)
		      disabled
		    "Cannot turn on X-Symbol mode"))))))

;;;###autoload
(defun turn-on-x-symbol-conditionally ()
  "Turn on x-symbol mode conditionally, see `x-symbol-mode'.
Call `x-symbol-mode' with a cons for ARG and a non-nil INIT.  Used in
`hack-local-variables-hook'."
  (x-symbol-mode (and (local-variable-p 'x-symbol-mode (current-buffer))
		      (if x-symbol-mode 1 0))
		 'init))

;;;###autoload
(defun x-symbol-fontify (&optional beg end)
  "Re-fontify region between BEG and END."
  (interactive (and (region-active-p) (list (region-beginning) (region-end))))
  (cond ((not font-lock-mode) (turn-on-font-lock))
	((and (featurep 'xemacs) (boundp 'lazy-shot-mode) lazy-shot-mode)
	 ;; copied from lazy-shot:
	 (setq font-lock-fontified
	       (and lazy-shot-minimum-size
		    (>= (buffer-size) lazy-shot-minimum-size)))
	 (lazy-shot-install-extents (point-min) (point-max)
				    font-lock-fontified))
	((and (featurep 'xemacs) (boundp 'lazy-lock-mode) lazy-lock-mode)
	 ;; copied from lazy-lock:
	 (let ((modified (buffer-modified-p)) (inhibit-read-only t)
	       (buffer-undo-list t)
	       ;;deactivate-mark
	       buffer-file-name buffer-file-truename)
	   (remove-text-properties (or beg 1) (or end (1+ (buffer-size)))
				   '(fontified nil))
	   (or modified (set-buffer-modified-p nil))))
	(t
	 (font-lock-fontify-buffer))))


;;;===========================================================================
;;;  comint support
;;;===========================================================================

(defun x-symbol-comint-output-filter (dummy)
  ;; checkdoc-params: (dummy)
  "Decode output of comint's process.
Used as value in `comint-output-filter-functions'."
  (and x-symbol-mode x-symbol-language
       (save-excursion
	 (x-symbol-decode-region (if (interactive-p)
				     comint-last-input-end
				   comint-last-output-start)
				 (process-mark (get-buffer-process
						(current-buffer)))))))

(defun x-symbol-comint-send (proc string)
  "Encode STRING and send it to process PROC.
Used as value of `comint-input-sender', uses
`x-symbol-orig-comint-input-sender'."
  (and x-symbol-mode x-symbol-language
       (setq string
	     (save-excursion
	       (let ((orig-buffer (current-buffer))
		     (selective selective-display))
		 (set-buffer (get-buffer-create " x-symbol comint"))
		 (erase-buffer)
		 (insert string)
		 (x-symbol-inherit-from-buffer orig-buffer)
		 (x-symbol-encode-all)
		 (setq selective-display selective))
		 (buffer-string))))
  (funcall x-symbol-orig-comint-input-sender proc string))


;;;===========================================================================
;;;  Hooks for automatic conversion
;;;===========================================================================

;; TODO: for format fns: check whether read-only stuff is still necessary...
;; TODO: check the narrow-to-region stuff

(defun x-symbol-format-decode (start end)
  (if (and x-symbol-mode x-symbol-language)
      (save-restriction
	(narrow-to-region start end)
	(let ((modified (buffer-modified-p)) ; t if `recover-file'!
	      ;;(buffer-undo-list t) ; do not record changes
	      ;; we cannot set buffer-undo-list to t even if the previous
	      ;; value is nil because M-x insert-file as the first command
	      ;; after reading a file would set the old insert-region
	      ;; boundaries into the undo-list
	      (buffer-read-only nil) ; always allow conversion
	      (inhibit-read-only t)
	      (first-change-hook nil) ; no `flyspell-mode' here
	      (after-change-functions nil)) ; no fontification
;;;	  (and orig-buffer
;;;	       (not (eq (current-buffer) orig-buffer))
;;;	       (x-symbol-inherit-from-buffer orig-buffer))
	  (x-symbol-decode-all)
	  (or modified (set-buffer-modified-p nil))
	  (point-max)))
    end))

(defun x-symbol-format-encode (start end orig-buffer)
  (let ((new-buffer (current-buffer)))
    (if (eq new-buffer orig-buffer)
	(and x-symbol-mode x-symbol-language
	     (save-restriction
	       (narrow-to-region start end)
	       (x-symbol-encode-all)))
      (set-buffer orig-buffer)
      (and x-symbol-mode x-symbol-language
	   (if (featurep 'mule)
	       (let ((cs buffer-file-coding-system))
		 (x-symbol-encode-all new-buffer)
		 (setq buffer-file-coding-system cs))
	     (x-symbol-encode-all new-buffer))))))

(defun x-symbol-after-insert-file (len)
  ;; checkdoc-params: (len)
  "Decode tokens, e.g., after \\[vc-register] or \\[vc-next-action].
Added to `after-insert-file-functions' if
`x-symbol-auto-conversion-method' has value `fast'."
  ;; TODO (outdated?, dropped coding): in old XEmacsen, there is no way to know
  ;; the start position of the region.  If `insert-file-contents' is called
  ;; with argument REPLACE being non-nil, it is not always point.  Thus, we use
  ;; `point-min', except when called from `M-x insert-file'.

  ;; The docstring of `after-insert-file-functions' talks about bytes, but that
  ;; seems to be nonsense and doesn't match the coding in lisp/format.el,
  ;; must be checked with src/fileio.c.
  (and x-symbol-mode x-symbol-language
       (if (<= (+ (point) len) (point-max))
	   (save-restriction
	     (narrow-to-region (point) (+ (point) len))
	     (let ((origpos (point))
		   (modified (buffer-modified-p)) ; t if `recover-file'!
		   ;;(buffer-undo-list t) ; do not record changes
		   ;; we cannot set buffer-undo-list to t even if the previous
		   ;; value is nil because M-x insert-file as the first command
		   ;; after reading a file would set the old insert-region
		   ;; boundaries into the undo-list
		   (buffer-read-only nil) ; always allow conversion
		   (inhibit-read-only t)
		   (first-change-hook nil) ; no `flyspell-mode' here
		   (after-change-functions nil)) ; no fontification
	       (x-symbol-decode-all)
	       (goto-char origpos)
	       (or modified (set-buffer-modified-p nil))
	       (setq len (- (point-max) (point-min)))))
	 (lwarn 'x-symbol 'warning
	   ;; might leed to quite a few warnings with old XEmacs, get those
	   "Wrong point position provided for function in `after-insert-file-functions'")))
  len)

(defun x-symbol-write-region-annotate-function (start end)
  ;; checkdoc-params: (start end)
  "Encode x-symbol characters using another buffer.
Added to `write-region-annotate-functions' if
`x-symbol-auto-conversion-method' has value `fast'."
  (and x-symbol-mode x-symbol-language
       (not (equal start ""))		; kludgy feature of `write-region'
       ;; Without the test, "x-symbol.el" is loaded twice, the initialization
       ;; done twice (resulting in warnings about charsym redefinitions).
       ;; Reason: in Emacs, `make-temp-name', used for the value of some var in
       ;; "x-symbol-vars.el", required by "x-symbol.el", calls `write-region'.
       (let ((selective selective-display))
	 ;; at least in XEmacs, this function might be called with both args
	 ;; nil
	 (x-symbol-encode-all (get-buffer-create " x-symbol conversion")
			      (or start (point-min)) (or end (point-max)))
	 ;; set `selective-display' according to orig buffer
	 (setq selective-display selective)))
  nil)

(defun x-symbol-write-file-hook ()
  "Encode x-symbol characters in current buffer.
Added to `write-file-hooks' if `x-symbol-auto-conversion-method' has a
value other than nil or `fast'.  Refontifies buffer if
`x-symbol-auto-conversion-method' has value `slowest'."
  (and x-symbol-mode x-symbol-language
      (let ((buffer-read-only nil)
	    ;; `buffer-read-only' is only dec/ if `inhibit-read-only' doesn't
	    ;; exist.  TODO: check whether still nec/ in XEmacs-21.1
	    (inhibit-read-only t)
	    (inhibit-modification-hooks t) ; Emacs only: then
					   ; `after-change-functions' not nec/
	    (first-change-hook nil)	; no `flyspell-mode' here
	    (after-change-functions nil)) ; no fontification!
	(widen)	;; Called inside `save-recursion' and `save-restriction'.
	;; TODO: define a common macro in x-symbol-macs.el instead, which can
	;; also be used in `x-symbol-tex-translate-locations', it has an
	;; addition argument for the var `changed' there, with that arg: no
	;; `unwind-protect'
	(if (featurep 'xemacs)
	    (call-with-transparent-undo
	     (lambda ()
	       (x-symbol-encode-all)	; not the safe version!
	       (continue-save-buffer)))
	  (let ((buffer-undo-list nil)
		;; Kludge to prevent undo list truncation:
		(undo-limit most-positive-fixnum) ; Emacs
		(undo-strong-limit most-positive-fixnum) ; Emacs
		(undo-high-threshold -1)	; XEmacs
		(undo-threshold -1))		; XEmacs
	    (unwind-protect
		(progn
		  (x-symbol-encode-all)	; not the safe version!
		  (continue-save-buffer))
	      (let ((tail buffer-undo-list))
		(setq buffer-undo-list t)
		(while tail
		  (setq tail (primitive-undo (length tail) tail)))))))
	(and (eq x-symbol-auto-conversion-method 'slowest)
	     font-lock-mode
	     (x-symbol-fontify))
	(set-buffer-modified-p nil)
	'x-symbol-write-file-hook)))	; do not write again


;;;===========================================================================
;;;  Init
;;;===========================================================================

(defvar x-symbol-modeline-string ""
  "String that should appear in the modeline when `x-symbol-mode' is on.
Its value is set by `x-symbol-update-modeline'.")
(make-variable-buffer-local 'x-symbol-modeline-string)

(defvar x-symbol-mode-map
  (let ((m (make-sparse-keymap)))
    ;; (substitute-key-definition 'x-symbol-map-autoload 'x-symbol-map
    ;; 			       m global-map)
    m))

(add-minor-mode 'x-symbol-mode 'x-symbol-modeline-string x-symbol-mode-map)
(put 'x-symbol-mode :menu-tag "X-Symbol")

(defvar x-symbol-early-language-access-alist
  '((x-symbol-name "name" nil stringp)
    (x-symbol-modes "modes" t listp)
    (x-symbol-auto-style "auto-style" require)))

(defun x-symbol-init-language-accesses (language alist)
  "Initialize accesses for token language LANGUAGE according to ALIST.
The symbol property `x-symbol-feature' of LANGUAGE must be set before.
See also `x-symbol-language-access-alist'."
  ;;If optional NO-TEST is nil, accesses which do not point to a bound
  ;;variable are not set.
  (let ((feature (get language 'x-symbol-feature))
	(ok t)
	symbol)
    (dolist (item alist)
      (setq symbol (intern (format "%s-%s" feature (cadr item))))
      (if (not (or (boundp symbol) (eq (caddr item) 'require)))
	  (or (eq (caddr item) t)	; optional access
	      (and (caddr item) (not (get language (caddr item))))
	      (progn
		(lwarn feature 'error
		  "Token language `%s' does not define `%s'" language symbol)
		(setq ok nil))
	      (put language (car item) symbol))
	(or (null (cadddr item))
	    (caddr item)		; optional access: value nil always ok
	    (funcall (cadddr item) (symbol-value symbol))
	    (progn
	      (lwarn feature 'error
		"Token language `%s' uses illegal type for value of `%s'"
		language symbol)
	      (setq ok nil)))
	(put language (car item) symbol)))
    ok))

;;;###autoload
(defun x-symbol-register-language (language feature &optional modes)
  "Register token language LANGUAGE.
FEATURE is a feature which `provide's LANGUAGE.  MODES are major modes
which typically use LANGUAGE.  Using LANGUAGE's accesses will initialize
LANGUAGE, see `x-symbol-language-value'."
  ;; TODO: modes are ignored
  ;; set (dolist (mode modes) (put mode 'x-symbol-style (cons language t)))
  (unless (get language 'x-symbol-feature)
    (put language 'x-symbol-feature feature))
  (unless
      (x-symbol-init-language-accesses language
				       x-symbol-early-language-access-alist)
    (error "Registration of X-Symbol language `%s' has failed" language))
;;  (x-symbol-init-language-accesses language '((x-symbol-name . "name")))
  (unless (assq language x-symbol-language-alist)
    (setq x-symbol-language-alist
	  (nconc x-symbol-language-alist
		 (list (cons language
			     (symbol-value (get language 'x-symbol-name))))))))

;;;###autoload
(defun x-symbol-initialize (&optional arg)
  "Initialize package X-Symbol.
See variable `x-symbol-initialize' and function `x-symbol-after-init'.
Also allocate colormap, see `x-symbol-image-colormap-allocation'.
Unless optional argument ARG is non-nil, do not initialize package
X-Symbol twice."
  (interactive "P")
  (unless (and (get 'x-symbol 'x-symbol-initialized) (null arg))
    (put 'x-symbol 'x-symbol-initialized t)
    ;; X-Symbol doesn't make sense without the following.  `ctl-arrow' is a
    ;; boolean in Emacs, but not in XEmacs: despite its docstring, value t
    ;; means the same as 256 (and 255 sometimes, which is probably wrong).
    (or (default-value 'ctl-arrow) (setq-default ctl-arrow 'iso-8859/1))
    ;; Token languages -------------------------------------------------------
    (when (or (eq x-symbol-initialize t)
	      (memq 'languages x-symbol-initialize))
      (x-symbol-register-language 'tex 'x-symbol-tex)
      (x-symbol-register-language 'sgml 'x-symbol-sgml)
      (x-symbol-register-language 'bib 'x-symbol-bib)
      (x-symbol-register-language 'texi 'x-symbol-texi))
    ;; Global mode -----------------------------------------------------------
    (when (or (eq x-symbol-initialize t)
	      (memq 'global x-symbol-initialize))
      (add-hook 'hack-local-variables-hook 'turn-on-x-symbol-conditionally))
    ;; Key bindings ----------------------------------------------------------
    (when (or (eq x-symbol-initialize t)
	      (memq 'keys x-symbol-initialize))
      (global-set-key (vector x-symbol-compose-key) 'x-symbol-map-autoload)
      (unless (featurep 'xemacs)
	(define-key isearch-mode-map (vector x-symbol-compose-key) nil)
	;;(define-key isearch-mode-map [mouse-2] 'isearch-mouse-2)
	(define-key isearch-mode-map [menu-bar X-Symbol] nil))
      (global-set-key [(control ?\,)] 'x-symbol-modify-key)
      (global-set-key [(control ?\.)] 'x-symbol-rotate-key))
    ;; Font path -------------------------------------------------------------
    (and (or (eq x-symbol-initialize t)
	     (memq 'font-path x-symbol-initialize))
	 x-symbol-font-directory
	 (file-accessible-directory-p x-symbol-font-directory)
	 ;; by Jim Radford <radford@robby.caltech.edu>:
	 (memq (console-type) '(x gtk))
	 (if (fboundp 'x-set-font-path)	; XEmacs >= 21.4
	     (let ((font-path (x-get-font-path)))
	       (condition-case nil
		   (unless (or (member (file-name-as-directory
					x-symbol-font-directory) font-path)
			       (member (directory-file-name
					x-symbol-font-directory) font-path))
		     (x-set-font-path (nconc font-path
					     (list x-symbol-font-directory)))
		     nil)
		 (t
		  (lwarn 'x-symbol 'error
		    "Couldn't add %s to X font path" x-symbol-font-directory)
		  t)))		; (error t) doesn't work (XEmacs bug?)
	   ;; This should be commented out until I can figure out how to
	   ;; get the display name into the -display arg for xset.
	   (with-temp-buffer
	     (call-process "xset" nil t nil "q")
	     (goto-char (point-min))
	     (unless (search-forward (directory-file-name
				      x-symbol-font-directory) nil t)
	       (not (eq 0 (call-process "xset" nil nil nil "fp+"
					x-symbol-font-directory))))))
	 (lwarn 'x-symbol 'error
	   "Couldn't add %s to X font path" x-symbol-font-directory))
    ;; Package fast-lock -----------------------------------------------------
    (when (or (eq x-symbol-initialize t)
	      (memq 'fast-lock x-symbol-initialize))
      (setq fast-lock-save-faces nil))
    ;; Package AucTeX ----------------------------------------------------------
    (when (or (eq x-symbol-initialize t)
	      (memq 'auctex x-symbol-initialize))
      (or (fboundp 'x-symbol-tex-error-location) ; esp for preview-latex
	  (fset 'x-symbol-tex-error-location 'ignore))
      (add-hook 'TeX-translate-location-hook 'x-symbol-tex-error-location)
      (add-hook 'TeX-region-hook 'x-symbol-inherit-from-buffer) ; v9.8a+
      (setq LaTeX-math-insert-function 'x-symbol-auctex-math-insert)) ; v9.8a+
    ;; Package RefTeX --------------------------------------------------------
    (when (or (eq x-symbol-initialize t)
	      (memq 'reftex x-symbol-initialize))
      (unless (and (boundp 'reftex-translate-to-ascii-function)
		   (fboundp reftex-translate-to-ascii-function)
		   (not (eq reftex-translate-to-ascii-function
			    'reftex-latin1-to-ascii)))
	(setq reftex-translate-to-ascii-function 'x-symbol-translate-to-ascii))
      (add-hook 'reftex-pre-refontification-functions
		'x-symbol-inherit-from-buffer)
      (unless (featurep 'mule)
	;; RefTeX might be invoked from a TeX buffer without X-Symbol
	(or (fboundp 'x-symbol-nomule-fontify-cstrings)
	    (fset 'x-symbol-nomule-fontify-cstrings 'ignore))
	(add-hook 'reftex-display-copied-context-hook
		  'x-symbol-nomule-fontify-cstrings)))
    ;; Miscellaneous ---------------------------------------------------------
    (x-symbol-image-set-colormap nil nil)
    (if init-file-loaded
	(x-symbol-after-init)
      (add-hook 'after-init-hook 'x-symbol-after-init))))

(defun x-symbol-after-init ()
  "Late initialization for package X-Symbol.
See function `x-symbol-initialize' and variables `x-symbol-initialize'
and `x-symbol-auto-conversion-method'.  Also add elements to
`x-symbol-auto-mode-suffixes' if necessary."
  (when x-symbol-auto-conversion-method
    (and (eq x-symbol-auto-conversion-method 'auto-slow)
	 (null (featurep 'crypt))
	 (setq x-symbol-auto-conversion-method 'fast))
    (cond ((eq x-symbol-auto-conversion-method 'format)
	   (or (assq 'x-symbol format-alist)
	       (push '(x-symbol "X-Symbol" nil
				x-symbol-format-decode x-symbol-format-encode
				t x-symbol-mode t)
		     format-alist)))
	  ((eq x-symbol-auto-conversion-method 'fast)
	   (add-hook 'after-insert-file-functions
		     'x-symbol-after-insert-file t)
	   ;; If we don't use APPEND for the hook below, we must use APPEND for
	   ;; the hook above (and v/v).  For Emacs-21.2, using APPEND when
	   ;; inserting is the only correct one, because function
	   ;; `after-insert-file-set-buffer-file-coding-system', which has been
	   ;; added to the hook, must run first (BTW, also for format.el...).
	   (add-hook 'write-region-annotate-functions
		     'x-symbol-write-region-annotate-function))
	  (t
	   (add-hook 'write-file-hooks 'x-symbol-write-file-hook))))
  ;; misc user additions to `auto-mode-alist':
  (setq x-symbol-auto-mode-suffixes (x-symbol-auto-mode-suffixes
				     x-symbol-auto-mode-suffixes))
  ;; Package comint ----------------------------------------------------------
  (when (or (eq x-symbol-initialize t)
	    (memq 'comint x-symbol-initialize))
    (add-hook 'comint-output-filter-functions 'x-symbol-comint-output-filter)
    (and (boundp 'comint-input-sender)
	 (not (eq comint-input-sender 'x-symbol-comint-send))
	 (setq x-symbol-orig-comint-input-sender comint-input-sender))
    (setq comint-input-sender 'x-symbol-comint-send))
  ;; Package bib-cite: X-Symbol decoding would overwrite cite highlighting with
  ;; normal installation of bib-cite -----------------------------------------
  (when (and (or (eq x-symbol-initialize t)
		 (memq 'bib-cite x-symbol-initialize))
	     (or (and (boundp 'LaTeX-mode-hook)
		      (memq 'turn-on-bib-cite LaTeX-mode-hook))
		 (and (boundp 'latex-mode-hook)
		      (memq 'turn-on-bib-cite latex-mode-hook))))
    (remove-hook 'LaTeX-mode-hook 'turn-on-bib-cite)
    (remove-hook 'latex-mode-hook 'turn-on-bib-cite)
    (add-hook 'find-file-hooks 'x-symbol-turn-on-bib-cite)))


;;;===========================================================================
;;;  Support for other packages
;;;===========================================================================

(defun x-symbol-inherit-from-buffer (&optional parent action)
  "Inherit X-Symbol's buffer-local variables from buffer PARENT.
Inherit `x-symbol-mode', `x-symbol-coding', `x-symbol-8bits',
`x-symbol-language', and `x-symbol-subscripts' from PARENT and set
`x-symbol-image' to nil.  If PARENT is nil, `orig-buffer' is used if
it is bound.  ACTION is ignored."
  (and (null parent) (boundp 'orig-buffer) (setq parent orig-buffer))
  ;; I don't care too much that people who use X-Symbol in the master buffer,
  ;; but not in the buffer where they invoke M-x TeX-command-region from, won't
  ;; have the X-Symbol characters in the "master envelope" decoded...
  (if (buffer-live-p (get-buffer parent))
      (let (mode-on coding 8bits unique language subscripts)
	(save-excursion
	  (set-buffer parent)
	  (setq mode-on    x-symbol-mode
		coding     x-symbol-coding
		8bits	   x-symbol-8bits
		unique     x-symbol-unique
		language   x-symbol-language
		subscripts x-symbol-subscripts))
	(setq x-symbol-mode mode-on)
	(if (local-variable-p 'x-symbol-coding parent)
	    (setq x-symbol-coding coding))
	(if (local-variable-p 'x-symbol-8bits parent)
	    (setq x-symbol-8bits 8bits))
	(if (local-variable-p 'x-symbol-unique parent)
	    (setq x-symbol-unique unique))
	(if (local-variable-p 'x-symbol-language parent)
	    (setq x-symbol-language language))
	(if (local-variable-p 'x-symbol-subscripts parent)
	    (setq x-symbol-subscripts subscripts))
	(setq x-symbol-image nil))))

(defun x-symbol-auctex-math-insert (string)
  "Insert the character for \\STRING.
Used as value for `LaTeX-math-insert-function'."
  (let ((cstring (and x-symbol-mode x-symbol-language
		      (x-symbol-decode-single-token (concat "\\" string)))))
    (if cstring
	(insert cstring)
      (TeX-insert-macro string))))

(defun x-symbol-turn-on-bib-cite ()
  "Run `turn-on-bib-cite' if we are in `latex-mode'.
Added to `find-file-hooks' if the initialization for X-Symbol has
removed `turn-on-bib-cite' from `LaTeX-mode-hook' or `latex-mode-hook'.
See variable `x-symbol-initialize'."
  (if (eq major-mode 'latex-mode) (turn-on-bib-cite)))

;;; Local IspellPersDict: .ispell_xsymb
;;; x-symbol-hooks.el ends here
