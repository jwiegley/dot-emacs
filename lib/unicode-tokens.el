;;; unicode-tokens.el --- Support for control and symbol tokens
;;
;; Copyright(C) 2008-2009 David Aspinall / LFCS Edinburgh
;; Author:    David Aspinall <David.Aspinall@ed.ac.uk>
;; License:     GPL (GNU GENERAL PUBLIC LICENSE)
;;
;; $Id$
;;
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

;;; Commentary:
;;
;; This is a replacement for X-Symbol for Proof General.
;;
;; Functions to display tokens that represent Unicode characters and
;; control code sequences for changing the layout.  Tokens are useful
;; for programs that do not understand a Unicode encoding.
;; 

;; Desirable improvements/enhancements
;;
;; -- insert tokens via numeric code (extra format string), cf HTML
;; -- simplify: unify region and control settings?
;; -- simplify/optimise property handling 

;;
;;; Code:
;;

(require 'cl)

(eval-when-compile
  (require 'maths-menu))		; nuke compile warnings

;;
;; Variables that should be set by client modes
;; 
;; Each variable may be set directly or indirectly; see
;; `unicode-tokens-copy-configuration-variables' below.
;;

(defvar unicode-tokens-token-symbol-map nil
  "Mapping of token names to compositions.
A list, each element of which is a list

  (TOKNAME COMPOSITION FONTSYMB ...)

A composition is typically a single Unicode character string, but
can be more complex: see documentation of `compose-region'.

TOKNAMEs may be repeated.  The first one with a usable
composition according to `unicode-tokens-usable-composition', 
if any.

The sequence of FONTSYMB are optional.  Each FONTSYMB is a symbol
indicating a set of additional text properties, looked up in
`unicode-tokens-fontsymb-properties'.

By default, tokens are displayed ")

(defvar unicode-tokens-token-format "%s"
  "Format string for formatting token a name into a token.
Will be regexp quoted for matching.  Not used for matching if
`unicode-tokens-token-variant-format-regexp' is set.
Also used to format shortcuts.")

(defvar unicode-tokens-token-variant-format-regexp nil
  "A regular expression which matches a token variant.
Will not be regexp quoted, and after format is applied, must

An example would be: \\\\(%s\\\\)\\\\(:?\\w+\\\\)

which matches plain token strings optionally followed by a colon and
variant name.

If set, this variable is used instead of `unicode-tokens-token-format'.")

(defvar unicode-tokens-shortcut-alist nil
  "An alist of keyboard shortcuts to unicode strings.
The alist is added to the input mode for tokens.
The shortcuts are only used for input convenience; no reverse 
mapping back to shortucts is performed.  Behaviour is like abbrev.")

(defvar unicode-tokens-shortcut-replacement-alist nil
  "Overrides `unicode-tokens-shortcut-alist' for `unicode-tokens-replace-shortcuts'.")


;;
;; Variables that may optionally be set in client modes
;;

(defvar unicode-tokens-control-region-format-regexp nil
  "A regexp for control regions, with up to two %s placeholders.
When fomatted with arguments START END, results in a regexp
that matches a control region.  There should be three delimited
subexpressions: (match-string 1) and (match-string 3) are hidden,
and (match-string 2) has the display control applied.")

(defvar unicode-tokens-control-char-format-regexp nil
  "A format string for control characters, possibly with a %s placeholder.
When fomatted with arguments STRING, results in a regexp
that matches a control character sequence.   There should be two
delimited subexpressions: (match-string 1) is hidden
and (match-string 2) has the display control applied.")

(defvar unicode-tokens-control-regions nil
  "A list of control regions.")

(defvar unicode-tokens-control-characters nil
  "A list of control characters.")

(defvar unicode-tokens-control-char-format nil
  "A format string for inserting a control character sequence.")

(defvar unicode-tokens-control-region-format-start nil
  "A format string for begining a control region sequence.")

(defvar unicode-tokens-control-region-format-end nil
  "A format string for ending a control region sequence.")

;;
;; A list of the above variables
;;

(defconst unicode-tokens-configuration-variables
  '(token-symbol-map
    token-format
    token-variant-format-regexp
    shortcut-alist
    shortcut-replacement-alist
    control-region-format-regexp
    control-region-format-start
    control-region-format-end
    control-char-format-regexp
    control-char-format
    control-regions
    control-characters))

(defun unicode-tokens-config (sym)
  "Construct the symbol name `unicode-tokens-SYM'."
  (intern (concat "unicode-tokens-" (symbol-name sym))))

(defun unicode-tokens-config-var (sym)
  "Construct the symbol name `unicode-tokens-SYM-variable'."
  (intern (concat "unicode-tokens-" (symbol-name sym) "-variable")))

(dolist (sym unicode-tokens-configuration-variables)
 (lambda (sym)
   (eval `(defvar ,(unicode-tokens-config-var sym)
	   nil
	   ,(format 
	     "Name of a variable used to configure %s.\nValue should be a symbol."
	     (symbol-name (unicode-tokens-config sym)))))))

(defun unicode-tokens-copy-configuration-variables ()
  "Initialise the configuration variables by copying from variable names.
Each configuration variable may be set directly or indirectly by client;
modes an indirect setting is made by this function from a variable named
<setting>-variable, e.g., `unicode-tokens-token-symbol-map'
will be initialised from `unicode-tokens-token-symbol-map-variable'
if it is bound, which should be the name of a variable."
  (dolist (sym unicode-tokens-configuration-variables)
    (let ((var (unicode-tokens-config-var sym)))
      (if (and (boundp var) (not (null (symbol-value var))))
	  (set (unicode-tokens-config sym)
	       (symbol-value (symbol-value
			      (unicode-tokens-config-var sym)))))))
  (unless unicode-tokens-shortcut-replacement-alist
    (setq unicode-tokens-shortcut-replacement-alist
	  unicode-tokens-shortcut-alist)))

(defun unicode-tokens-customize (sym)
  "Customize the configuration variable held in `unicode-tokens-SYM-variable'."
  (interactive "sCustomize setting: ") ;; TODO: completing read, check if customizable
  (customize-variable
   (symbol-value (unicode-tokens-config-var (intern sym)))))
  



;;
;; Variables set in the mode
;;

(defvar unicode-tokens-token-list nil
  "List of usable token names in order from `unicode-tokens-token-symbol-map'.")

(defvar unicode-tokens-hash-table nil
  "Hash table mapping token names (strings) to composition and properties.")

(defvar unicode-tokens-token-match-regexp nil
  "Regular expression used by font-lock to match known tokens.")

(defvar unicode-tokens-uchar-hash-table nil
  "Hash table mapping unicode strings to symbolic token names.
This is used for an approximate reverse mapping, see `unicode-tokens-paste'.")

(defvar unicode-tokens-uchar-regexp nil
  "Regular expression matching converted tokens.
This is used for an approximate reverse mapping, see `unicode-tokens-paste'.")


;;
;; Make all of those buffer local
;; 
;; TODO: use per *mode* defaults for them, cf proof-unicode-tokens
;;

;; (mapcar 'make-variable-buffer-local
;;  	unicode-tokens-configuration-variables)

;; (mapcar 'make-variable-buffer-local
;;  	'(unicode-tokens-token-list
;;  	  unicode-tokens-hash-table
;;  	  unicode-tokens-token-match-regexp
;;  	  unicode-tokens-uchar-hash-table
;;  	  unicode-tokens-uchar-regexp))

;;
;; Faces
;;

(defgroup unicode-tokens-faces nil
  "The faces used in Unicode Tokens mode."
  :group 'faces)

(defconst unicode-tokens-font-family-alternatives
  '(("STIXGeneral" 
     "DejaVu Sans Mono" "DejaVuLGC Sans Mono")
    ("Script" 
     "Lucida Calligraphy" "URW Chancery L")
    ("Fraktur"
     "Lucida Blackletter" "URW Bookman L")))

(if (boundp 'face-font-family-alternatives)
    (custom-set-default 
     'face-font-family-alternatives
     (append face-font-family-alternatives
	     unicode-tokens-font-family-alternatives)))

(defface unicode-tokens-symbol-font-face
  '((t :family "STIXGeneral"))
  "The default font used for symbols.  Only :family attribute is used."
  :group 'unicode-tokens-faces)

;; (defface unicode-tokens-large-symbol-font-face
;;    '((t :family "STIXSize3"))
;;    "The font used for large symbols."
;;    :group 'unicode-tokens-faces)

(defface unicode-tokens-script-font-face
  '((t :family "Script"))
  "Script font face."
  :group 'unicode-tokens-faces)

(defface unicode-tokens-fraktur-font-face
  '((t :family "Fraktur"))
  "Fraktur font face."
  :group 'unicode-tokens-faces)

(defface unicode-tokens-serif-font-face
  '((t :family "Times-Roman"))
  "Serif (roman) font face."
  :group 'unicode-tokens-faces)

(defface unicode-tokens-sans-font-face
  '((t :family "Sans"))
  "Sans serif font face."
  :group 'unicode-tokens-faces)

(defface unicode-tokens-highlight-face
  '((((min-colors 88) (background dark))
     (:background "yellow1" :foreground "black"))
    (((background dark)) (:background "yellow" :foreground "black"))
    (((min-colors 88)) (:background "yellow1"))
    (t (:background "yellow")))
  "Face used for highlighting in Unicode tokens."
  :group 'unicode-tokens-faces)

(defconst unicode-tokens-fonts
  '(symbol script fraktur serif sans) ; large-symbol
  "A list of the faces used for setting fonts for Unicode Tokens.")


;;
;; Standard text properties used to build fontification
;;

(defconst unicode-tokens-fontsymb-properties 
  '((sub       	  "Lower"     	  (display (raise -0.4)))
    (sup       	  "Raise"     	  (display (raise 0.4)))
    (bold      	  "Bold"      	  (face (:weight bold)))
    (italic    	  "Italic"    	  (face (:slant italic)))
    (big       	  "Bigger"    	  (face (:height 1.5)))
    (small     	  "Smaller"   	  (face (:height 0.75)))
    (underline 	  "Underline" 	  (face (:underline t)))
    (overline  	  "Overline"  	  (face (:overline t)))
    ;; NB: symbols for fonts need to be as in unicode-tokens-fonts
    (script    	  "Script font"   (face unicode-tokens-script-font-face))
    (frakt     	  "Frakt font"    (face unicode-tokens-fraktur-font-face))
    (serif     	  "Serif font"    (face unicode-tokens-serif-font-face))
    (sans      	  "Sans font"     (face unicode-tokens-sans-font-face))
;    (large-symbol "Large Symbol font" 
;		  (face unicode-tokens-large-symbol-font-face))
    ;; NB: next ones not really generic.  Previously this was
    ;; configured per-prover, but above are generic. 
    (dec       "Declaration face" (face proof-declaration-name-face))
    (tactic    "Tactic face"      (face proof-tactics-name-face))
    (tactical  "Tactical face"    (face proof-tactical-name-face)))
 "Association list mapping a symbol to a name and list of text properties.
Used in `unicode-tokens-token-symbol-map', `unicode-tokens-control-regions',
and `unicode-tokens-control-characters'.
Several symbols can be used at once, in `unicode-tokens-token-symbol-map'.")

(define-widget 'unicode-tokens-token-symbol-map 'lazy
  "Type for customize variables used to set `unicode-tokens-token-symbol-map'."
  :offset 4
  :tag "Token symbol map"
  :type  
  ;; TODO: improve this so customize editing is more pleasant.
  (list 'repeat :tag "Map entries"
	(append
	 '(list :tag "Mapping"
		(string :tag "Token name")	 
		(string :tag "Unicode string"))
	 (list (append
		'(set :tag "Text property styles"  :inline t)
		(mapcar (lambda (fsp)
			  (list 'const :tag 
				(cadr fsp) (car fsp)))
			unicode-tokens-fontsymb-properties))))))

(define-widget 'unicode-tokens-shortcut-alist 'lazy
  "Type for customize variables used to set `unicode-tokens-shortcut-alist'."
  :offset 4
  :tag "Shortcut list"
  :type '(repeat :tag "Shortcut list"
		 (cons (string :tag "Shortcut sequence")
		       (string :tag "Buffer string"))))


;;
;; Calculating font-lock-keywords
;;

(defconst unicode-tokens-font-lock-extra-managed-props
  '(composition help-echo display invisible)
  "Value for `font-lock-extra-managed-props' here.")

(defun unicode-tokens-font-lock-keywords ()
  "Calculate and return value for `font-lock-keywords'.
This function also initialises the important tables for the mode."
  ;; Credit to Stefan Monnier for much slimmer original version
  (let ((hash       (make-hash-table :test 'equal))
	(ucharhash  (make-hash-table :test 'equal))
	toks uchars)
     (dolist (x   unicode-tokens-token-symbol-map)
       (let ((tok  (car x))
	     (comp (cadr x)))
	 (when (unicode-tokens-usable-composition comp)
	   (unless (gethash tok hash)
	     (puthash tok (cdr x) hash)
	       (push tok toks)
	       (if (stringp comp) ;; reverse map only for string comps
		   (unless (or (gethash comp ucharhash)
			       ;; ignore plain chars for reverse map
			       (string-match "[a-zA-Z0-9]+" comp))
		     (push comp uchars)
		     (puthash comp tok ucharhash)))))))
     (when toks
       (setq unicode-tokens-hash-table hash)
       (setq unicode-tokens-uchar-hash-table ucharhash)
       (setq unicode-tokens-token-list (reverse toks))
       (setq unicode-tokens-uchar-regexp (regexp-opt uchars))
       (setq unicode-tokens-token-match-regexp
	     (if unicode-tokens-token-variant-format-regexp
		 (format unicode-tokens-token-variant-format-regexp
			 (regexp-opt toks t))
	       (regexp-opt (mapcar (lambda (tok)
				     (format unicode-tokens-token-format tok))
				   toks) 'words)))
       (cons
	`(,unicode-tokens-token-match-regexp
	  (0 (unicode-tokens-help-echo) prepend)
	  (0 (unicode-tokens-font-lock-compose-symbol
	      ,(- (regexp-opt-depth unicode-tokens-token-match-regexp) 1))
	      prepend))
	(unicode-tokens-control-font-lock-keywords)))))

(defun unicode-tokens-usable-composition (comp)
  "Return non-nil if the composition COMP seems to be usable.
The check is with `char-displayable-p'."
  (cond
   ((stringp comp)
    (reduce (lambda (x y) (and x (char-displayable-p y)))
	    comp
	    :initial-value t))
   ((char-valid-p comp)
    (char-displayable-p comp))
   (comp ;; assume any other non-null is OK
    t)))

(defun unicode-tokens-help-echo ()
  "Return a help-echo text property to display the contents of match string."
    (list 'face nil 'help-echo (match-string 0)))

(defvar unicode-tokens-show-symbols nil
  "Non-nil to reveal symbol (composed) tokens instead of compositions.")

(defun unicode-tokens-font-lock-compose-symbol (match)
  "Compose a sequence of chars into a symbol.
Regexp match data number MATCH selects the token name, while 0 matches the
whole expression.
Token name from MATCH is searched for in `unicode-tokens-hash-table'.
The face property is set to the :family of `unicode-tokens-symbol-font-face'."
  (let* ((start     (match-beginning 0))
         (end       (match-end 0))
	 (compps    (gethash (match-string match)
		    	   unicode-tokens-hash-table))
	 (propsyms  (cdr-safe compps)))
    (if (and compps (not unicode-tokens-show-symbols))
	(compose-region start end (car compps)))
    (if propsyms
	(let ((props (unicode-tokens-symbs-to-props propsyms)))
	  (while props
	    (font-lock-append-text-property start end
					    (car props) (cadr props))
	    (setq props (cddr props)))))
    (unless (intersection unicode-tokens-fonts propsyms)
      (font-lock-append-text-property
       start end 'face
       ;; just use family to enhance merging with other faces
       (list :family
	     (face-attribute 'unicode-tokens-symbol-font-face :family))))
    ;; [returning face property here seems to have no effect?]
    nil))

(defun unicode-tokens-prepend-text-properties-in-match (props matchno)
  (let ((start     (match-beginning matchno))
	(end       (match-end matchno)))
    (while props
      (unicode-tokens-prepend-text-property start end
					    (car props) (cadr props))
      (setq props (cddr props)))
    nil))

;; this is adapted from font-lock-prepend-text-property, which 
;; currently fails to merge property values for 'face property properly.
;; e.g., it makes (:slant italic (:weight bold font-lock-string-face))
;; rather than  (:slant italic :weight bold font-lock-string-face)
;;
(defun unicode-tokens-prepend-text-property (start end prop value &optional object)
  "Prepend to one property of the text from START to END.
Arguments PROP and VALUE specify the property and value to append to the value
already in place.  The resulting property values are always lists.
Optional argument OBJECT is the string or buffer containing the text."
  (let ((val (if (listp value) value (list value))) next prev)
    (while (/= start end)
      (setq next (next-single-property-change start prop object end)
	    prev (get-text-property start prop object))
      ;; Canonicalize old forms of face property.
      (and (memq prop '(face font-lock-face))
      	   (listp prev)
      	   (or (keywordp (car prev))
      	       (memq (car prev) '(foreground-color background-color)))
      	   (setq prev (list prev)))
      (setq prev (if (listp prev) prev (list prev)))
      ;; hack to flatten erroneously nested face property lists
      (if (and (memq prop '(face font-lock-face))
	       (listp (car prev)) (null (cdr prev)))
	  (setq prev (car prev)))
      (put-text-property start next prop
			 (append prev val)
			 object)
      (setq start next))))

(defun unicode-tokens-show-symbols (&optional arg)
  "Toggle variable `unicode-tokens-show-symbols'.  With ARG, turn on iff positive."
  (interactive "P")
  (setq unicode-tokens-show-symbols
	(if (null arg) (not unicode-tokens-show-symbols)
	  (> (prefix-numeric-value arg) 0)))
  (font-lock-fontify-buffer))

(defun unicode-tokens-symbs-to-props (symbs &optional facenil)
  "Turn the property name list SYMBS into a list of text properties.
Symbols are looked up in `unicode-tokens-fontsymb-properties'.
Optional argument FACENIL means set the face property to nil, unless 'face is in the property list."
  (let (props ps)
    (dolist (s symbs)
      (setq ps (cdr-safe
		(cdr-safe (assoc s unicode-tokens-fontsymb-properties))))
      (dolist (p ps)
	(setq props (append p props))))
    (if (and facenil
	     (not (memq 'face props)))
	(setq props (append '(face nil) props)))
    props))

;; 
;; Control tokens: as "characters" CTRL <stuff>
;;                 and regions     BEGINCTRL <stuff> ENDCTRL
;;

(defvar unicode-tokens-show-controls nil
  "Non-nil supresses hiding of control tokens.")

(defun unicode-tokens-show-controls (&optional arg)
  "Toggle variable `unicode-tokens-show-controls'.  With ARG, turn on iff positive."
  (interactive "P")
  (setq unicode-tokens-show-controls
	(if (null arg) (not unicode-tokens-show-controls)
	  (> (prefix-numeric-value arg) 0)))
  (when unicode-tokens-show-controls
    (remove-from-invisibility-spec 'unicode-tokens-show-controls))
  (when (not unicode-tokens-show-controls)
    (add-to-invisibility-spec 'unicode-tokens-show-controls))
  ;; EMACS ISSUE: how to force redisplay here to notice invis spec change?
  (redisplay t))

(defun unicode-tokens-control-char (name s &rest props)
  `(,(format unicode-tokens-control-char-format-regexp (regexp-quote s))
    (1 '(face nil invisible unicode-tokens-show-controls) prepend)
    ;; simpler but buggy with font-lock-prepend-text-property:
    ;; (2 ',(unicode-tokens-symbs-to-props props t) prepend)
    (2 (unicode-tokens-prepend-text-properties-in-match
	',(unicode-tokens-symbs-to-props props t) 2) prepend)
    ))

(defun unicode-tokens-control-region (name start end &rest props)
  `(,(format unicode-tokens-control-region-format-regexp
	     (regexp-quote start) (regexp-quote end))
    (1 '(face nil invisible unicode-tokens-show-controls) prepend)
    ;; simpler but buggy with font-lock-prepend-text-property:
    ;; (2 ',(unicode-tokens-symbs-to-props props t) prepend)
    (2 (unicode-tokens-prepend-text-properties-in-match
	',(unicode-tokens-symbs-to-props props t) 2) prepend)
    (3 '(face nil invisible unicode-tokens-show-controls) prepend)))

(defun unicode-tokens-control-font-lock-keywords ()
  (append
   (mapcar (lambda (args) (apply 'unicode-tokens-control-char args))
 	   unicode-tokens-control-characters)
   (mapcar (lambda (args) (apply 'unicode-tokens-control-region args))
 	   unicode-tokens-control-regions)))

;;
;; Shortcuts for typing, using quail
;;
    
(defvar unicode-tokens-use-shortcuts t
  "Non-nil means use `unicode-tokens-shortcut-alist' if set.")

(defun unicode-tokens-use-shortcuts (&optional arg)
  "Toggle variable `unicode-tokens-use-shortcuts'.  With ARG, turn on iff positive."
  (interactive "P")
  (setq unicode-tokens-use-shortcuts
	(if (null arg) (not unicode-tokens-use-shortcuts)
	  (> (prefix-numeric-value arg) 0)))
  (if unicode-tokens-use-shortcuts
    (set-input-method "Unicode tokens")
    (set-input-method nil)))

(require 'quail)

(quail-define-package
 "Unicode tokens" "UTF-8" "u" t
 "Unicode characters input method using application specific token names"
 nil t nil nil nil nil nil ; max shortest, could try t
 nil nil nil t)

(defun unicode-tokens-map-ordering (s1 s2)
  "Ordering on (car S1, car S2): order longer strings first."
  (>= (length (car s1)) (length (car s2))))

(defun unicode-tokens-quail-define-rules ()
  "Define the token and shortcut input rules.
Calculated from `unicode-tokens-token-name-alist' and
`unicode-tokens-shortcut-alist'."
  (let ((unicode-tokens-quail-define-rules
	 (list 'quail-define-rules)))
    (let ((ulist (copy-list unicode-tokens-shortcut-alist))
	  ustring shortcut)
      (setq ulist (sort ulist 'unicode-tokens-map-ordering))
      (while ulist
	(setq shortcut (caar ulist))
	(setq ustring (cdar ulist))
	(nconc unicode-tokens-quail-define-rules
	       (list (list shortcut
			   (vector ustring))))
	(setq ulist (cdr ulist))))
    (eval unicode-tokens-quail-define-rules)))


;;
;; User-level functions
;;

(defun unicode-tokens-insert-token (tok)
  "Insert symbolic token named TOK, giving a message."
  (interactive (list (completing-read
		      "Insert token: "
		      unicode-tokens-hash-table)))
  (let ((ins (format unicode-tokens-token-format tok)))
    (insert ins)
    (message "Inserted %s" ins)))

(defun unicode-tokens-annotate-region (name)
  "Annotate region with region markup tokens for scheme NAME.
Available annotations chosen from `unicode-tokens-control-regions'."
  (interactive (let ((completion-ignore-case t))
		 (list (completing-read
			"Annotate region with: "
			unicode-tokens-control-regions nil
			'requirematch))))
  (assert (assoc name unicode-tokens-control-regions))
  (let* ((entry (assoc name unicode-tokens-control-regions))
	 (beg   (region-beginning))
	 (end   (region-end))
	 (begtok
	  (format unicode-tokens-control-region-format-start (nth 1 entry)))
	 (endtok
	  (format unicode-tokens-control-region-format-end (nth 2 entry))))
    (when (> beg end)
	(setq beg end)
	(setq end (region-beginning)))
    (goto-char beg)
    (insert begtok)
    (goto-char (+ end (- (point) beg)))
    (insert endtok)))

(defun unicode-tokens-insert-control (name)
  "Insert a control symbol sequence.  NAME is from `unicode-tokens-control-characters'."
  (interactive (list (completing-read
		      "Insert control symbol: "
		      unicode-tokens-control-characters
		      nil 'requirematch)))
  (assert (assoc name unicode-tokens-control-characters))
  (insert (format unicode-tokens-control-char-format
		  (cadr (assoc name unicode-tokens-control-characters)))))

(defun unicode-tokens-insert-uchar-as-token (char)
  "Insert CHAR as a symbolic token, if possible."
  (let ((tok (gethash char unicode-tokens-uchar-hash-table)))
    (when tok
      (unicode-tokens-insert-token tok))))

(defun unicode-tokens-delete-token-near-point ()
  "Delete the token near point; try first before point, then after."
  (interactive)
  (if (or
       (re-search-backward unicode-tokens-token-match-regexp
			   (save-excursion
			     (beginning-of-line) (point)) t)
       (re-search-forward unicode-tokens-token-match-regexp
			   (save-excursion
			     (end-of-line) (point)) t))
      (kill-region (match-beginning 0) (match-end 0))))

;; FIXME: behaviour with unknown tokens not good.  Should
;; use separate regexp for matching tokens known or not known.
(defun unicode-tokens-prev-token ()
  "Return the token before point, matching with `unicode-tokens-token-match-regexp'."
  (let ((match (re-search-backward unicode-tokens-token-match-regexp
				    (save-excursion
				      (beginning-of-line 0) (point)) t)))
    (if match
	(match-string
	 (regexp-opt-depth unicode-tokens-token-match-regexp)))))

(defun unicode-tokens-rotate-token-forward (&optional n)
  "Rotate the token before point by N steps in the table."
  (interactive "p")
  (if (> (point) (point-min))
      (save-match-data
	(let ((pos    (point))
	      (token  (unicode-tokens-prev-token)))
	  (when (not token)
	    (goto-char (point))
	    (error "Cannot find token before point"))
	  (when token
	    (let* ((tokennumber
		    (search (list token) unicode-tokens-token-list :test 'equal))
		   (numtoks
		    (hash-table-count unicode-tokens-hash-table))
		   (newtok
		    (if tokennumber
			(nth (mod (+ tokennumber (or n 1)) numtoks)
			     unicode-tokens-token-list))))
	      (when newtok
		(delete-region (match-beginning 0) (match-end 0))
		(insert (format unicode-tokens-token-format newtok)))
	      (when (not newtok)
		;; FIXME: currently impossible case
		(message "Token not in tables: %s" token))))))))

	
(defun unicode-tokens-rotate-token-backward (&optional n)
  "Rotate the token before point, by -N steps in the token list."
  (interactive "p")
  (unicode-tokens-rotate-token-forward (if n (- n) -1)))

(defun unicode-tokens-replace-shortcut-match (&rest ignore)
  "Subroutine for `unicode-tokens-replace-shortcuts'."
  (let* ((match (match-string-no-properties 0))
	 (repl  (if match
		    (cdr-safe
		     (assoc match unicode-tokens-shortcut-replacement-alist)))))
    (if repl (regexp-quote repl))))

(defun unicode-tokens-replace-shortcuts ()
  "Query-replace shortcuts in the buffer with compositions they expand to."
  (interactive)
  (let ((shortcut-regexp
	 (regexp-opt (mapcar 'car unicode-tokens-shortcut-replacement-alist))))
    ;; override the display of the regexp because it's huge!
    ;; (doesn't help with C-h: need way to programmatically show string)
    (flet ((query-replace-descr (str) (if (eq str shortcut-regexp)
					  "shortcut" str)))
      (perform-replace shortcut-regexp (cons 'unicode-tokens-replace-shortcut-match
					     nil)
		       t t nil))))

;; 
;; Token and shortcut tables
;;

(defun unicode-tokens-copy-token (tokname)
  "Copy the token TOKNAME into the kill ring."
  (interactive "s")
  (kill-new
   (format unicode-tokens-token-format tokname)
   (eq last-command 'unicode-tokens-copy-token)))

(define-button-type 'unicode-tokens-list
  'help-echo "mouse-2, RET: copy this character"
  'face nil
  'action #'(lambda (button)
	      (unicode-tokens-copy-token (button-get button 'unicode-token))))

(defun unicode-tokens-list-tokens ()
  "Show a buffer of all tokens."
  (interactive)
  (with-output-to-temp-buffer "*Unicode Tokens List*"
    (with-current-buffer standard-output
      (make-local-variable 'unicode-tokens-show-symbols)
      (setq unicode-tokens-show-symbols nil)
      (unicode-tokens-mode)
      (setq tab-width 7)
      (insert "Hover to see token.  Mouse-2 or RET to copy into kill ring.\n")
      (let ((count 10) 
	    (toks unicode-tokens-token-list)
	    tok)
	;; display in originally given order
	(while (or (/= 1 (mod count 10)) toks)
	  (unless (null toks)
	    (setq tok (car toks)))
	  (if (/= 0 (mod count 10))
	      (insert "\t")
	    (insert "\n")
	    (unless (null toks)
	      (insert (format "%4d. " (/ count 10))))
	    (if (= 0 (mod count 20))
		(overlay-put (make-overlay 
			      (save-excursion
				(forward-line -1) (point))
			      (point))
			     'face
			     '(background-color . "gray90")))
	    (insert " "))
	  (incf count)
	  (if (null toks)
	      (insert " ")
	    (insert-text-button
	     (format unicode-tokens-token-format tok)
	     :type 'unicode-tokens-list
	     'unicode-token tok)
	    (setq toks (cdr toks))))))))

(defun unicode-tokens-list-shortcuts ()
  "Show a buffer of all the shortcuts available."
  (interactive)
  (with-output-to-temp-buffer "*Unicode Tokens Shortcuts*"
    (with-current-buffer standard-output
      (make-local-variable 'unicode-tokens-show-symbols)
      (setq unicode-tokens-show-symbols nil)
      (unicode-tokens-mode)
      (let (grey start)
	(dolist (short unicode-tokens-shortcut-alist)
	  (setq start (point))
	  (insert "Typing  " (car short) "\tinserts \t"
		  (cdr short) "\n")
	  (if (setq grey (not grey))
	      (overlay-put (make-overlay start (point))
			   'face
			   '(background-color . "gray90"))))))))
	  


(defun unicode-tokens-encode-in-temp-buffer (str fn)
  "Call FN on encoded version of STR."
  (let ((match   (- (regexp-opt-depth
		     unicode-tokens-token-match-regexp) 1)))
    (with-temp-buffer
      (insert str)
      (goto-char (point-min))
      (while (re-search-forward unicode-tokens-token-match-regexp nil t)
	;; TODO: interpret more exotic compositions here
	(let* ((tstart    (match-beginning 0))
	       (tend      (match-end 0))
	       (comp      (car-safe
			   (gethash (match-string match)
				    unicode-tokens-hash-table))))
	  (when comp
	    (delete-region tstart tend)
	    ;; TODO: improve this: interpret vector, strip tabs
	    (insert comp)))) ;; gross approximation to compose-region
      (funcall fn (point-min) (point-max)))))

(defun unicode-tokens-encode (beg end)
  "Return a unicode encoded version of the presentation in region BEG..END."
  (unicode-tokens-encode-in-temp-buffer
   (buffer-substring-no-properties beg end) 'buffer-substring))

(defun unicode-tokens-encode-str (str)
  "Return a unicode encoded version presentation of STR."
  (unicode-tokens-encode-in-temp-buffer str 'buffer-substring))

(defun unicode-tokens-copy (beg end)
  "Copy presentation of region between BEG and END.
This is an approximation; it makes assumptions about the behaviour
of symbol compositions, and will lose layout information."
  (interactive "r")
  ;; cf kill-ring-save, uncode-tokens-font-lock-compose-symbol
  (unicode-tokens-encode-in-temp-buffer
   (buffer-substring-no-properties beg end) 'copy-region-as-kill))

(defun unicode-tokens-paste ()
  "Paste text from clipboard, converting Unicode to tokens where possible."
  (interactive)
  (let ((start (point)) end)
    (clipboard-yank)
    (setq end (point-marker))
    (while (re-search-backward unicode-tokens-uchar-regexp start t)
      (let* ((useq	(match-string 0))
	     (token     (gethash useq unicode-tokens-uchar-hash-table))
	     (pos	(point)))
	(when token
	  (replace-match (format unicode-tokens-token-format token) t t)
	  (goto-char pos))))
    (goto-char end)
    (set-marker end nil)))

(defvar unicode-tokens-highlight-unicode nil
  "Non-nil to highlight Unicode characters.")

(defconst unicode-tokens-unicode-highlight-patterns
  '(("[^\000-\177]" (0 'unicode-tokens-highlight-face t)))
  "Font lock patterns for highlighting Unicode tokens.")

(defun unicode-tokens-highlight-unicode ()
  "Hilight Unicode characters in the buffer.
Toggles highlighting of Unicode characters used in the
buffer beyond the legacy 8-bit character set codes.  This is
useful to manually determine if a buffer contains Unicode or
tokenised symbols."
  (interactive)
  (setq unicode-tokens-highlight-unicode
	(not unicode-tokens-highlight-unicode))
  (unicode-tokens-highlight-unicode-setkeywords)
  (font-lock-fontify-buffer))

(defun unicode-tokens-highlight-unicode-setkeywords ()
  "Adjust font lock keywords according to variable `unicode-tokens-highlight-unicode'."
  (if unicode-tokens-highlight-unicode
    (font-lock-add-keywords
     nil unicode-tokens-unicode-highlight-patterns)
    (font-lock-remove-keywords
     nil unicode-tokens-unicode-highlight-patterns)))

;; 
;; Minor mode
;;

(defun unicode-tokens-initialise ()
  "Perform (re)initialisation for Unicode Tokens minor mode.
Invoke this function to recalculate `font-lock-keywords' and other configuration
variables."
  (interactive)
  (unicode-tokens-copy-configuration-variables)
  (let ((flks (unicode-tokens-font-lock-keywords)))
    (put 'unicode-tokens-font-lock-keywords major-mode flks)
    (unicode-tokens-quail-define-rules)
    (unicode-tokens-define-menu)
    flks))

(defvar unicode-tokens-mode-map (make-sparse-keymap)
  "Key map used for Unicode Tokens mode.")

(define-minor-mode unicode-tokens-mode
  "Toggle Tokens mode for current buffer.
With optional argument ARG, turn Tokens mode on if ARG is
positive, otherwise turn it off.

In Unicode Tokens mode (Utoks appears in the modeline), a
sequence of characters in the buffer (a token) may be presented
instead as a Unicode character. The underlying buffer contents is
not changed, only what is presented on the display.  Other tokens
may be used to control layout, for example, enabling sub/super
scripts, bold and italic fonts, etc.  Keyboard shortcut sequences
for entering tokens quickly can be defined.

Tokens mode needs configuration with a set of tokens, their
presentation forms, and keyboard shortcuts.  See documentation in
`unicode-tokens.el' for more information.

Commands available are:

\\{unicode-tokens-mode-map}"
  :keymap unicode-tokens-mode-map
  :init-value nil
  :lighter " Utoks"
  :group 'unicode-tokens
  (let ((flks (get 'unicode-tokens-font-lock-keywords major-mode)))
    (when unicode-tokens-mode
      (unless flks
	(setq flks (unicode-tokens-initialise)))
      ;; make sure buffer can display 16 bit chars
      (if (and
	   (fboundp 'set-buffer-multibyte)
	   (not (buffer-base-buffer)))
	  (set-buffer-multibyte t))

      (make-local-variable 'font-lock-extra-managed-props)

      (when (not unicode-tokens-show-controls)
	(add-to-invisibility-spec 'unicode-tokens-show-controls))

      (make-local-variable 'unicode-tokens-highlight-unicode)
      
      ;; a convention:
      ;; - set default for font-lock-extra-managed-props
      ;;   as property on major mode symbol (ordinarily nil).
      (font-lock-add-keywords nil flks)

      (setq font-lock-extra-managed-props
	    (get 'font-lock-extra-managed-props major-mode))
      (mapc
       (lambda (p) (add-to-list 'font-lock-extra-managed-props p))
       unicode-tokens-font-lock-extra-managed-props)

      (unicode-tokens-highlight-unicode-setkeywords)

      (font-lock-fontify-buffer)
	
      (if unicode-tokens-use-shortcuts
	  (set-input-method "Unicode tokens"))

      ;; adjust maths menu to insert tokens
      (set (make-local-variable 'maths-menu-filter-predicate)
	   (lambda (uchar) (gethash (char-to-string uchar)
				    unicode-tokens-uchar-hash-table)))
      (set (make-local-variable 'maths-menu-tokenise-insert)
	   (lambda (uchar)
	     (unicode-tokens-insert-token
	      (gethash (char-to-string uchar)
		       unicode-tokens-uchar-hash-table)))))

    (when (not unicode-tokens-mode)
      (when flks
	(font-lock-unfontify-buffer)
	(setq font-lock-extra-managed-props
	      (get 'font-lock-extra-managed-props major-mode))
	(setq font-lock-set-defaults nil) ; force font-lock-set-defaults to reinit
	(font-lock-fontify-buffer)
	(set-input-method nil))
      
      ;; Remove hooks from maths menu
      (kill-local-variable 'maths-menu-filter-predicate)
      (kill-local-variable 'maths-menu-tokenise-insert))))


;;
;; Font selection
;;

;; parameterised version of function from menu-bar.el
(defun unicode-tokens-set-font-var (fontvar)
    "Interactively select a font for FONTVAR."
  (interactive)
  (let ((font (if (fboundp 'x-select-font)
  		  (x-select-font)
  		(mouse-select-font)))
	spec)
    (when font
      ;; Be careful here: when set-face-attribute is called for the
      ;; :font attribute, Emacs tries to guess the best matching font
      ;; by examining the other face attributes (Bug#2476).
      (set-face-attribute fontvar (selected-frame)
			  :width 'normal
			  :weight 'normal
			  :slant 'normal
			  :font font)
      (let ((font-object (face-attribute fontvar :font)))
	(dolist (f (frame-list))
	  (and (not (eq f (selected-frame)))
	       (display-graphic-p f)
	       (set-face-attribute fontvar f :font font-object)))
	(set-face-attribute fontvar t :font font-object))
      (setq spec (list (list t (face-attr-construct fontvar))))
      (put fontvar 'customized-face spec)
      (custom-push-theme 'theme-face fontvar 'user 'set spec)
      (put fontvar 'face-modified nil))))

(defun unicode-tokens-set-font-restart (fontsym)
  "Open a dialog to set the font for FONTSYM, and reinitialise."
  (let ((facevar (intern (concat "unicode-tokens-" (symbol-name fontsym) "-font-face"))))
    (unicode-tokens-set-font-var facevar)
    (unicode-tokens-initialise)
    (font-lock-fontify-buffer)))

(defun unicode-tokens-save-fonts ()
  "Save the customized font variables."
  ;; save all customized faces (tricky to do less)
  (interactive)
  (custom-save-faces))


;; 
;; Key bindings
;;
(define-key unicode-tokens-mode-map [(control ?,)]
  'unicode-tokens-rotate-token-backward)
(define-key unicode-tokens-mode-map [(control ?.)]
  'unicode-tokens-rotate-token-forward)
(define-key unicode-tokens-mode-map
  [(control c) (control t) (control t)] 'unicode-tokens-insert-token)
(define-key unicode-tokens-mode-map
  [(control c) (control backspace)]
  'unicode-tokens-delete-token-near-point)
(define-key unicode-tokens-mode-map
  [(control c) (control t) (control r)] 'unicode-tokens-annotate-region)
(define-key unicode-tokens-mode-map
  [(control c) (control t) (control e)] 'unicode-tokens-insert-control)
(define-key unicode-tokens-mode-map
  [(control c) (control t) (control z)] 'unicode-tokens-show-symbols)
(define-key unicode-tokens-mode-map
  [(control c) (control t) (control t)] 'unicode-tokens-show-controls)

    
;;
;; Menu
;;

(defun unicode-tokens-define-menu ()
  "Define Tokens menu."
  (easy-menu-define unicode-tokens-menu unicode-tokens-mode-map
   "Tokens menu"
    (cons "Tokens"
     (list
      ["Insert token..." unicode-tokens-insert-token]
      ["Next token"      unicode-tokens-rotate-token-forward]
      ["Prev token"      unicode-tokens-rotate-token-backward]
      ["Delete token"    unicode-tokens-delete-token-near-point]
       (cons "Format char"
	     (mapcar
 	     (lambda (fmt)
 	       (vector (car fmt)
  		       `(lambda () (interactive)
			  (funcall 'unicode-tokens-insert-control ',(car fmt)))
 		       :help (concat "Format next item as "
 				     (downcase (car fmt)))))
 	     unicode-tokens-control-characters))
       (cons "Format region"
 	    (mapcar
 	     (lambda (fmt)
 	       (vector (car fmt)
  		       `(lambda () (interactive)
  			 (funcall 'unicode-tokens-annotate-region ',(car fmt)))
  		       :help (concat "Format region as "
  				     (downcase (car fmt)))
  		       :active 'mark-active))
 	     unicode-tokens-control-regions))
       "---"
      ["List tokens"     unicode-tokens-list-tokens]
      ["List shortcuts"  unicode-tokens-list-shortcuts]
      ["Customize tokens"     (unicode-tokens-customize "token-symbol-map")]
      ["Customize shortcuts"  (unicode-tokens-customize "shortcut-alist")]
      ["Replace shortcuts" unicode-tokens-replace-shortcuts]
      "---"
      ["Copy as unicode" unicode-tokens-copy
       :active 'mark-active
       :help "Copy text from buffer, converting tokens to Unicode"]
      ["Paste from unicode" unicode-tokens-paste
       :active (and kill-ring (not buffer-read-only))
       :help "Paste from clipboard, converting Unicode to tokens where possible"]
       "---"
      ["Show control tokens" unicode-tokens-show-controls
       :style toggle
       :selected unicode-tokens-show-controls
       :active (or
		unicode-tokens-control-region-format-regexp
		unicode-tokens-control-char-format-regexp)
       :help "Prevent hiding of control tokens"]
      ["Show symbol tokens" unicode-tokens-show-symbols
       :style toggle
       :selected unicode-tokens-show-symbols
       :help "Show tokens for symbols"]
      ["Highlight real Unicode chars" unicode-tokens-highlight-unicode
       :style toggle
       :selected unicode-tokens-highlight-unicode
       :help "Hightlight non-ASCII characters in buffer which are saved as Unicode"]
      ["Enable shortcuts" unicode-tokens-use-shortcuts
       :style toggle
       :selected unicode-tokens-use-shortcuts
       :active unicode-tokens-shortcut-alist
       :help "Use short cuts for typing tokens"]
      (cons "Set fonts"
       (append
        (mapcar
         (lambda (var)
           (vector 
	    (upcase-initials (symbol-name var))
	    `(lambda () (interactive)
	        (funcall 'unicode-tokens-set-font-restart ',var))
	     :help (concat "Set the " (symbol-name var) " font")))
	 unicode-tokens-fonts)
         (list "----"
	["Save fonts" unicode-tokens-save-fonts
	 :help "Save the customized font choices"]
	["Make fontsets"
	 (lambda () (interactive) (require 'pg-fontsets))
	 :active (not (featurep 'pg-fontsets))
	 :help "Define fontsets (for Options->Set fontsets)"
	 :visible (< emacs-major-version 23) ; not useful on 23,
	 ;; at least when font menu provided.  Drawback: this
	 ;; is done too late: displayable tokens have already been
	 ;; chosen now, before fontsets generated.
	 ;; Never mind: non-issue with platform fonts menu.
	 ])))))))


	     
(provide 'unicode-tokens)

;;; unicode-tokens.el ends here
