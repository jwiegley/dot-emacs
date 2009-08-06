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

;; TODO:
;; -- insert tokens via numeric code (extra format string)
;; -- insert unicode character as token (reverse lookup)

(require 'cl)

(eval-when-compile
  (require 'maths-menu))		; nuke compile warnings

;;
;; Variables that should be set by client modes
;;

(defvar unicode-tokens-token-symbol-map nil
  "Mapping of token names to compositions.
Each element is a list

  (TOKNAME COMPOSITION FONTSYMB ...)

A composition is typically a single Unicode character string, but
can be more complex: see documentation of `compose-region'.

The list of FONTSYMB are optional.  Each FONTSYMB is a symbol
indicating a set of text properties, looked up in
`unicode-tokens-fontsymb-properties'.")

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
;; (setq ut-tvfr  "\\(%s\\)\\(:?\\w+\\)")
;; (string-match (format ut-tvfr ".*?") "alpha:x") 

(defvar unicode-tokens-fontsymb-properties nil
 "Association list mapping a symbol to a list of text properties.
Used in `unicode-tokens-token-symbol-map', `unicode-tokens-control-regions',
and `unicode-tokens-control-characters'.")

(defvar unicode-tokens-shortcut-alist nil
  "An alist of keyboard shortcuts to unicode strings.
The alist is added to the input mode for tokens.
Behaviour is much like abbrev.")


;;
;; Variables that can be overridden in instances: control tokens
;;

;; TODO: docs
(defvar unicode-tokens-control-region-format-regexp nil)
(defvar unicode-tokens-control-char-format-regexp nil)
(defvar unicode-tokens-control-regions nil)
(defvar unicode-tokens-control-characters nil)
(defvar unicode-tokens-control-char-format nil)

;;
;; A list of the above variables
;;

(defconst unicode-tokens-configuration-variables
  '(token-symbol-map
    token-format
    token-variant-format-regexp
    fontsymb-properties
    shortcut-alist
    control-region-format-regexp
    control-char-format-regexp
    control-char-format
    control-regions
    control-characters))

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
;; Constants
;;

(defgroup unicode-tokens-faces nil
  "The faces used in Unicode Tokens mode."
  :group 'faces)

(defface unicode-tokens-script-font-face
  (cond
   ((eq window-system 'x) ; Linux/Unix
    '((t :family "PakTypeNaqsh")))  ; 
   ((or ; Mac
     (eq window-system 'ns)
     (eq window-system 'carbon))
    '((t :family "Lucida Calligraphy"))))
  "Script font face"
  :group 'unicode-tokens-faces)

(defface unicode-tokens-fraktur-font-face
  (cond
   ((eq window-system 'x) ; Linux/Unix
    '((t :family "URW Bookman L"))) ;; not at all black letter!
   ((or ; Mac
     (eq window-system 'ns)
     (eq window-system 'carbon))
    '((t :family "Lucida Blackletter"))))
  "Fraktur font face"
  :group 'unicode-tokens-faces)

(defface unicode-tokens-serif-font-face
  (cond
   ((eq window-system 'x) ; Linux/Unix
    '((t :family "Liberation Serif"))) 
   ((or ; Mac
     (eq window-system 'ns)
     (eq window-system 'carbon))
    '((t :family "Lucida"))))
  "Serif (roman) font face"
  :group 'unicode-tokens-faces)

(defface unicode-tokens-highlight-face
  '((((min-colors 88) (background dark))
     (:background "yellow1" :foreground "black"))
    (((background dark)) (:background "yellow" :foreground "black"))
    (((min-colors 88)) (:background "yellow1"))
    (t (:background "yellow")))
  "Face used for highlighting in Unicode tokens."
  :group 'unicode-tokens-faces)

(defconst unicode-tokens-font-lock-extra-managed-props 
  '(composition help-echo display invisible)
  "Value for `font-lock-extra-managed-props' here.")

;;
;;; Code:
;;

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
	  (0 (unicode-tokens-help-echo) 'prepend)
	  (0 (unicode-tokens-font-lock-compose-symbol 
	      ,(- (regexp-opt-depth unicode-tokens-token-match-regexp) 1))
	      'prepend))
	(unicode-tokens-control-font-lock-keywords)))))

(defun unicode-tokens-usable-composition (comp)
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
  "Return a help-echo text property to display the contents of match string"
    (list 'face nil 'help-echo (match-string 0)))

(defvar unicode-tokens-show-symbols nil
  "Non-nil to reveal symbol (composed) tokens instead of compositions.")

(defun unicode-tokens-font-lock-compose-symbol (match)
  "Compose a sequence of chars into a symbol, maybe returning a face property.
Regexp match data number MATCH selects the token name, while 0 matches the
whole expression. 
Token symbol is searched for in `unicode-tokens-hash-table'."
  (let* ((start     (match-beginning 0))
         (end       (match-end 0))
	 (compps    (gethash (match-string match) 
		    	   unicode-tokens-hash-table))
	 (props     (cdr-safe compps)))
    (if (and compps (not unicode-tokens-show-symbols))
	(compose-region start end (car compps)))
    (if props
	(add-text-properties ;; font-lock should do this but fails?
	 start end (unicode-tokens-symbs-to-props props)))
    nil))

(defun unicode-tokens-show-symbols (&optional arg)
  "Toggle `unicode-tokens-show-symbols'.  With ARG, turn on iff positive."
  (interactive "P")
  (setq unicode-tokens-show-symbols
	(if (null arg) (not unicode-tokens-show-symbols)
	  (> (prefix-numeric-value arg) 0)))
  (font-lock-fontify-buffer))

(defun unicode-tokens-symbs-to-props (symbs &optional facenil)
  (let (props ps)
    (dolist (s symbs)
      (setq ps (cdr-safe (assoc s unicode-tokens-fontsymb-properties)))
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
  "Toggle `unicode-tokens-show-controls'.  With ARG, turn on iff positive."
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
  `(,(format unicode-tokens-control-char-format-regexp s)
    (1 '(face nil invisible unicode-tokens-show-controls) prepend)
    (2 ',(unicode-tokens-symbs-to-props props t) prepend)))

(defun unicode-tokens-control-region (name start end &rest props)
  `(,(format unicode-tokens-control-region-format-regexp start end)
    (1 '(face nil invisible unicode-tokens-show-controls) prepend)
    (2 ',(unicode-tokens-symbs-to-props props t) prepend)
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
  "Toggle `unicode-tokens-use-shortcuts'.  With ARG, turn on iff positive."
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
	 (beg (region-beginning))
	 (end (region-end))
	 (begtok 
	  (format unicode-tokens-control-region-format-end (nth 1 entry)))
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

;;unused
(defun unicode-tokens-delete-token-at-point ()
  (interactive)
  (when (looking-at unicode-tokens-token-match-regexp)
    (kill-region (match-beginning 0) (match-end 0))))

;; FIXME: behaviour with unknown tokens not good.  Should 
;; use separate regexp for matching tokens known or not known.
(defun unicode-tokens-prev-token ()
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

(defun unicode-tokens-copy-token (tokname)
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
      (insert "Mouse-2 or RET on a character to copy into kill ring.\n\n")
      (let ((count 0) toks)
	;; display in originally given order
	(dolist (tok unicode-tokens-token-list)
	    (insert-text-button 
	     (format unicode-tokens-token-format tok)
	     :type 'unicode-tokens-list
	     'unicode-token tok)
	    (incf count)
	    (if (< count 10)
		(insert "\t")
	      (insert "\n")
	      (setq count 0)))))))

(defun unicode-tokens-list-shortcuts ()
  "Show a buffer of all the shortcuts available."
  (interactive)
  (with-output-to-temp-buffer "*Unicode Tokens Shortcuts*"
    (with-current-buffer standard-output
      (make-local-variable 'unicode-tokens-show-symbols)
      (setq unicode-tokens-show-symbols nil)
      (unicode-tokens-mode)
      (let (gray start)
	(dolist (short unicode-tokens-shortcut-alist)
	  (setq start (point))
	  (insert "Typing  " (car short) "\tinserts \t" 
		  (cdr short) "\n")
	  (setq gray (not gray))
	  (if gray 
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
  "Return a unicode encoded version of the region presentation ."
  (unicode-tokens-encode-in-temp-buffer 
   (buffer-substring-no-properties beg end) 'buffer-substring))

(defun unicode-tokens-encode-str (str)
  "Return a unicode encoded version of the region presentation ."
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
  (if unicode-tokens-highlight-unicode
    (font-lock-add-keywords 
     nil unicode-tokens-unicode-highlight-patterns)
    (font-lock-remove-keywords 
     nil unicode-tokens-unicode-highlight-patterns)))

;; 
;; Minor mode
;;

(defun unicode-tokens-initialise ()
  (interactive)
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
      (mapcar 
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
;; Key bindings
;;
(define-key unicode-tokens-mode-map [(control ?,)]
  'unicode-tokens-rotate-token-backward)
(define-key unicode-tokens-mode-map [(control ?.)]
  'unicode-tokens-rotate-token-forward)
(define-key unicode-tokens-mode-map 
  [(control c) (control t) (control t)] 'unicode-tokens-insert-token)
(define-key unicode-tokens-mode-map 
  [(control c) (control t) (control r)] 'unicode-tokens-annotate-region)
(define-key unicode-tokens-mode-map 
  [(control c) (control t) (control e)] 'unicode-tokens-insert-control)
(define-key unicode-tokens-mode-map 
  [(control c) (control t) (control z)] 'unicode-tokens-show-symbols)
(define-key unicode-tokens-mode-map 
  [(control c) (control t) (control x)] 'unicode-tokens-show-controls)

    
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
      ["List tokens"     unicode-tokens-list-tokens]
      ["List shortcuts"  unicode-tokens-list-shortcuts]
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
       ["Make fontsets" 
	(lambda () (interactive) (require 'pg-fontsets))
	:active (not (featurep 'pg-fontsets))
	:help "Define fontsets (for Options->Set fontsets)"
	; :visible (< emacs-major-version 23) ; not useful on 23,
	; at least when font menu provided.  Drawback: this 
	; is done too late: displayable tokens have already been
	; chosen now, before fontsets generated.
	; Never mind: non-issue with platform fonts menu.
	]))))


	     
(provide 'unicode-tokens)

;;; unicode-tokens.el ends here
