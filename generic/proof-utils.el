;; proof-utils.el   Proof General utility functions
;;
;; Copyright (C) 1998-2002 LFCS Edinburgh. 
;; Author:      David Aspinall <da@dcs.ed.ac.uk> and others
;; License:     GPL (GNU GENERAL PUBLIC LICENSE)
;;
;; $Id$
;;
;;
;; Loading note: this file is required immediately from proof.el, so
;; no autoloads are used here.


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Handy macros

(defmacro deflocal (var value &optional docstring)
  "Define a buffer local variable VAR with default value VALUE."
 `(progn
    (defvar ,var nil ,docstring)
    (make-variable-buffer-local (quote ,var))
    (setq-default ,var ,value)))

(defmacro proof-with-current-buffer-if-exists (buf &rest body)
  "As with-current-buffer if BUF exists and is live, otherwise nothing."
  `(if (buffer-live-p ,buf)
       (with-current-buffer ,buf
	 ,@body)))

;; Slightly specialized version of above.  This is used in commands
;; which work from different PG buffers (goals, response), typically
;; bound to toolbar commands.
(defmacro proof-with-script-buffer (&rest body)
  "Execute BODY in some script buffer: current buf or otherwise proof-script-buffer.
Return nil if not a script buffer or if no active scripting buffer."
  `(cond
    ((eq proof-buffer-type 'script)
     (progn
       ,@body))
    ((buffer-live-p proof-script-buffer)
     (with-current-buffer proof-script-buffer
       ,@body))))
      
(defmacro proof-map-buffers (buflist &rest body)
  "Do BODY on each buffer in BUFLIST, if it exists."
  `(dolist (buf ,buflist)
     (proof-with-current-buffer-if-exists buf ,@body)))

(defmacro proof-sym (string)
  "Return symbol for current proof assistant using STRING."
 `(intern (concat (symbol-name proof-assistant-symbol) "-" ,string)))


(defun proof-try-require (symbol)
  "Try requiring SYMBOL.  No error if the file for SYMBOL isn't found."
  (condition-case ()
      (require symbol)
    (file-error nil))
  (featurep symbol))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Function for taking action when dynamically adjusting customize values
;;
(defun proof-set-value (sym value)
  "Set a customize variable using set-default and a function.
We first call `set-default' to set SYM to VALUE.
Then if there is a function SYM (i.e. with the same name as the
variable SYM), it is called to take some dynamic action for the new
setting.  

If there is no function SYM, we try stripping 
proof-assistant-symbol and adding \"proof-\" instead to get
a function name.  This extends proof-set-value to work with
generic individual settings.

The dynamic action call only happens when values *change*: as an
approximation we test whether proof-config is fully-loaded yet."
  (set-default sym value)
  (if (featurep 'proof-config)
      (if (fboundp sym)
	  (funcall sym)
	(if (> (length (symbol-name sym)) 
	       (+ 3 (length (symbol-name proof-assistant-symbol))))
	    (let ((generic  
		   (intern
		    (concat "proof"
			    (substring (symbol-name sym)
				       (length (symbol-name
						proof-assistant-symbol)))))))
	      (if (fboundp generic)
		  (funcall generic)))))))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Macros for defining per-assistant customization settings.
;;
;; This new mechanism is an improved way to handle per-assistant
;; settings.  Instead of declaring a variable
;; "proof-assistant-web-page" and duplicating it in the prover
;; specific code to make the generic setting, we automatically declare
;; "isabelle-web-page", "coq-web-page", etc, using these macros.
;;
;; The advantage of this is that people's save settings will work
;; properly, and that it will become more possible to use more than
;; one instance of PG at a time.  The disadvantage is that it is
;; slightly more complicated, and less "object-oriented" than the
;; previous approach.  It is also a big change to move all settings.
;;
;; NB: this mechanism is work in progress in 3.2.  It will
;; be expanded, although we may leave most low-level 
;; settings to use the current mechanism.
;;
;; Notes:
;;
;; Two mechanisms for accessing generic vars:
;;
;; (proof-ass name)   or (proof-assistant-name)
;;
;; Later is more efficient, though defining function
;; for each setting seems wasteful?

(defun proof-ass-symv (sym)
  "Return the symbol for SYM for the current prover.  SYM is evaluated."
  (intern (concat (symbol-name proof-assistant-symbol) "-" 
		  (symbol-name sym))))

(defmacro proof-ass-sym (sym)
  "Return the symbol for SYM for the current prover.  SYM not evaluated."
  `(proof-ass-symv (quote ,sym)))

(defun proof-defpgcustom-fn (sym args)
  "Define a new customization variable <PA>-sym for the current proof assistant.
Helper for macro `defpgcustom'."
  (let ((specific-var (proof-ass-symv sym))
	(generic-var  (intern (concat "proof-assistant-" (symbol-name sym)))))
    (eval
     `(defcustom ,specific-var 
	,@args
	;; FIXME: would be nicer to grab group from @args here and
	;; prefix it automatically.  For now, default to internals
	;; setting for PA.
	;; FIXME 2: would also be nice to grab docstring from args
	;; and allow substitution for prover name, etc.  A bit too 
	;; fancy perhaps!
	:group ,(quote proof-assistant-internals-cusgrp)))
    ;; For functions, we could simply use defalias.  Unfortunately there
    ;; is nothing similar for values, so we define a new set/get function.
    (eval
     `(defun ,generic-var (&optional newval) 
	,(concat "Set or get value of " (symbol-name sym) " for current proof assistant.
If NEWVAL is present, set the variable, otherwise return its current value.")
	(if newval 
	    (setq ,specific-var newval)
	  ,specific-var)))))

(defmacro defpgcustom (sym &rest args)
  "Define a new customization variable <PA>-SYM for the current proof assistant.
The function proof-assistant-<SYM> is also defined, which can be used in the 
generic portion of Proof General to set and retrieve the value for the current p.a.
Arguments as for `defcustom', which see.

Usage: (defpgcustom SYM &rest ARGS)."
  `(proof-defpgcustom-fn (quote ,sym) (quote ,args)))

(defmacro proof-ass (sym)
  "Return the value for SYM for the current prover."
  (eval `(proof-ass-sym ,sym)))

(defun proof-defpgdefault-fn (sym value)
  "Helper for `defpgdefault', which see.  SYM and VALUE are evaluated."
  ;; NB: we need this because nothing in customize library seems to do
  ;; the right thing.
  (let ((symbol  (proof-ass-symv sym)))
    (set-default symbol 
		 (cond
		  ;; Use saved value if it's set
		  ((get symbol 'saved-value)
		   (car (get symbol 'saved-value)))
		  ;; Otherwise override old default with new one
		  (t
		   value)))))

(defmacro defpgdefault (sym value)
  "Set default for the proof assistant specific variable <PA>-SYM to VALUE.
This should be used in prover-specific code to alter the default values
for prover specific settings.

Usage: (defpgdefault SYM VALUE)"
    `(proof-defpgdefault-fn (quote ,sym) ,value))

;;
;; Make a function named for the current proof assistant.
;;
(defmacro defpgfun (name arglist &rest args)
  "Define function <PA>-SYM as for defun."
  `(defun ,(proof-ass-symv name) ,arglist
     ,@args))


;;
;; End macros
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Buffers and filenames

(defun proof-file-truename (filename)
  "Returns the true name of the file FILENAME or nil if file non-existent."
  (and filename (file-exists-p filename) (file-truename filename)))

(defun proof-file-to-buffer (filename)
  "Find a buffer visiting file FILENAME, or nil if there isn't one."
  (let* ((buffers (buffer-list))
	 (pos
	  (position (file-truename filename)
		    (mapcar 'proof-file-truename
			    (mapcar 'buffer-file-name
				    buffers))
		    :test 'equal)))
    (and pos (nth pos buffers))))

(defun proof-files-to-buffers (filenames)
  "Converts a list of FILENAMES into a list of BUFFERS."
  (if (null filenames) nil
    (let* ((buffer (proof-file-to-buffer (car filenames)))
	  (rest (proof-files-to-buffers (cdr filenames))))
      (if buffer (cons buffer rest) rest))))

(defun proof-buffers-in-mode (mode &optional buflist)
  "Return a list of the buffers in the buffer list in major-mode MODE.
Restrict to BUFLIST if it's set."
  (let ((bufs-left (or buflist (buffer-list))) 
	bufs-got)
    (dolist (buf bufs-left bufs-got)
      (if (with-current-buffer buf (eq mode major-mode))
	  (setq bufs-got (cons buf bufs-got))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Key functions

(defun proof-define-keys (map kbl)
  "Adds keybindings KBL in MAP.
The argument KBL is a list of tuples (k . f) where `k' is a keybinding
(vector) and `f' the designated function."
  (mapcar
   (lambda (kbl)
     (let ((k (car kbl)) (f (cdr kbl)))
         (define-key map k f)))
   kbl))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Managing font-lock
;;

;; Notes:
;;
;; * Various mechanisms for setting defaults, different between 
;;   Emacsen.  Old method(?) was to set "blah-mode-font-lock-keywords"
;;   and copy it into "font-lock-keywords" to engage font-lock.
;;   Present method for XEmacs is to put a 'font-lock-defaults 
;;   property on the major-mode symbol, or use font-lock-defaults
;;   buffer local variable.  We use the later.
;;
;; * Buffers which are output-only are *not* kept in special minor
;;   modes font-lock-mode (or x-symbol-mode).  In case the user
;;   doesn't want fontification we have a user option,
;;   proof-output-fontify-enable.

(deflocal proof-font-lock-keywords nil
  "Value of font-lock-keywords in this buffer.
We set font-lock-defaults to '(proof-font-lock-keywords t) for
compatibility with X-Symbol, which may hack proof-font-lock-keywords
with extra patterns (in non-mule mode).")

(deflocal proof-font-lock-keywords-case-fold-search nil
  "Value of font-lock-keywords-case-fold-search in this buffer.")

(defun proof-font-lock-configure-defaults (autofontify &optional case-fold)
  "Set defaults for font-lock based on current font-lock-keywords.
This is a delicate operation, because we only want to use font-lock-mode
in some buffers, so we have to tread carefully around the font-lock
code to avoid it turning itself on in the buffers where that actually
*breaks* fontification.

AUTOFONTIFY must be nil for buffers where we may want to really use
font-lock-mode."
  ;;
  ;; At the moment, the specific assistant code hacks
  ;; font-lock-keywords.  Here we use that value to hack
  ;; font-lock-defaults, which is used by font-lock to set
  ;; font-lock-keywords from again!!  Yuk.
  ;;
  ;; Previously, 'font-lock-keywords was used directly as a setting
  ;; for the defaults.  This has a bad interaction with x-symbol which
  ;; edits font-lock-keywords and loses the setting.  So we make a
  ;; copy of it in a new local variable, proof-font-lock-keywords.
  ;;
  (make-local-variable 'proof-font-lock-keywords)
  (make-local-variable 'proof-font-lock-keywords-case-fold-search)
  (setq proof-font-lock-keywords font-lock-keywords)
  (setq proof-font-lock-keywords-case-fold-search case-fold)
    ;; Setting font-lock-defaults explicitly is required by FSF Emacs
  ;; 20.4's version of font-lock in any case.

  (if autofontify
      (progn
	(make-local-variable 'font-lock-defaults) ; needed??
	(setq font-lock-defaults `(proof-font-lock-keywords nil ,case-fold))
	;; 12.1.99: For XEmacs, we must also set the mode property.
	;; This is needed for buffers which are put into font-lock-mode
	;; (rather than fontified by hand).
	(put major-mode 'font-lock-defaults font-lock-defaults))
    ;; 11.12.01: Emacs 21 is very eager about turning on font
    ;; lock and has hooks all over the place to do it.  To make
    ;; sure it doesn't happen we have to eradicate all sense of
    ;; having any fontification ability.  
    (proof-font-lock-clear-font-lock-vars)
    ;; In fact, this still leaves font-lock switched on! But
    ;; hopefully in a useless way.  XEmacs has better control
    ;; over which modes not to enable it for (although annoying
    ;; that it's a custom setting)
    (if proof-running-on-XEmacs
	(setq font-lock-mode-disable-list 
	      (cons major-mode font-lock-mode-disable-list)))))

(defun proof-font-lock-clear-font-lock-vars ()
  (kill-local-variable 'font-lock-defaults)
  (kill-local-variable 'font-lock-keywords)
  (setq font-lock-keywords nil)
  (put major-mode 'font-lock-defaults nil)
  ;; Ensure it's switched off, too.
  ;; NB: this tends to undo the hard work we've done
  ;; by unfontifying, so don't do that now
  ;; (font-lock-mode -1))
  )

(defun proof-font-lock-set-font-lock-vars ()
  (setq font-lock-defaults 
	`(proof-font-lock-keywords 
	  nil 
	  ,proof-font-lock-keywords-case-fold-search))
  (setq font-lock-keywords proof-font-lock-keywords))

(defun proof-fontify-region (start end &optional keepspecials)
  "Fontify and decode X-Symbols in region START...END.
Fontifies according to the buffer's font lock defaults.
Uses proof-x-symbol-decode to decode tokens if x-symbol is present.

If `pg-use-specials-for-fontify' is set, remove characters
with top bit set after fontifying so they don't spoil cut and paste,
unless KEEPSPECIALS is set to override this.

Returns new END value."
  ;; We fontify first because X-sym decoding changes char positions.
  ;; It's okay because x-symbol-decode works even without font lock.
  ;; Possible disadvantage is that font lock patterns can't refer
  ;; to X-Symbol characters.  
  (if proof-output-fontify-enable
      (progn
	;; Temporarily set font-lock defaults
	(proof-font-lock-set-font-lock-vars)

	;; Yukky hacks to immorally interface with font-lock
	(unless proof-running-on-XEmacs
	  (font-lock-set-defaults))
	(let ((font-lock-keywords proof-font-lock-keywords))
	  (if (and proof-running-on-XEmacs
		   (>= emacs-minor-version 4)
		   (not font-lock-cache-position))
	      (progn
		(setq font-lock-cache-position (make-marker))
		(set-marker font-lock-cache-position 0)))

	  (run-hooks 'pg-before-fontify-output-hook)
	  (font-lock-default-fontify-region start end nil)
	  ;; after-fontify hook might do this ugly zap commas thing.
	  (proof-zap-commas-region start end))))
  (if (and pg-use-specials-for-fontify (not keepspecials))
      (progn
	(pg-remove-specials start end)
	(setq end (point))))
  (prog1
      ;; Return new end value
      (proof-x-symbol-decode-region start end)
    (proof-font-lock-clear-font-lock-vars)))


(defconst pg-special-char-regexp
  (let ((c 128) (r "\200"))
    (while (< c 256) 
      (setq r (concat r "\\|" (regexp-quote (char-to-string c))))
      (incf c))
    r)
  "Regexp matchin any special character (top bit set).")


(defun pg-remove-specials (&optional start end)
  "Remove special characters (with top bit set) in region.
Default to whole buffer.  Leave point at END."
  (save-restriction
    (if (and start end) 
	(narrow-to-region start end))
    (goto-char (or start (point-min)))
    (proof-replace-regexp pg-special-char-regexp "")
    (point-max)))

  

;; FIXME todo: add toggle for fontify region which turns it on/off

(defun proof-fontify-buffer ()
  "Call proof-fontify-region on whole buffer."
  (proof-fontify-region (point-min) (point-max)))




;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Messaging and display functions
;;


(defun proof-warn-if-unset (tag sym)
  "Give a warning (with TAG) if symbol SYM is unbound or nil."
  (unless (and (boundp sym) (symbol-value sym))
    (warn "Proof General %s: %s is unset."  tag (symbol-name sym))))

(defun proof-display-and-keep-buffer (buffer &optional pos)
  "Display BUFFER and mark window according to `proof-dont-switch-windows'.
If optional POS is present, will set point to POS.  
Otherwise move point to the end of the buffer.
Ensure that point is visible in window."
  (let (window)
    (save-excursion
      (set-buffer buffer)
      ;; Here's a hack: if we're asking to display BUFFER from a
      ;; secondary window and the (next) other one is displaying the
      ;; script buffer, then we do switch-buffer instead.  This means
      ;; that goals and response buffer are swapped as expected in
      ;; two-pane mode even if either one is used to "drive" the
      ;; scripting.
      ;; FIXME: would be better to deduce here which buffer
      ;; we're displaying, and use get-buffer-window-list to do
      ;; something sensible.
      (if (and 
	   (not proof-dont-switch-windows)
	   (not (eq (next-window) (selected-window)))
	   (eq (window-buffer (next-window nil 'ignoreminibuf))
	       proof-script-buffer))
	  (if (eq (selected-window) (minibuffer-window))
	      ;; 17.8.01: avoid switching the minibuffer's contents 
	      ;; -- terrrible confusion -- use next-window after
	      ;; script buffer instead.
	      ;; (another hack which is mostly right)
	      (set-window-buffer 
	       (next-window 
		(car-safe (get-buffer-window-list proof-script-buffer))
		'ignoreminibuf) buffer)
	    (set-window-buffer (selected-window) buffer))
	(display-buffer buffer))
      (setq window (get-buffer-window buffer 'visible))
      (set-window-dedicated-p window proof-dont-switch-windows)
      (and window
	   (save-selected-window
	     (select-window window)
	     ;; For various reasons, point may get moved
	     ;; around in response buffer.
	     (goto-char (or pos (point-max)))
	     (if pos (beginning-of-line))
	     ;; Ensure point visible
	     (or (pos-visible-in-window-p (point) window)
		 (recenter -1)))))))

(defun proof-clean-buffer (buffer)
  "Erase buffer and hide from display if proof-delete-empty-windows set.
Auto deletion only affects selected frame.  (We assume that the selected
frame is the one showing the script buffer.)"
  (with-current-buffer buffer
    ;; NB: useful optional arg to erase buffer is XEmacs specific, 8-(.
    (erase-buffer)
    (if (eq buffer proof-response-buffer)
	(setq proof-shell-next-error nil))	; all error msgs lost!
    (if proof-delete-empty-windows
	(delete-windows-on buffer t))))

(defun proof-message (&rest args)
  "Issue the message ARGS in the response buffer and display it."
    (pg-response-display-with-face (apply 'concat args))
    (proof-display-and-keep-buffer proof-response-buffer))

(defun proof-warning (&rest args)
  "Issue the warning ARGS in the response buffer and display it.
The warning is coloured with proof-warning-face."
    (pg-response-display-with-face (apply 'concat args) 'proof-warning-face)
    (proof-display-and-keep-buffer proof-response-buffer))

;; could be a macro for efficiency in compiled code
(defun proof-debug (&rest args)
  "Issue the debugging messages ARGS in the response buffer, display it.
If proof-show-debug-messages is nil, do nothing."
  (if proof-show-debug-messages
      (progn
	(pg-response-display-with-face (apply 'concat 
					      "PG debug: " 
					      args)
				       'proof-debug-message-face)
	(proof-display-and-keep-buffer proof-response-buffer))))


;;; A handy utility function used in the "Buffers" menu.
(defun proof-switch-to-buffer (buf &optional noselect)
  "Switch to or display buffer BUF in other window unless already displayed.
If optional arg NOSELECT is true, don't switch, only display it.
No action if BUF is nil or killed."
  ;; Maybe this needs to be more sophisticated, using 
  ;; proof-display-and-keep-buffer ?
  (and (buffer-live-p buf)
       (unless (eq buf (window-buffer (selected-window)))
	 (if noselect
	     (display-buffer buf t)
	   (switch-to-buffer-other-window buf)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Function for submitting bug reports.
;;

(defun proof-submit-bug-report ()
  "Submit an bug report or other report for Proof General."
  (interactive)
  (require 'reporter)
  (let
      ((reporter-prompt-for-summary-p 
	"(Very) brief summary of problem or suggestion: "))
    (reporter-submit-bug-report
     "bugs@proofgeneral.org"
     "Proof General" 
     (list 'proof-general-version 'proof-assistant)
     nil nil
     "[ When reporting a bug, please include a small test case for us to repeat it.
 Please also check that it is not already covered in the BUGS files that came with
 the distribution, or the latest versions at 
 http://www.proofgeneral.org/ProofGeneral/BUGS ]")))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Utils for making functions to adjust user settings
;;;


(defun proof-deftoggle-fn (var &optional othername)
  "Define a function <VAR>-toggle for toggling a boolean customize setting VAR.
Args as for the macro `proof-deftoggle', except will be evaluated."
  (eval
   `(defun ,(if othername othername 
	      (intern (concat (symbol-name var) "-toggle"))) (arg)
	      ,(concat "Toggle `" (symbol-name var) "'. With ARG, turn on iff ARG>0.
This function simply uses customize-set-variable to set the variable.
It was constructed with `proof-deftoggle-fn'.")
	      (interactive "P")
	      (customize-set-variable 
	       (quote ,var)
	       (if (null arg) (not ,var)
		 (> (prefix-numeric-value arg) 0))))))

(defmacro proof-deftoggle (var &optional othername)
  "Define a function VAR-toggle for toggling a boolean customize setting VAR.
The toggle function uses customize-set-variable to change the variable.
OTHERNAME gives an alternative name than the default <VAR>-toggle.
The name of the defined function is returned."
  `(proof-deftoggle-fn (quote ,var) (quote ,othername)))

(defun proof-defintset-fn (var &optional othername)
  "Define a function <VAR>-intset for setting an integer customize setting VAR.
Args as for the macro `proof-defintset', except will be evaluated."
  (eval
   `(defun ,(if othername othername 
	      (intern (concat (symbol-name var) "-intset"))) (arg)
	      ,(concat "Set `" (symbol-name var) "' to ARG.
This function simply uses customize-set-variable to set the variable.
It was constructed with `proof-defintset-fn'.")
	      (interactive ,(concat "nValue for " (symbol-name var) 
				    " (integer): "))
	      (customize-set-variable (quote ,var) arg))))

(defmacro proof-defintset (var &optional othername)
  "Define a function <VAR>-intset for setting an integer customize setting VAR.
The setting function uses customize-set-variable to change the variable.
OTHERNAME gives an alternative name than the default <VAR>-intset.
The name of the defined function is returned."
  `(proof-defintset-fn (quote ,var) (quote ,othername)))

(defun proof-defstringset-fn (var &optional othername)
  "Define a function <VAR>-toggle for setting an integer customize setting VAR.
Args as for the macro `proof-defstringset', except will be evaluated."
  (eval
   `(defun ,(if othername othername 
	      (intern (concat (symbol-name var) "-stringset"))) (arg)
	      ,(concat "Set `" (symbol-name var) "' to ARG.
This function simply uses customize-set-variable to set the variable.
It was constructed with `proof-defstringset-fn'.")
	      (interactive ,(concat "sValue for " (symbol-name var) 
				    " (a string): "))
	      (customize-set-variable (quote ,var) arg))))

(defmacro proof-defstringset (var &optional othername)
  "The setting function uses customize-set-variable to change the variable.
OTHERNAME gives an alternative name than the default <VAR>-stringset.
The name of the defined function is returned."
  `(proof-defstringset-fn (quote ,var) (quote ,othername)))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Finding executables
;;

(defun proof-locate-executable (progname &optional returnnopath)
  ;; XEmacs can search the paths for us.  Probably FSF Emacs is too
  ;; daft to provide a useful function to do that, and I don't have
  ;; the time to waste writing one or trying to find one.
  "Search for PROGNAME on PATH.  Return the full path to PROGNAME, or nil.
If RETURNNOPATH is non-nil, return PROGNAME even if we can't find a full path."
  (or 
   (cond
    ((fboundp 'executable-find)
     (executable-find progname))	;; PG 3.4: try a new Emacs function.
    ((fboundp 'locate-file)
     (locate-file progname
		  (split-path (getenv "PATH")) 
		  (if proof-running-on-win32 '(".exe"))
		  1))
    (and
     returnnopath
     progname))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Stuff for developing PG, not needed for ordinary users really.
;; [Could consider moving this to a new file `proof-devel.el']
;;

(put 'proof-if-setting-configured 'lisp-indent-function 1)
(put 'proof-define-assistant-command 'lisp-indent-function 'defun)
(put 'proof-define-assistant-command-witharg 'lisp-indent-function 'defun)
(put 'defpgcustom 'lisp-indent-function 'defun)

(defconst proof-extra-fls
  (list
   (list "^(\\(proof-def\\"
	 ;; Variable like things
	 "\\(asscustom)\\|"
	 ;; Function like things
	 "\\([^ \t\n\(\)]+\\)"
	 ;; Any whitespace and declared object.
	 "[ \t'\(]*"
	 "\\([^ \t\n\)]+\\)?")
   '(1 font-lock-keyword-face)
   '(8 (cond ((match-beginning 3) 'font-lock-variable-name-face)
	     ;; ((match-beginning 6) 'font-lock-type-face)
	     (t 'font-lock-function-name-face))
       nil t)))

;; This doesn't work for FSF's font lock, developers should use
;; XEmacs!
(if (boundp 'lisp-font-lock-keywords)	; compatibility hack
    (setq lisp-font-lock-keywords 
	  (append proof-extra-fls
		  lisp-font-lock-keywords)))
       
(setq autoload-package-name "proof")
(setq generated-autoload-file "proof-autoloads.el")
	
;; End of proof-utils.el
(provide 'proof-utils)