;; proof-utils.el   Proof General utility functions
;;
;; Copyright (C) 1998-2000 LFCS Edinburgh. 
;;
;; Author:      David Aspinall <da@dcs.ed.ac.uk> and others
;; Maintainer:  Proof General maintainer <proofgen@dcs.ed.ac.uk>
;;
;; $Id$
;;


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

; (deflocal proof-font-lock-defaults nil
;  "Value of font-lock-defaults in this buffer.

(defun proof-font-lock-configure-defaults (&optional case-fold)
  "Set defaults for font-lock based on current font-lock-keywords."
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
  ;; FIXME: specific code could set this variable directly, really.
  (setq proof-font-lock-keywords font-lock-keywords)
  (setq font-lock-keywords-case-fold-search case-fold)
  ;; Setting font-lock-defaults explicitly is required by FSF Emacs
  ;; 20.4's version of font-lock in any case.
  (make-local-variable 'font-lock-defaults) ; not needed in XEmacs, FSF?
  (setq font-lock-defaults `(proof-font-lock-keywords nil ,case-fold))
  ;; 12.1.99: testing: For XEmacs, we must also set the property.
  ;; This is needed for buffers which are put into font-lock-mode
  ;; (rather than fontified by hand).
  (put major-mode 'font-lock-defaults font-lock-defaults)
  (setq font-lock-keywords nil))

(defun proof-fontify-region (start end)
  "Fontify and decode X-Symbols in region START...END.
Fontifies according to the buffer's font lock defaults.
Uses proof-x-symbol-decode to decode tokens if x-symbol is present.

If proof-shell-leave-annotations-in-output is set, remove characters
with top bit set after fontifying so they can be used for
fontification.

Returns new END value."
  ;; We fontify first because decoding changes char positions.
  ;; It's okay because x-symbol-decode works even without font lock.
  ;; Possible disadvantage is that font lock patterns can't refer
  ;; to X-Symbol characters.  Probably they shouldn't!
  (narrow-to-region start end)

  (if proof-output-fontify-enable
      (progn
	;; FSF hack, yuk.
	(unless (string-match "XEmacs" emacs-version)
	  (font-lock-set-defaults))
	(let ((font-lock-keywords proof-font-lock-keywords))
	  ;; FIXME: should set other bits of font lock defaults,
	  ;; perhaps, such as case fold etc.  What happened to
	  ;; the careful buffer local font-lock-defaults??
	  (font-lock-fontify-region start end)
	  (proof-zap-commas-region start end))))
  (if proof-shell-leave-annotations-in-output
      ;; Remove special characters that were used for font lock,
      ;; so cut and paste works from here.
      (let ((p (point)))
	(goto-char start)
	(while (< (point) (point-max))
	  (forward-char)
	  (unless (< (char-before (point)) 128) ; char-to-int in XEmacs
	    (delete-char -1)))
	(goto-char p)))
  (proof-x-symbol-decode-region start (point-max))
  (prog1 (point-max)
    (widen)))

;; FIXME todo: add toggle for fontify region which turns it on/off
;; (maybe).

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

;; FIXME: this function should be combined with
;; proof-shell-maybe-erase-response-buffer. 
(defun proof-response-buffer-display (str &optional face)
  "Display STR with FACE in response buffer and return fontified STR."
  (if (string-equal str "\n")	
      str				; quick exit, no display.
  (let (start end)
    (with-current-buffer proof-response-buffer
      ;; da: I've moved newline before the string itself, to match
      ;; the other cases when messages are inserted and to cope
      ;; with warnings after delayed output (non newline terminated).
      ; (ugit (format "End is %i" (point-max)))
      (goto-char (point-max))
      (newline)				
      (setq start (point))
      (insert str)
      (unless (bolp) (newline))
      (setq end (proof-fontify-region start (point)))
      ;; This is one reason why we don't keep the buffer in font-lock
      ;; minor mode: it destroys this hacky property as soon as it's
      ;; made!  (Using the minor mode is much more convenient, tho')
      (if (and face proof-output-fontify-enable)
	  (font-lock-append-text-property start end 'face face))
      ;; This returns the decorated string, but it doesn't appear 
      ;; decorated in the minibuffer, unfortunately.
      (buffer-substring start (point-max))))))

(defun proof-display-and-keep-buffer (buffer &optional pos)
  "Display BUFFER and mark window according to `proof-dont-switch-windows'.
If optional POS is present, will set point to POS.  
Otherwise move point to the end of the buffer.
Ensure that point is visible in window."
  (let (window)
    (save-excursion
      (set-buffer buffer)
      (display-buffer buffer)
      (setq window (get-buffer-window buffer 'visible))
      (set-window-dedicated-p window proof-dont-switch-windows)
      (and window
	   (save-selected-window
	     (select-window window)
	     
	     ;; tms: I don't understand why the point in
	     ;; proof-response-buffer is not at the end anyway.
	     ;; Is there a superfluous save-excursion somewhere?
	     ;; da replies: I think it's because of a *missing*
	     ;; save-excursion above around the font-lock stuff.
	     ;; Adding one has maybe fixed this problem.
	     ;; 10.12.98 Experiment removing this so that point
	     ;; doesn't always go to end of goals buffer
	     ;; RESULT: point doesn't go to end of response
	     ;; buffer.  Hypothesis above was wrong, so this
	     ;; is re-added and optional POS argument added
	     ;; for this function.
	     (goto-char (or pos (point-max)))
	     (if pos (beginning-of-line)) ;  Normalization

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
    (if proof-delete-empty-windows
	(delete-windows-on buffer t))))

(defun proof-message (&rest args)
  "Issue the message ARGS in the response buffer and display it."
    (proof-response-buffer-display (apply 'concat args))
    (proof-display-and-keep-buffer proof-response-buffer))

(defun proof-warning (&rest args)
  "Issue the warning ARGS in the response buffer and display it.
The warning is coloured with proof-warning-face."
    (proof-response-buffer-display (apply 'concat args) 'proof-warning-face)
    (proof-display-and-keep-buffer proof-response-buffer))

;; could be a macro for efficiency in compiled code
(defun proof-debug (&rest args)
  "Issue the debugging messages ARGS in the response buffer, display it.
If proof-show-debug-messages is nil, do nothing."
  (if proof-show-debug-messages
      (progn
	(proof-response-buffer-display (apply 'concat 
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

;;
;; Flag and function to keep response buffer tidy.
;;
;; FIXME: rename this now it's moved out of proof-shell.
;;
(defvar proof-shell-erase-response-flag nil
  "Indicates that the response buffer should be cleared before next message.")

(defun proof-shell-maybe-erase-response
  (&optional erase-next-time clean-windows force)
  "Erase the response buffer according to proof-shell-erase-response-flag.
ERASE-NEXT-TIME is the new value for the flag.
If CLEAN-WINDOWS is set, use proof-clean-buffer to do the erasing.
If FORCE, override proof-shell-erase-response-flag.

If the user option proof-tidy-response is nil, then
the buffer is only cleared when FORCE is set.

No effect if there is no response buffer currently.
Returns non-nil if response buffer was cleared."
  (when (buffer-live-p proof-response-buffer)
    (let ((doit (or (and
		     proof-tidy-response
		     (not (eq proof-shell-erase-response-flag 'invisible))
		     proof-shell-erase-response-flag) 
		    force)))
      (if doit
	  (if clean-windows
	      (proof-clean-buffer proof-response-buffer)
	  ;; NB: useful optional arg to erase buffer is XEmacs specific, 8-(.
	  ;; (erase-buffer proof-response-buffer)
	    (with-current-buffer proof-response-buffer
	      (erase-buffer))))
      (setq proof-shell-erase-response-flag erase-next-time)
      doit)))



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
     "proofgen@dcs.ed.ac.uk"
     "Proof General" 
     (list 'proof-general-version 'proof-assistant)
     nil nil
     "[ When reporting a bug, please include a small test case for us to repeat it.
 Please also check that it is not already covered in the BUGS files that came with
 the distribution, or the latest versions at 
 http://zermelo.dcs.ed.ac.uk/~proofgen/ProofGeneral/BUGS ]")))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Stuff for developing PG, not needed for ordinary users really.
;; [Could consider moving this to a new file `proof-devel.el']
;;

(put 'proof-if-setting-configured 'lisp-indent-function 1)
(put 'proof-define-assistant-command 'lisp-indent-function 'defun)
(put 'proof-define-assistant-command-witharg 'lisp-indent-function 'defun)
(put 'proof-defasscustom 'lisp-indent-function 'defun)

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