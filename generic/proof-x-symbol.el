;; proof-x-symbol.el  Support for X-Symbol package
;;
;; Copyright (C) 1998-2002 LFCS Edinburgh
;; Author:    David Aspinall <da@dcs.ed.ac.uk>
;; License:   GPL (GNU GENERAL PUBLIC LICENSE)
;;
;; The X-Symbol package is currently available at
;; http://x-symbol.sourceforge.net/
;;
;; With thanks to David von Oheimb for providing the original 
;; patches for using X-Symbol with Isabelle Proof General, 
;; and helping to write this file.
;;
;; This file is standalone so that the X-Symbol mode for particular
;; proof assistants may be used elsewhere (e.g. in document modes),
;; without loading all of Proof General.
;;
;; proof-x-symbol.el,v 2.4 1999/08/23 18:38:40 da Exp
;;

(defvar proof-x-symbol-initialized nil
  "Non-nil if x-symbol support has been initialized.")

;;; ###autoload
(defun proof-x-symbol-support-maybe-available ()
  "A test to see whether x-symbol support may be available."
  (and window-system		    ; Not on a tty
       (condition-case ()
	   (require 'x-symbol-hooks)
	 (t (featurep 'x-symbol-hooks)))))


(defun proof-x-symbol-initialize (&optional error)
  "Initialize x-symbol support for Proof General, if possible.
If ERROR is non-nil, give error on failure, otherwise a warning."
  (interactive)
  ; (unless proof-x-symbol-initialized
    (let*
	((xs-lang        (proof-ass x-symbol-language))
	 (xs-lang-name	 (symbol-name xs-lang))
	 (xs-feature     (concat "x-symbol-" xs-lang-name))
	 (xs-feature-sym (intern xs-feature))
	 (error-or-warn	 
	  (lambda (str) (if error (error str) (warn str)))))
      ;; Check that support is provided.
      (cond
       ;;
       ;; First, some checks on x-symbol.
       ;;
       ((and (not (featurep 'x-symbol))
	     (not (proof-try-require 'x-symbol)))
	(funcall error-or-warn
 "Proof General: x-symbol package must be installed for x-symbol-support!
The package is available at http://x-symbol.sourceforge.net/"))
       ((not window-system)
	(funcall error-or-warn 
 "Proof General: x-symbol package only runs under a window system!"))
       ((or (not (fboundp 'x-symbol-initialize))
	    (not (fboundp 'x-symbol-register-language)))
	(funcall error-or-warn 
		 "Proof General: x-symbol package installation faulty!"))
       ;;
       ;; Now check proof assistant has support provided
       ;;
       ;; FIXME: maybe we should let x-symbol load the feature, in
       ;; case it uses x-symbol stuff inside.
       ;; Is there an easy way of testing for library exists?
       ((not (proof-try-require xs-feature-sym))
	(funcall error-or-warn 
		 (format
 "Proof General: for x-symbol support, you must provide a library %s.el"
		  xs-feature)))
       (t
	;; We've got everything we need!   So initialize.
	(require 'x-symbol-vars)  ;; [new requirement to require this]
	(let*
	    ((xs-xtra-modes  proof-xsym-extra-modes)
	     (xs-std-modes   (list
			      ;; NB: there is a problem with
			      ;; initialization order here, these
			      ;; variables are set in script/shell
			      ;; mode initialization.  They ought to
			      ;; be set earlier, and enforced as part
			      ;; of the generic scheme.  For the time
			      ;; being, we use default constructed
			      ;; names [which every prover should
			      ;; follow]
			      (or proof-mode-for-shell
				  (intern (concat assistant "-shell-mode")))
			      (or proof-mode-for-response
				  (intern (concat assistant "-response-mode")))
			      (or proof-mode-for-script
				  ;; FIXME: next one only correct for isabelle
				  (intern (concat assistant "-proofscript-mode")))
			      (or  proof-mode-for-goals
				   (intern (concat assistant "-goals-mode")))))
	     (all-xs-modes   (append xs-std-modes xs-xtra-modes))
	     (am-entry       (list proof-xsym-extra-modes t 
				   `(quote ,xs-lang)))
	     (symmode-nm     (concat xs-lang-name "sym-mode"))
	     (symmode        (intern symmode-nm))
	     (symnamevar     (intern (concat xs-feature "-name")))
	     (symname	     (concat (capitalize xs-lang-name) " Symbols"))
	     (symmodelinevar (intern (concat xs-feature "-modeline-name")))
	     (symmodelinenm  xs-lang-name)
	     (flks	     proof-xsym-font-lock-keywords))


	  (x-symbol-initialize)    ;; No harm in doing this multiple times
	  ;; Set default name and modeline indicator for the symbol
	  ;; minor mode
	  (set symnamevar symname)
	  (set symmodelinevar symmodelinenm)
	  (x-symbol-register-language xs-lang xs-feature-sym all-xs-modes)
	  ;; Put the extra modes on the auto-mode-alist
	  ;; 3.0: don't bother: rashly assume that their mode
	  ;; functions invoke proof-x-symbol-mode.  That way we can
	  ;; turn on/off cleanly in proof-x-symbol-mode-all-buffers.
	  ;; (if xs-xtra-modes (push am-entry x-symbol-auto-mode-alist))
	  ;; Okay, let's be less rash and put it on a hook list.
	  ;; 12.1.00: Nope, there's a problem here!  
	  ;; Results in thy-mode invoking 
	  ;; proof-x-symbol-mode twice, first via hook, then
	  ;; from proof-config-done-related, which blasts 
	  ;; font-lock-keywords (whilst font-lock is turned on!)
          ;; .  Temporarily disable this,
	  ;; and consider what to do for other extra modes
	  ;; (isa-latex).
;	  (dolist (mode proof-xsym-extra-modes)
;	    (add-hook 
;	     (intern (concat (symbol-name mode) "-hook"))
;	     'proof-x-symbol-mode))
	  ;; Font lock support is optional

	  ;; FIXME: Isabelle wants this for sup/sub scripts
	  ;; presently loads too early and extends in modedef
	  ;; setups.  Want to adjust here.
	  (if flks
	      (put symmode 'font-lock-defaults (list flks)))
	  ;;
	  ;; Finished.
	  (setq proof-x-symbol-initialized t))))))


;;;###autoload
(defun proof-x-symbol-enable ()
  "Turn on or off support for x-symbol, initializing if necessary.
Calls proof-x-symbol-toggle-clean-buffers afterwards."
  (if (and (proof-ass x-symbol-enable) (not proof-x-symbol-initialized))
      (progn
	(set (proof-ass-sym x-symbol-enable) nil) ; assume failure!
	(proof-x-symbol-initialize 'giveerrors)
	(set (proof-ass-sym x-symbol-enable) t)))
  (proof-x-symbol-mode-all-buffers)
  (proof-x-symbol-toggle-clean-buffers))

;; First inclination was to put this function in a hook called by
;; enable function.  But rather than proliferate hooks needlessly, it
;; seems better to wait to find out whether they're really needed.
(defun proof-x-symbol-toggle-clean-buffers ()
  "Clear the response buffer and send proof-showproof-command.
This function is intended to clean the display after a change
in the status of X-Symbol display.
This is a subroutine of proof-x-symbol-enable."
  (proof-shell-maybe-erase-response nil t t)
  (if (and proof-showproof-command (proof-shell-available-p))
    (proof-shell-invisible-command proof-showproof-command)))

;;;###autoload
(defun proof-x-symbol-decode-region (start end) 
  "Call (x-symbol-decode-region START END), if x-symbol support is enabled.
This converts tokens in the region into X-Symbol characters.
Return new END value."
  (if (proof-ass x-symbol-enable)
      (save-excursion
	(save-restriction
	  (narrow-to-region start end)
	  ;; FIXME: for GNU 21, this doesn't work always?? 
	  ;; (OK for response, but not for goals, why?)
	  (x-symbol-decode-region start end)
	  ;; Decoding may change character positions.  
	  ;; Return new end value
	  (point-max)))
    end))

(defun proof-x-symbol-encode-shell-input ()
  "Encode shell input in the variable STRING.
A value for proof-shell-insert-hook."
  (and x-symbol-language
       (setq string
             (save-excursion
               (let ((language x-symbol-language)
                     (coding x-symbol-coding)
                     (selective selective-display)) ;FIXME: needed?
                 (set-buffer (get-buffer-create "x-symbol comint"))
                 (erase-buffer)
                 (insert string)
                 (setq x-symbol-language language)
		 (setq x-symbol-8bits nil)
		 (setq x-symbol-coding nil)
                 (x-symbol-encode-all nil coding))
               (prog1 
		   (buffer-substring (point-min) (point-max))
		 ;; FIXME da: maybe more efficient just to delete
		 ;; region.  Make buffer name start with space
		 ;; to be unselectable.
                 (kill-buffer (current-buffer)))))))




(defun proof-x-symbol-mode-all-buffers ()
  "Activate/deactivate x-symbols in all Proof General buffers.
A subroutine of proof-x-symbol-enable."
  ;; Response and goals buffer are fontified/decoded 
  ;; manually in the code, configuration only sets
  ;; x-symbol-language.
  (proof-map-buffers (list proof-goals-buffer 
			   proof-response-buffer
			   proof-trace-buffer)
   (proof-x-symbol-configure))
  ;; Shell has its own configuration
  (proof-with-current-buffer-if-exists proof-shell-buffer
   (proof-x-symbol-shell-config))
  ;; Script buffers are in X-Symbol's minor mode, 
  ;; And so are any other buffers kept in the same token language
  (dolist (mode (cons proof-mode-for-script proof-xsym-extra-modes))
    (proof-map-buffers 
     (proof-buffers-in-mode mode)
     (proof-x-symbol-mode))))

;;
;; Three functions for configuring buffers:
;;
;;  proof-x-symbol-mode:	  for script buffer (X-Symbol minor mode)
;;  proof-x-symbol-shell-config:  for shell buffer (input hook)
;;  proof-x-symbol-configure:     for goals/response buffer (font lock)
;;

(defun proof-x-symbol-set-language ()
  "Set x-symbol-language for the current proof assistant."
  (setq x-symbol-language (proof-ass x-symbol-language)))

;;;###autoload
(defun proof-x-symbol-mode ()
  "Turn on/off x-symbol mode in current buffer, from proof-x-symbol-enable.
The X-Symbol minor mode is only useful in buffers where symbol input
takes place (it isn't used for output-only buffers)."
  (interactive)
  (save-excursion			; needed or point moves: why?
    (if proof-x-symbol-initialized
	(progn
	  ;; Buffers which have XS minor mode toggled always keep 
	  ;; x-symbol-language set.
	  (proof-x-symbol-set-language)
	  (x-symbol-mode (if (proof-ass x-symbol-enable) 1 0))
	  ;; Font lock mode must be engaged for x-symbol to do its job
          ;; properly, at least when there is no mule around.
	  (if (and x-symbol-mode (not (featurep 'mule)))
	      (if (not font-lock-mode)
		  (font-lock-mode)
		;; Even if font-lock was on before we may need to
		;; refontify now that the patterns (and buffer
		;; contents) have changed. Shouldn't x-symbol do this?
		(font-lock-fontify-buffer)))))))

;;;####autoload
(defun proof-x-symbol-shell-config ()
  "Configure the proof shell for x-symbol, if proof-x-symbol-support<>nil.
Assumes that the current buffer is the proof shell buffer."
  ;; The best strategy seems to be *not* to turn on decoding
  ;; in the shell itself.  The reason is that there can be
  ;; a clash between annotations and X-Symbol characters
  ;; which leads to funny effects later.  Moreover, the
  ;; user isn't encouraged to interact directly with the
  ;; shell, so we don't need to be helpful there.
  ;; So we keep the shell buffer as plain text plus annotations.
  ;; Even font-lock is problematical, so it should be switched off
  ;; too.
  (if proof-x-symbol-initialized
      (progn
	(cond
	 ((proof-ass x-symbol-enable)
	  (proof-x-symbol-set-language)
	  (if (and proof-xsym-activate-command 
		   (proof-shell-live-buffer))
	      (proof-shell-invisible-command 
	       proof-xsym-activate-command 'wait))
	  ;; We do encoding as the first step of input manipulation
	  (add-hook 'proof-shell-insert-hook
		    'proof-x-symbol-encode-shell-input))
	 ((not (proof-ass x-symbol-enable))
	  (if (and proof-xsym-deactivate-command 
		   (proof-shell-live-buffer))
	      (proof-shell-invisible-command 
	       proof-xsym-deactivate-command 'wait))
	  (remove-hook 'proof-shell-insert-hook
		       'proof-x-symbol-encode-shell-input)
	  ;; NB: x-symbol automatically adds an output filter but
	  ;; it doesn't actually get used unless the minor mode is 
	  ;; active. Removing it here is just tidying up.
	  (remove-hook 'comint-output-filter-functions
		       'x-symbol-comint-output-filter))))))

;;;###autoload
(defun proof-x-symbol-configure ()
  "Configure the current output buffer (goals/response/trace) for X-Symbol."
  (if (proof-ass x-symbol-enable)
      (progn
	(proof-x-symbol-set-language)
	;; BEGIN: Code below from x-symbol.el/x-symbol-mode-internal
	(unless (or (not (boundp 'enable-multibyte-characters))
		    (not (fboundp 'set-buffer-multibyte))
		    enable-multibyte-characters)
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
	      (set-buffer-modified-p modified))))
	;; END code from x-symbol.el/x-symbol-mode-internal

	;; If we're turning on x-symbol, attempt to convert to 
	;; characters.  (Only works if the buffer already
	;; contains tokens!)
	(x-symbol-decode))))
  ;; Encoding back to tokens doesn't work too well: needs to 
  ;; do some de-fontification to remove font properties, and
  ;; is flaky anyway because token -> char not nec injective.
  ;  (if (boundp 'x-symbol-language)
  ;	;; If we're turning off x-symbol, convert back to tokens.
  ;     (x-symbol-encode))))


;; Compatibility with completion package

(put 'completion-separator-self-insert-command 'x-symbol-input t)
(put 'completion-separator-self-insert-autofilling 'x-symbol-input t)


;;
;; Try to initialize x-symbol-support on load-up if user has asked for it
;;
(if (proof-ass x-symbol-enable) 
    (progn
      (proof-x-symbol-initialize)
      (unless proof-x-symbol-initialized
	;; If initialization failed, turn off
	;; x-symbol-enable for the session.
	(customize-set-variable (proof-ass-sym x-symbol-enable) nil))))

(provide 'proof-x-symbol)
;; End of proof-x-symbol.el
