;; proof-x-symbol.el  Support for x-symbol package
;;
;; Copyright (C) 1998,9 LFCS Edinburgh. 
;; Author: David Aspinall <da@dcs.ed.ac.uk>
;;
;; With thanks to David von Oheimb for providing the original 
;; patches for using X-Symbol with Isabelle Proof General, 
;; and helping to write this file.
;;
;; Maintainer:  Proof General maintainer <proofgen@dcs.ed.ac.uk>
;;
;; proof-x-symbol.el,v 2.4 1999/08/23 18:38:40 da Exp
;;

(defvar proof-x-symbol-initialized nil
  "Non-nil if x-symbol support has been initialized.")

;;; ###autoload
(defun proof-x-symbol-support-maybe-available ()
  "A test to see whether x-symbol support may be available."
  (and (fboundp 'console-type)		; FSF Emacs doesn't have this
       (eq (console-type) 'x)		; (neither does it have x-symbol)
       (condition-case ()
	   (require 'x-symbol-autoloads) 
	 (t (featurep 'x-symbol-autoloads)))))


(defun proof-x-symbol-initialize (&optional error)
  "Initialize x-symbol support for Proof General, if possible.
If ERROR is non-nil, give error on failure, otherwise a warning."
  (interactive)
  ; (unless proof-x-symbol-initialized
    (let*
	((assistant	 (symbol-name proof-assistant-symbol))
	 (xs-feature     (concat "x-symbol-" assistant))
	 (xs-feature-sym (intern xs-feature))
	 (error-or-warn	 
	  (lambda (str) (if error (error str) (warn str)))))
      ;; Check that support is provided.
      (cond
       ;;
       ;; First, some checks on x-symbol.
       ;;
       ((and (not (featurep 'x-symbol-autoloads))
	     (not (proof-try-require 'x-symbol)))
	(funcall error-or-warn
 "Proof General: x-symbol package must be installed for x-symbol-support!
The package is available at http://www.fmi.uni-passau.de/~wedler/x-symbol"))
       ((not (and (fboundp 'console-type)  ; FSF doesn't have this
		  (eq (console-type) 'x))) ; (window-system) instead
	(funcall error-or-warn 
 "Proof General: x-symbol package only runs under X!"))
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
	(let*
	    ((xs-lang	     proof-assistant-symbol)
	     (xs-xtra-modes  proof-xsym-extra-modes)
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
			      (or  proof-mode-for-pbp
				   (intern (concat assistant "-pbp-mode")))))
	     (all-xs-modes   (append xs-std-modes xs-xtra-modes))
	     (am-entry       (list proof-xsym-extra-modes t 
				   `(quote ,xs-lang)))
	     (symmode-nm     (concat assistant "sym-mode"))
	     (symmode        (intern symmode-nm))
	     (symnamevar     (intern (concat xs-feature "-name")))
	     (symname	     (concat proof-assistant " Symbols"))
	     (symmodelinevar (intern (concat xs-feature "-modeline-name")))
	     (symmodelinenm  assistant)
	     (flks	     proof-xsym-font-lock-keywords))


	  (x-symbol-initialize)    ;; No harm in doing this multiple times
	  ;; Set default name and modeline indicator for the symbol
	  ;; minor mode
	  (set symnamevar symname)
	  (set symmodelinevar symmodelinenm)
	  (x-symbol-register-language xs-lang xs-feature-sym all-xs-modes)
	  ;; Put the extra modes on the auto-mode-alist
	  ;; 3.0: don't bother: rashly assume that their mode
	  ;; functions invoke proof-x-symbol.  That way we can
	  ;; turn on/off cleanly in proof-x-symbol-mode-all-buffers.
	  ;; (if xs-xtra-modes (push am-entry x-symbol-auto-mode-alist))
	  ;; Font lock support is optional
	  (if flks
	      (put symmode 'font-lock-defaults (list flks)))
	  ;;
	  ;; Finished.
	  (setq proof-x-symbol-initialized t))))))


;;;###autoload
(defun proof-x-symbol-enable ()
  "Turn on or off support for x-symbol, initializing if necessary.
Calls proof-x-symbol-toggle-clean-buffers afterwards."
  (if (and proof-x-symbol-enable (not proof-x-symbol-initialized))
      (progn
	(setq proof-x-symbol-enable nil) ; assume failure!
	(proof-x-symbol-initialize 'giveerrors)
	(setq proof-x-symbol-enable t)))
  (proof-x-symbol-mode-all-buffers)
  (proof-x-symbol-toggle-clean-buffers))

;; First inclination was to put this function in a hook called by
;; enable function.  But rather than proliferate hooks needlessly, it
;; seems better to wait to find out whether they're really needed.
(defun proof-x-symbol-toggle-clean-buffers ()
  "Clear the response buffer and send proof-showproof-command.
This function is intended to clean the display after a change
in the status of X-Symbol display.
This is a subroutine of x-symbol-enable."
  (proof-shell-maybe-erase-response nil t t)
  (if (and proof-showproof-command (proof-shell-available-p))
    (proof-shell-invisible-command proof-showproof-command)))

;;;###autoload
(defun proof-x-symbol-decode-region (start end) 
  "Call (x-symbol-decode-region A Z), if x-symbol support is enabled.
This converts tokens in the region into X-Symbol characters."
  (if (and proof-x-symbol-enable)
      (x-symbol-decode-region start end)))

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
                 (x-symbol-encode-all nil coding))
               (prog1 (buffer-substring)
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
  (proof-map-buffers (list proof-goals-buffer proof-response-buffer)
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

;;;### autoload
(defun proof-x-symbol-mode ()
  "Turn on/off x-symbol mode in current buffer, from proof-x-symbol-enable.
The X-Symbol minor mode is only useful in script buffers."
  (interactive)
  (save-excursion			; needed or point moves: why?
    (if proof-x-symbol-initialized
	(progn
	  ;; Buffers which have XS minor mode toggled always keep 
	  ;; x-symbol-language set.
	  (setq x-symbol-language proof-assistant-symbol)
	  (x-symbol-mode (if proof-x-symbol-enable 1 0))
	  ;; Font lock mode must be engaged for x-symbol to do its job
          ;; properly, at least when there is no mule around.
	  (if (and x-symbol-mode (not (featurep 'mule)))
	      (if (not font-lock-mode)
		  (font-lock-mode)
		;; Even if font-lock was on before we may need to
		;; refontify now that the patterns (and buffer
		;; contents) have changed. Shouldn't x-symbol do this?
		(font-lock-fontify-buffer)))))))

;;;#### autoload
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
	 (proof-x-symbol-enable
	  (setq x-symbol-language proof-assistant-symbol)
	  (if (and proof-xsym-activate-command 
		   (proof-shell-live-buffer))
	      (proof-shell-invisible-command 
	       proof-xsym-activate-command 'wait))
	  ;; We do encoding as the first step of input manipulation
	  (add-hook 'proof-shell-insert-hook
		    'proof-x-symbol-encode-shell-input))
	 ((not proof-x-symbol-enable)
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
  "Configure the current buffer (goals or response) for X-Symbol."
  (if proof-x-symbol-enable
      (progn
	(setq x-symbol-language proof-assistant-symbol)
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




;;
;; Try to initialize x-symbol-support on load-up if user has asked for it
;;
(if proof-x-symbol-enable (proof-x-symbol-initialize))
;;
;; If initialization failed, the next line will turn off
;; proof-x-symbol-enable for the session.
;;
(customize-set-variable 'proof-x-symbol-enable proof-x-symbol-initialized)



(provide 'proof-x-symbol)
;; End of proof-x-symbol.el
