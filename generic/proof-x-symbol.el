;; proof-x-symbol.el  Support for X-Symbol package
;;
;; Copyright (C) 1998-2002 LFCS Edinburgh
;; Author:    David Aspinall <da@dcs.ed.ac.uk>
;; License:   GPL (GNU GENERAL PUBLIC LICENSE)
;; Id:	      $Id$
;;
;; The X-Symbol package is at http://x-symbol.sourceforge.net/
;;
;; With enormous thanks to David von Oheimb for providing the original
;; patches for using X-Symbol with Isabelle Proof General, and 
;; of course, to Christoph Wedler for providing the wonderful
;; X-Symbol package in the first place.  Christoph also helped
;; with configuration and tweaks in X-Symbol for Proof General.
;;
;; ================================================================
;;
;; NB: X-Symbol is now bundled with Proof General, and PG will select
;; it's own version before any other version on the Emacs load path.
;; If you want to override this, simply load your version before
;; starting Emacs, with (require 'x-symbol-hooks).
;;
;; =================================================================
;;
;; Notes on interacing to X-Symbol.
;;
;; 1. Proof script buffers.
;; Font lock and X-Symbol minor modes are engaged as usual.  We use
;; proof-x-symbol-enable to add/remove PG buffers to X-Symbol's
;; auto-mode list.
;;
;; 2. Output buffers (goals, response, tracing)
;; Neither font-lock nor X-Symbol mode is engaged.  Instead, we simply
;; set `x-symbol-language', and call `x-symbol-decode' or
;; `x-symbol-decode-region', via `proof-fontify-region' (which see).
;;
;; ================================================================
;;
;; Ideally this file ought to be standalone so that the X-Symbol mode
;; for particular proof assistants may be used elsewhere (e.g. in
;; document modes), without loading all of Proof General.
;;
;; =================================================================

;; Current TODO here:
;;
;; -- Is it possible to remove setting of language in x-symbol-enable?
;; -- Simplify proof-x-symbol-initialize
;; -- Investigate font-lock errors (XEmacs 21.4.8):
;;     Error caught in `font-lock-pre-idle-hook': (wrong-type-argument markerp nil)


(defvar proof-x-symbol-initialized nil
  "Non-nil if x-symbol support has been initialized.")

(defun proof-x-symbol-tokenlang-file ()
  "Return filename (sans extension) of token language file."
  (concat "x-symbol-" 
	  (symbol-name proof-assistant-symbol)))

;;;###autoload
(defun proof-x-symbol-support-maybe-available ()
  "A test to see whether x-symbol support may be available."
  (and
   (or (featurep 'x-symbol-hooks)
       (and window-system		; Not on a tty
	    (progn
	      ;; put bundled version on load path
	      (setq load-path
		    (cons 
		     (concat proof-home-directory "x-symbol/lisp/") 
		     load-path))
	      ;; avoid warning about installing in proper place
	      (setq x-symbol-data-directory 
		    (concat proof-home-directory "x-symbol/etc/"))
	      ;; *should* always succeed unless bundled version broken
	      (proof-try-require 'x-symbol-hooks))))
   ;; See if there is prover-specific config in x-symbol-<foo>.el
   (if (locate-library (proof-x-symbol-tokenlang-file)) t)))


(defun proof-x-symbol-initialize (&optional error)
  "Initialize x-symbol support for Proof General, if possible.
If ERROR is non-nil, give error on failure, otherwise a warning."
  (interactive)
  (unless (or proof-x-symbol-initialized ;; already done
	      ;; or can't be done
	      (not (proof-x-symbol-support-maybe-available)))
    (let*
	((xs-lang        (proof-ass x-symbol-language))
	 (xs-lang-name	 (symbol-name xs-lang))
	 (xs-feature     (concat "x-symbol-" xs-lang-name))
	 (xs-feature-sym (intern xs-feature))
	 (error-or-warn	 
	  (lambda (str) 
	    (progn
	      (if error (error str) (warn str))))))
      ;; Check that support is provided.
      (cond
       ;; First, some checks on x-symbol.
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
       ;; case it uses x-symbol stuff inside?  
       ;; NB: however, we're going to assume two files (thanks
       ;; to Isabelle: the standard x-symbol-<foo>.el, and one
       ;; named after the language feature).  
       ((not (proof-try-require (intern (proof-x-symbol-tokenlang-file))))
	(funcall error-or-warn 
		 (format
 "Proof General: for x-symbol support, you must provide a library %s.el"
		  xs-feature)))
       (t
	;; We've got everything we need!   So initialize.
	(require 'x-symbol-vars)  ;; [new requirement to require this]
	(let*
	    ((xs-xtra-modes  proof-xsym-extra-modes)
	     (xs-std-modes   
	      (list
	       ;; NB: there is a problem with initialization order
	       ;; here, these variables are set in script/shell mode
	       ;; initialization.  They ought to be set earlier, and
	       ;; enforced as part of the generic scheme.  For the
	       ;; time being, we use default constructed names [which
	       ;; every prover should follow]
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
	  ;; FIXME: Need for Isabelle sup/sub scripts presently; loads
	  ;; too early and extends in modedef setups.  Adjust here.
	  (if flks
	      (put symmode 'font-lock-defaults (list flks)))
	  ;;
	  ;; Finished.
	  (setq proof-x-symbol-initialized t)))))))



;;;###autoload
(defun proof-x-symbol-enable ()
  "Turn on or off X-Symbol in current Proof General script buffer.
This invokes `x-symbol-mode' to toggle the setting for the current
buffer, and then sets PG's option for default to match.
Also we arrange to have X-Symbol mode turn itself on automatically 
in future if we have just activated it for this buffer."
;; Calls proof-x-symbol-toggle-clean-buffers afterwards.
  (if (not proof-x-symbol-initialized) ;; Check inited
      (progn
	(set (proof-ass-sym x-symbol-enable) nil) ; assume failure!
	(proof-x-symbol-initialize 'giveerrors)
	(set (proof-ass-sym x-symbol-enable) t)))
  (x-symbol-mode)
  (proof-x-symbol-mode-associated-buffers))

;; Old behaviour for proof-x-symbol-enable was to update state in all
;; buffers --- but this can take ages if there are many buffers!  
;; We also used to refresh the output, but this doesn't always work.
;; (proof-x-symbol-mode-all-buffers)
;; (proof-x-symbol-refresh-output-buffers))


(defun proof-x-symbol-refresh-output-buffers ()
  ;; FIXME: this isn't used.  Might be nice to do so again, turning
  ;; off X-Sym can leave junk displayed.  OTOH, sending messages to PA
  ;; can give errors, because there is no generic "refresh" or
  ;; "repeat" option.  (Isar: gives errors outside proof mode).
  ;; Another possibility would just be to clear the display.
  "Clear the response buffer and send proof-showproof-command.
This function is intended to clean the display after a change
in the status of X-Symbol display.
This is a subroutine of proof-x-symbol-enable."
  (proof-shell-maybe-erase-response nil t t)
  (if (and proof-showproof-command (proof-shell-available-p))
    (proof-shell-invisible-command proof-showproof-command)))


(defun proof-x-symbol-mode-associated-buffers ()
  "Activate/deactivate x-symbols in all Proof General associated buffers.
A subroutine of proof-x-symbol-enable."
  ;; Response and goals buffer are fontified/decoded 
  ;; manually in the code, configuration only sets
  ;; x-symbol-language.
  (proof-map-buffers (list proof-goals-buffer 
			   proof-response-buffer
			   proof-trace-buffer)
   (proof-x-symbol-config-output-buffer))
  ;; Shell has its own configuration
  (proof-with-current-buffer-if-exists proof-shell-buffer
   (proof-x-symbol-shell-config)))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Functions to decode output and encode input
;; 

;;;###autoload
(defalias 'proof-x-symbol-decode-region 'x-symbol-decode-region)

(defun proof-x-symbol-encode-shell-input ()
  "Encode shell input in the variable STRING.
A value for proof-shell-insert-hook."
  (and x-symbol-language
       (setq string
             (x-symbol-encode-string 
	      string (current-buffer)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; There are three functions for configuring buffers:
;;
;;  x-symbol-mode:	                 script buffer (X-Symbol minor mode)
;;  proof-x-symbol-shell-config:         shell buffer (input hook)
;;  proof-x-symbol-config-output-buffer: goals/response buffer (font lock)
;;

(defun proof-x-symbol-set-language ()
  "Set x-symbol-language for the current proof assistant."
  (setq x-symbol-language (proof-ass x-symbol-language)))

;;;###autoload
(defun proof-x-symbol-shell-config ()
  "Configure the proof shell for x-symbol, if proof-x-symbol-support<>nil.
Assumes that the current buffer is the proof shell buffer."
  ;; The best strategy seems to be *not* to turn on decoding in the
  ;; shell itself.  The reason is that there can be a clash between
  ;; annotations and X-Symbol characters which leads to funny effects
  ;; later.  Moreover, the user isn't encouraged to interact directly
  ;; with the shell, so we don't need to be helpful there.  So we keep
  ;; the shell buffer as plain text plus annotations.  Even font-lock
  ;; is problematical, so it should be switched off too.

  ;; NB: after changing X-Symbols in output it would be nice to
  ;; refresh display, but there's no robust way of doing that yet
  ;; (see proof-x-symbol-refresh-output-buffers above)
  ;; [ Actually, we could ask that the activate/decativate command
  ;;   itself does this ]
  ;;
  (if proof-x-symbol-initialized
      (progn
	(cond
	 ((proof-ass x-symbol-enable)
	  (proof-x-symbol-set-language)
	  (if (and proof-xsym-activate-command 
		   (proof-shell-live-buffer)
		   ;; may fail if triggered during scripting.
		   ;; Also: should cache status of x-symbol mode in
		   ;; proof shell; current behaviour re-calls this
		   ;; code every time a script file is loaded...
		   (proof-shell-available-p))
	      (proof-shell-invisible-command-invisible-result
	       proof-xsym-activate-command))
	 ;; We do encoding as the first step of input manipulation
	 (add-hook 'proof-shell-insert-hook
	  	    'proof-x-symbol-encode-shell-input))
	 ((not (proof-ass x-symbol-enable))
	  (if (and proof-xsym-deactivate-command 
		   (proof-shell-live-buffer))
	      (proof-shell-invisible-command-invisible-result
	       proof-xsym-deactivate-command))
	  (remove-hook 'proof-shell-insert-hook
		       'proof-x-symbol-encode-shell-input)
	  ;; NB: x-symbol automatically adds an output filter but
	  ;; it doesn't actually get used unless the minor mode is 
	  ;; active. Removing it here is just tidying up.
	  (remove-hook 'comint-output-filter-functions
		       'x-symbol-comint-output-filter))))))

;;;###autoload
(defun proof-x-symbol-config-output-buffer ()
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


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Initialize x-symbol-support on load-up if user has asked for it
;;
;; FIXME: this initialization seems to result in x-symbol-language not
;; being set properly.  We let this be called on demand instead.
;(if (proof-ass x-symbol-enable) 
;      (proof-x-symbol-initialize))

(provide 'proof-x-symbol)
;; End of proof-x-symbol.el
