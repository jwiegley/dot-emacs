;; proof-x-symbol.el  Support for x-symbol package
;;
;; Copyright (C) 1998,9 LFCS Edinburgh. 
;; Author: David Aspinall <da@dcs.ed.ac.uk>
;;
;; With thanks to David von Oheimb for providing the original 
;; patches for using x-symbol with Isabelle Proof General, 
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
  (and (eq (console-type) 'x)
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
	 ;; utility fn
	 (error-or-warn	 
	  (lambda (str) (if error (error str) (warn str)))))
      ;;
      ;; Check that support is provided.
      (cond
       ;;
       ;; First, some checks on x-symbol.
       ;;
       ((and (not (featurep 'x-symbol-autoloads))
	     ;; try requiring it
	     (not (condition-case ()
		      (require 'x-symbol) ;; NB: lose all errors!
		    (t (featurep 'x-symbol)))))
	(funcall error-or-warn
 "Proof General: x-symbol package must be installed for x-symbol-support!
The package is available at http://www.fmi.uni-passau.de/~wedler/x-symbol"))
       ((not (eq (console-type) 'x))
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
       ((not (condition-case ()
		 (require xs-feature-sym) ;; NB: lose all errors!
	       (t (featurep xs-feature-sym))))
 (format
  "Proof General: for x-symbol support, you must provide a library %s.el"
  xs-feature))
       (t
	;;
	;; We've got everything we need!   So initialize.
	;; 
	(let*
	    ((xs-lang	     proof-assistant-symbol)
	     (xs-xtra-modes  proof-xsym-extra-modes)
	     (xs-std-modes   (list
			      ;; NB: there is a problem with
			      ;; initialization order here, these
			      ;; variables are set in script/shell mode
			      ;; initialization.  They ought to be set
			      ;; earlier, and enforced as part of the
			      ;; generic scheme.  For the time being,
			      ;; we use default constructed names
			      ;; [which every prover should follow]
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
	     (am-entry       (list proof-xsym-extra-modes t xs-lang))
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
	  ;; Put just the extra modes on the auto-mode-alist
	  (if xs-xtra-modes (push am-entry x-symbol-auto-mode-alist))
	  ;; Font lock support is optional
	  (if flks
	      (put symmode 'font-lock-defaults (list flks)))
	  ;;
	  ;; Finished.
	  (setq proof-x-symbol-initialized t))))))
;)

;;;###autoload
(defun proof-x-symbol-enable ()
  "Turn on or off support for x-symbol, initializing if necessary."
  (if ;(and proof-x-symbol-enable (not proof-x-symbol-initialized))
      proof-x-symbol-enable
      (progn
	(setq proof-x-symbol-enable nil) ; assume failure!
	(proof-x-symbol-initialize 'giveerrors)
	(setq proof-x-symbol-enable t)))
  (proof-x-symbol-mode-all-buffers))

;; A toggling function for the menu.
;;;###autload
(fset 'proof-x-symbol-toggle
      (proof-customize-toggle proof-x-symbol-enable))

(defun proof-x-symbol-decode-region (start end) 
  "Call (x-symbol-decode-region START END), if x-symbol support is enabled."
  (if proof-x-symbol-enable
      (x-symbol-decode-region start end)))

(defun proof-x-symbol-encode-shell-input ()
  "Encode shell input in the variable STRING.
A value for proof-shell-insert-hook."
  (and x-symbol-language
       (setq string
             (save-excursion
               (let ((language x-symbol-language)
                     (coding x-symbol-coding)
                     (selective selective-display))
                 (set-buffer (get-buffer-create "x-symbol comint"))
                 (erase-buffer)
                 (insert string)
                 (setq x-symbol-language language)
                 (x-symbol-encode-all nil coding))
               (prog1 (buffer-substring)
                 (kill-buffer (current-buffer)))))))

;; ### autoload
(defun proof-x-symbol-mode ()
  "Turn on/off x-symbol mode in current buffer, from proof-x-symbol-enable."
  (interactive)
  (save-excursion			; needed or point moves: why?
    (if proof-x-symbol-initialized
	(progn
	  (setq x-symbol-language proof-assistant-symbol)
	  (if (eq x-symbol-mode (not proof-x-symbol-enable))
	      ;; toggle x-symbol-mode
	      (x-symbol-mode))
	  ;; Font lock mode must be engaged for x-symbol to do its job
          ;; properly, at least when there is no mule around.
	  (if (and x-symbol-mode (not (featurep 'mule)))
	      (if (not font-lock-mode)
		  (font-lock-mode)
		;; Even if font-lock was on before we may need
		;; to refontify now that the patterns (and buffer
		;; contents) have changed. I think x-symbol
		;; ought to do this really!
		(font-lock-fontify-buffer)))))))
	  
(defun proof-x-symbol-mode-all-buffers ()
  "Activate/deactivate x-symbol mode in all Proof General buffers.
A subroutine of proof-x-symbol-enable."
  (proof-with-current-buffer-if-exists 
   proof-shell-buffer
   (proof-x-symbol-shell-config))
  (let
      ((bufs   (append
		(list proof-goals-buffer proof-response-buffer)
		(proof-buffers-in-mode proof-mode-for-script))))
    (while bufs
      ;; mapcar doesn't work with macros
      (proof-with-current-buffer-if-exists (car bufs)
					   (proof-x-symbol-mode))
      (setq bufs (cdr bufs)))))

;; #### autoload
(defun proof-x-symbol-shell-config ()
  "Configure the proof shell for x-symbol, if proof-x-symbol-support<>nil.
Assumes that the current buffer is the proof shell buffer."
  (if proof-x-symbol-initialized
      (progn
	(cond
	 (proof-x-symbol-enable
	  (if (and proof-xsym-activate-command 
		   (proof-shell-live-buffer))
	      (proof-shell-invisible-command 
	       proof-xsym-activate-command 'wait))
	  ;; Do the encoding as the first step of input manipulation
	  (add-hook 'proof-shell-insert-hook
		    'proof-x-symbol-encode-shell-input))
	 ((not proof-x-symbol-enable)
	  (if (and proof-xsym-deactivate-command 
		   (proof-shell-live-buffer))
	      (proof-shell-invisible-command 
	       proof-xsym-deactivate-command 'wait))
	  (remove-hook 'proof-shell-insert-hook
		       'proof-x-symbol-encode-shell-input)
	  (remove-hook 'comint-output-filter-functions
		       'x-symbol-comint-output-filter)))
	;; switch the mode on/off in the buffer
	(proof-x-symbol-mode))))



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
