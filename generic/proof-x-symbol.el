;; proof-x-symbol.el  Support for x-symbol package
;;
;; Copyright (C) 1998,9 LFCS Edinburgh. 
;; Author: David Aspinall <da@dcs.ed.ac.uk>
;;
;; With thanks to David von Oheimb for providing the original 
;; patches for using x-symbol with Isabelle Proof General, 
;; and suggesting improvements here.
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
  (unless proof-x-symbol-initialized
    (let* 
;;; Values for x-symbol-register-language are constructed
;;; from proof-assistant-symbol.
;;; To initialise we call, for example:
;;;
;;;  (x-symbol-register-language 'isa x-symbol-isa x-symbol-isa-modes)
;;;
	((assistant	(symbol-name proof-assistant-symbol))
	 (xs-lang	proof-assistant-symbol)
	 (xs-feature	(intern (concat "x-symbol-" assistant)))
	 (xs-modes	(intern (concat "x-symbol-" assistant "-modes")))
	 (am-entry      (list xs-modes t xs-lang))
	 (symmode-nm	(concat assistant "sym-mode"))
	 (sym-flks	(intern (concat symmode-nm "-font-lock-keywords")))
	 (symmode       (intern symmode-nm))
	 ;;
	 ;; Standard modes for using x-symbol. 
	 ;;
	 ;; NB: there is a problem with initialization order here,
	 ;; these variables are set in script/shell mode initialization.
	 ;; They ought to be set earlier, and enforced as part of the
	 ;; generic scheme.   For the time being, these should appear 
	 ;; on xs-modes (later that setting could be optional).
;	 (stnd-modes	(list
;			 proof-mode-for-script
;			 proof-mode-for-shell
;			 proof-mode-for-pbp
;			 proof-mode-for-response))
	 ;; 
	 ;;
	 ;; utility fn
	 (error-or-warn	 
	  (lambda (str) (if error (error str) (warn str)))))

      ;;
      ;; Now check that support is provided.
      ;;
      (cond
       ;;
       ;; First, some checks on x-symbol.
       ;;
       ((and (not (featurep 'x-symbol-autoloads))
	     ;; try requiring it
	     (not (condition-case ()
		      (require 'x-symbol) ;; NB: lose any errors!
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
       ((or 
	 (not (boundp xs-modes))
	 ;; FIXME: add here a test that we can find file
	 ;; x-symbol-<xs-lang>.el but maybe let x-symbol-load it.
	 ;; [might be okay to do condition-case require as above]
	 )
	(funcall error-or-warn
 (format
  "Proof General: for x-symbol support, you must set %s."
  (symbol-name xs-modes))))
       (t
	;;
	;; We've got everything we need!   So initialize.
	;; 
	(x-symbol-initialize)    ;; No harm in doing this multiple times
	(x-symbol-register-language xs-lang xs-feature (eval xs-modes))
	(push am-entry x-symbol-auto-mode-alist)
	;; Font lock support is optional
	(if (boundp sym-flks)
	    (put symmode 'font-lock-defaults (list sym-flks)))
	;;
	;; Finished.
	(setq proof-x-symbol-initialized t))))))

;;;###autoload
(defun proof-x-symbol-enable ()
  "Turn on or off support for x-symbol, initializing if necessary."
  (if (and proof-x-symbol-enable (not proof-x-symbol-initialized))
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
	  (if (eq x-symbol-mode 
		  (not proof-x-symbol-enable))
	      (x-symbol-mode)) ;; DvO: this is a toggle
	  ;; Needed ?  Should let users do this in the 
	  ;; usual way, if it works.
	  (if (and x-symbol-mode 
		   (not font-lock-mode));;DvO
	      (font-lock-mode)
	    ;; da: Is this supposed to be called only if we don't turn on
	    ;; font-lock???
	    (unless (featurep 'mule)
	      (if (fboundp 'x-symbol-nomule-fontify-cstrings)
		  (x-symbol-nomule-fontify-cstrings))))))));;DvO


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
