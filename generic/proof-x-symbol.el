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

;; Idea is that Proof General will only let this next variable
;; become t if all the necessary infrastructure is in place.
(defvar proof-x-symbol-support-on nil
  "Non-nil if x-symbol support is currently switched on.")

(defvar proof-x-symbol-initialized nil
  "Non-nil if x-symbol support has been initialized.")

;;;###autoload
(defun proof-x-symbol-toggle (&optional arg)
  "Toggle support for x-symbol.  With optional ARG, force on if ARG<>0.
In other words, you can type M-1 M-x proof-x-symbol-toggle to turn it
on, M-0 M-x proof-x-symbol-toggle to turn it off."
  (interactive "p")
  (let ((enable  (or (and arg (> arg 0))
		     (if arg;;DvO to DA: why that difficult calculations?
			 ;; da: see explanation I've put in docstring.
			 ;; probably over the top!
			 (and (not (= arg 0))
			      (not proof-x-symbol-support-on))
		       (not proof-x-symbol-support-on)))))
    ;; Initialize if it hasn't been done already
    (if (and (eq proof-x-symbol-support-on 'init) enable)
	(proof-x-symbol-initialize 'giveerrors))
    ;; Turn on or off support in prover
    ;; FIXME: need to decide how best to do this?
    ;; maybe by editing proof-init-cmd, but also want to turn
    ;; x-symbol on/off during use perhaps.
    ;; Hacking init command is a bit ugly!
    (if (and enable proof-xsym-activate-command)
	(proof-shell-invisible-command proof-xsym-activate-command))
    (if (and (not enable) proof-xsym-deactivate-command)
	(proof-shell-invisible-command proof-xsym-activate-command))
    (setq proof-x-symbol-support-on enable)))

(defun proof-x-symbol-initialize (&optional error)
  "Initialize x-symbol support for Proof General, if possible.
If ERROR is non-nil, give error on failure, otherwise a warning."
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
 "Proof General: x-symbol package must be installed for x-symbol-support!"))
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


(defun proof-x-symbol-decode-region (start end) 
  "Call (x-symbol-decode-region START END), if x-symbol support is enabled."
  (if proof-x-symbol-support-on
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

(defun proof-x-symbol-mode ()
  "Hook function to turn on/off x-symbol mode in the current buffer."
    (setq x-symbol-language proof-assistant-symbol)
    (if (eq x-symbol-mode 
	    (not proof-x-symbol-support-on))
	(x-symbol-mode)) ;; DvO: this is a toggle
    ;; Needed ?  Should let users do this in the 
    ;; usual way, if it works.
    (if (and x-symbol-mode 
	     (not font-lock-mode));;DvO
	(font-lock-mode)
      (unless (featurep 'mule)
	(x-symbol-nomule-fontify-cstrings))));;DvO

;; FIXME: this is called in proof-shell-start, but perhaps
;; it would be better enabled via hooks for the mode 
;; functions?  Or somewhere else?  (Problem at the moment
;; is that we don't get x-symbol in script buffers before
;; proof assistant is started, presumably).
;;
;; Suggestion: add functions
;;
;;  proof-x-symbol-activate
;;  proof-x-symbol-deactivate
;;
;; which do what this function does, but also add/remove
;; hooks for shell mode, etc, 'proof-x-symbol-mode. 
;; (or variation of that function to just turn x-symbol mode
;;  *on*).

;; ### autoload
(defun proof-x-symbol-mode-all-buffers ()
  "Activate/deactivate x-symbol in Proof General shell, goals, and response buffer."
  (if proof-x-symbol-initialized
      (progn
	(if proof-x-symbol-support-on
	    (add-hook 'proof-shell-insert-hook
		      'proof-x-symbol-encode-shell-input)
	  (remove-hook 'proof-shell-insert-hook
		       'proof-x-symbol-encode-shell-input)
	  (remove-hook 'comint-output-filter-functions
		       'x-symbol-comint-output-filter))
	(save-excursion
	  (and proof-shell-buffer
	       (set-buffer proof-shell-buffer)
	       (proof-x-symbol-mode))
	  (and proof-goals-buffer
	       (set-buffer proof-goals-buffer)
	       (proof-x-symbol-mode))
	  (and proof-response-buffer
	       (set-buffer proof-response-buffer)
	       (proof-x-symbol-mode))))))


;;
;; Initialize x-symbol-support on load-up if user has asked for it
;;
(if proof-x-symbol-support (proof-x-symbol-initialize))

;; Need a hook in shell to do this, maybe
;; (if proof-x-symbol-initialized (proof-x-symbol-toggle 1))



(provide 'proof-x-symbol)
;; End of proof-x-symbol.el
