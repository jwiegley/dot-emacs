;; proof-x-symbol.el  Support for x-symbol package
;;
;; Copyright (C) 1998 LFCS Edinburgh. 
;; Author: David Aspinall <da@dcs.ed.ac.uk>
;;
;; With thanks to David von Oheimb for providing original 
;; patches for using x-symbol with Isabelle Proof General.
;;
;; Maintainer:  Proof General maintainer <proofgen@dcs.ed.ac.uk>
;;
;; proof-x-symbol.el,v 2.4 1999/08/23 18:38:40 da Exp
;;

;; TODO: Move proof-x-symbol-support to proof-config.
;;       Add autoloads for this file.

(defcustom proof-x-symbol-support nil
  "*Whether to use x-symbol in Proof General buffers.
If you activate this variable, whether or not you get x-symbol support
depends on if your proof assistant supports it and it is enabled
inside your Emacs."
  :type 'boolean
  :group 'proof-general)

;; Idea is that Proof General will only let this next variable
;; become t if all the necessary infrastructure is in place.
(defvar proof-x-symbol-support-on nil
  "Non-nil if x-symbol support is currently switched on.")

(defun proof-x-symbol-toggle (&optional arg)
  "Toggle support for x-symbol.  With optional ARG, force on if ARG<>0"
  (interactive "p")
  (let ((enable  (or (and arg (> arg 0))
		     (if arg;;DvO to DA: why that difficult calculations?
			 (and (not (= arg 0))
			      (not proof-x-symbol-support-on))
		       (not proof-x-symbol-support-on)))))
    (if enable
	;; Check that support is correctly set up: exit if
	;; some condition is not satisfied.
	(cond
	 ((not (featurep 'x-symbol))
	  (error "Proof General: x-symbol package must be loaded into Emacs."))
	 ;; Check proof assistant specific settings here
	 ))
    ;; 
    (setq proof-x-symbol-support-on enable)))

;; Initialize x-symbol-support.
;; DvO: if uncommented here, i.e. invoked at initialization time, 
;;      it does not work because it cannot find x-symbol feature -- why?
;;      calling it in proof-shell-start at least works
;; (proof-x-symbol-toggle (if proof-x-symbol-support 1 0))

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

;; sets x-symbol mode for the current buffer
(defun proof-x-symbol-mode (enable)
    (setq x-symbol-language proof-assistant-symbol)
    (if (eq x-symbol-mode (not enable))
	(x-symbol-mode)) ;; DvO: this is a toggle
    ;; Needed ?  Should let users do this in the 
    ;; usual way, if it works.
    (if (and x-symbol-mode (not font-lock-mode));;DvO
	(font-lock-mode)
      (unless (featurep 'mule)(x-symbol-nomule-fontify-cstrings))));;DvO

;;DvO: where to invoke this? 
;;     calling it in proof-shell-start at least works
(defun proof-x-symbol-mode-all-buffers (enable)
  (if enable
      (add-hook 'proof-shell-insert-hook
		'proof-x-symbol-encode-shell-input)
      (remove-hook 'proof-shell-insert-hook
		   'proof-x-symbol-encode-shell-input)
  )
  (remove-hook 'comint-output-filter-functions
		   'x-symbol-comint-output-filter)
  (save-excursion
    (and proof-shell-buffer
	 (set-buffer proof-shell-buffer)
	 (proof-x-symbol-mode enable))
    (and proof-goals-buffer
	 (set-buffer proof-goals-buffer)
	 (proof-x-symbol-mode enable))
    (and proof-response-buffer
	 (set-buffer proof-response-buffer)
	 (proof-x-symbol-mode enable))))


;; FIXME da: shouldn't the next part be in x-symbol-isa.el ??
;; DvO: no, at least part of it has to remain outside x-symbol-isa.el, because
;;          it is required to register x-symbol-isa s.th. it can be autoloaded

;; name of minor isa mode
(defvar x-symbol-isa-name "Isabelle Symbols")

(defvar proof-general-isabelle-modes '(thy-mode isa-proofscript-mode 
		proof-response-mode isa-shell-mode isa-pbp-mode isasym-mode))
(defvar isa-modes '(isa-thy-mode isa-mode proofstate-mode))
;; major modes that  should invoke minor isa mode
(defvar x-symbol-isa-modes (cons 'shell-mode (cons 'isasym-mode 
			(append isa-modes proof-general-isabelle-modes))))


;; FIXME da: this (or something) needs to be put into a function with
;; a require on x-symbol, so we fail more gracefully.
(if (fboundp 'x-symbol-register-language)
    (progn
      (x-symbol-register-language 'isa 'x-symbol-isa x-symbol-isa-modes)
      ;; install auto-invocation
      (push (list x-symbol-isa-modes t ''isa) x-symbol-auto-mode-alist)
      (put 'isasym-mode 'font-lock-defaults '(isasym-font-lock-keywords))
      (defvar isasym-font-lock-keywords
	'(("\\\\<[A-Za-z][A-Za-z0-9_']*>" (0 font-lock-type-face))))))

(provide 'proof-x-symbol)
;; End of proof-x-symbol.el
