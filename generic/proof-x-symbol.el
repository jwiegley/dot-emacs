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
;; $Id$
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
		     (if arg
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
    (if enable
	;; Turn it on
	(progn
	  (add-hook 'proof-shell-insert-hook
		    'proof-x-symbol-encode-shell-input))
      ;; Turn it off
      (remove-hook  'proof-shell-insert-hook
		    'proof-x-symbol-encode-shell-input))

    (setq proof-x-symbol-support-on enable)))

;; Initialize x-symbol-support.
;; (proof-x-symbol-toggle (if proof-x-symbol-support 1 0))

;(defun proof-x-symbol-mode 
;  (if proof-x-symbol-support-on
;      (setq x-symbol-language 

(defun proof-x-symbol-decode-region (start end)
  "Decode region START to END using x-symbol-decode-all.
No action if proof-x-symbol-support-on is nil."
  (if proof-x-symbol-support-on
      (save-restriction
	(narrow-to-region start end)
	(x-symbol-decode-all)
	(unless (featurep 'mule) (x-symbol-nomule-fontify-cstrings)))))


(defun proof-x-symbol-encode-shell-input ()
  "Encode shell input in the variable STRING.
A value for proof-shell-insert-hook."
  (and x-symbol-mode x-symbol-language
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
  (if proof-x-symbol-support-on
      (progn
	(setq x-symbol-language proof-assistant-symbol)
	(if (not x-symbol-mode)
	    (x-symbol-mode))
	;; Needed ?  Should let users do this in the 
	;; usual way, if it works.
	(if (not font-lock-mode) 
	    (font-lock-mode)))))
 ;; 
 ;;(setq comint-input-sender 'x-symbol-comint-send)


;; FIXME: where do we need the next function?
(defun proof-x-symbol-comint-send (proc string)
  (and x-symbol-mode x-symbol-language
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
                 (kill-buffer (current-buffer))))))
  (funcall x-symbol-orig-compint-input-sender proc string))




(provide 'proof-x-symbol)
;; End of proof-x-symbol.el


