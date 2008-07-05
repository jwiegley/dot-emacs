;; proof-unicode-tokens2.el   Support Unicode tokens package
;;
;; Copyright (C) 2008 David Aspinall / LFCS Edinburgh
;; Author:    David Aspinall <David.Aspinall@ed.ac.uk>
;; License:   GPL (GNU GENERAL PUBLIC LICENSE)
;;
;; $Id$
;;

(eval-when-compile
  (require 'proof-utils) ; for proof-ass, proof-eval-when-ready-for-assistant
  (require 'cl))

(eval-when (compile)
  (require 'unicode-tokens2)) ; it's loaded dynamically at runtime

(defvar proof-unicode-tokens2-initialised nil
  "Flag indicating whether or not we've performed startup.")

(defun proof-unicode-tokens2-init ()
  "Initialise settings for unicode tokens from prover specific variables."
  (mapcar
   (lambda (var) ;; or defass?
     (if (boundp (proof-ass-symv var))
	 (set (intern (concat "unicode-tokens2-" (symbol-name var)))
	      (eval `(proof-ass ,var)))))
   '(charref-format
     token-format
     control-token-format
     token-name-alist
     glyph-list
     token-match
     control-token-match
     hexcode-match
     next-character-regexp
     token-prefix
     token-suffix
     shortcut-alist))
  (unicode-tokens2-initialise)
  (setq proof-unicode-tokens2-initialised t))
  
;;;###autoload
(defun proof-unicode-tokens2-enable ()
  "Turn on or off Unicode tokens mode in Proof General script buffer.
This invokes `unicode-tokens2-mode' to toggle the setting for the current
buffer, and then sets PG's option for default to match.
Also we arrange to have unicode tokens mode turn itself on automatically 
in future if we have just activated it for this buffer."
  (interactive)
  (when (proof-unicode-tokens2-support-available) ;; loads unicode-tokens2
    (unless proof-unicode-tokens2-initialised
      (proof-unicode-tokens2-init))
    (proof-unicode-tokens2-set-global (not unicode-tokens2-mode))))


;;;###autoload
(defun proof-unicode-tokens2-set-global (flag)
  "Set global status of unicode tokens mode for PG buffers to be FLAG.
Turn on/off menu in all script buffers and ensure new buffers follow suit."
  (unless proof-unicode-tokens2-initialised 
      (proof-unicode-tokens2-init))
  (let ((hook (proof-ass-sym mode-hook)))
    (if flag
	(add-hook hook 'unicode-tokens2-mode)
      (remove-hook hook 'unicode-tokens2-mode))
    (proof-map-buffers 
      (proof-buffers-in-mode proof-mode-for-script)
      (unicode-tokens2-mode (if flag 1 0)))
    (proof-unicode-tokens2-shell-config)))

  
;;;
;;; Interface to custom to dynamically change tables (via proof-set-value)
;;;

(defun proof-token-name-alist ()
  "Function called after the current token name alist has been changed.
Switch off tokens in all buffers, recalculate maps, turn on again."
  (when proof-unicode-tokens2-initialised ; not on startup
    (when (proof-ass unicode-tokens2-enable)
      (proof-map-buffers 
       (proof-buffers-in-mode proof-mode-for-script)
       (unicode-tokens2-mode 0)))
    (setq unicode-tokens2-token-name-alist (proof-ass token-name-alist))
    (unicode-tokens2-initialise)
    (when (proof-ass unicode-tokens2-enable)
      (proof-map-buffers 
       (proof-buffers-in-mode proof-mode-for-script)
       (unicode-tokens2-mode 1)))))
  
(defun proof-shortcut-alist ()
  "Function called after the shortcut alist has been changed.
Updates the input mapping for reading shortcuts."
  (when proof-unicode-tokens2-initialised ; not on startup
    (setq unicode-tokens2-shortcut-alist (proof-ass shortcut-alist))
    (unicode-tokens2-initialise)))

;;;
;;; Interface to shell
;;;


(defun proof-unicode-tokens2-activate-prover ()
  (when (and proof-xsym-activate-command 
	     (proof-shell-live-buffer)
	     (proof-shell-available-p))
    (proof-shell-invisible-command-invisible-result
     proof-xsym-activate-command)))

(defun proof-unicode-tokens2-deactivate-prover ()
  (when (and proof-xsym-deactivate-command 
	     ;; NB: clash with X-symbols since use same commands in prover!
	     (not (proof-ass x-symbol-enable))
	     (proof-shell-live-buffer)
	     (proof-shell-available-p))
    (proof-shell-invisible-command-invisible-result
     proof-xsym-deactivate-command)))

;;; NB: we shouldn't bother load this if it's not enabled.
;;;###autoload
(defun proof-unicode-tokens2-shell-config ()
  (when (proof-ass unicode-tokens2-enable)
    (add-hook 'proof-shell-insert-hook
	      'proof-unicode-tokens2-encode-shell-input)
    (proof-unicode-tokens2-activate-prover))
  (unless (proof-ass unicode-tokens2-enable)
    (remove-hook 'proof-shell-insert-hook
		 'proof-unicode-tokens2-encode-shell-input)
    (proof-unicode-tokens2-deactivate-prover)))

(defun proof-unicode-tokens2-encode-shell-input ()
  "Encode shell input in the variable STRING.
A value for proof-shell-insert-hook."
  (if (proof-ass unicode-tokens2-enable)
      (with-temp-buffer ;; TODO: better to do directly in *prover*
	(insert string)
	(unicode-tokens2-unicode-to-tokens)
	(setq string (buffer-substring-no-properties
		      (point-min) (point-max))))))

(provide 'proof-unicode-tokens2)
;; End of proof-unicode-tokens2.el
