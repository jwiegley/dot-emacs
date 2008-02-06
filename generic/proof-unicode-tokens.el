;; proof-unicode-tokens.el   Support Unicode tokens package
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
  (require 'unicode-tokens)) ; it's loaded dynamically at runtime

(defvar proof-unicode-tokens-initialised nil
  "Flag indicating whether or not we've performed startup.")

(defun proof-unicode-tokens-init ()
  "Initialise settings for unicode tokens from prover specific variables."
  (mapcar
   (lambda (var) ;; or defass?
     (if (boundp (proof-ass-symv var))
	 (set (intern (concat "unicode-tokens-" (symbol-name var)))
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
  (unicode-tokens-initialise)
  (setq proof-unicode-tokens-initialised t))
  
;;;###autoload
(defun proof-unicode-tokens-enable ()
  "Turn on or off Unicode tokens mode in Proof General script buffer.
This invokes `unicode-tokens-mode' to toggle the setting for the current
buffer, and then sets PG's option for default to match.
Also we arrange to have unicode tokens mode turn itself on automatically 
in future if we have just activated it for this buffer."
  (interactive)
  (when (proof-unicode-tokens-support-available) ;; loads unicode-tokens
    (unless proof-unicode-tokens-initialised
      (proof-unicode-tokens-init))
    (proof-unicode-tokens-set-global (not unicode-tokens-mode))))


;;;###autoload
(defun proof-unicode-tokens-set-global (flag)
  "Set global status of unicode tokens mode for PG buffers to be FLAG.
Turn on/off menu in all script buffers and ensure new buffers follow suit."
  (unless proof-unicode-tokens-initialised 
      (proof-unicode-tokens-init))
  (let ((hook (proof-ass-sym mode-hook)))
    (if flag
	(add-hook hook 'unicode-tokens-mode)
      (remove-hook hook 'unicode-tokens-mode))
    (proof-map-buffers 
      (proof-buffers-in-mode proof-mode-for-script)
      (unicode-tokens-mode (if flag 1 0)))
    (proof-unicode-tokens-shell-config)))

  
;;;
;;; Interface to custom to dynamically change tables (via proof-set-value)
;;;

(defun proof-token-name-alist ()
  "Function called after the current token name alist has been changed.
Switch off tokens in all buffers, recalculate maps, turn on again."
  (when proof-unicode-tokens-initialised ; not on startup
    (when (proof-ass unicode-tokens-enable)
      (proof-map-buffers 
       (proof-buffers-in-mode proof-mode-for-script)
       (unicode-tokens-mode 0)))
    (setq unicode-tokens-token-name-alist (proof-ass token-name-alist))
    (unicode-tokens-initialise)
    (when (proof-ass unicode-tokens-enable)
      (proof-map-buffers 
       (proof-buffers-in-mode proof-mode-for-script)
       (unicode-tokens-mode 1)))))
  
(defun proof-shortcut-alist ()
  "Function called after the shortcut alist has been changed.
Updates the input mapping for reading shortcuts."
  (when proof-unicode-tokens-initialised ; not on startup
    (setq unicode-tokens-shortcut-alist (proof-ass shortcut-alist))
    (unicode-tokens-initialise)))

;;;
;;; Interface to shell
;;;

(defun proof-unicode-tokens-activate-prover ()
  (when (and proof-xsym-activate-command 
	     (proof-shell-live-buffer)
	     (proof-shell-available-p))
    (proof-shell-invisible-command-invisible-result
     proof-xsym-activate-command)))

(defun proof-unicode-tokens-deactivate-prover ()
  (when (and proof-xsym-deactivate-command 
	     (proof-shell-live-buffer)
	     (proof-shell-available-p))
    (proof-shell-invisible-command-invisible-result
     proof-xsym-deactivate-command)))

;;; NB: we shouldn't bother load this if it's not enabled.
;;;###autoload
(defun proof-unicode-tokens-shell-config ()
  (when (proof-ass unicode-tokens-enable)
    (add-hook 'proof-shell-insert-hook
	      'proof-unicode-tokens-encode-shell-input)
    (proof-unicode-tokens-activate-prover))
  (unless (proof-ass unicode-tokens-enable)
    (remove-hook 'proof-shell-insert-hook
		 'proof-unicode-tokens-encode-shell-input)
    (proof-unicode-tokens-deactivate-prover)))

(defun proof-unicode-tokens-encode-shell-input ()
  "Encode shell input in the variable STRING.
A value for proof-shell-insert-hook."
  (if (proof-ass unicode-tokens-enable)
      (with-temp-buffer ;; TODO: better to do directly in *prover*
	(insert string)
	(unicode-tokens-unicode-to-tokens)
	(setq string (buffer-substring-no-properties
		      (point-min) (point-max))))))

(provide 'proof-unicode-tokens)
;; End of proof-unicode-tokens.el
