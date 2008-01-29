;; proof-unicode-tokens.el   Support Unicode tokens package
;;
;; Copyright (C) 2008 David Aspinall / LFCS Edinburgh
;; Author:    David Aspinall <David.Aspinall@ed.ac.uk>
;; License:   GPL (GNU GENERAL PUBLIC LICENSE)
;;

(eval-when-compile
  (require 'proof-utils) ; for proof-ass, proof-eval-when-ready-for-assistant
  (require 'cl))

(eval-when (compile)
  (if (not (featurep 'xemacs))
      (require 'unicode-tokens))) ; it's loaded dynamically at runtime


;;;###autoload
(defun proof-unicode-tokens-support-available ()
  "A test to see whether unicode tokens support is available."
  (and
   (not (featurep 'xemacs)) ;; not XEmacs compatible
   (or (featurep 'unicode-tokens)
       (proof-try-require 'unicode-tokens))
   ;; Requires prover-specific config in <foo>-unicode-tokens.el
   (proof-try-require (proof-ass-sym unicode-tokens))))

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
     token-name-alist
     glyph-list
     token-match
     hexcode-match
     token-prefix
     token-suffix
     shortcut-alist))
  (unicode-tokens-initialise)
  (setq proof-unicode-tokens-initialised t))
  
(defun proof-unicode-tokens-set-global (flag)
  "Set global status of unicode tokens mode for PG buffers to be FLAG.
Turn on/off menu in all script buffers and ensure new buffers follow suit."
  (let ((hook (proof-ass-sym mode-hook)))
    (if flag
	(add-hook hook 'unicode-tokens-mode)
      (remove-hook hook 'unicode-tokens-mode))
    (proof-map-buffers 
      (proof-buffers-in-mode proof-mode-for-script)
      (unicode-tokens-mode (if flag 1 0)))
    (proof-unicode-tokens-shell-config)))

  
  
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

	
	    


;;
;; On start up, adjust automode according to user setting
;;
(proof-eval-when-ready-for-assistant 
    (if (and (proof-ass unicode-tokens-enable) 
	     (proof-unicode-tokens-support-available))
	(proof-unicode-tokens-set-global t)))

(provide 'proof-unicode-tokens)
;; End of proof-unicode-tokens.el
