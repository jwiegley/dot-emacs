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
     token-suffix))
  (unicode-tokens-initialise))
  
(defun proof-unicode-tokens-set-global (flag)
  "Set global status of unicode tokens mode for PG buffers to be FLAG.
Turn on/off menu in all script buffers and ensure new buffers follow suit."
  (let ((hook (proof-ass-sym mode-hook)))
    (if flag
	(add-hook hook 'unicode-tokens-mode)
      (remove-hook hook 'unicode-tokens-mode))
    (proof-map-buffers 
      (proof-buffers-in-mode proof-mode-for-script)
      (unicode-tokens-mode (if flag 1 0)))))

  
  
;;;###autoload
(defun proof-unicode-tokens-enable ()
  "Turn on or off Unicode tokens mode in Proof General script buffer.
This invokes `maths-menu-mode' to toggle the setting for the current
buffer, and then sets PG's option for default to match.
Also we arrange to have maths menu mode turn itself on automatically 
in future if we have just activated it for this buffer."
  (interactive)
  (if (proof-unicode-tokens-support-available) ;; will load maths-menu-mode
      (proof-unicode-tokens-set-global (not unicode-tokens-mode))))

;;
;; On start up, adjust automode according to user setting
;;
(proof-eval-when-ready-for-assistant 
    (if (and (proof-ass unicode-tokens-enable) 
	     (proof-unicode-tokens-support-available))
	(progn
	  (proof-unicode-tokens-init)
	  (proof-unicode-tokens-set-global t))))

(provide 'proof-maths-menu)
;; End of proof-maths-menu.el
