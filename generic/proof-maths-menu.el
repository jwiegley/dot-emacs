;; proof-maths-menu.el   Support for maths menu mode package
;;
;; Copyright (C) 2007 LFCS Edinburgh / David Aspinall
;; Author:    David Aspinall <David.Aspinall@ed.ac.uk>
;; License:   GPL (GNU GENERAL PUBLIC LICENSE)
;;
;;
;; With thanks to Dave Love for the original maths menu code,
;; provided at http://www.loveshack.ukfsn.org/emacs/
;;
;; $Id$
;;
;; =================================================================
;;
;; NB: maths-menu is bundled with Proof General in lib/, and PG will select
;; it's own version before any other version on the Emacs load path.
;; If you want to override this, simply load your version before
;; starting Emacs, with (require 'maths-menu).
;;

(require 'proof-utils)

;;;###autoload
(defun proof-maths-menu-support-available ()
  "A test to see whether maths-menu support is available."
  (and
   (not proof-running-on-XEmacs) ;; not XEmacs compatible
   (or (featurep 'maths-menu)
       ;; *should* always succeed unless bundled version broken
       (proof-try-require 'maths-menu))
   ;; Load any optional prover-specific config in <foo>-maths-menu.el
   (or (proof-try-require (proof-ass-sym maths-menu)) t)))

(eval-when-compile
  (proof-maths-menu-support-available))

(defun proof-maths-menu-set-global (flag)
  "Set global status of maths-menu mode for PG buffers to be FLAG.
Turn on/off menu in all script buffers and ensure new buffers follow suit."
  (let ((hook (proof-ass-sym mode-hook)))
    (if flag
	(add-hook hook 'maths-menu-mode)
      (remove-hook hook 'maths-menu-mode))
    (proof-map-buffers 
      (proof-buffers-in-mode proof-mode-for-script)
      (maths-menu-mode (if flag 1 0)))))

  
  
;;;###autoload
(defun proof-maths-menu-enable ()
  "Turn on or off maths-menu mode in Proof General script buffer.
This invokes `maths-menu-mode' to toggle the setting for the current
buffer, and then sets PG's option for default to match.
Also we arrange to have maths menu mode turn itself on automatically 
in future if we have just activated it for this buffer."
  (interactive)
  (if (proof-maths-menu-support-available) ;; will load maths-menu-mode
      (proof-maths-menu-set-global (not maths-menu-mode))))

;;
;; On start up, adjust automode according to user setting
;;
(if (and (proof-ass maths-menu-enable) 
	 (proof-maths-menu-support-available))
    (proof-maths-menu-set-global t))


(provide 'proof-maths-menu)
;; End of proof-maths-menu.el
