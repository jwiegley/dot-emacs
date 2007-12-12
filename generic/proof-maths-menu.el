;; proof-maths-menu.el   Support for maths menu mode package
;;
;; Copyright (C) 2007 LFCS Edinburgh / David Aspinall
;; Author:    David Aspinall <David.Aspinall@ed.ac.uk>
;; License:   GPL (GNU GENERAL PUBLIC LICENSE)
;;
;;
;; With thanks to Dave Love for the original maths menu code.
;; The maths menu file is from XXXXXXXXX
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
   (or (featurep 'maths-menu)
       ;; *should* always succeed unless bundled version broken
       (proof-try-require 'maths-menu))
   ;; Load any optional prover-specific config in <foo>-maths-menu.el
   (or (proof-try-require (proof-ass-sym maths-menu)) t)))

(eval-when-compile
  (proof-maths-menu-support-available))

;; The following function is called by the menu item for
;; maths-menu.  It is an attempt at an intuitive behaviour
;; without confusing the user with extra "in this buffer" 
;; and "everywhere" options.  We simply make the global
;; option track the last setting made for any buffer.
;; The menu toggle displays the status of the buffer
;; (as seen in the modeline) rather than the PG setting.

(defvar maths-menu-modes-list nil)

(defun proof-maths-menu-set-global (flag)
  "Set global status of maths-menu mode for PG buffers to be FLAG."
  (let ((automode-entry (list (proof-ass-sym mode) nil
			      proof-assistant-symbol)))
    (if flag
	(add-to-list 'maths-menu-mode automode-entry)
      (setq maths-menu-modes-list 
	    (delete automode-entry maths-menu-modes-list)))))
  
;;;###autoload
(defun proof-maths-menu-enable ()
  "Turn on or off maths-menu mode in Proof General script buffer.
This invokes `maths-menu-mode' to toggle the setting for the current
buffer, and then sets PG's option for default to match.
Also we arrange to have maths menu mode turn itself on automatically 
in future if we have just activated it for this buffer."
  (interactive)
  (if (proof-maths-menu-support-available) ;; will load maths-menu-mode
      (progn
	;; Make sure auto mode follows PG's global setting. (NB: might
	;; do this only if global state changes, but by the time we
	;; get here, (proof-ass maths-menu-mode) has been set.
	(proof-maths-menu-set-global (not maths-menu-mode))
	(maths-menu-mode t))))

;;
;; On start up, adjust automode according to user setting
;;
(if (and (proof-ass maths-menu-enable) 
	 (proof-maths-menu-support-available))
    (proof-maths-menu-set-global t))


(provide 'proof-maths-menu)
;; End of proof-maths-menu.el
