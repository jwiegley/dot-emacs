;; proof-mmm.el   Support for MMM mode package
;;
;; Copyright (C) 2003 LFCS Edinburgh / David Aspinall
;; Author:    David Aspinall <David.Aspinall@ed.ac.uk>
;; License:   GPL (GNU GENERAL PUBLIC LICENSE)
;;
;; The MMM package is at http://mmm-mode.sourceforge.net/
;;
;; With thanks to Stefan Monnier for pointing me to this package, 
;; and Michael Abraham Shulman for providing it.
;;
;; $Id$
;;
;; =================================================================
;;
;; NB: mmm-mode is bundled with Proof General, and PG will select
;; it's own version before any other version on the Emacs load path.
;; If you want to override this, simply load your version before
;; starting Emacs, with (require 'mmm-auto).
;;
;; Configuration for the prover is expected to reside in <foo>-mmm.el
;; It should define an MMM submode class called <foo>.

;;;###autoload
(defun proof-mmm-support-available ()
  "A test to see whether mmm support is available."
  (and
   (or (featurep 'mmm-auto)
       (progn
	 ;; put bundled version on load path
	 (setq load-path
	       (cons 
		(concat proof-home-directory "mmm/") 
		load-path))
	 ;; *should* always succeed unless bundled version broken
	 (proof-try-require 'mmm-auto)))
   ;; Load prover-specific config in <foo>-mmm.el
   (proof-try-require (proof-ass-sym mmm))))


;; The following function is called by the menu item for
;; MMM-Mode.  It is an attempt at an intuitive behaviour
;; without confusing the user with extra "in this buffer" 
;; and "everywhere" options.  We simply make the global
;; option track the last setting made for any buffer.
;; The menu toggle displays the status of the buffer
;; (as seen in the modeline) rather than the PG setting.

(defun proof-mmm-set-global (flag)
  "Set global status of MMM mode for PG buffers to be FLAG."
  (let ((automode-entry (list (proof-ass-sym mode) nil
			      proof-assistant-symbol)))
    (if flag
	(add-to-list 'mmm-mode-ext-classes-alist
		     automode-entry)
      (setq mmm-mode-ext-classes-alist
	    (delete automode-entry
		    mmm-mode-ext-classes-alist)))
    ;; make sure MMM obeys the mmm-mode-ext-classes-alist
    (unless (eq mmm-global-mode t)
      (setq mmm-global-mode 'pg-use-mode-ext-classes-alist))))
  
;;;###autoload
(defun proof-mmm-enable ()
  "Turn on or off MMM mode in Proof General script buffer.
This invokes `mmm-mode' to toggle the setting for the current
buffer, and then sets PG's option for default to match.
Also we arrange to have MMM mode turn itself on automatically 
in future if we have just activated it for this buffer."
  (interactive)
  (if (proof-mmm-support-available) ;; will load mmm-mode
      (progn
	;; Make sure auto mode follows PG's global setting. (NB: might
	;; do this only if global state changes, but by the time we
	;; get here, (proof-ass mmm-mode) has been set.
	(proof-mmm-set-global (not mmm-mode))
	(mmm-mode))))

;;
;; On start up, adjust automode according to user setting
;;
(if (and (proof-ass mmm-enable) 
	 (proof-mmm-support-available))
    (proof-mmm-set-global t))


(provide 'proof-mmm)
;; End of proof-mmm.el
