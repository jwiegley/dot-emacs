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
;; NB: mmm-mode is bundled with Proof General.  If you have installed
;; mmm-mode already, PG will use that version instead of the bundled
;; version.
;;
;; Configuration for the prover is expected to reside in <foo>-mmm.el
;; It should define an MMM submode class called <foo>.

;;;###autoload
(defun proof-mmm-support-available ()
  "A test to see whether mmm support is available."
  (and
   (or (featurep 'mmm-auto)
       (or (proof-try-require 'mmm-auto) ; local install?
	   (progn
	     ;; try bundled version
	     (setq load-path
		   (cons proof-home-directory "mmm/" load-path))
	     (proof-try-require 'mmm-auto))))
   ;; Load prover-specific config in <foo>-mmm.el
   (proof-try-require (proof-ass-sym mmm))))


;;;###autoload
(defun proof-mmm-enable ()
  "Turn on or off MMM mode in Proof General script buffers.
This invokes `mmm-mode' with appropriate setting for current
buffer, and adjusts 
on MMM regions for the prover's class."
  (if (proof-mmm-support-available)
      (progn
	(if (proof-ass mmm-enable)
	    (setq mmm-mode-ext-classes-alist
		  (cons (list (proof-ass-sym mode) nil 
			      proof-assistant-symbol)
			mmm-mode-ext-classes-alist))
	  (setq mmm-mode-ext-classes-alist
		(remassoc (proof-ass-sym mode)
			  mmm-mode-ext-classes-alist)))
	(mmm-mode (if (proof-ass mmm-enable) 1)))))



(provide 'proof-mmm)
;; End of proof-mmm.el
