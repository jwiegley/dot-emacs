;; proof-splash.el -- Splash welcome screen for Proof General
;;
;; Copyright (C) 1998 LFCS Edinburgh. 
;; Author: David Aspinall
;; Maintainer:  Proof General maintainer <proofgen@dcs.ed.ac.uk>
;;
;; $Id$
;;

(require 'annotations)
(defconst proof-welcome "*Proof General Welcome*"
  "Name of the Proof General splash buffer.")

(defconst proof-display-splash-image
  ;; Use jpeg if we can, otherwise assume gif will work.
  (if (featurep 'jpeg)
      (cons 'jpeg
	    (concat proof-internal-images-directory 
		    "ProofGeneral.jpg"))
  (cons 'gif
	(concat proof-internal-images-directory 
		(concat "ProofGeneral"
			(or (and
			     (fboundp 'device-pixel-depth)
			     (> (device-pixel-depth) 8)
			     ".gif")
			    ;; Low colour gif for poor displays
			    ".8bit.gif")))))
  "Format and File name of Proof General Image.")

(defcustom proof-display-splash 
  (valid-instantiator-p
   (vector (car proof-display-splash-image)
		 :file (cdr proof-display-splash-image)) 'image)
  "*Display splash screen when Proof General is loaded."
  :type 'boolean
  :group 'proof)

(defcustom proof-internal-display-splash-time 4
  "Minimum number of seconds to display splash screen for.
If the machine gets to the end of proof-mode faster than this,
we wait for the remaining time.  Must be a value less than 40."
  :type 'integer
  :group 'proof-internal)

;; We take some care to preserve the users window configuration
;; underneath the splash screen.  This is just to be polite.
(defun proof-remove-splash-screen (conf)
  "Make function to remove splash screen and restore window config to conf."
  `(lambda ()
     (and ;; If splash buffer is still alive 
      (get-buffer proof-welcome)
      (if (get-buffer-window (get-buffer proof-welcome))
	  ;; Restore the window config if splash is being displayed
	  (set-window-configuration ,conf)
	t)
      ;; And destroy splash buffer.
      (kill-buffer proof-welcome))))

(defun proof-display-splash-screen ()
  "Save window config and display Proof General splash screen.
No effect if proof-display-splash-time is zero."
  (interactive)
  (if proof-display-splash
      (let*
	  ((splashbuf   (get-buffer-create proof-welcome))
	   (imglyph	(make-glyph
			 (list (vector (car proof-display-splash-image) ':file
				       (cdr proof-display-splash-image)))))
	   ;; Keep win config explicitly instead of pushing/popping because
	   ;; if the user switches windows by hand in some way, we want
	   ;; to ignore the saved value.  Unfortunately there seems to
	   ;; be no way currently to remove the top item of the stack.
	   (removefn    (proof-remove-splash-screen
			 (current-window-configuration))))
	(save-excursion
	  (set-buffer splashbuf)
	  (erase-buffer)
	  ;; FIXME: centre display better.  support FSFmacs.
	  (insert "\n\n\n\t\t")
	  (insert-char ?\  (/ (length proof-assistant) 2))
	  (insert "    Welcome to\n\t\t  "
		  proof-assistant " Proof General!\n\n\n\t\t ")
	  (let ((ann (make-annotation imglyph))) ; reveal-annotation doesn't
	    (reveal-annotation ann))	;      autoload, so use let form.  
	  (insert "\n\n")
	  (delete-other-windows (display-buffer splashbuf)))
	;; Start the timer with a dummy value of 40 secs, to time the
	;; loading of the rest of the mode.  This is a kludge to make
	;; sure that the splash screen appears at least throughout the
	;; load (which shouldn't last 40 secs!).  But if the load is
	;; triggered by something other than a call to proof-mode,
	;; the splash screen *will* appear for 40 secs (unless the
	;; user kills it or switches buffer).
	(redisplay-frame nil t)
	(start-itimer proof-welcome removefn 40))))

;; PROBLEM: when to call proof-display-splash-screen?  Effect we'd
;; like is to call it during loading/initialising.  It's hard to make
;; the screen persist after loading because of the action of
;; display-buffer acting after the mode function during find-file.
;; To approximate the best behaviour, we assume that this file is
;; loaded by a call to proof-mode.  We display the screen now and add
;; a wait procedure temporarily to proof-mode-hook which prevents
;; redisplay until at least proof-internal-display-splash-time
;; has elapsed. 

;; Display the screen ASAP...
(proof-display-splash-screen)

(defun proof-wait-for-splash-proof-mode-hook-fn ()
  "Wait for a while displaying splash screen, then remove self from hook." 
  (if proof-display-splash
       (let ((timer (get-itimer proof-welcome)))
	 (if timer
	     (if (< (- 40 proof-internal-display-splash-time)
		    (itimer-value timer))
		 ;; Splash has still not been seen for all of
		 ;; internal-display-splash-time, set the timer
		 ;; for the remaining time...
		 (progn
		   (set-itimer-value timer
		    (- proof-internal-display-splash-time
		       (- 40 (itimer-value timer))))
		   ;; and wait until it finishes or user-input
		   (while (and (get-itimer proof-welcome)
			       (sit-for 1 t)))
		   ;; If timer still running, run function
		   ;; and delete timer.
		   (if (itimer-live-p timer)
		       (progn
			 (funcall (itimer-function timer))
			 (delete-itimer timer))))))))
  (remove-hook 'proof-mode-hook 'proof-wait-for-splash-hook))

(add-hook 'proof-mode-hook 'proof-wait-for-splash-proof-mode-hook-fn)


(provide 'proof-splash)
;; End of proof-splash.
