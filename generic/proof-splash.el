;; proof-splash.el -- Splash welcome screen for Proof General
;;
;; Copyright (C) 1998 LFCS Edinburgh. 
;; Author: David Aspinall
;; Maintainer:  Proof General maintainer <proofgen@dcs.ed.ac.uk>
;;
;; $Id$
;;
;; NB: try not to use functions which autoload large packages
;; here, to minimise the delay before splash screen is shown. 
;;

(require 'proof-config)			; for 

(defconst proof-splash-welcome "*Proof General Welcome*"
  "Name of the Proof General splash buffer.")

(defun proof-splash-display-image (name &optional nojpeg)
  "Construct an image instantiator for an image, or string failing that.
Different formats are chosen from according to what can be displayed.
Unless NOJPEG is set, try jpeg first. Then try gif.
Gif filename depends on colour depth of display."
  (let ((jpg (vector 'jpeg :file
		     (concat proof-images-directory name ".jpg"))))
  (cond
   ((and window-system (featurep 'jpeg) (not nojpeg)
	 ;; Actually, jpeg can fail even if it is compiled in.
	 ;; FIXME: this test doesn't work, though: still gives
	 ;; t when visiting the file displays failure message.
	 ;; What's the correct test?
	 (valid-instantiator-p jpg 'image))
    jpg)
   ((and window-system (featurep 'gif))
    (vector 'gif :file
	    (concat proof-images-directory 
		    (concat name
			    (or (and
				 (fboundp 'device-pixel-depth)
				 (> (device-pixel-depth) 8)
				 ".gif")
				;; Low colour gif for poor displays
				".8bit.gif")))))
   (t
    (concat "[ image " name " ]")))))

;; Would be nice to get rid of this variable, but it's tricky
;; to construct a hook function, with a higher order function,
;; which can easily remove itself.
(defvar proof-splash-timeout-conf nil
  "Holds timeout ID and previous window config for proof splash screen.")

(defun proof-splash-centre-spaces (glyph)
  "Return number of spaces to insert in order to center given glyph or string.
Borrowed from startup-center-spaces."
  (let* ((avg-pixwidth     (round (/ (frame-pixel-width) (frame-width))))
	 (fill-area-width  (* avg-pixwidth (- fill-column left-margin)))
	 (glyph-pixwidth   (cond ((stringp glyph) 
				  (* avg-pixwidth (length glyph)))
				 ((glyphp glyph)
				  (glyph-width glyph))
				 (t
				  (error
				   "proof-splash-centre-spaces: bad arg")))))
    (+ left-margin
       (round (/ (/ (- fill-area-width glyph-pixwidth) 2) avg-pixwidth)))))
  
;; We take some care to preserve the users window configuration
;; underneath the splash screen.  This is just to be polite.
(defun proof-splash-remove-screen (conf)
  "Remove splash screen and restore window config to CONF."
  (let
      ((splashbuf (get-buffer proof-splash-welcome)))
    (if splashbuf
	(progn
	  (if (get-buffer-window splashbuf)
	      ;; Restore the window config if splash is being displayed
	      (set-window-configuration conf))
	  ;; Destroy splash buffer 
	  (kill-buffer splashbuf)))))

(defvar proof-splash-seen nil
  "Flag indicating the user has been subjected to a welcome message.")

;;;###autoload
(defun proof-splash-display-screen ()
  "Save window config and display Proof General splash screen."
  (let
      ;; Keep win config explicitly instead of pushing/popping because
      ;; if the user switches windows by hand in some way, we want
      ;; to ignore the saved value.  Unfortunately there seems to
      ;; be no way currently to remove the top item of the stack.
      ((winconf   (current-window-configuration))
       (splashbuf (get-buffer-create proof-splash-welcome))
       (after-change-functions nil) ; no font-lock, thank you
       (splash-contents (append
			 (eval proof-splash-contents)
			 (eval proof-splash-extensions)))
       s)
    (with-current-buffer splashbuf
      (erase-buffer)
      ;; [ Don't use do-list to avoid loading cl ]
      (while splash-contents
	(setq s (car splash-contents))
	(cond
	 ((and (vectorp s)		; vectorp for FSF
	       (valid-instantiator-p s 'image))
	  (let ((gly (make-glyph s)))
	    (indent-to (proof-splash-centre-spaces gly))
	    (set-extent-begin-glyph (make-extent (point) (point)) gly)))
	 ((stringp s)
	  (indent-to (proof-splash-centre-spaces s))
	  (insert s)))
	(newline)
	(setq splash-contents (cdr splash-contents)))
      (goto-char (point-min))
      (set-buffer-modified-p nil)
	(delete-other-windows (display-buffer splashbuf))
	(if (fboundp 'redisplay-frame)
	    (redisplay-frame nil t)	; XEmacs special
	  (sit-for 0))
	(setq proof-splash-timeout-conf
	      (cons
	       (add-timeout proof-splash-time
			    'proof-splash-remove-screen
			    winconf)
	       winconf)))
    ;; PROBLEM: when to call proof-splash-display-screen?
    ;; We'd like to call it during loading/initialising.  But it's
    ;; hard to make the screen persist after loading because of the
    ;; action of display-buffer invoked after the mode function
    ;; during find-file.
    ;; To approximate the best behaviour, we assume that this file is
    ;; loaded by a call to proof-mode.  We display the screen now and add
    ;; a wait procedure temporarily to proof-mode-hook which prevents
    ;; redisplay until proof-splash-time has elapsed. 
    (add-hook 'proof-mode-hook 'proof-splash-timeout-waiter)
    (setq proof-splash-seen t)))

(defun proof-splash-message ()
  "Make sure the user gets welcomed one way or another."
  (unless proof-splash-seen
    (message "Welcome to %s Proof General!" proof-assistant)
    (setq proof-splash-seen t)
    (sit-for 0)))

(defun proof-splash-timeout-waiter ()
  "Wait for proof-splash-timeout or input, then remove self from hook."
  (while (and (get-buffer proof-splash-welcome)
	      (not (input-pending-p)))
    (if proof-running-on-XEmacs
	(sit-for 0 t)			; XEmacs: wait without redisplay
      ; (sit-for 1 0 t)))		; FSF: NODISP arg seems broken
      (sit-for 0)))
  (if (get-buffer proof-splash-welcome)
      (proof-splash-remove-screen (cdr proof-splash-timeout-conf)))
  ;; Make sure timeout is stopped
  (disable-timeout (car proof-splash-timeout-conf))
  (if (input-pending-p)
      (setq unread-command-event (next-command-event)))
  (remove-hook 'proof-mode-hook 'proof-splash-timeout-waiter))

(provide 'proof-splash)
;; End of proof-splash.
