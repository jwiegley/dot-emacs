;; proof-splash.el -- Splash welcome screen for Proof General
;;
;; Copyright (C) 1998 LFCS Edinburgh. 
;; Author: David Aspinall
;; Maintainer:  Proof General maintainer <proofgen@dcs.ed.ac.uk>
;;
;; $Id$
;;
;; TODO: centre display better.  support FSFmacs.
;;
;; NB: try not to use cl or other autoloaded macro sets here,
;; to minimise delay before splash screen is shown. 
;;

(require 'proof-site)

(defconst proof-splash-welcome "*Proof General Welcome*"
  "Name of the Proof General splash buffer.")

(defun proof-splash-display-image (name &optional nojpeg)
  "Construct an image instantiator for an image, or string failing that.
Different formats are chosen from according to what can be displayed.
Unless NOJPEG is set, try jpeg first. Then try gif.
Gif filename depends on colour depth of display."
  (cond
   ((and window-system (featurep 'jpeg) (not nojpeg))
    (vector 'jpeg :file
	    (concat proof-images-directory name ".jpg")))
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
    (concat "[ image " name " ]"))))

(defcustom proof-splash-inhibit
  nil
  "*Non-nil prevents splash screen display when Proof General is loaded."
  :type 'boolean
  :group 'proof)

(defcustom proof-splash-extensions nil
  "*Prover specific extensions of splash screen.
These are evaluated and appended to proof-splash-contents, which see."
  :type 'sexp
  :group 'proof-config)
  
  
(defcustom proof-splash-contents
  (list
   nil
   nil
   (proof-splash-display-image "text_proof" t)
   (proof-splash-display-image "text_general" t)
   nil
   (proof-splash-display-image "ProofGeneral")
   nil
   "Welcome to"
   (concat proof-assistant " Proof General!")
   nil)
  "List defining splash screen displayed when Proof General is started.
If an element is a string or an image specifier, it is displayed
centred on the window on its own line.  If it is nil, a new line is
inserted."
  :type 'sexp
  :group 'proof-general-internals)

(defcustom proof-splash-time 1.5
  "Minimum number of seconds to display splash screen for.
The splash screen may be displayed for a couple of seconds longer than
this, depending on how long it takes the machine to initialise proof mode."
  :type 'number
  :group 'proof-general-internals)

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

(defun proof-splash-display-screen ()
  "Save window config and display Proof General splash screen.
Only do it if proof-splash-display is nil."
  (if (and
       ;; Next check avoids XEmacs giving "Arithmetic Error"
       ;; during byte compilation.
       (if (fboundp 'noninteractive) (not (noninteractive)) t)
       (not proof-splash-inhibit))
    (let
	;; Keep win config explicitly instead of pushing/popping because
	;; if the user switches windows by hand in some way, we want
	;; to ignore the saved value.  Unfortunately there seems to
	;; be no way currently to remove the top item of the stack.
	((winconf   (current-window-configuration))
	 (splashbuf (get-buffer-create proof-splash-welcome))
	 (after-change-functions nil) ; no font-lock, thank you
	 (splash-contents (append
			   proof-splash-contents
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
	       winconf))))))

;; PROBLEM: when to call proof-splash-display-screen?
;; We'd like to call it during loading/initialising.  But it's
;; hard to make the screen persist after loading because of the
;; action of display-buffer invoked after the mode function
;; during find-file.
;; To approximate the best behaviour, we assume that this file is
;; loaded by a call to proof-mode.  We display the screen now and add
;; a wait procedure temporarily to proof-mode-hook which prevents
;; redisplay until proof-splash-time has elapsed. 

;; Display the screen ASAP...
(proof-splash-display-screen)

(defun proof-splash-timeout-waiter ()
  "Wait for proof-splash-timeout, then remove self from hook."
  (while (and (get-buffer proof-splash-welcome)
	      (not (input-pending-p)))
    (if (string-match "XEmacs" emacs-version)
	(sit-for 0 t)			; XEmacs: wait without redisplay
      (sit-for 0)))			; FSF: FIXME
  (if (get-buffer proof-splash-welcome)
      (proof-splash-remove-screen (cdr proof-splash-timeout-conf)))
  ;; Make sure timeout is stopped
  (disable-timeout (car proof-splash-timeout-conf))
  (if (input-pending-p)
      (setq unread-command-event (next-command-event)))
  (remove-hook 'proof-mode-hook 'proof-splash-timeout-waiter))

(add-hook 'proof-mode-hook 'proof-splash-timeout-waiter)

(provide 'proof-splash)
;; End of proof-splash.
