;; proof-splash.el -- Splash welcome screen for Proof General
;;
;; Copyright (C) 1998-2001 LFCS Edinburgh. 
;; Author:    David Aspinall
;; License:   GPL (GNU GENERAL PUBLIC LICENSE)
;;
;; $Id$
;;
;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Customization of splash screen (was in proof-config)

(defcustom proof-splash-enable t
  "*If non-nil, display a splash screen when Proof General is loaded."
  :type 'boolean
  :group 'proof-user-options)

(defcustom proof-splash-time 2
  "Minimum number of seconds to display splash screen for.
The splash screen may be displayed for a couple of seconds longer than
this, depending on how long it takes the machine to initialise 
Proof General."
  :type 'number
  :group 'proof-general-internals)

(defcustom proof-splash-contents
  '(list
    nil
;;; Remove the text for now: XEmacs makes a mess of displaying the
;;; transparent parts of the gif (at least, on all machines I have seen)
;;;    (proof-get-image "pg-text" t)
    nil
    (proof-get-image "ProofGeneral")
    nil
    "Welcome to"
    (concat proof-assistant " Proof General!")
    nil
    (substring proof-general-version
	       (string-match "Version [^ ]+ " 
			     proof-general-version)
	       (match-end 0))
    nil
    "(C) LFCS, University of Edinburgh, 2002."
    nil
    nil
"    Please send problems and suggestions to support@proofgeneral.org, 
     or use the menu command Proof-General -> Submit bug report."
    nil
    (unless (or proof-running-on-XEmacs proof-running-on-Emacs21)
     "For a better Proof General experience, please use XEmacs or Emacs 21.X"))
  "Evaluated to configure splash screen displayed when entering Proof General.
A list of the screen contents.  If an element is a string or an image
specifier, it is displayed centred on the window on its own line.  
If it is nil, a new line is inserted."
  :type 'sexp
  :group 'proof-general-internals)

(defconst proof-splash-extensions 
  (if (featurep 'proof-config) nil
    ;; Display additional hint if we guess we're being loaded
    ;; by shell script rather than find-file.
    '(list
      "To start using Proof General, visit a proof script file"
      "for your prover, using C-x C-f or the \"File\" menu.")))

(defconst proof-splash-welcome "*Proof General Welcome*"
  "Name of the Proof General splash buffer.")

;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;; Compatibility between Emacs/XEmacs.
(if (string-match "XEmacs" emacs-version)
  ;; Constant nil function
  (defun proof-emacs-imagep (img)
    "See if IMG is an Emacs 21 image descriptor (returns nil since not E21)."
    nil)
  (defun proof-emacs-imagep (img)
    "See if IMG is an Emacs 21 image descriptor."
    (and (listp img) (eq (car img) 'image))))


;; could be in proof-utils 
(defun proof-get-image (name &optional nojpeg default)
  "Construct an image instantiator for an image, or string failing that.
Different formats are chosen from according to what can be displayed.
Unless NOJPEG is set, try jpeg first. Then try gif, then xpm.
Gif filename depends on colour depth of display.
DEFAULT gives return value in case image not valid."
  (let ((jpg (vector 'jpeg :file
		     (concat proof-images-directory name ".jpg")))
	(gif (vector 'gif :file
		     (concat proof-images-directory 
			     name
			     (or (and
				  (fboundp 'device-pixel-depth)
				  (> (device-pixel-depth) 8)
				  ".gif")
				 ;; Low colour gif for poor displays
				 ".8bit.gif"))))
	(xpm (vector 'xpm :file
		     (concat proof-images-directory name ".xpm")))
	(validfn (lambda (inst)
		   (and (valid-instantiator-p inst 'image)
			(file-readable-p (aref inst 2)))))
	img)
  (cond
   ((and window-system proof-running-on-XEmacs (featurep 'jpeg) (not nojpeg)
	 (funcall validfn jpg))
    jpg)
   ((and window-system proof-running-on-XEmacs (featurep 'gif) (funcall validfn gif))
    gif)
   ((and window-system proof-running-on-XEmacs (featurep 'xpm) (funcall validfn xpm))
    xpm)
   ;; Support GNU Emacs 21
   ((and
     proof-running-on-Emacs21
     (setq img
	   (find-image
	    (list
	     (list :type 'jpeg
		   :file (concat proof-images-directory name ".jpg"))
	     (list :type 'gif
		   :file (concat proof-images-directory name ".gif"))
	     (list :type 'xpm
		   :file (concat proof-images-directory name ".xpm"))))))
    img)
   (t
    (or default (concat "[ image " name " ]"))))))

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
				 ((and (fboundp 'glyphp)
				       (glyphp glyph))
				  (glyph-width glyph))
				 ((proof-emacs-imagep glyph)
				  (car (image-size glyph 'inpixels)))
				 (t
				  (error
				   "proof-splash-centre-spaces: bad arg")))))
    (+ left-margin
       (round (/ (/ (- fill-area-width glyph-pixwidth) 2) avg-pixwidth)))))
  
;; We take some care to preserve the users window configuration
;; underneath the splash screen.  This is just to be polite.
;; FIXME: not as polite as it could be: if minibuffer is active,
;; this may deactivate it.
(defun proof-splash-remove-screen (conf)
  "Remove splash screen and restore window config to CONF."
  (let
      ((splashbuf (get-buffer proof-splash-welcome)))
    (if splashbuf
	(progn
	  (if (get-buffer-window splashbuf)
	      ;; Restore the window config if splash is being displayed
	      (progn
		(kill-buffer splashbuf)
		(set-window-configuration conf)
		(if proof-running-on-XEmacs
		    (redraw-frame nil t)))
	    (kill-buffer splashbuf))))))

(defvar proof-splash-seen nil
  "Flag indicating the user has been subjected to a welcome message.")

;;;###autoload
(defun proof-splash-display-screen (&optional timeout)
  "Save window config and display Proof General splash screen.
If TIMEOUT is non-nil, time out outside this function, definitely
by end of configuring proof mode. 
Otherwise, timeout inside this function after 10 seconds or so."
 (interactive "P")
  (let
      ;; Keep win config explicitly instead of pushing/popping because
      ;; if the user switches windows by hand in some way, we want
      ;; to ignore the saved value.  Unfortunately there seems to
      ;; be no way currently to remove the top item of the stack.
      ((winconf   (current-window-configuration))
       (splashbuf (get-buffer-create proof-splash-welcome))
       (after-change-functions nil)	; no font-lock, thank-you.
       (pop-up-frames nil)		; display in the same frame.
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
	 ((and proof-running-on-XEmacs
	       (vectorp s)
	       (valid-instantiator-p s 'image))
	  (let ((gly (make-glyph s)))
	    (indent-to (proof-splash-centre-spaces gly))
	    (set-extent-begin-glyph (make-extent (point) (point)) gly)))
	 ((proof-emacs-imagep s)
	  (indent-to (proof-splash-centre-spaces s))
	  (insert-image s))
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
	       (add-timeout (if timeout proof-splash-time 10)
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
    (if timeout
	(add-hook 'proof-mode-hook 'proof-splash-timeout-waiter)
      ;; Otherwise, this was an "about" type of call, so we wait
      ;; for a key press or timeout event
      (proof-splash-timeout-waiter))
    (setq proof-splash-seen t)))

;;;###autoload
(defun proof-splash-message ()
  "Make sure the user gets welcomed one way or another."
  (interactive)
  (unless (or proof-splash-seen (noninteractive))
    (if proof-splash-enable
	(proof-splash-display-screen (not (interactive-p)))
      ;; Otherwise, a message
      (message "Welcome to %s Proof General!" proof-assistant))
    (setq proof-splash-seen t)))

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
  (if (and (input-pending-p)
	   (fboundp 'next-command-event)) ; 3.3: this function
					  ; disappeared from emacs, sigh
      (setq unread-command-events	
	    (cons (next-command-event) unread-command-events)))
  (remove-hook 'proof-mode-hook 'proof-splash-timeout-waiter))

(provide 'proof-splash)
;; End of proof-splash.
