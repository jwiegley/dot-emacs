;; proof-splash.el -- Splash welcome screen for Proof General
;;
;; Copyright (C) 1998-2005 LFCS Edinburgh. 
;; Author:    David Aspinall
;; License:   GPL (GNU GENERAL PUBLIC LICENSE)
;;
;; $Id$
;;
;;

(require 'proof-site)

;;
;; Customization of splash screen 
;;

(defcustom proof-splash-enable t
  "*If non-nil, display a splash screen when Proof General is loaded."
  :type 'boolean
  :group 'proof-user-options)

(defcustom proof-splash-time 3
  "Minimum number of seconds to display splash screen for.
The splash screen may be displayed for a wee while longer than
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
    (concat "Version " proof-general-short-version ".")
    nil
    (concat "(C) LFCS, University of Edinburgh " proof-general-version-year)
    nil
    nil
"    Please report problems at http://proofgeneral.inf.ed.ac.uk/trac
    Visit the Proof General wiki at http://proofgeneral.inf.ed.ac.uk/wiki"
    nil
    "Find out more about Emacs via the Help menu.")
  "Evaluated to configure splash screen displayed when entering Proof General.
A list of the screen contents.  If an element is a string or an image
specifier, it is displayed centred on the window on its own line.  
If it is nil, a new line is inserted."
  :type 'sexp
  :group 'proof-general-internals)

(defconst proof-splash-startup-msg 
  '(if (featurep 'proof-config) nil
     ;; Display additional hint if we guess we're being loaded
     ;; by shell script rather than find-file.
     '(list
       "To start using Proof General, visit a proof script file"
       "for your prover, using C-x C-f or the File menu."))
  "Additional form evaluated and put onto splash screen.")

(defconst proof-splash-welcome "*Proof General Welcome*"
  "Name of the Proof General splash buffer.")

;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(defsubst proof-emacs-imagep (img)
  "See if IMG is an Emacs image descriptor."
  (and (listp img) (eq (car img) 'image)))


(defun proof-get-image (name &optional nojpeg default)
  "Construct an image instantiator for an image, or string failing that.
Different formats are chosen from according to what can be displayed.
Unless NOJPEG is set, try jpeg first. Then try gif, then xpm.
Gif filename depends on colour depth of display.
DEFAULT gives return value in case image not valid."
  (let ((jpg (vector 'jpeg :file
		     (concat proof-images-directory name ".jpg")))
	(gif (vector 'gif :file
		     (concat proof-images-directory ".gif")))
	img)
  (cond
   (window-system
    (find-image
     (list
      (list :type 'jpeg
	    :file (concat proof-images-directory name ".jpg"))
      (list :type 'gif
	    :file (concat proof-images-directory name ".gif")))))
   (t
    (or default (concat "[ image " name " ]"))))))

;; Would be nice to get rid of this variable, but it's tricky
;; to construct a hook function, with a higher order function,
;; which can easily remove itself.
(defvar proof-splash-timeout-conf nil
  "Holds timeout ID and previous window config for proof splash screen.")

(defun proof-splash-centre-spaces (glyph)
  "Return number of spaces to insert in order to center given GLYPH or string.
Borrowed from startup-center-spaces."
  (let* ((avg-pixwidth     (round (/ (frame-pixel-width) (frame-width))))
	 (fill-area-width  (* avg-pixwidth (- fill-column left-margin)))
	 (glyph-pixwidth   (cond ((stringp glyph) 
				  (* avg-pixwidth (length glyph)))
				 ((proof-emacs-imagep glyph)
				  (car (image-size glyph 'inpixels)))
				 (t
				  (error
				   "proof-splash-centre-spaces: bad arg")))))
    (+ left-margin
       (round (/ (/ (- fill-area-width glyph-pixwidth) 2) avg-pixwidth)))))

;; We take some care to preserve the users window configuration
;; underneath the splash screen.  This is just to be polite.
;; NB: not as polite as it could be: if minibuffer is active,
;; this may deactivate it.
;; NB2: There is something worse here: pending input 
;; causes this function to spoil the mode startup, if the splash
;; buffer is killed before the input has been processed.
;; Symptom is ProofGeneral mode instead of the native script mode.
;; 

(defun proof-splash-remove-screen (&optional nothing)
  "Remove splash screen and restore window config."
  (let ((splashbuf (get-buffer proof-splash-welcome)))
    (proof-splash-unset-frame-titles)
    (if (and 
	 splashbuf
	 proof-splash-timeout-conf)
	(progn
	  (if (get-buffer-window splashbuf)
	      ;; Restore the window config if splash is being displayed
	      (if (cdr proof-splash-timeout-conf)
		  (set-window-configuration (cdr proof-splash-timeout-conf))))
	  ;; Indicate removed splash screen; disable timeout
	  (disable-timeout (car proof-splash-timeout-conf))
	  (setq proof-splash-timeout-conf nil)
	  (proof-splash-remove-buffer)))))

(defun proof-splash-remove-buffer ()
  "Remove the splash buffer if it's still present."
  ;; FIXME: Removing buffer here causes bug on loading if key is
  ;; pressed in XEmacs: breaks loading of script buffer mode,
  ;; presumably because some events are related to splash buffer which
  ;; has died.   Sometimes even worse: XEmacs dumps core or
  ;; gives error about unallocated event.  (21.4.8)
  (let
      ((splashbuf (get-buffer proof-splash-welcome)))
    (if splashbuf 
	;; Kill should be right, but it can cause core dump
	;; (kill-buffer splashbuf)
	(if (eq (selected-window) (window-buffer 
				   (selected-window)))
	    (bury-buffer splashbuf)))))

(defvar proof-splash-seen nil
  "Flag indicating the user has been subjected to a welcome message.")

;;;###autoload
(defun proof-splash-display-screen (&optional timeout)
  "Save window config and display Proof General splash screen.
If TIMEOUT is non-nil, time out outside this function, definitely
by end of configuring proof mode.
Otherwise, timeout inside this function after 10 seconds or so."
 (interactive "P")
 (proof-splash-set-frame-titles)
 (let*
     ;; Keep win config explicitly instead of pushing/popping because
     ;; if the user switches windows by hand in some way, we want
     ;; to ignore the saved value.  Unfortunately there seems to
     ;; be no way currently to remove the top item of the stack.
     ((winconf   (current-window-configuration))
      (curwin	  (get-buffer-window (current-buffer)))
      (curfrm    (and curwin (window-frame curwin)))
      (splashbuf (get-buffer-create proof-splash-welcome))
      (after-change-functions nil)	; no font-lock, thank-you.
      ;; NB: maybe leave next one in for frame-crazy folk
      ;;(pop-up-frames nil)		; display in the same frame.
      (splash-contents (append
			(eval proof-splash-contents)
			(eval proof-splash-startup-msg)))
      s)
   (with-current-buffer splashbuf
     (erase-buffer)
     ;; [ Don't use do-list to avoid loading cl ]
     (while splash-contents
       (setq s (car splash-contents))
       (cond
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
     (let* ((splashwin     (display-buffer splashbuf))
	    (splashfm      (window-frame splashwin))
	    ;; Only save window config if we're on same frame
	    (savedwincnf   (if (eq curfrm splashfm) winconf)))
       (delete-other-windows splashwin)
       (sit-for 10)
       (setq proof-splash-timeout-conf
	     (cons
	      (add-timeout (if timeout proof-splash-time 10)
			   'proof-splash-remove-screen nil)
	      savedwincnf))))
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
  (unless (or proof-splash-seen noninteractive)
    (if proof-splash-enable
	(progn
	  ;; disable ordinary emacs splash
	  (setq inhibit-startup-message t)
	  (proof-splash-display-screen (not (interactive-p))))
      ;; Otherwise, a message
      (message "Welcome to %s Proof General!" proof-assistant))
    (setq proof-splash-seen t)))

(defun proof-splash-timeout-waiter ()
  "Wait for proof-splash-timeout or input, then remove self from hook."
  (while (and proof-splash-timeout-conf ;; timeout still active
	      (not (input-pending-p)))
    (sit-for 0))
  (if proof-splash-timeout-conf         ;; not removed yet
      (proof-splash-remove-screen))
  (if (fboundp 'next-command-event) ; 3.3: Emacs removed this
      (if (input-pending-p)
	  (setq unread-command-events
		(cons (next-command-event) unread-command-events))))
  (remove-hook 'proof-mode-hook 'proof-splash-timeout-waiter))

(defvar proof-splash-old-frame-title-format nil)

(defun proof-splash-set-frame-titles ()
  (let ((instance-name (concat
			(if (not (zerop (length proof-assistant)))
			   (concat proof-assistant " "))
		       "Proof General")))
    (setq proof-splash-old-frame-title-format frame-title-format)
    (setq frame-title-format 
	  (concat instance-name ":   %b"))))

(defun proof-splash-unset-frame-titles ()
  (when proof-splash-old-frame-title-format
    (setq frame-title-format proof-splash-old-frame-title-format)
    (setq proof-splash-old-frame-title-format nil)))

(provide 'proof-splash)
;; End of proof-splash.
