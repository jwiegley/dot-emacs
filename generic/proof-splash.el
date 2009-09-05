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
    (proof-get-image "pg-text" t)
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
    :link '("    Read the "
	    "Proof General documentation"
	   (lambda (button) (info "ProofGeneral")))
    :link '("    Please report problems at "
	    "Proof General trac"
	   (lambda (button)
	     (browse-url "http://proofgeneral.inf.ed.ac.uk/trac"))
	   "Browse http://proofgeneral.inf.ed.ac.uk/trac")
    :link '("Visit the " "Proof General wiki"
	   (lambda (button)
	     (browse-url "http://proofgeneral.inf.ed.ac.uk/wiki"))
	   "Browse http://proofgeneral.inf.ed.ac.uk/wiki")
    nil
     :link '("Find out about Emacs on the Help menu -- start with the "
	     "Emacs Tutorial" (lambda (button) (help-with-tutorial)))
    nil
    "See this screen again with Proof-General -> About"
    )
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

(defvar proof-splash-timeout-conf nil
  "Holds timeout ID for proof splash screen.")

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

(defun proof-splash-remove-screen (&optional nothing)
  "Remove splash screen and restore window config."
  (let ((splashbuf (get-buffer proof-splash-welcome)))
    (proof-splash-unset-frame-titles)
    (if (and
	 splashbuf
	 proof-splash-timeout-conf)
	(progn
	  (with-current-buffer splashbuf
	    (View-quit))
	  ;; Indicate removed splash screen; disable timeout
	  (disable-timeout proof-splash-timeout-conf)
	  (setq proof-splash-timeout-conf nil)))))

(defvar proof-splash-seen nil
  "Flag indicating the user has been subjected to a welcome message.")

(defun proof-splash-insert-contents ()
  "Insert splash buffer contents into current buffer."
     (let ((splash-contents (append
			     (eval proof-splash-contents)
			     (eval proof-splash-startup-msg)))
	   (inhibit-read-only t)
	   s)
       (erase-buffer)
       ;; [ Don't use do-list to avoid loading cl ]
       (while splash-contents
	 (setq s (car splash-contents))
	 (cond
	  ((proof-emacs-imagep s)
	   (indent-to (proof-splash-centre-spaces s))
	   (insert-image s))
	  ((eq s :link)
	   (setq splash-contents (cdr splash-contents))
	   (let ((spec (car splash-contents)))
	     (if (functionp spec)
		 (setq spec (funcall spec)))
	     (indent-to (proof-splash-centre-spaces
			 (concat (car spec) (cadr spec))))
	     (insert (car spec))
	     (insert-button (cadr spec)
			    'face (list 'link)
			    'action (nth 2 spec)
			    'help-echo (concat "mouse-2, RET: "
					       (or (nth 3 spec)
						   "Follow this link"))
			    'follow-link t)))
	  ((stringp s)
	   (indent-to (proof-splash-centre-spaces s))
	   (insert s)))
	 (newline)
	 (setq splash-contents (cdr splash-contents)))
       (goto-char (point-min))
       (set-buffer-modified-p nil)))

;;;###autoload
(defun proof-splash-display-screen (&optional timeout)
  "Save window config and display Proof General splash screen.
If TIMEOUT is non-nil, arrange for a time-out to occur outside this function."
 (interactive "P")
 (proof-splash-set-frame-titles)
 (let* ((splashbuf (get-buffer-create proof-splash-welcome)))
   (with-current-buffer splashbuf
     (proof-splash-insert-contents))
   (view-buffer splashbuf 'kill-buffer)
   (if timeout
       (progn
	 (setq proof-splash-timeout-conf
	       (add-timeout proof-splash-time
			    'proof-splash-remove-screen nil))
	 (add-hook 'proof-mode-hook 'proof-splash-timeout-waiter)))
   (setq proof-splash-seen t)))

(defalias 'pg-about 'proof-splash-display-screen)

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
	      (not unread-command-events))
    (sit-for 1))
  (if proof-splash-timeout-conf         ;; not removed yet
      (proof-splash-remove-screen))
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
