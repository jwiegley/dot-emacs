;; proof-toolbar.el    Toolbar for Proof General
;;
;; Copyright (C) 1998,9  David Aspinall / LFCS.
;; Author:    David Aspinall <da@dcs.ed.ac.uk>
;; License:   GPL (GNU GENERAL PUBLIC LICENSE)
;;
;; $Id$
;;
;; NB: FSF GNU Emacs has no toolbar facility. This file defines
;; proof-toolbar-menu which holds the same commands and is put on the
;; menubar by proof-toolbar-setup (perhaps surprisingly).
;; Could consider moving the generic table stuff to proof-menu now.
;;
;; Toolbar is just for the scripting buffer, currently.
;;
;;
;; TODO (minor things):
;;
;; 1. edit-toolbar cannot edit proof toolbar (even in a proof mode)
;; Need a variable containing  a specifier or similar.
;; (defvar proof-toolbar-specifier nil
;;   "Specifier for proof toolbar.")
;; This doesn't seem worth fixing until XEmacs toolbar implementation
;; settles a bit.  Enablers don't work too well at the moment.

;; 2. It's a little bit tricky to add prover-specific items:
;; presently it must be done before this file is loaded.
;; We could improve on that by generating everything on-thy-fly
;; in proof-toolbar-setup.

;; 3. We could consider automatically disabling buttons which are
;; not configured for the prover, e.g. if proof-info-command is
;; not set, then the Info button should not be shown. 


;;; IMPORT declaration  (only to suppress warnings for byte compile)
;;; NB: can't put require proof-script here: leads to circular
;;; requirement via proof-menu.
;; (require 'proof-script)
;; (autoload 'proof-shell-live-buffer "proof-shell")
;; (autoload 'proof-shell-restart "proof-shell")


(require 'proof-config)			; for <PA>-toolbar-entries

;;
;; See `proof-toolbar-entries-default' and
;;     `<PA>-toolbar-entries' in proof-config
;; for the default generic toolbar and 
;; the per-prover toolbar contents variable.
;;

;;
;; Function, icon, button names
;; 

(defun proof-toolbar-function (token)
  (intern (concat "proof-toolbar-" (symbol-name token))))

(defun proof-toolbar-icon (token)
  (intern (concat "proof-toolbar-" (symbol-name token) "-icon")))

(defun proof-toolbar-enabler (token)
  (intern (concat "proof-toolbar-" (symbol-name token) "-enable-p")))

(defun proof-toolbar-function-with-enabler (token)
  (intern (concat "proof-toolbar-" (symbol-name token) "-with-enabler-p")))

;;
;; Now the toolbar icons and buttons
;; 

(defun proof-toolbar-make-icon (tle)
  "Make icon variable and icon list entry from a PA-toolbar-entries entry."
  (let* ((icon     (car tle))
	 (tooltip  (nth 2 tle))
	 (iconname (symbol-name icon))
	 (iconvar  (proof-toolbar-icon icon)))
    ;; first declare variable
    ;;  (eval
    ;;  `(defvar ,iconvar nil
    ;;  ,(concat 
    ;;   "Glyph list for " iconname " button in Proof General toolbar.")))
    ;; FIXME: above doesn't quite work right.  However, we only lose
    ;; the docstring which is no big deal.
    ;; now the list entry
    (if tooltip
	(list (list iconvar iconname)))))
  

(defun proof-toolbar-make-toolbar-item (tle)
  "Make a toolbar button descriptor from a PA-toolbar-entries entry."
  (let*
      ((token	      (nth 0 tle))
       (includep      (or (< (length tle) 5) (eval (nth 4 tle))))
       (menuname      (and includep (nth 1 tle)))
       (tooltip       (and includep (nth 2 tle)))
       (existsenabler (nth 3 tle))
       (enablep	      (and proof-toolbar-use-button-enablers
			   (>= emacs-major-version 21)
			   existsenabler))
       (enabler	      (proof-toolbar-enabler token))
       (enableritem   (if enablep (list enabler) t))
       (buttonfn      (proof-toolbar-function token))
       (buttonfnwe    (proof-toolbar-function-with-enabler token))
       (icon	      (proof-toolbar-icon token))
       (actualfn      
	(if (or enablep (not existsenabler))
	    buttonfn
	  ;; Add the enabler onto the function if necessary.
	  (eval `(defun ,buttonfnwe ()
		   (interactive)
		   (if (,enabler) 
		       (call-interactively (quote ,buttonfn))
		     (message ,(concat "Button \"" menuname "\" disabled")))))
	  buttonfnwe)))
    (if tooltip	;; no tooltip means menu-only item
	(if proof-running-on-XEmacs
	    (list (vector icon actualfn enableritem tooltip))
	  (list (append (list icon actualfn token
			      :help tooltip)
			(if enabler (list :enable (list enabler)))))))))
		


;;
;; Code for displaying and refreshing toolbar
;;

(defvar proof-toolbar nil
  "Proof mode toolbar button list.  Set in proof-toolbar-build.
For GNU Emacs, this holds a keymap.")

(deflocal proof-toolbar-itimer nil
  "itimer for updating the toolbar in the current buffer")

;;;###autoload
(defun proof-toolbar-setup ()
  "Initialize Proof General toolbar and enable it for current buffer.
If proof-mode-use-toolbar is nil, change the current buffer toolbar
to the default toolbar."
  (interactive)
  (if
   (and ;; Check support in Emacs
    (or (and (featurep 'tool-bar)	; GNU Emacs tool-bar library
	     (member 'xpm image-types))	; and XPM support
	(and (featurep 'toolbar)	; or XEmacs toolbar library
	     (featurep 'xpm)))		; and XPM support
    ;; Check support in Window system
    (memq (if proof-running-on-XEmacs (console-type) window-system)
	  '(x mswindows gtk)))

      ;; Toolbar support is possible.  
      (progn
	;; Check the toolbar has been built.
	(or proof-toolbar (proof-toolbar-build))

	;; Now see if user wants toolbar
	;; or not (this can be changed dyamically).
	(if proof-toolbar-enable

	    ;; Enable the toolbar in this buffer
	    (if proof-running-on-Emacs21
		;; For GNU Emacs, we make a local tool-bar-map
		(set (make-local-variable 'tool-bar-map) proof-toolbar)
	      
	      ;; For XEmacs, we set the toolbar specifier for this buffer.
	      (set-specifier default-toolbar proof-toolbar (current-buffer))
	      ;; We also setup refresh hackery
	      (proof-toolbar-setup-refresh))

	  ;; Disable the toolbar in this buffer
	  (if proof-running-on-Emacs21
	      ;; For GNU Emacs, we remove local value of tool-bar-map
	      (kill-local-variable 'tool-bar-map)
	    ;; For XEmacs, we remove specifier and disable refresh.
	    (remove-specifier default-toolbar (current-buffer))
	    (proof-toolbar-disable-refresh)))

	;; Update the display
	(sit-for 0))))

(defun proof-toolbar-build ()
  "Build proof-toolbar."
  (let 
      ((icontype (if (and (boundp 'device-pixel-depth)
			  (< (device-pixel-depth) 16))
		     ;; Select 8bit xpm's if we've got a 
		     ;; limited colour depth.
		     ".8bit.xpm" ".xpm"))

       (proof-toolbar-icon-list
	;; List of icon variable names and their associated image
	;; files.  A list of lists of the form (VAR IMAGE).  IMAGE is
	;; the root name for ;an image file in proof-images-directory.
	;; The toolbar code expects to find files IMAGE.xpm or
	;; IMAGE.8bit.xpm and chooses the best one for the display
	;; properites.
	(apply 'append
	       (mapcar 'proof-toolbar-make-icon 
		       (proof-ass toolbar-entries))))

       (proof-toolbar-button-list
	;; A toolbar descriptor evaluated in proof-toolbar-setup.
	;; Specifically, a list of sexps which evaluate to entries in
	;; a toolbar descriptor.  The default value
	;; proof-toolbar-default-button-list will work for any proof
	;; assistant.
	(append
	 (apply 'append (mapcar 'proof-toolbar-make-toolbar-item 
				(proof-ass toolbar-entries)))
	 (if proof-running-on-XEmacs
	     (list [:style 3d])))))

    ;; First set the button variables to glyphs.  
    ;; (NB: this is a bit long-winded).
    (mapcar
     (lambda (buttons)
       (let ((var	(car buttons))
	     (iconfiles (mapcar (lambda (name)
				  (concat proof-images-directory
					  name
					  icontype)) (cdr buttons))))
	 (set var 
	      (if proof-running-on-XEmacs
		  ;; On XEmacs, icon variable holds a list of glyphs
		  (toolbar-make-button-list iconfiles)
		;; On GNU emacs, it holds a filename for the icon,
		;; without path or extension.
		(eval (cadr buttons))))))
     proof-toolbar-icon-list)

    (if proof-running-on-XEmacs
	;; For XEmacs, we evaluate the specifier.
	(setq proof-toolbar (mapcar 'eval proof-toolbar-button-list))

      ;; On GNU emacs, we need to make a new "key"map, 
      ;; and set a local copy of tool-bar-map to it.
      (setq proof-toolbar (make-sparse-keymap))
      (let ((tool-bar-map proof-toolbar)
	    (load-path (list proof-images-directory))) ; for finding images
	(dolist (but proof-toolbar-button-list)
	  (apply 
	   'tool-bar-add-item 
	   (eval (nth 0 but))		; image filename
	   (nth 1 but)			; function symbol
	   (nth 2 but)			; dummy key
	   (nthcdr 3 but)))))		; remaining properties
    ;; Finished
    ))


;; Action to take after altering proof-toolbar-enable
(defalias 'proof-toolbar-enable 'proof-toolbar-setup)
(proof-deftoggle proof-toolbar-enable proof-toolbar-toggle)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Toolbar refresh functions (hackery for XEmacs)
;;

(defun proof-toolbar-setup-refresh ()
  "Enable the XEmacs hackery to update the toolbar."
  (if  proof-toolbar-use-button-enablers
      (progn
	;; Set the callback for updating the enablers
	(add-hook 'proof-state-change-hook 'proof-toolbar-refresh)
	;; Also call it whenever text changes in this buffer,
	;; provided it's a script buffer.
	(if (eq proof-buffer-type 'script)
	    (add-hook 'after-change-functions 
		      'proof-toolbar-refresh nil t))
	;; And the interval timer for really refreshing the toolbar
	(setq proof-toolbar-itimer
	      (start-itimer "proof toolbar refresh"
			    'proof-toolbar-really-refresh
			    0.5		 ; seconds of delay
			    0.5		 ; repeated
			    t		 ; count idle time
			    t		 ; pass argument
			    (current-buffer))))))

(defun proof-toolbar-disable-refresh ()
  "Disable the XEmacs hackery to update the toolbar."
  (remove-hook 'proof-state-change-hook 'proof-toolbar-refresh)
  (remove-hook 'after-change-functions 'proof-toolbar-refresh)
  (if proof-toolbar-itimer (delete-itimer proof-toolbar-itimer))
  (setq proof-toolbar-itimer nil))

(deflocal proof-toolbar-refresh-flag nil
  "Flag indicating that the toolbar should be refreshed.")

;; &rest args needed for after change function args
;; FIXME: don't want to do this in every buffer, really;
;; we'll have proof-toolbar-refresh-flag defined everywhere.
(defun proof-toolbar-refresh (&rest args)
  "Set flag to indicate that the toolbar should be refreshed."
  (setq proof-toolbar-refresh-flag t))

(defvar proof-toolbar-enablers
   (mapcar (lambda (tle) 
	     (list (proof-toolbar-enabler (car tle)))) 
	   (proof-ass toolbar-entries))
  "List of all toolbar's enablers")

(defvar proof-toolbar-enablers-last-state
  nil
  "Last state of the toolbar's enablers")

(defun proof-toolbar-really-refresh (buf)
  "Force refresh of toolbar display to re-evaluate enablers.
This function needs to be called anytime that enablers may have 
changed state."
  (if ;; Be careful to only add to correct buffer, and if it's live
       (buffer-live-p buf)
      (let ((enabler-state (mapcar 'eval proof-toolbar-enablers)))
	(if 
	    (not (equal enabler-state proof-toolbar-enablers-last-state))
	    (progn
	      (setq proof-toolbar-enablers-last-state enabler-state)
	      ;; The official way to do this should be 
	      ;; (set-specifier-dirty-flag default-toolbar)
	      ;; but it doesn't work, so we do what VM does instead,
	      ;; removing and re-adding.  
	      (remove-specifier default-toolbar buf)
	      (set-specifier default-toolbar proof-toolbar buf)
	      ;; We set the dirty flag as well just in case it helps...
	      (set-specifier-dirty-flag default-toolbar)
	      (setq proof-toolbar-refresh-flag nil))))
    ;; Kill off this itimer if it's owning buffer has died
    (delete-itimer current-itimer)))

;;
;; =================================================================
;;
;;
;; GENERIC PROOF TOOLBAR BUTTON FUNCTIONS
;;
;; Defaults functions are provided below for: up, down, restart
;; Code for specific provers may define the symbols below to use
;; the other buttons: next, prev, goal, qed (images are provided).
;;
;;  proof-toolbar-next		   next function
;;  proof-toolbar-next-enable      enable predicate for next (or t)
;;
;; etc.
;;
;; To add support for more buttons or alter the default
;; images, <PA>-toolbar-entries should be adjusted.
;; See proof-config.el for that.
;;
;; Note that since the toolbar is displayed for goals and response
;; buffers too, enablers and command functions must potentially
;; switch buffer first.
;;
;;


;;
;; Undo button
;;

(defun proof-toolbar-undo-enable-p () 
  (proof-with-script-buffer
   (and (proof-shell-available-p)
	(> (proof-unprocessed-begin) (point-min)))))

(defalias 'proof-toolbar-undo 'proof-undo-last-successful-command)

;;
;; Delete button  (not actually on toolbar)
;;

(defun proof-toolbar-delete-enable-p () 
  (proof-with-script-buffer
   (and (not buffer-read-only)
	(proof-shell-available-p)
	(> (proof-unprocessed-begin) (point-min)))))

(defalias 'proof-toolbar-delete 'proof-undo-and-delete-last-successful-command)


;;
;; Lockedend button  (not actually on toolbar)
;;

(defun proof-toolbar-lockedend-enable-p () 
  t)

(defalias 'proof-toolbar-lockedend 'proof-goto-end-of-locked)




;;
;; Next button
;;

(defun proof-toolbar-next-enable-p ()
  (proof-with-script-buffer
   (not (proof-locked-region-full-p))))

(defalias 'proof-toolbar-next 'proof-assert-next-command-interactive)


;;
;; Goto button
;;

(defun proof-toolbar-goto-enable-p ()
  (eq proof-buffer-type 'script))

(defalias 'proof-toolbar-goto 'proof-goto-point)


;;
;; Retract button
;;

(defun proof-toolbar-retract-enable-p ()
  (proof-with-script-buffer
   (not (proof-locked-region-empty-p))))

(defalias 'proof-toolbar-retract 'proof-retract-buffer)


;;
;; Use button
;;

(defalias 'proof-toolbar-use-enable-p 'proof-toolbar-next-enable-p)
(defalias 'proof-toolbar-use 'proof-process-buffer)

;;
;; Restart button
;;

(defun proof-toolbar-restart-enable-p ()
  ;; Could disable this unless there's something running.
  ;; But it's handy to clearup extents, etc, I suppose.
  t)

(defalias 'proof-toolbar-restart 'proof-shell-restart)

;;
;; Goal button
;;

(defun proof-toolbar-goal-enable-p ()
  ;; Goals are always allowed, provided proof-goal-command is set.
  ;; Will crank up process if need be.
  ;; (Actually this should only be available when "no subgoals")
  proof-goal-command)


(defalias 'proof-toolbar-goal 'proof-issue-goal)


;;
;; QED button
;;

(defun proof-toolbar-qed-enable-p ()
  (proof-with-script-buffer
   (and proof-save-command
	proof-shell-proof-completed
	(proof-shell-available-p))))

(defalias 'proof-toolbar-qed 'proof-issue-save)

;;
;; State button
;;

(defun proof-toolbar-state-enable-p ()
  (proof-shell-available-p))
  
(defalias 'proof-toolbar-state 'proof-prf)

;;
;; Context button
;;

(defun proof-toolbar-context-enable-p ()
  (proof-shell-available-p))
  
(defalias 'proof-toolbar-context 'proof-ctxt)

;;
;; Info button
;;
;; Might as well enable it all the time; convenient trick to
;; start the proof assistant.

(defun proof-toolbar-info-enable-p ()
  t)

(defalias 'proof-toolbar-info 'proof-help)

;;
;; Command button
;;

(defun proof-toolbar-command-enable-p ()
  (proof-shell-available-p))

(defalias 'proof-toolbar-command 'proof-minibuffer-cmd)

;;
;; Help button
;;
 
(defun proof-toolbar-help-enable-p () 
  t)

(defun proof-toolbar-help ()
  (interactive)
  (info "ProofGeneral"))

;;
;; Find button
;;
 
(defun proof-toolbar-find-enable-p () 
  (proof-shell-available-p))

(defalias 'proof-toolbar-find 'proof-find-theorems)

;;
;; Interrupt button
;; 

(defun proof-toolbar-interrupt-enable-p ()
  proof-shell-busy)

(defalias 'proof-toolbar-interrupt 'proof-interrupt-process)


;;
;; =================================================================
;;
;; Scripting menu built from toolbar functions
;;

(defun proof-toolbar-make-menu-item (tle)
  "Make a menu item from a PA-toolbar-entries entry."
  (let*
      ((token	  (car tle))
       (menuname  (cadr tle))
       (tooltip   (nth 2 tle))
       (enablep	  (nth 3 tle))
       (fnname	  (proof-toolbar-function token))
       ;; fnval: remove defalias to get keybinding onto menu; 
       ;; NB: function and alias must both be defined for this 
       ;; to work!!
       (fnval	  (if (symbolp (symbol-function fnname))
		      (symbol-function fnname)
		    fnname)))
    (if menuname
	(list 
	 (apply 'vector
	   (append
	    (list menuname fnval)
	    (if enablep 
		(list ':active (list (proof-toolbar-enabler token))))))))))
   
(defconst proof-toolbar-scripting-menu
  ;; Toolbar contains commands to manipulate script and
  ;; other handy stuff.  
  (apply 'append
	  (mapcar 'proof-toolbar-make-menu-item 
		  (proof-ass toolbar-entries)))
  "Menu made from the Proof General toolbar commands.")

 
;; 
(provide 'proof-toolbar)

