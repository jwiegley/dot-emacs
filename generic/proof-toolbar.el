;; proof-toolbar.el    Toolbar for Proof General
;;
;; Copyright (C) 1998,9  David Aspinall / LFCS.
;; Author:     David Aspinall <da@dcs.ed.ac.uk>
;; Maintainer: Proof General maintainer <proofgen@dcs.ed.ac.uk>
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
;; TODO:
;;
;; FIXME: edit-toolbar cannot edit proof toolbar (even in a proof mode)
;; Need a variable containing  a specifier or similar.
;; (defvar proof-toolbar-specifier nil
;;   "Specifier for proof toolbar.")
;; This doesn't seem worth fixing until XEmacs toolbar implementation
;; settles a bit.  Enablers don't work too well at the moment.

;; FIXME: it's a little bit tricky to add prover-specific items.
;; We can improve on that by generating everything on-thy-fly
;; in proof-toolbar-setup.

;; FIXME: consider automatically disabling buttons which are
;; not configured for the prover, e.g. if proof-info-command is
;; not set, then the Info button should not be show. 


;;; IMPORT declaration 
(require 'proof-script)
(autoload 'proof-shell-live-buffer "proof-shell")
(autoload 'proof-shell-restart "proof-shell")


;;
;; The default generic toolbar and toolbar variable
;;

(defconst proof-toolbar-entries-default
  `((state	"Display proof state" "Display the current proof state" t)
    (context	"Display context"     "Display the current context" t)
    (goal	"Start a new proof"   "Start a new proof" t)
    (retract	"Retract buffer"      "Retract (undo) whole buffer" t)
    (undo	"Undo step"           "Undo the previous proof command" t)
    (delete	"Delete step"         nil t)
    (next	"Next step"           "Process the next proof command" t)
    (use	"Use buffer"  	      "Process whole buffer" t)
    (goto	"Goto point"	      "Process or undo to the cursor position" t)
    (restart	"Restart scripting"   "Restart scripting (clear all locked regions)" t)
    (qed	"Finish proof"     "Close/save proved theorem" t)
    (lockedend  "Locked end"	   nil t)
    (find	"Find theorems"	   "Find theorems" t)
    (command    "Issue command"	   "Issue a non-scripting command" t)
    (interrupt  "Interrupt prover" "Interrupt the proof assistant (warning: may break synchronization)" t)
    (info	nil		   "Show online proof assistant information" t)
    (help	nil		   "Proof General manual" t))
"Example value for proof-toolbar-entries.  Also used to define Scripting menu.
This gives a bare toolbar that works for any prover.  To add
prover specific buttons, see documentation for proof-toolbar-entries
and the file proof-toolbar.el.")

;; FIXME: defcustom next one, to set on a per-prover basis
(defvar proof-toolbar-entries
  proof-toolbar-entries-default
  "List of entries for Proof General toolbar and Scripting menu.
Format of each entry is (TOKEN MENUNAME TOOLTIP ENABLER-P).
For each TOKEN, we expect an icon with base filename TOKEN,
		          a function proof-toolbar-<TOKEN>,
         and (optionally) an enabler proof-toolbar-<TOKEN>-enable-p.
If MENUNAME is nil, item will not appear on the scripting menu.
If TOOLTIP is nil, item will not appear on the toolbar.")



;;
;; Function, icon, button names
;; 

(defun proof-toolbar-function (token)
  (intern (concat "proof-toolbar-" (symbol-name token))))

(defun proof-toolbar-icon (token)
  (intern (concat "proof-toolbar-" (symbol-name token) "-icon")))

(defun proof-toolbar-enabler (token)
  (intern (concat "proof-toolbar-" (symbol-name token) "-enable-p")))


;;
;; Now the toolbar icons and buttons
;; 

(defun proof-toolbar-make-icon (tle)
  "Make icon variable and icon list entry from a proof-toolbar-entries entry."
  (let* ((icon (car tle))
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
    (list iconvar iconname)))
  
(defconst proof-toolbar-iconlist
  (mapcar 'proof-toolbar-make-icon proof-toolbar-entries)
  "List of icon variable names and their associated image files.
A list of lists of the form (VAR IMAGE).  IMAGE is the root name
for an image file in proof-images-directory.  The toolbar
code expects to find files IMAGE.xbm, IMAGE.xpm, IMAGE.8bit.xpm
and chooses the best one for the display properites.")

(defun proof-toolbar-make-toolbar-item (tle)
  "Make a toolbar button descriptor from a proof-toolbar-entries entry."
  (let*
      ((token	      (car tle))
       (menuname      (cadr tle))
       (tooltip       (nth 2 tle))
       (existsenabler (nth 3 tle))
       (enablep	      (and proof-toolbar-use-button-enablers
			   (>= emacs-major-version 21)
			   existsenabler))
       (enabler	      (proof-toolbar-enabler token))
       (enableritem   (if enablep (list enabler) t))
       (buttonfn      (proof-toolbar-function token))
       (icon	      (proof-toolbar-icon token))
       (actualfn      (if (or enablep (not existsenabler))
			  buttonfn
			;; Add the enabler onto the function if necessary.
			`(lambda ()
				   (if (,enabler) 
				       (call-interactively (quote ,buttonfn)))))))
    (if tooltip
	(list (vector icon actualfn enableritem tooltip)))))

(defvar proof-toolbar-button-list 
  (append
   (apply 'append (mapcar 'proof-toolbar-make-toolbar-item proof-toolbar-entries))
   (list [:style 3d]))
  "A toolbar descriptor evaluated in proof-toolbar-setup.
Specifically, a list of sexps which evaluate to entries in a toolbar
descriptor.   The default value proof-toolbar-default-button-list
will work for any proof assistant.")

;;
;; Code for displaying and refreshing toolbar
;;

(defvar proof-toolbar nil
  "Proof mode toolbar button list.  Set in proof-toolbar-setup.")

(deflocal proof-toolbar-itimer nil
  "itimer for updating the toolbar in the current buffer")

;;;###autoload
(defun proof-toolbar-setup ()
  "Initialize Proof General toolbar and enable it for the current buffer.
If proof-mode-use-toolbar is nil, change the current buffer toolbar
to the default toolbar."
  (interactive)
  (if (featurep 'toolbar)		; won't work in FSF Emacs
      (if (and	
	   proof-toolbar-enable
	   ;; NB for FSFmacs use window-system, not console-type
	   (or (eq (console-type) 'x)
	       (eq (console-type) 'mswindows)))
	  (let
	      ((icontype   (if (featurep 'xpm)
			       (if (< (device-pixel-depth) 16)
				   ".8bit.xpm" ".xpm")
			     ".xbm")))
	    ;; First set the button variables to glyphs.  
	    (mapcar
	     (lambda (buttons)
	       (let ((var	(car buttons))
		     (iconfiles (mapcar (lambda (name)
					  (concat proof-images-directory
						  name
						  icontype)) (cdr buttons))))
		 (set var (toolbar-make-button-list iconfiles))))
	     proof-toolbar-iconlist)
	    ;; Now evaluate the toolbar descriptor
	    (setq proof-toolbar (mapcar 'eval proof-toolbar-button-list))
	    ;; Ensure current buffer will display this toolbar
	    (set-specifier default-toolbar proof-toolbar (current-buffer))
	    (if proof-toolbar-use-button-enablers
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
				(current-buffer))))) ;  - current buffer
	    ;; Attempt to refresh to display toolbar
	    (sit-for 0))
	;; Disabling toolbar: remove specifier, hooks, timer.
	(remove-specifier default-toolbar (current-buffer))
	(remove-hook 'proof-state-change-hook 'proof-toolbar-refresh)
	(remove-hook 'after-change-functions 'proof-toolbar-refresh)
	(if proof-toolbar-itimer (delete-itimer proof-toolbar-itimer))
	(setq proof-toolbar-itimer nil))))

;; Action to take after altering proof-toolbar-enable
(defalias 'proof-toolbar-enable 'proof-toolbar-setup)
(proof-deftoggle proof-toolbar-enable proof-toolbar-toggle)

(deflocal proof-toolbar-refresh-flag nil
  "Flag indicating that the toolbar should be refreshed.")

;; &rest args needed for after change function args
;; FIXME: don't want to do this in every buffer, really;
;; we'll have proof-toolbar-refresh-flag defined everywhere.
(defun proof-toolbar-refresh (&rest args)
  "Set flag to indicate that the toolbar should be refreshed."
  (setq proof-toolbar-refresh-flag t))

(defun proof-toolbar-really-refresh (buf)
  "Force refresh of toolbar display to re-evaluate enablers.
This function needs to be called anytime that enablers may have 
changed state."
  ;; FIXME: could improve performance here and reduce flickeryness
  ;; by caching result of last evaluation of enablers.  If nothing
  ;; has changed, don't remove and re-add.
  (if ;; Be careful to only add to correct buffer, and if it's live
      (buffer-live-p buf)
      ;; I'm not sure if this is "the" official way to do this,
      ;; but it's what VM does and it works.
      (progn
	(remove-specifier default-toolbar buf)
	(set-specifier default-toolbar proof-toolbar buf)
	(setq proof-toolbar-refresh-flag nil))
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
;; images, proof-toolbar-entries should be adjusted.
;;
;;

;;
;; Undo button
;;

(defun proof-toolbar-undo-enable-p () 
  (and (proof-shell-available-p)
       (> (proof-unprocessed-begin) (point-min))))

(defalias 'proof-toolbar-undo 'proof-undo-last-successful-command)

;;
;; Delete button  (not actually on toolbar)
;;

(defun proof-toolbar-delete-enable-p () 
  (and (not buffer-read-only)
       (proof-shell-available-p)
       (> (proof-unprocessed-begin) (point-min))))

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
  (not (proof-locked-region-full-p)))

(defalias 'proof-toolbar-next 'proof-assert-next-command-interactive)


;;
;; Goto button
;;

(defun proof-toolbar-goto-enable-p ()
  ;; we don't want to update the toolbar on every movement of point
  ;; so no test here.
  ;;  (and
  ;;   (not (equal (point) (proof-locked-end))) ; bug in powtlrp
  ;;   (or
  ;;    (< (point) (proof-locked-end))
  ;;    (not (save-excursion
  ;;          (proof-only-whitespace-to-locked-region-p))))))
  t)  

(defalias 'proof-toolbar-goto 'proof-goto-point)


;;
;; Retract button
;;

(defun proof-toolbar-retract-enable-p ()
  (not (proof-locked-region-empty-p)))

(defalias 'proof-toolbar-retract 'proof-retract-buffer)


;;
;; Use button
;;

(defun proof-toolbar-use-enable-p ()
  (not (proof-locked-region-full-p)))

(defalias 'proof-toolbar-use 'proof-process-buffer)

;;
;; Restart button
;;

(defun proof-toolbar-restart-enable-p ()
  ;; Could disable this unless there's something running.
  ;; But it's handy to clearup extents, etc, I suppose.
  (eq proof-buffer-type 'script)	; should always be t 
					; (toolbar only in scripts)
  )

(defalias 'proof-toolbar-restart 'proof-shell-restart)

;;
;; Goal button
;;

(defun proof-toolbar-goal-enable-p ()
  ;; Goals are always allowed: will crank up process if need be.
  ;; Actually this should only be available when "no subgoals"
  t)

(defalias 'proof-toolbar-goal 'proof-issue-goal)


;;
;; QED button
;;

(defun proof-toolbar-qed-enable-p ()
  (and proof-shell-proof-completed
       (proof-shell-available-p)))

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
  "Make a menu item from a proof-toolbar-entries entry."
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
		  proof-toolbar-entries))
  "Menu made from the Proof General toolbar commands.")

 
;; 
(provide 'proof-toolbar)

