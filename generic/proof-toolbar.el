;; proof-toolbar.el    Toolbar for Proof General
;;
;; Copyright (C) 1998 David Aspinall.
;; Author:     David Aspinall <da@dcs.ed.ac.uk>
;; Maintainer: Proof General maintainer <proofgen@dcs.ed.ac.uk>
;;
;; $Id$
;;
;; NB: FSF GNU Emacs has no toolbar facility. This file defines
;; proof-toolbar-menu which holds the same commands and is put on the
;; menubar by proof-toolbar-setup (surprisingly).
;;
;; Toolbar is just for the scripting buffer currently.
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

;; FIXME: In the future, add back the enabler functions.
;; As of 20.4, they *almost* work, but it seems difficult
;; to get the toolbar to update at the right times.
;; For older versions of XEmacs (19.15, P.C.Callaghan@durham.ac.uk
;; reports) the toolbar specifier format doesn't like
;; arbitrary sexps as the enabler, either.


;;; IMPORT declaration 
(require 'proof-script)
(autoload 'proof-shell-live-buffer "proof-shell")
(autoload 'proof-shell-restart "proof-shell")


;;
;; The default generic toolbar
;;
(defconst proof-toolbar-entries-default
  '((show	"Show"		"Show the current proof state" t)
    (context	"Context"	"Show the current context" t)
    (goal	"Goal"		"Start a new proof" t)
    (retract	"Retract"	"Retract (undo) whole buffer" t)
    (undo	"Undo"		"Undo the previous proof command" t)
    (next	"Next"		"Process the next proof command" t)
    (use	"Use"		"Process whole buffer" t)
    (restart	"Restart"	"Restart scripting (clear all locked regions)" t)
    (qed	"QED"		"Close/save proved theorem" t)
    (command    "Command"	"Issue a non-scripting command")
    (info	"Info"		"Show proof assistant information" t))
"Example value for proof-toolbar-entries.
This gives a bare toolbar that works for any prover.  To add
prover specific buttons, see documentation for proof-toolbar-entries
and the file proof-toolbar.el.")

(defvar proof-toolbar-entries
  proof-toolbar-entries-default
  "List of entries for Proof General toolbar.
Format of each entry is (TOKEN MENUNAME TOOLBARTEXT ENABLER-P).
For each TOKEN, we expect an icon with base filename TOKEN,
		          a function proof-toolbar-<TOKEN>,
         and (optionally) an enabler proof-toolbar-<TOKEN>-enable-p.")


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
;; Menu built from toolbar functions
;;

(defun proof-toolbar-make-menu-item (tle)
  "Make a menu item from a proof-toolbar-entries entry."
  (let
      ((token	  (car tle))
       (menuname  (cadr tle))
       (tooltip   (nth 2 tle))
       (enablep	  (nth 3 tle)))
    (apply 'vector
	   (append
	    (list menuname (proof-toolbar-function token))
	    (if enablep 
		(list ':active (list (proof-toolbar-enabler token))))))))
   
(defconst proof-toolbar-menu
  ;; Toolbar contains commands to manipulate script and
  ;; other handy stuff.  Called "Scripting"
  (append
   '("Scripting")
   (mapcar 'proof-toolbar-make-menu-item 
	   proof-toolbar-entries))
  "Menu made from the Proof General toolbar commands.")

;;
;; Add this menu to proof-menu
;;
(setq proof-menu
      (append proof-menu (list proof-toolbar-menu)))

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
  (let
      ((token	  (car tle))
       (menuname  (cadr tle))
       (tooltip   (nth 2 tle))
       ;; FIXME: enabler now enabled, for testing at least.
       ;; (enablep nil))
       (enablep  (nth 3 tle)))
    (vector
     (proof-toolbar-icon token)
     (proof-toolbar-function token)
     (if enablep 
	 (list (proof-toolbar-enabler token))
       t)
     tooltip)))

(defvar proof-toolbar-button-list 
  (append
   (mapcar 'proof-toolbar-make-toolbar-item proof-toolbar-entries)
   (list [:style 3d]))
  "A toolbar descriptor evaluated in proof-toolbar-setup.
Specifically, a list of sexps which evaluate to entries in a toolbar
descriptor.   The default value proof-toolbar-default-button-list
will work for any proof assistant.")

(defvar proof-toolbar nil
  "Proof mode toolbar button list.  Set in proof-toolbar-setup.")

;;; ###autoload
(defun proof-toolbar-setup ()
  "Initialize Proof General toolbar and enable it for the current buffer.
If proof-mode-use-toolbar is nil, change the current buffer toolbar
to the default toolbar."
  (interactive)
  (if (featurep 'toolbar)		; won't work in FSF Emacs
      (if (and	
	   (not proof-toolbar-inhibit)
	   ;; NB for FSFmacs use window-system, not console-type
	   (eq (console-type) 'x))
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
	    ;; Set the callback for updating the enablers
	    (add-hook 'proof-state-change-hook 'proof-toolbar-refresh))
	
	;; Disabling toolbar: remove specifier and state change hook.
	(remove-specifier default-toolbar (current-buffer))
	(remove-hook 'proof-state-change-hook 'proof-toolbar-refresh))))

(defun proof-toolbar-toggle (&optional force-on)
  "Toggle display of Proof General toolbar."
  (interactive "P")
  (setq proof-toolbar-inhibit
       (or force-on (not proof-toolbar-inhibit)))
  (proof-toolbar-setup))

(defun proof-toolbar-refresh ()
  "Force refresh of toolbar display to re-evaluate enablers.
This function needs to be called anytime that enablers may have 
changed state."
  (if (featurep 'toolbar)		; won't work in FSF Emacs
      (progn
	;; I'm not sure if this is "the" official way to do this,
	;; but it's what VM does and it works.
	(remove-specifier default-toolbar (current-buffer))
	(set-specifier default-toolbar proof-toolbar (current-buffer)))))
  

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
;; Helper functions 
;;

(defmacro proof-toolbar-move (&rest body)
  "Save point according to proof-toolbar-follow-mode, execute BODY."
  `(if (eq proof-toolbar-follow-mode 'locked)
       (progn
	 ,@body)				; nb no error catching
     (save-excursion
	,@body)))

(defun proof-toolbar-follow ()
  "Maybe point to the make sure the locked region is displayed."
  (if (eq proof-toolbar-follow-mode 'follow)
    (proof-goto-end-of-queue-or-locked-if-not-visible)))


;;
;; Undo button
;;

(defun proof-toolbar-undo-enable-p () 
  (and (proof-shell-available-p)
       (> (proof-unprocessed-begin) (point-min))))

;; No error if enabler fails: if it is because proof shell is busy,
;; it gets messy when clicked quickly in succession.

(defun proof-toolbar-undo ()
  "Undo last successful in locked region, without deleting it."
  (interactive)
  (proof-toolbar-move
   (proof-undo-last-successful-command t))
  (proof-toolbar-follow))

;;
;; Next button
;;

(defun proof-toolbar-next-enable-p ()
  (and
   (not (proof-locked-region-full-p))
   (not (and (proof-shell-live-buffer) proof-shell-busy))))

;; No error if enabler fails: if it is because proof shell is busy,
;; it gets messy when clicked quickly in succession.

(defun proof-toolbar-next ()
  "Assert next command in proof to proof process.
Move point if the end of the locked position is invisible."
  (interactive)
  (proof-toolbar-move
   (goto-char (proof-unprocessed-begin))
   (proof-assert-next-command-interactive))
  (proof-toolbar-follow))


;;
;; Retract button
;;

(defun proof-toolbar-retract-enable-p ()
  (not (proof-locked-region-empty-p)))

(defun proof-toolbar-retract ()
  "Retract entire buffer."
  ;; proof-retract-file might be better here!
  (interactive)
  (proof-toolbar-move
   (goto-char (point-min))
   (proof-retract-until-point-interactive))	; gives error if process busy
  (proof-toolbar-follow))

;;
;; Use button
;;

(defun proof-toolbar-use-enable-p ()
  (not (proof-locked-region-full-p)))

(defun proof-toolbar-use ()
  "Process the whole buffer."
  (interactive)
  (proof-toolbar-move
   (proof-process-buffer))	; gives error if process busy
  (proof-toolbar-follow))

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
;; Show button
;;

(defun proof-toolbar-show-enable-p ()
  (proof-shell-available-p))
  
(defalias 'proof-toolbar-show 'proof-prf)

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

(defalias 'proof-toolbar-command 'proof-execute-minibuffer-cmd)
  
;; 
(provide 'proof-toolbar)
