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
;; Toolbar is just for scripting buffer at  the moment.
;;

(require 'proof-script)
(autoload 'proof-shell-live-buffer "proof-shell")

(defconst proof-toolbar-default-button-list
  '(proof-toolbar-goal-button
    proof-toolbar-retract-button
    proof-toolbar-undo-button
    proof-toolbar-next-button
    proof-toolbar-use-button
    proof-toolbar-restart-button
    proof-toolbar-qed-button
    '[:style 3d]
    nil)
  "Example value for proof-toolbar-button-list.
This gives a bare toolbar that works for any prover.  To add
prover specific buttons, see proof-toolbar.el.")

;;
;; Menu built from toolbar functions
;;

(defconst proof-toolbar-menu
  ;; Toolbar contains commands to manipulate script: "Scripting"
  '("Scripting"
    ["Goal"
     proof-toolbar-goal
     :active (proof-toolbar-goal-enable-p)]
    ["Retract"
     proof-toolbar-retract
     :active (proof-toolbar-retract-enable-p)]
    ["Undo"
     proof-toolbar-undo
     :active (proof-toolbar-undo-enable-p)]
    ["Next"
     proof-toolbar-next
     :active (proof-toolbar-next-enable-p)]
    ["Use"
     proof-toolbar-use
     :active (proof-toolbar-use-enable-p)]
    ["Restart"
     proof-toolbar-restart
     :active (proof-toolbar-restart-enable-p)]
    ["QED"
     proof-toolbar-qed
     :active (proof-toolbar-qed-enable-p)])
  "Menu made from the toolbar commands.")

;;
;; Add this menu to proof-menu
;;
(setq proof-menu
      (append proof-menu (list proof-toolbar-menu)))

(defconst proof-toolbar-iconlist
  '((proof-toolbar-next-icon "next")
    (proof-toolbar-undo-icon "undo")
    (proof-toolbar-retract-icon "retract")
    (proof-toolbar-use-icon "use")
    (proof-toolbar-goal-icon "goal")
    (proof-toolbar-qed-icon  "qed")
    (proof-toolbar-restart-icon "restart"))
  "List of icon variable names and their associated image files.
A list of lists of the form (VAR IMAGE).  IMAGE is the root name
for an image file in proof-images-directory.  The toolbar
code expects to find files IMAGE.xbm, IMAGE.xpm, IMAGE.8bit.xpm
and chooses the best one for the display properites.")

(defvar proof-toolbar-button-list proof-toolbar-default-button-list
  "A toolbar descriptor evaluated in proof-toolbar-setup.
Specifically, a list of sexps which evaluate to entries in a toolbar
descriptor.   The default value proof-toolbar-default-button-list
will work for any proof assistant.")

(defvar proof-toolbar nil
  "Proof mode toolbar button list.  Set in proof-toolbar-setup.")

(defconst proof-old-toolbar (and (boundp 'default-toolbar) default-toolbar)
  "Saved value of default-toolbar for proofmode.")


;; FIXME: edit-toolbar cannot edit proof toolbar (even in a proof mode)
;; Need a variable containing  a specifier or similar.
;; (defvar proof-toolbar-specifier nil
;;   "Specifier for proof toolbar.")
;; This doesn't seem worth fixing until XEmacs toolbar implementation
;; settles a bit.  Enablers don't work too well at the moment.

;; FIXME: could automatically defvar the icon variables.

;;; ###autoload
(defun proof-toolbar-setup ()
  "Initialize Proof General toolbar and enable it for the current buffer.
If proof-mode-use-toolbar is nil, change the current buffer toolbar
to the default toolbar."
  (interactive)
  (if (featurep 'toolbar)		; won't work in FSF Emacs
      (if (and	
	   proof-toolbar-wanted
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
	    ;; Finally ensure current buffer will display this toolbar
	    (set-specifier default-toolbar proof-toolbar (current-buffer)))
	(set-specifier default-toolbar proof-old-toolbar (current-buffer)))))

;;
;; GENERIC PROOF TOOLBAR BUTTONS
;;
;; Defaults functions are provided below for: up, down, restart
;; Code for specific provers may define the symbols below to use
;; the other buttons: next, prev, goal, qed (images are provided).
;;
;;  proof-toolbar-next		   next function
;;  proof-toolbar-next-enable    enable predicate for next (or t)
;;
;; etc.
;;
;; To add support for more buttons or alter the default
;; images, proof-toolbar-iconlist should be adjusted.
;; 
;;

;; FIXME: In the future, add back the enabler functions.
;; As of 20.4, they *almost* work, but it seems difficult
;; to get the toolbar to update at the right times.
;; For older versions of XEmacs (19.15, P.C.Callaghan@durham.ac.uk
;; reports) the toolbar specifier format doesn't like
;; arbitrary sexps as the enabler, either.
;;

(defvar proof-toolbar-next-icon nil
  "Glyph list for next button in proof toolbar.
Initialised in proof-toolbar-setup.")

(defvar proof-toolbar-next-button
  [proof-toolbar-next-icon
   proof-toolbar-next
   ;; XEmacs isn't ready for enablers yet
   t
   ;; (proof-toolbar-next-enable-p)
   "Process the next proof command"])

(defvar proof-toolbar-undo-icon nil
  "Glyph list for undo button in proof toolbar.
Initialised in proof-toolbar-setup.")

(defvar proof-toolbar-undo-button
  [proof-toolbar-undo-icon
   proof-toolbar-undo
   ;; XEmacs isn't ready for enablers yet
   t
   ;; (proof-toolbar-undo-enable-p)
   "Undo the previous proof command"])

(defvar proof-toolbar-retract-icon nil
  "Glyph list for retract button in proof toolbar.
Initialised in proof-toolbar-setup.")

(defvar proof-toolbar-retract-button
  [proof-toolbar-retract-icon
   proof-toolbar-retract
   ;; XEmacs isn't ready for enablers yet
   t
   ;; (proof-toolbar-retract-enable-p)
   "Retract buffer"])

(defvar proof-toolbar-use-icon nil
  "Glyph list for use button in proof toolbar.
Initialised in proof-toolbar-setup.")

(defvar proof-toolbar-use-button
  [proof-toolbar-use-icon
   proof-toolbar-use
   ;; XEmacs isn't ready for enablers yet
   t
   ;; (proof-toolbar-use-enable-p)
   "Process whole buffer"])

(defvar proof-toolbar-restart-icon nil
  "Glyph list for down button in proof toolbar.
Initialised in proof-toolbar-setup.")

(defvar proof-toolbar-restart-button
  [proof-toolbar-restart-icon
   proof-toolbar-restart
   ;; XEmacs isn't ready for enablers yet
   t
   ;; (proof-toolbar-restart-enable-p)
   "Restart the proof assistant"])

(defvar proof-toolbar-goal-icon nil
    "Glyph list for goal button in proof toolbar.
Initialised in proof-toolbar-setup.")

(defvar proof-toolbar-goal-button
  [proof-toolbar-goal-icon
   proof-toolbar-goal
   ;; XEmacs isn't ready for enablers yet
   t
   ;; (proof-toolbar-goal-enable-p)
   "Start a new proof"])

(defvar proof-toolbar-qed-icon nil
    "Glyph list for QED button in proof toolbar.
Initialised in proof-toolbar-setup.")

(defvar proof-toolbar-qed-button
  [proof-toolbar-qed-icon
   proof-toolbar-qed
   ;; XEmacs isn't ready for enablers yet
   t
   ;; (proof-toolbar-qed-enable-p)
   "Save proved theorem"])

;;
;; GENERIC PROOF TOOLBAR FUNCTIONS
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
  (if (proof-toolbar-undo-enable-p)
      (progn
	(proof-toolbar-move
	 (proof-undo-last-successful-command t))
	(proof-toolbar-follow))))

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
  (if (proof-toolbar-next-enable-p)
      (progn
	(proof-toolbar-move
	 (goto-char (proof-unprocessed-begin))
	 (proof-assert-next-command))
	(proof-toolbar-follow))))


;;
;; Retract button
;;

(defun proof-toolbar-retract-enable-p ()
  (and (eq (current-buffer) proof-script-buffer)
       (not (proof-locked-region-empty-p))))

(defun proof-toolbar-retract ()
  "Retract entire buffer."
  ;; proof-retract-file might be better here!
  (interactive)
  (if (proof-toolbar-retract-enable-p)
      (progn
	(proof-toolbar-move
	  (goto-char (point-min))
	  (proof-retract-until-point))	; gives error if process busy
	(proof-toolbar-follow))
    (error "Nothing to retract in this buffer!")))

;;
;; Use button
;;

(defun proof-toolbar-use-enable-p ()
  (not (proof-locked-region-full-p)))

(defun proof-toolbar-use ()
  "Process the whole buffer"
  (interactive)
  (if (proof-toolbar-use-enable-p)
      (progn
	(proof-toolbar-move
	 (proof-process-buffer))	; gives error if process busy
	(proof-toolbar-follow))
    (error "There's nothing to do in this buffer!")))

;;
;; Restart button
;;

(defun proof-toolbar-restart-enable-p ()
  ;; Could disable this unless there's something running.
  ;; But it's handy to clearup extents, etc, I suppose.
  (eq proof-buffer-type 'script)	; should always be t
  )

(defun proof-toolbar-restart  ()
  "Restart scripting via proof-shell-restart."
  (interactive)
  (if (proof-toolbar-restart-enable-p)
      (proof-shell-restart)))

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

(defun proof-toolbar-qed () 
  "Insert a save theorem command into the script buffer, issue it."
  (interactive)
  (if (proof-toolbar-qed-enable-p)
      (call-interactively 'proof-issue-save)
    (error "I can't see a completed proof!")))




;; 
(provide 'proof-toolbar)
