;; proof-toolbar.el    Toolbar for Proof General
;;
;; David Aspinall <da@dcs.ed.ac.uk>
;; Maintainer: Proof General maintainer <proofgen@dcs.ed.ac.uk>
;;
;; $Id$
;;
;; NB: XEmacs specific code!
;;
;; Toolbar is just for scripting buffer at  the moment.
;;

(defcustom proof-toolbar-wanted t
  "*Whether to use toolbar in proof mode."
  :type 'boolean
  :group 'proof)

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

(defvar proof-toolbar-button-list proof-toolbar-default-button-list
  "A toolbar descriptor evaluated in proof-toolbar-setup.
Specifically, a list of sexps which evaluate to entries in a toolbar
descriptor.   The default value proof-toolbar-default-button-list
will work for any proof assistant.")

(defvar proof-toolbar nil
  "Proof mode toolbar button list.  Set in proof-toolbar-setup.")

;; FIXME: edit-toolbar cannot edit proof toolbar (even in a proof mode)
;; Need a variable containing  a specifier or similar.
; (defvar proof-toolbar-specifier nil
;   "Specifier for proof toolbar.")

(defun proof-toolbar-setup ()
  "Initialize proof-toolbar and enable it for the current buffer.
If proof-mode-use-toolbar is nil, change the current buffer toolbar
to the default toolbar."
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
				      (concat proof-internal-images-directory
					      name
					      icontype)) (cdr buttons))))
	     (set var (toolbar-make-button-list iconfiles))))
	 proof-toolbar-iconlist)
	;; Now evaluate the toolbar descriptor
	(setq proof-toolbar (mapcar 'eval proof-toolbar-button-list))
	;; Finally ensure current buffer will display this toolbar
	(set-specifier default-toolbar proof-toolbar (current-buffer)))
    (set-specifier default-toolbar proof-old-toolbar (current-buffer))))

(defconst proof-old-toolbar default-toolbar
  "Saved value of default-toolbar for proofmode.")

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

(defvar proof-toolbar-next-icon nil
  "Glyph list for next button in proof toolbar.
Initialised in proof-toolbar-setup.")

(defvar proof-toolbar-next-button
  [proof-toolbar-next-icon
   proof-toolbar-next
   (proof-toolbar-next-enable-p)
   "Process the next proof command"])

(defvar proof-toolbar-undo-icon nil
  "Glyph list for undo button in proof toolbar.
Initialised in proof-toolbar-setup.")

(defvar proof-toolbar-undo-button
  [proof-toolbar-undo-icon
   proof-toolbar-undo
   (proof-toolbar-undo-enable-p)
   "Undo the previous proof command"])

(defvar proof-toolbar-retract-icon nil
  "Glyph list for retract button in proof toolbar.
Initialised in proof-toolbar-setup.")

(defvar proof-toolbar-retract-button
  [proof-toolbar-retract-icon
   proof-toolbar-retract
   (proof-toolbar-retract-enable-p)
   "Retract buffer"])

(defvar proof-toolbar-use-icon nil
  "Glyph list for use button in proof toolbar.
Initialised in proof-toolbar-setup.")

(defvar proof-toolbar-use-button
  [proof-toolbar-use-icon
   proof-toolbar-use
   (proof-toolbar-use-enable-p)
   "Process whole buffer"])

(defvar proof-toolbar-restart-icon nil
  "Glyph list for down button in proof toolbar.
Initialised in proof-toolbar-setup.")

(defvar proof-toolbar-restart-button
  [proof-toolbar-restart-icon
   proof-toolbar-restart
   (proof-toolbar-restart-enable-p)
   "Restart the proof assistant"])

(defvar proof-toolbar-goal-icon nil
    "Glyph list for goal button in proof toolbar.
Initialised in proof-toolbar-setup.")

(defvar proof-toolbar-goal-button
  [proof-toolbar-goal-icon
   proof-toolbar-goal
   (proof-toolbar-goal-enable-p)
   "Start a new proof"])

(defvar proof-toolbar-qed-icon nil
    "Glyph list for QED button in proof toolbar.
Initialised in proof-toolbar-setup.")

(defvar proof-toolbar-qed-button
  [proof-toolbar-qed-icon
   proof-toolbar-qed
   (proof-toolbar-qed-enable-p)
   "Save proved theorem"])

(defconst proof-toolbar-iconlist
  '((proof-toolbar-next-icon "next")
    (proof-toolbar-undo-icon "undo")
    (proof-toolbar-retract-icon "retract")
    (proof-toolbar-use-icon "use")
    (proof-toolbar-goal-icon "goal")
    (proof-toolbar-qed-icon  "qed")
    (proof-toolbar-restart-icon "restart"))
  "List of icon variable names and their associated image files")

;;
;; GENERIC PROOF TOOLBAR FUNCTIONS
;;

(defun proof-toolbar-process-available-p 
  "Enabler for toolbar functions.
Checks based on those in proof-check-process-available, but
without giving error messages."
  (and (eq proof-buffer-type 'script)
       (proof-shell-live-buffer)
       (not proof-shell-busy)
       ;; this last check is wrong for pbp buffer!
       (eq proof-script-buffer (current-buffer))))

(defun proof-toolbar-undo-enable-p () 
  (and (proof-toolbar-process-available-p)
       (proof-locked-end)))

(defun proof-toolbar-undo ()
  "Undo last successful in locked region, without deleting it."
  (save-excursion
    (proof-undo-last-successful-command t)))

(defun proof-toolbar-next-enable-p ()
  ;; Could check if there *is* a next command here, to avoid
  ;; stupid "nothing to do" errors.
  t)

(defun proof-toolbar-next ()
  "Assert next command in proof to proof process.
Move point if the end of the locked position is invisible."
  (save-excursion
    (if (proof-shell-live-buffer)
      (goto-char (proof-locked-end))
      (goto-char (point-min)))
    (proof-assert-next-command))
  ;; FIXME: not sure about whether this is nice or not.
  (proof-goto-end-of-locked-if-pos-not-visible-in-window))

(defun proof-toolbar-retract-enable-p ()
  (proof-toolbar-process-available-p))

(defun proof-toolbar-retract ()
  "Retract buffer."
  ;; proof-retract-file might be better here!
  (save-excursion
    (goto-char (point-min))
    (proof-retract-until-point)))

(defun proof-toolbar-use-enable-p ()
  ;; Could check to see that whole buffer hasn't been
  ;; processed already.
  t)

(defun proof-toolbar-use 
  "Process the whole buffer"
  (save-excursion
    (proof-process-buffer)))

(defun proof-toolbar-restart-enable-p ()
  ;; Could disable this unless there's something running.
  ;; But it's handy to clearup extents, etc, I suppose.
  (eq proof-buffer-type 'script))

(defun proof-toolbar-restart  ()
  (if (yes-or-no-p (concat "Restart " proof-assistant " scripting?"))
      (proof-restart-script)))

(defun proof-toolbar-goal-enable-p ()
  ;; Goals are always allowed: will crank up process if need be.
  t)

(defalias 'proof-toolbar-goal 'proof-issue-goal)

;; Actually this should only be available when "no subgoals"

(defun proof-toolbar-qed-enable-p ()
  (and proof-shell-proof-completed
       (proof-toolbar-process-available-p)))

(defalias 'proof-toolbar-qed 'proof-issue-save)

;; 
(provide 'proof-toolbar)