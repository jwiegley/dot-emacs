;; proof-toolbar.el    Toolbar for Proof General
;;
;; David Aspinall <da@dcs.ed.ac.uk>
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
  :group 'proof-general)

(defconst proof-toolbar-bare-button-list
  '(proof-toolbar-goal-button
    proof-toolbar-retract-button
    proof-toolbar-undo-button
    proof-toolbar-next-button
    proof-toolbar-use-button
    proof-toolbar-restart-button
    '[:style 3d]
    nil)
  "Example value for proof-toolbar-button-list.
This gives a bare toolbar that works for any prover.  To add
prover specific buttons, see proof-toolbar.el.")

(defconst proof-toolbar-full-button-list
  '(proof-toolbar-goal-button
    proof-toolbar-next-button
    proof-toolbar-undo-button
    proof-toolbar-retract-button
    proof-toolbar-restart-button
    '[:style 3d]
    nil)
  "Example value for proof-toolbar-button-list.
This button list includes all the buttons which have icons
and hooks provided.  Some hooks must be set for prover-specific
functions.")

(defvar proof-toolbar-button-list proof-toolbar-bare-button-list
  "A toolbar descriptor evaluated in proof-toolbar-setup.
Specifically, a list of sexps which evaluate to entries in a toolbar
descriptor.")

(defvar proof-toolbar nil
  "Proof mode toolbar.  Set in proof-toolbar-setup.")

(defun proof-toolbar-setup ()
  "Initialize proof-toolbar and enable it for the current buffer.
If proof-mode-use-toolbar is nil, change the current buffer toolbar
to the default toolbar."
  (if proof-toolbar-wanted
      (let
	  ((icontype   (if (featurep 'xpm) "xpm" "xbm")))
	;; First set the button variables to glyphs.  
	(mapcar
	 (lambda (buttons)
	   (let ((var	(car buttons))
		 (iconfiles (mapcar (lambda (name)
				      (concat proof-image-directory name
					      "." icontype)) (cdr buttons))))
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
   proof-toolbar-next-enable
   "Process the next proof command"])

(defvar proof-toolbar-undo-icon nil
  "Glyph list for undo button in proof toolbar.
Initialised in proof-toolbar-setup.")

(defvar proof-toolbar-undo-button
  [proof-toolbar-undo-icon
   proof-toolbar-undo
   proof-toolbar-undo-enable
   "Undo the previous proof command"])

(defvar proof-toolbar-retract-icon nil
  "Glyph list for retract button in proof toolbar.
Initialised in proof-toolbar-setup.")

(defvar proof-toolbar-retract-button
  [proof-toolbar-retract-icon
   proof-toolbar-retract
   proof-toolbar-retract-enable
   "Retract buffer"])

(defvar proof-toolbar-use-icon nil
  "Glyph list for use button in proof toolbar.
Initialised in proof-toolbar-setup.")

(defvar proof-toolbar-use-button
  [proof-toolbar-use-icon
   proof-toolbar-use
   proof-toolbar-use-enable
   "Process whole buffer"])

(defvar proof-toolbar-restart-icon nil
  "Glyph list for down button in proof toolbar.
Initialised in proof-toolbar-setup.")

(defvar proof-toolbar-restart-button
  [proof-toolbar-restart-icon
   proof-toolbar-restart
   proof-toolbar-restart-enable
   "Restart the proof assistant"])


(defvar proof-toolbar-next-icon nil
  "Glyph list for next level button in proof toolbar.
Initialised in proof-toolbar-setup.")

(defvar proof-toolbar-next-button
  [proof-toolbar-next-icon
   proof-toolbar-next
   proof-toolbar-next-enable
   "Display the next level of the proofstate"])

(defvar proof-toolbar-prev-icon nil
  "Glyph list for previous level button in proof toolbar.
Initialised in proof-toolbar-setup.")

(defvar proof-toolbar-prev-button
  [proof-toolbar-prev-icon
   proof-toolbar-prev
   proof-toolbar-prev-enable
   "Display the prev level of the proofstate"])

(defvar proof-toolbar-goal-icon nil
    "Glyph list for goal button in proof toolbar.
Initialised in proof-toolbar-setup.")

(defvar proof-toolbar-goal-button
  [proof-toolbar-goal-icon
   proof-toolbar-goal
   proof-toolbar-goal-enable
   "Start a new proof"])

(defvar proof-toolbar-qed-icon nil
    "Glyph list for QED button in proof toolbar.
Initialised in proof-toolbar-setup.")

(defvar proof-toolbar-qed-button
  [proof-toolbar-qed-icon
   proof-toolbar-qed
   proof-toolbar-qed-enable
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

(defvar proof-toolbar-undo-enable 
  (lambda ()
    (and (proof-toolbar-process-available-p)
       (proof-locked-end))))

(defun proof-toolbar-undo ()
  "Undo last successful in locked region, without deleting it."
  (proof-undo-last-successful-command t))

(defvar proof-toolbar-next-enable 
  ;; Could also check if there *is* a next command here,
  ;; but using proof-segment-up-to can involve tedious parsing.
  (lambda () 
    (proof-toolbar-process-available-p)))

(defun proof-toolbar-next ()
  "Assert next command in proof to proof process."
  (proof-assert-next-command))

(defconst proof-toolbar-retract-enable 
  (lambda () 
    (proof-toolbar-process-available-p)))

(defun proof-toolbar-retract ()
  "Retract buffer."
  ;; proof-retract-file might be better here!
  (goto-char (point-min))
  (proof-retract-until-point))

(defconst proof-toolbar-use-enable
  (symbol-function 'proof-toolbar-process-available-p))

(defalias 'proof-toolbar-use 'proof-process-buffer)

(defconst proof-toolbar-restart-enable
  (lambda () (eq proof-buffer-type 'script)))

(defun proof-toolbar-restart  ()
  (if (yes-or-no-p (concat "Restart " proof-assistant "?"))
      (proof-restart-script)))

;; A goal button will need a variable for string to insert,
;; actually.
(defconst proof-toolbar-goal-enable
  (symbol-function 'proof-toolbar-process-available-p))

(defalias 'proof-toolbar-goal 'proof-issue-goal)

;; 
(provide 'proof-toolbar)