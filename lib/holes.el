;;; holes.el --- a little piece of elisp to define holes in your buffer
;; Copyright (C) 2001 Pierre Courtieu
;;
;; This file uses spans, an interface for extent (XEmacs) and overlays
;; (emacs), by Healfdene Goguen for the proofgeneral mode.
;; 
;; Credits also to Stefan Monnier for great help in making this file
;; cleaner.
;; 
;; This software is free software; you can redistribute it and/or
;; modify it under the terms of the GNU General Public
;; License version 2, as published by the Free Software Foundation.
;; 
;; This software is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.
;; 
;; See the GNU General Public License version 2 for more details
;; (enclosed in the file GPL).
;;
;; See documentation in variable holes-short-doc.
;;

;;; Commentary:
;; See documentation in variable holes-doc.

;;; History:
;; 

(require 'span)
(require 'cl)

;;; Help:

(defvar holes-doc nil
  "The mode `holes-mode' is meant to help program editing.
It is useful to build complicated expressions by copy pasting several
peaces of text from different parts of a buffer (or even from
different buffers).

                          HOLES

A hole is a piece of (highlighted) text that may be replaced by
another part of text later.  There is no information stored on the
file for holes, so you can save and modify files containing holes with
no harm... You can even insert or delete characters inside holes like
any other characters.

                          USE

At any time only one particular hole, called \"active\", can be
\"filled\".  Holes can be in several buffers but there is always one or
zero active hole globally.  It is highlighted with a different color.

Functions described below have default shortcuts when `holes-mode' is
on that you can customize.

TO DEFINE A HOLE, two methods:

 o Select a region with keyboard or mouse, then use
   \\[holes-set-make-active-hole].  If the selected region is empty,
   then a hole containing # is created at point.

 o Select text with mouse while pressing ctrl and meta (`C-M-select').
   If the selected region is empty (i.e. if you just click while
   pressing ctrl+meta), then a hole containing # is created.

TO ACTIVATE A HOLE, click on it with the button 1 of your mouse.  The
previous active hole will be deactivated.

TO FORGET A HOLE without deleting its text, click on it with the
button 2 (middle) of your mouse.

TO DESTROY A HOLE and delete its text, click on it with the button 3
of your mouse.

TO FILL A HOLE with a text selection, first make sure it is active,
then two methods:

 o Select text with keyboard or mouse and hit
   \\[holes-replace-update-active-hole]

 o Select text with mouse while pressing ctrl, meta and shift
   (`C-M-S-select').  This is a
   generalization of the `mouse-track-insert' feature of XEmacs.  This
   method allows you to fill different holes faster than with the usual
   copy-paste method.

After replacement the next hole is automatically made active so you
can fill it immediately by hitting again
\\[holes-replace-update-active-hole] or `C-M-S-select'.

TO JUMP TO THE ACTIVE HOLE, just hit
\\[holes-set-point-next-hole-destroy].  You must
be in the buffer containing the active hole.  the point will move to
the active hole, and the active hole will be destroyed so you can type
something to put at its place.  The following hole is automatically
made active, so you can hit \\[holes-set-point-next-hole-destroy]
again.

It is useful in combination with abbreviations.  For example in
`coq-mode' \"fix\" is an abbreviation for Fixpoint # (# : #) {struct #} :
# := #, where each # is a hole. Then hitting
\\[holes-set-point-next-hole-destroy] goes from one hole to the
following and you can fill-in each hole very quickly.

COMBINING HOLES AND SKELETONS

`holes' minor mode is made to work with minor mode `skeleton' minor
mode. For the moment only Emacs version of `skeleton' is compatible
with `holes', not XEmacs's. When you insert a skeleton, each
interesting position will be replaced by a hole. 

                          KNOWN BUGS

 o Don't try to make overlapping holes, it doesn't work. (what would
it mean anyway?)

 o With Emacs, cutting or pasting a hole wil not produce new
holes, and undoing on holes cannot make holes re-appear. With XEmacs
it will, but if you copy paste the active hole, you will get several
holes highlighted as the active one (whereas only one of them really
is), which is annoying.
")

 
;;; Code:

(cond
 ((featurep 'xemacs)
  (defalias 'holes-region-exists-p 'region-exists-p)
  (defalias 'holes-get-selection 'get-selection))
 (t
  ;;Pierre: should do almost what region-exists-p does in XEmacs
  (defun holes-region-exists-p nil
    "Return t if the mark is active, nil otherwise."
    mark-active)
  (defun holes-get-selection nil "See `current-kill'."
    (current-kill 0))))


;;; initialization
(defvar holes-default-hole (make-detached-span)
  "An empty detached hole used as the default hole.
You should not use this variable.")
(detach-span holes-default-hole)
(defvar holes-active-hole holes-default-hole
  "The current active hole.
There can be only one active hole at a time,
and this is this one.  This is not buffer local.")
;;; end initialization

;;;customizable
(defcustom holes-empty-hole-string "#"
  "String to be inserted for empty hole (don't put an empty string).")

(defcustom holes-empty-hole-regexp "#\\|@{\\([^{}]*\\)}"
  "Regexp denoting a hole in abbrevs.
Subgroup 1 is treated specially: if it matches, it is assumed that
everything before it and after it in the regexp matches delimiters
which should be removed when making the text into a hole.")


(defcustom holes-search-limit 1000
  "Number of chars to look forward when looking for the next hole, unused for now.") ;unused for the moment

;; The following is customizable by a command of the form:
;;for dark background
;;(custom-set-faces
;; '(holes-active-hole-face
;;   ((((type x) (class color) (background light))
;;     (:background "paleVioletRed")))
;;   )
;; )

(defface active-hole-face
  '((((class grayscale) (background light)) (:background "dimgrey"))
    (((class grayscale) (background dark))  (:background "LightGray"))
    (((class color) (background dark))
     (:background "darkred") (:foreground "white"))
    (((class color) (background light))
     (:background "paleVioletRed" (:foreground "black")))
    ;;??(t (:background t))
    )
  "Font Lock face used to highlight the active hole."
  )

(defface inactive-hole-face
  '((((class grayscale) (background light)) (:background "lightgrey"))
    (((class grayscale) (background dark))  (:background "Grey"))
    (((class color) (background dark))
     (:background "mediumblue") (:foreground "white"))
    (((class color) (background light))
     (:background "lightsteelblue" (:foreground "black")))
    ;;??(t (:background t))
    )
  "Font Lock  face used to highlight the active hole."
  )

;;; end customizable
 

(defun holes-region-beginning-or-nil ()
  "Internal."
  (and (holes-region-exists-p) (region-beginning))
  )

(defun holes-region-end-or-nil ()
  "Internal."
  (and (holes-region-exists-p) (region-end))
  )

(defun holes-copy-active-region ()
  "Internal."
  (assert (holes-region-exists-p) nil "the region is not active now.")
  (copy-region-as-kill (region-beginning) (region-end))
  (car kill-ring)
  )

(defun holes-is-hole-p (SPAN)
  ;; checkdoc-params: (SPAN)
  "Internal."
  (span-property SPAN 'hole)
  )

(defun holes-hole-start-position (HOLE)
 ;; checkdoc-params: (HOLE)
  "Internal."
  (assert (holes-is-hole-p HOLE) t "holes-hole-start-position: %s is not a hole")
  (span-start HOLE)
  )

(defun holes-hole-end-position (HOLE)
  ;; checkdoc-params: (HOLE)
  "Internal."
  (assert (holes-is-hole-p HOLE) t "holes-hole-end-position: %s is not a hole")
  (span-end HOLE)
  )

(defun holes-hole-buffer (HOLE)
  ;; checkdoc-params: (HOLE)
  "Internal."
  (assert (holes-is-hole-p HOLE) t "holes-hole-buffer: %s is not a hole")
  (span-buffer HOLE)
  )

(defun holes-hole-at (&optional pos)
  "Return the hole (an span) at POS in current buffer.
If pos is not in a hole raises an error."
  (span-at (or pos (point)) 'hole)
  )


(defun holes-active-hole-exist-p ()

  "Return t if the active hole exists and is not empty (ie detached).
Use this to know if the active hole is set and usable (don't use the
active-hole-marker variable)."

  (not (span-detached-p holes-active-hole))
  )


(defun holes-active-hole-start-position ()
  "Return the position of the start of the active hole.
See `active-hole-buffer' to get its buffer.  Returns an error if
active hole doesn't exist (the marker is set to nothing)."

  (assert (holes-active-hole-exist-p) t
	  "holes-active-hole-start-position: no active hole")
  (holes-hole-start-position holes-active-hole)
  )

(defun holes-active-hole-end-position ()
  "Return the position of the start of the active hole.
See `active-hole-buffer' to get its buffer.  Returns an error if
active hole doesn't exist (the marker is set to nothing)."
  
  (assert (holes-active-hole-exist-p) t
	  "holes-active-hole-end-position: no active hole")
  (holes-hole-end-position holes-active-hole)
  )


(defun holes-active-hole-buffer ()

  "Return the buffer containing the active hole.
Raise an error if the active hole is not set.  Don't care if the
active hole is empty."

  (assert (holes-active-hole-exist-p) t
	  "holes-active-hole-buffer: no active hole")
  (holes-hole-buffer holes-active-hole)
  )

(defun holes-goto-active-hole ()
  
  "Set point to active hole.
Raises an error if active-hole is not set."
  
  (interactive)
  (assert (holes-active-hole-exist-p) t
	  "holes-goto-active-hole: no active hole")
  (goto-char (holes-active-hole-start-position))
  )


(defun holes-highlight-hole-as-active (HOLE)
  "Highlight a HOLE with the `active-hole-face'.
DON'T USE this as it would break synchronization (non active hole
highlighted)."

  (assert (holes-is-hole-p HOLE) t
	  "holes-highlight-hole-as-active: %s is not a hole")
  (set-span-face HOLE 'active-hole-face)
  )

(defun holes-highlight-hole (HOLE)
  "Highlight a HOLE with the not active face.
DON'T USE this as it would break synchronization (active hole non
highlighted)."

  (assert (holes-is-hole-p HOLE) t
	  "holes-highlight-hole: %s is not a hole")
  (set-span-face HOLE 'inactive-hole-face)
  )


(defun holes-disable-active-hole ()
  "Disable the active hole.
The goal remains but is not the active one anymore.  Does nothing if
the active hole is already disable."

  (if (not (holes-active-hole-exist-p))
      ()
    ;; HACK: normal hole color, this way undo will show this hole
    ;; normally and not as active hole.  Ideally, undo should restore
    ;; the active hole, but it doesn't, so we put the 'not active'
    ;; color.
    (holes-highlight-hole holes-active-hole)
    (setq holes-active-hole holes-default-hole)
    )
  )



(defun holes-set-active-hole (HOLE)

  "Set active hole to HOLE.
Error if HOLE is not a hole."
  
  (assert (holes-is-hole-p HOLE) t
	  "holes-set-active-hole: %s is not a hole")
  (if (holes-active-hole-exist-p) (holes-highlight-hole holes-active-hole))
  (setq holes-active-hole HOLE)
  (holes-highlight-hole-as-active holes-active-hole)
  )


(defun holes-is-in-hole-p (&optional pos)
  "Return non-nil if POS (default: point) is in a hole, nil otherwise."
  (holes-hole-at pos)
  )



(defun holes-make-hole (start end)
  "Make and return an (span) hole from START to END."
  (let ((ext (make-span start end)))
    (set-span-properties
     ext `(
	   hole t
	   mouse-face highlight
	   priority 100 ;; what should I put here? I want big priority
	   face secondary-selection
	   start-open nil
	   end-open t
	   duplicable t
	   ;; unique t
	   ;; really disappear if empty:
	   evaporate t  ;; Emacs
	   detachable t ;; XEmacs
	   ;; pointer frame-icon-glyph
	   help-echo "this is a \"hole\", button 2 to forget, button 3 to destroy, button 1 to make active"
	   'balloon-help "this is a \"hole\", button 2 to forget, button 3 to destroy, button 1 to make active"
	   ))

    (set-span-keymap ext hole-map)
    ext
    )
  )

(defun holes-make-hole-at (&optional start end)
  "Make a hole from START to END.
If no arg default hole after point.  If only one arg: error.  Return
the span."
  (interactive)
  
  (let* ((rstart (or start (holes-region-beginning-or-nil) (point)))
	 (rend (or end (holes-region-end-or-nil) (point))))
    (if (eq rstart rend)
	(progn
	  (goto-char rstart)
	  (insert holes-empty-hole-string)
	  (setq rend (point))
	  )
      )
    (holes-make-hole rstart rend)
    )
  )


(defun holes-clear-hole (HOLE)
					; checkdoc-params: (HOLE)
  "Internal."
  (assert (holes-is-hole-p HOLE) t
	  "holes-clear-hole: %s is not a hole")
  
  (if (and (holes-active-hole-exist-p) (eq holes-active-hole HOLE))
      (holes-disable-active-hole)
    )
  (delete-span HOLE)
  )

(defun holes-clear-hole-at (&optional pos)
  "Clear hole at POS (default=point)."
  (interactive)
  (if (not (holes-is-in-hole-p (or pos (point))))
      (error "Holes-clear-hole-at: no hole here"))
  (holes-clear-hole (holes-hole-at (or pos (point))))
  )


(defun holes-map-holes (FUNCTION &optional OBJECT FROM TO)
					; checkdoc-params: (FUNCTION OBJECT FROM TO)
  "Internal."
  (fold-spans FUNCTION OBJECT FROM TO nil nil 'hole)
  )



(defun holes-mapcar-holes (FUNCTION &optional FROM TO PROP)
					; checkdoc-params: (FUNCTION FROM TO PROP)
  "Internal."
  (mapcar-spans FUNCTION FROM TO 'hole)
  )

(defun holes-clear-all-buffer-holes (&optional start end)
  "Clear all holes leaving their contents.
Operate betwenn START and END if non nil."
  (interactive)
  (holes-disable-active-hole)
  (holes-mapcar-holes 'holes-clear-hole (or start (point-min)) (or end (point-max)) 'hole)
  )



;;; limit ?
(defun holes-next (pos BUFFER)
  "Return the first hole after POS in BUFFER.
Or after the hole at pos if there is one (default pos=point).  If no
hole found, return nil."
  (holes-map-holes '(lambda (h x) (and (holes-is-hole-p h) h)) BUFFER pos)
  )

(defun holes-next-after-active-hole ()
  "Internal."
  (assert (holes-active-hole-exist-p) t
	  "next-active-hole: no active hole")
  (holes-next (holes-active-hole-end-position)
	      (holes-active-hole-buffer))
  )

(defun holes-set-active-hole-next (&optional buffer pos)
  "Set the active hole in BUFFER to the first hole after POS.
Default pos = point and buffer = current."
  (interactive)
  (let ((nxthole (holes-next (or pos (point))
			     (or buffer (current-buffer)))))
    (if nxthole 
	(holes-set-active-hole nxthole)
      (holes-disable-active-hole)
      )
    )
  )

;;;(defun holes-set-active-hole-next-after-active ()
;;  "sets the active hole to the first hole after active
;;  hole.";;;;

;;;  (interactive)
;;  (holes-next-after-active-hole)
;;)


(defun holes-replace-segment (start end str &optional buffer)
  "Erase chars between START and END, and replace them with STR."
  (with-current-buffer (or buffer (current-buffer))
    (goto-char end)
    ;; Insert before deleting, so the markers at `start' and `end' don't get
    ;; mixed up together.
    (insert str)
    (delete-region start end)))


(defun holes-replace (str &optional thehole)
  "Replace the current hole by STR, replace THEHOLE instead if given.
Do not use this, it breaks the right colorization of the active
goal(FIXME?).  Use `replace-active-hole' instead."
  (if (and (not thehole)
	   (not (holes-active-hole-exist-p)))
      (error "No hole to fill")
    ;; defensive: replacing the hole should make it detached and
    ;; therefore inexistent.  other reason: this is a hack: unhighlight
    ;; so that undo wont show it highlighted)
    (if (and (holes-active-hole-exist-p)
	     thehole
	     (eq holes-active-hole thehole))
	(holes-disable-active-hole)
      )
    (let ((exthole (or thehole holes-active-hole)))
      (holes-replace-segment (holes-hole-start-position exthole)
			     (holes-hole-end-position exthole)
			     (or str (car kill-ring)) ;kill ring?
			     (span-buffer exthole)
			     )
      (detach-span exthole) ;; this seems necessary for span overlays,
      ;; where the buffer attached to the span is
      ;; not removed automatically by the fact
      ;; that the span is removed from the buffer
      ;; (holes-replace-segment should perhaps
      ;; take care of that)
      )
    )
  )

(defun holes-replace-active-hole (&optional str)
  "Replace the active hole by STR, if no str is given, then put the selection instead."
  (if (not (holes-active-hole-exist-p)) ()
    (holes-replace
     (or str (holes-get-selection) (error "Nothing to put in hole"))
     holes-active-hole)
    ))


(defun holes-replace-update-active-hole (&optional str)
  "Replace the active hole by STR.
Like `holes-replace-active-hole', but then sets the active hole to the
following hole if it exists."
  (interactive)
  (assert (holes-active-hole-exist-p) t
	  "holes-replace-update-active-hole: no active hole")
  (if (not (holes-active-hole-exist-p))
      ()
    (let ((nxthole (holes-next-after-active-hole)))
      (holes-replace-active-hole
       (or str
	   (and (holes-region-exists-p) (holes-copy-active-region))
	   (holes-get-selection) (error "Nothing to put in hole")))
      (if nxthole (holes-set-active-hole nxthole)
	(setq holes-active-hole holes-default-hole))
      )
    )
  )


(defun holes-delete-update-active-hole ()
  "Deletes the active hole and supresses its content.
Sets `holes-active-hole' to the next hole if it exists."
  (interactive)
  (holes-replace-update-active-hole "")
  )

(defun holes-set-make-active-hole (&optional start end)
  "Make a new hole between START and END or at point, and make it active."

  (interactive)
  (holes-set-active-hole (holes-make-hole-at start end))
  )


;; mouse stuff, I want to make something close to `mouse-track-insert'
;; of XEmacs, but with modifier ctrl-meta and ctrl-meta-shift

;;; Emacs and XEmacs have different ways of dealing with mouse
;; selection, but `mouse-track'(XEmacs) mouse-drag-region(Emacs)
;; have nearly the same meaning for me.  So I define this
;; track-mouse-selection.

(eval-and-compile
  (cond
   ;; XEmacs's mouse-track.
   ((fboundp 'mouse-track)
    (defalias 'holes-track-mouse-selection 'mouse-track)
    (defsubst holes-track-mouse-clicks ()
      "see `mouse-track-click-count'"
      mouse-track-click-count))
   ;; Emacs-22's mouse-drag-track.
   ((fboundp 'mouse-drag-track)
    (defalias 'holes-track-mouse-selection 'mouse-drag-track)
    (defsubst holes-track-mouse-clicks ()
      "see `mouse-track-click-count'"
      (+ mouse-selection-click-count 1)))
   ;; Emacs<22
   ((fboundp 'mouse-drag-region)
    (defun holes-track-mouse-selection (event)
      ;; Emacs-21's mouse-drag-region has a bug that makes it behave more or
      ;; less like we want it as long as transient-mark-mode is active.
      (let ((transient-mark-mode nil))
        (mouse-drag-region event)))
    (defsubst holes-track-mouse-clicks ()
      "see `mouse-selection-click-count'"
      (+ mouse-selection-click-count 1)))
   (t
    (error
     "Your (X)Emacs version is not compatible with holes (too old or
    new version?), sorry"))
   )
  )

(defun holes-mouse-replace-active-hole (event)
					; checkdoc-params: (event)
  "Internal."
  (interactive "*e")
  (holes-track-mouse-selection event)
  (save-excursion
    ;;HACK: nothing if one click (but a second is perhaps coming)
    (if (and (eq (holes-track-mouse-clicks) 1)
	     (not (holes-region-exists-p)))
	()
      (if (not (holes-region-exists-p))
	  (error "Nothing to put in hole")
	(holes-replace-update-active-hole (holes-get-selection))
	(message "hole replaced")
	)
      )
    )
  ;;  (zmacs-deactivate-region)
  )

(defun holes-destroy-hole (&optional SPAN)
					; checkdoc-params: (SPAN)
  "Internal."
  (interactive)
  (let* ((sp (or SPAN (holes-hole-at (point)) (error "No hole to destroy"))))
    (save-excursion
      (if (and (holes-active-hole-exist-p)
	       (eq sp holes-active-hole))
	  (holes-disable-active-hole))
      (holes-replace "" sp)
      (detach-span sp)
      )
    (message "hole killed")
    )
  )


(defun holes-hole-at-event (event)
					; checkdoc-params: (event)
  "Internal."
  (span-at-event event 'hole))

(defun holes-mouse-destroy-hole (event)
					; checkdoc-params: (event)
  "Internal."
  (interactive "*e")
  (holes-destroy-hole (holes-hole-at-event event))
  )


;;;(span-at-event EVENT &optional PROPERTY BEFORE AT-FLAG)
;;comprend pas??
(defun holes-mouse-forget-hole (event)
					; checkdoc-params: (event)
  "Internal."
  (interactive "*e")
  (save-excursion
    (let ((ext (holes-hole-at-event event)))
      (if (eq ext holes-active-hole)
	  (holes-disable-active-hole))
      (detach-span ext)
      )
    )
  (message "hole deleted")
  )



(defun holes-mouse-set-make-active-hole (event)
					; checkdoc-params: (event)
  "Internal."
  (interactive "*e")
  ;;(set-mark (point))
  (holes-track-mouse-selection event)

  (if (and (eq (holes-track-mouse-clicks) 1)
	   (not (holes-region-exists-p)))
      (holes-set-make-active-hole (point) (point))

    (if (holes-region-exists-p)
	(holes-set-make-active-hole)
      (let ((ext (holes-hole-at-event event)))
	(if (and ext (holes-is-hole-p ext))
	    (error "Already a hole here")
	  (holes-set-active-hole (holes-make-hole-at)))
	)
      )
    )
  )

(defun holes-mouse-set-active-hole (event)
					; checkdoc-params: (event)
  "Internal."
  (interactive "*e")
  (let ((ext (holes-hole-at-event event)))
    (if (and ext (holes-is-hole-p ext))
	(holes-set-active-hole ext)
      (error "No hole here"))
    )
  )


(defun holes-set-point-next-hole-destroy ()
  "Moves the point to current active hole (if any and if in current buffer).
Destroy it and makes the next hole active if any."
  (interactive)
  (assert (holes-active-hole-exist-p) nil "no active hole")
  (assert (eq (current-buffer) (holes-active-hole-buffer)) nil
	  "active hole not in this buffer")
  (holes-goto-active-hole)
  (holes-delete-update-active-hole)
  )


;;; Customizable key bindings



(defvar hole-map
  (let ((map (make-sparse-keymap)))
    (cond
     ((featurep 'xemacs)
      (define-key map [(button1)] 'holes-mouse-set-active-hole)
      (define-key map [(button3)] 'holes-mouse-destroy-hole)
      (define-key map [(button2)] 'holes-mouse-forget-hole))
     (t
      (define-key map [(mouse-1)] 'holes-mouse-set-active-hole)
      (define-key map [(mouse-3)] 'holes-mouse-destroy-hole)
      (define-key map [(mouse-2)] 'holes-mouse-forget-hole)))
    map)
  "Keymap to use on the holes's overlays.
This keymap is used only when
  on a hole.  See `holes-mode-map' for the keymap of `holes-mode'.")

(defvar holes-mode-map
  (let ((map (make-sparse-keymap)))
    (define-key map [(control c) (h)] 'holes-set-make-active-hole)
    (define-key map [(control c) (control y)] 'holes-replace-update-active-hole)
    (define-key map [(control meta down-mouse-1)] 'holes-mouse-set-make-active-hole)
    (define-key map [(control meta shift down-mouse-1)] 'holes-mouse-replace-active-hole)
    (define-key map [(meta return)] 'holes-set-point-next-hole-destroy)
    map)
  "Keymap of `holes-mode'.
This is not the keymap used on holes's overlay
  (see `hole-map' instead).  This one is active whenever we are on a
  buffer where `holes-mode' is active.")

(or (assq 'holes-mode minor-mode-map-alist)
    (push (cons 'holes-mode holes-mode-map)
	  minor-mode-map-alist))

;;;(global-set-key  [(control meta **WRONG** space ) ] 'holes-set-active-hole-next)


;;;;;;;;;;; End Customizable key bindings ;;;;;

;; utilities to be used in conjunction with abbrevs.
;; The idea is to put abbrevs of the form:
;;(define-abbrev-table 'tuareg-mode-abbrev-table
;;      '(
;;	("l" "let # = # in" replace-#-after-abbrev2 0)
;;	)
;;      )
;; where replace-#-after-abbrev2 should be a function which replace the
;; two #'s (two occurences going backward from abbrev expantion point)
;; by holes and leave point at the first # (deleting
;; it).  holes-set-point-next-hole-destroy allow to go to the next hole.

;;following function allow to replace occurrences of a string by a
;;hole.

(defun holes-replace-string-by-holes-backward (limit)
  "Change each occurrence of REGEXP into a hole.
Sets the active hole to the last created hole and unsets it if no hole is
created.  Return the number of holes created."
  (holes-disable-active-hole)
  (let ((n 0))
    (save-excursion
      (while (re-search-backward holes-empty-hole-regexp limit t)
	(incf n)
	(if (not (match-end 1))
	    (holes-make-hole (match-beginning 0) (match-end 0))
	  (holes-make-hole (match-beginning 1) (match-end 1))
	  ;; delete end first to avoid shifting of marks
	  (delete-region (match-end 1) (match-end 0)) 
	  (delete-region (match-beginning 0) (match-beginning 1)))
	(holes-set-active-hole-next)))
    n))

(defun holes-skeleton-end-hook ()
  "Default hook after a skeleton insertion: put holes at each interesting position."
  ;; Not all versions of skeleton provide `skeleton-positions' and the
  ;; corresponding @ operation :-(
  (unless (boundp 'mmm-inside-insert-by-key) ; pc: this hack is ok for me
    (when (boundp 'skeleton-positions)
      (dolist (pos skeleton-positions)	;; put holes here
	(holes-set-make-active-hole pos pos)))))

(defconst holes-jump-doc 
  (concat "Hit \\[holes-set-point-next-hole-destroy] to jump "
	  "to active hole.  C-h v holes-doc to see holes doc.")
  "Shortcut reminder string for jumping to active hole.")



(defun holes-replace-string-by-holes-backward-jump (pos)
  "Put holes between POS and point, backward, indenting.
\"#\" and \"@{..}\" between this positions will become holes."
  (save-excursion (indent-region pos (point) nil))
  (let ((n (holes-replace-string-by-holes-backward pos)))
    (case n
      (0 nil)				; no hole, stay here.
      (1
       (goto-char pos)
       (holes-set-point-next-hole-destroy)) ; if only one hole, go to it.
      (t
       (goto-char pos)
       (message (substitute-command-keys
		 "\\[holes-set-point-next-hole-destroy] to jump to active hole.  \\[holes-short-doc] to see holes doc."))))))



(defun holes-abbrev-complete ()
  "Complete abbrev by putting holes and indenting.
Moves point at beginning of expanded text.  Put this function as
call-back for your abbrevs, and just expanded \"#\" and \"@{..}\" will
become holes."
  (holes-replace-string-by-holes-backward-jump last-abbrev-location))



(defun holes-insert-and-expand (s)
  "Insert S, expand it and replace #s and @{]s by holes."
  ;; insert the expansion of abbrev s, and replace #s by holes.  It was
  ;; possible to implement it with a simple ((insert s) (expand-abbrev))
  ;; but undo would show the 2 steps, which is bad.
  (let ((pos (point))
	(ins (abbrev-expansion s)))
    (insert (or ins s))
    (setq last-abbrev-location pos)
    (holes-abbrev-complete)))

(defvar holes-mode nil
  "Is equal to t if holes mode is on, nil otherwise.")
(make-variable-buffer-local 'holes-mode)

;; FIXME: Use define-minor-mode, or at least add-minor-mode.
;;;###autoload
(defun holes-mode (&optional arg)
  "If ARG is nil, then toggle holes mode on/off.
If arg is positive, then turn holes mode on.  If arg is negative, then
turn it off."
  (interactive)
  (setq holes-mode (if (null arg) (not holes-mode)
		     (> (prefix-numeric-value arg) 0)))
  (cond
   (holes-mode
    (add-hook 'skeleton-end-hook 'holes-skeleton-end-hook nil t))
   (t
    (remove-hook 'skeleton-end-hook 'holes-skeleton-end-hook t)))
  (run-hooks 'holes-mode-hook))

(or (assq 'holes-mode minor-mode-alist)
    (setq minor-mode-alist
	  (cons '(holes-mode " Holes") minor-mode-alist)))

(provide 'holes)

;;; holes.el ends here
