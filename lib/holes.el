;
; holes.el - a little piece of elisp to define holes in your buffer
; Copyright (C) 2001 Pierre Courtieu 
;
; This file uses spans, an interface for extent (Xemacs) and overlays
; (emacs), by Healfdene Goguen for the proofgeneral mode.
; 
; This software is free software; you can redistribute it and/or
; modify it under the terms of the GNU General Public
; License version 2, as published by the Free Software Foundation.
; 
; This software is distributed in the hope that it will be useful,
; but WITHOUT ANY WARRANTY; without even the implied warranty of
; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.
; 
; See the GNU General Public License version 2 for more details
; (enclosed in the file GPL).
;


(require 'span)

(defun holes-short-doc ()
  "prints a short doc for holes"
  (interactive)
  (switch-to-buffer-other-window "*doc holes*")
  (insert "

The highlighted characters in your buffer are \"holes\", holes are a
powerful feature for program editing.  You can delete them like usual
characters. If you don't replace holes by something else (see below),
they will be saved in the buffer's file as usual characters. See the
short documentation below to learn how to use holes.

                          HOLES


A hole is a piece of (highlighted) text that may be replaced by
another part of text later. This feature is useful to build
complicated expressions by copy pasting several peaces of text from
different parts of a buffer (or even from different buffers).

                          USE

At any time only one particular hole, called \"active\", can be
\"filled\". Holes can be in several buffers but there is always one or
zero active hole globally.  It is highlighted with a different color.

TO DEFINE A HOLE, two methods:

 o Select a region with keyboard (ctrl-space) or mouse, then hit
ctrl-meta-h. If the selected region is empty (i.e. if you just hit
ctrl+meta+h), then a hole containing '#' is created.

 o Select text with mouse while pressing ctrl + meta.  If the selected
region is empty (i.e. if you just click while pressing ctrl+meta),
then a hole containing '#' is created.

TO ACTIVATE A HOLE, click on it with the button 1 of your mouse. You
can also hit meta-space, it will activate the first hole following the
point. The previous active hole will be deactivated.

TO FORGET A HOLE without deleting its text, click on it with the
button 2 (middle) of your mouse.

TO DESTROY A HOLE and delete its text, click on it with the button 3
of your mouse.

TO FILL A HOLE with a text selection, first make sure it is active,
then two methods:

 o Select text with keyboard (ctrl-space) or mouse and hit ctrl-meta-y

 o Select text with mouse while pressing ctrl + meta + shift. This is
a generalization of the mouse-track-insert feature (ctrl + select
text, if you don't know this trick, try it :-)). This method allows to
fill different holes faster than with the usual copy-paste method.

After replacement the next hole is automatically made active so you
can fill it immediately by hitting again ctrl-meta-y or ctrl + meta +
shift + mouse select.

TO JUMP TO THE ACTIVE HOLE, just hit meta-return. You must be in the
buffer containing the active hole. the point will move to the active
hole, and the active hole will be destroyed so you can type something
to put at its place. The following hole is automatically made active,
so you can hit meta-return again.

It is useful in combination with abbreviations. For example in
coq-mode \"fix\" is an abbreviation for Fixpoint # (# : #) {struct #} :
# := #, where each # is a hole. Then hitting meta-return goes from one
hole to the following and you can fill-in each hole very quickly.

                          BUGS

 o Replacing holes with mouse in fsf emacs works but it seems that one
more click is needed to really see the replacement

 o Don't try to make overlapping holes, it doesn't work. (what would
it mean anyway?)

 o With FSF emacs, cutting or pasting a hole wil not produce new
holes, and undoing on holes cannot make holes re-appear. With Xemacs
it will, but if you copy paste the active hole, you will get several
holes highlighted as the active one (whereas only one of them really
is), which is annoying.

 o Tell me (Pierre.Courtieu@univ-orleans.fr)

")
  (goto-char (point-min))
  (if (string-match "NU Emacs" (emacs-version))
		(view-buffer (current-buffer) (function (lambda (b) (bury-buffer))))
	 (view-mode nil (function (lambda (b) (bury-buffer))))
	 )
  )



(cond
 ((string-match "NU Emacs" (emacs-version))
  (transient-mark-mode 1)  ; for holes created by a simple click
;Pierre: should do almost what region-exists-p does in xemacs
  (defmacro holes-region-exists-p nil
	 "Returns t if the mark is active, nil otherwise."
	 `(not (eq mark-active nil))
	 )
  (defmacro holes-get-selection nil "see x-get-selection"
	 '(x-get-selection))))

(cond
 ((string-match "XEmacs" (emacs-version))
  (defmacro holes-region-exists-p nil "see region-exists-p"
	 '(region-exists-p)
	 )
  (defmacro holes-get-selection nil "see get-selection"
	 '(get-selection))))

;intialization;;;;;;;;;;;;;;;;;;;;;;;;;
(defvar holes-default-hole (make-detached-span)
  "A empty detached hole used as the default hole. You should not use 
this variable.")
(detach-span holes-default-hole)
(defvar holes-active-hole holes-default-hole
  "The current active hole. There can be only one active hole at a time, 
and this is this one. This is not buffer local.")
;this counter is used to differenciate every hole
(defvar holes-counter 0 
  "The global number of holes. For internal use only.")
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;customizable;;;;;;;;;;;;;;;;;;;;;;;;;;
(defcustom holes-empty-hole-string "#"
  "string to be inserted for empty hole (don't put an empty string).")

(defcustom holes-empty-hole-regexp "#\\|\\(@{\\)\\([^{}]*\\)\\(}\\)"
  "Regexp denoting a hole in abbrevs. Must match either `holes-empty-hole-string' or a regexp formed by three consecutive groups (i.e. \\\\(...\\\\) )  (other groups must be shy (i.e. \\\\(?:...\\\\))), denoting the exact limits of the hole (the middle group), the opening and closing delimiters of the hole (first and third groups) which will be deleted after abbrev expand. For example: \"#\\|\\(@{\\)\\([^{}]*\\)\\(}\\)\" matches any # or @{text} but in the second case the abbrev expand will be a hole containing text without brackets.")

(defcustom holes-search-limit 1000
  "number of chars to look forward when looking for the next hole, unused for now");unused for the moment


; The following is customizable by a command of the form:
;for dark background
;(custom-set-faces
; '(holes-active-hole-face 
;   ((((type x) (class color) (background light))     
;     (:background "paleVioletRed")))
;   )
; )

(defface active-hole-face
    '((((class grayscale) (background light)) (:background "dimgrey"))
      (((class grayscale) (background dark))  (:background "LightGray"))
      (((class color) (background dark)) (:background "darkred") (:foreground "white"))
      (((class color) (background light))     (:background "paleVioletRed" (:foreground "black")))
					;??(t (:background t))
      )
    "Font Lock  face used to highlight the active hole."
    )

(defface inactive-hole-face
    '((((class grayscale) (background light)) (:background "lightgrey"))
      (((class grayscale) (background dark))  (:background "Grey"))
      (((class color) (background dark)) (:background "mediumblue") (:foreground "white"))
      (((class color) (background light))     (:background "lightsteelblue" (:foreground "black")))
					;??(t (:background t))
      )
    "Font Lock  face used to highlight the active hole."
    )

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
 





(defun holes-region-beginning-or-nil ()
  (and (holes-region-exists-p) (region-beginning))
  )

(defun holes-region-end-or-nil ()  
  (and (holes-region-exists-p) (region-end))
  )

(defun holes-copy-active-region ()
  (assert (holes-region-exists-p) nil "the region is not active now.")
  (copy-region-as-kill (region-beginning) (region-end))
  (car kill-ring)
  )

(defun holes-is-hole-p (SPAN) 
	(span-property SPAN 'hole)
	
  )

(defun holes-hole-start-position (HOLE)
  (assert (holes-is-hole-p HOLE) t "holes-hole-start-position: given span is not a hole")
  (span-start HOLE)
  )

(defun holes-hole-end-position (HOLE)
  (assert (holes-is-hole-p HOLE) t "holes-hole-end-position:given span is not a hole")
  (span-end HOLE)
  )

(defun holes-hole-buffer (HOLE)
  (assert (holes-is-hole-p HOLE) t "holes-hole-buffer: given span is not a hole")
  (span-buffer HOLE)
  )

(defun holes-hole-at (&optional pos)
  "Returns the hole (an span) at pos in current buffer if pos is not
  in a hole raises an error."

  (interactive)
  (span-at (or pos (point)) 'hole)
  )


(defun holes-active-hole-exist-p ()

  "Returns t if the active hole exists and is not empty (ie
  detached). Use this to know if the active hole is set and
  usable (don't use the active-hole-marker variable)."

  (not (span-detached-p holes-active-hole))
  )


(defun holes-active-hole-start-position ()
  "Returns the position of the start of the active hole
  (see `active-hole-buffer' to get its buffer). Returns an
  error if active hole doesn't exist (the marker is set to
  nothing)."

  (assert (holes-active-hole-exist-p) t 
	  "holes-active-hole-start-position: no active hole")
  (holes-hole-start-position holes-active-hole)
  )

(defun holes-active-hole-end-position ()
  "Returns the position of the start of the active hole
  (see `active-hole-buffer' to get its buffer). Returns an
  error if active hole doesn't exist (the marker is set to
  nothing)."
  
  (assert (holes-active-hole-exist-p) t
	  "holes-active-hole-end-position: no active hole")
  (holes-hole-end-position holes-active-hole)
  )


(defun holes-active-hole-buffer ()

  "Returns the buffer containing the active hole, raise an
  error if the active hole is not set. Don't care if the
  active hole is empty."

  (assert (holes-active-hole-exist-p) t
	  "holes-active-hole-buffer: no active hole")
  (holes-hole-buffer holes-active-hole)
  )

(defun holes-goto-active-hole ()
  
  "Sets point to active hole and raises an error if
  active-hole is not set"
  
  (interactive)
  (assert (holes-active-hole-exist-p) t 
	  "holes-goto-active-hole: no active hole")
  (goto-char (holes-active-hole-start-position)) ; (holes-active-hole-buffer)
  )


(defun holes-highlight-hole-as-active (HOLE)
  "Highlights a hole with the `active-hole-face'. DON'T USE
  this as it would break synchronization (non active hole
  highlighted)."

  (assert (holes-is-hole-p HOLE) t
	  "holes-highlight-hole-as-active: given span is not a hole")
  (set-span-face HOLE 'active-hole-face)
  )

(defun holes-highlight-hole (HOLE)
  "Highlights a hole with the not active face. DON'T USE
  this as it would break synchronization (active hole non
  highlighted)."

  (assert (holes-is-hole-p HOLE) t
	  "holes-highlight-hole: given span is not a hole %S" HOLE)
  (set-span-face HOLE 'inactive-hole-face)
  )


(defun holes-disable-active-hole ()
  "Disable the active hole, the goal remains but is not the
  active one anymore. Does nothing if the active hole is
  already disable."

  (if (not (holes-active-hole-exist-p)) 
      ()
     ; HACK: normal hole color, this way undo will show this
     ; hole normally and not as active hole. Ideally, undo
     ; should restore the active hole, but it doesn't, so
     ; we put the 'not active' color
    (holes-highlight-hole holes-active-hole)
    (setq holes-active-hole holes-default-hole)
    )
  )



(defun holes-set-active-hole (HOLE)

  "Sets active hole to HOLE. Error if HOle is not a hole."
  
  (assert (holes-is-hole-p HOLE) t
	  "holes-set-active-hole: given span is not a hole")
  (if (holes-active-hole-exist-p) (holes-highlight-hole holes-active-hole))
  (setq holes-active-hole HOLE)
  (holes-highlight-hole-as-active holes-active-hole)
  )


(defun holes-is-in-hole-p (&optional pos)

  "Returns t if pos (default: point) is in a hole, nil
  otherwise."

  (not (eq (holes-hole-at pos) nil))
  )



(defun holes-make-hole (start end)
  "Makes and returns an (span) hole from start to end."
  (let ((ext (make-span start end)))
    (set-span-properties
     ext `(
			  hole ,holes-counter
			  mouse-face highlight
			  priority 100		; what should I put here? I want holes to have big priority 
			  face secondary-selection
			  start-open nil
			  end-open t
			  duplicable t
;       unique t
			  detachable t			 ;really disappear if empty; doesn't work with gnu emacs
;       pointer frame-icon-glyph
			  help-echo "this is a \"hole\", button 2 to forget, button 3 to destroy, button 1 to make active"
			  'balloon-help "this is a \"hole\", button 2 to forget, button 3 to destroy, button 1 to make active"
			  ))

    (set-span-keymap ext hole-map)
    (setq holes-counter (+ holes-counter 1))
    ext
    ) 
  )

(defun holes-make-hole-at (&optional start end)

  "makes a hole from start to end, if no arg default hole after point,
  if only one arg: error. Returns the span"
  (interactive)
  
  (let* ((rstart (or start (holes-region-beginning-or-nil) (point)))
			(rend (or end (holes-region-end-or-nil) (point))))
    (if (eq rstart rend) 
		  (progn 
			 (insert-string holes-empty-hole-string)
			 (setq rend (point))
			 )
      )
    (holes-make-hole rstart rend)
    )
  )


(defun holes-clear-hole (HOLE)
  (assert (holes-is-hole-p HOLE) t
			 "holes-clear-hole: given span is not a hole")
  
  (if (and (holes-active-hole-exist-p) (eq holes-active-hole HOLE))
      (holes-disable-active-hole)
    )
  (delete-span HOLE)
  )

(defun holes-clear-hole-at (&optional pos)
  "Clears hole at pos (default=point)."
  (interactive)
  (if (not (holes-is-in-hole-p (or pos (point)))) 
	   (error "holes-clear-hole-at: no hole here"))
  (holes-clear-hole (holes-hole-at (or pos (point))))
  )


(defun holes-map-holes (FUNCTION &optional OBJECT FROM TO)
  (fold-spans FUNCTION OBJECT FROM TO nil nil 'hole) 
  )



(defun holes-mapcar-holes (FUNCTION &optional FROM TO PROP)
  (mapcar-spans FUNCTION FROM TO 'hole)
  )

(defun holes-clear-all-buffer-holes (&optional start end)

  "clears all holes leaving their contents"

  (interactive)
  (holes-disable-active-hole)
  (holes-mapcar-holes 'holes-clear-hole (or start (point-min)) (or end (point-max)) 'hole)
  )



; limit ?
(defun holes-next (pos BUFFER)

  "returns the first hole after pos (or after the hole at pos if there
  is one) (default pos= point), if no hole found, returns nil. limit
  is unused for now."
  
  (holes-map-holes '(lambda (h x) (and (holes-is-hole-p h) h)) BUFFER pos)
  )

(defun holes-next-after-active-hole ()
  (assert (holes-active-hole-exist-p) t 
			 "next-active-hole: no active hole")
  (holes-next (holes-active-hole-end-position)
				 (holes-active-hole-buffer))
  )

(defun holes-set-active-hole-next (&optional BUFFER pos)

  "sets the active hole to the first hole after pos
  (default pos=point), in BUFFER."
  
  (interactive)
  (let ((nxthole (holes-next (or pos (point))
									 (or BUFFER (current-buffer)))))
    (if nxthole 
		  (progn 
	       (holes-set-active-hole nxthole)
			 )
		(holes-disable-active-hole)
      )
    )
  )

;(defun holes-set-active-hole-next-after-active ()
;  "sets the active hole to the first hole after active
;  hole.";;;;

;  (interactive)
;  (holes-next-after-active-hole)
;)




(defun holes-replace-segment (start end str &optional BUFFER)

  "Erase chars between start and end, and insert str at its
  place, shifting markers."

  (interactive)
  (save-excursion 
    (set-buffer (or BUFFER (current-buffer)))
    (delete-region start end)
    (goto-char start)
    (insert-string str)
    )
  )



(defun holes-replace (str &optional thehole)

  "Replace the hole (default = the active hole) by str (str was
  optionnal but not anymore), do not use this, it breaks the right
  colorization of the active goal(FIXME?). Use `replace-active-hole'
  instead. "

  (if (and (not thehole)
	   (not (holes-active-hole-exist-p)))
      (error "no hole to fill")
    ; defensive: replacing the hole should make it 
    ; detached and therefore inexistent
    ; other reason: this a hack: unhighlight so
    ; that undo wont show it highlighted)
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
		(detach-span exthole) ; this seems necessary for span overlays,
			    ; where the buffer attached to the span is not removed
			    ; automatically by the fact that the span is removed from
			    ; the buffer (holes-replace-segment should perhaps take care of
			    ; that)
		)
    )
  )

(defun holes-replace-active-hole (&optional str)
   "Replace the active hole by str, if no str is given, then put the selection instead."
  (if (not (holes-active-hole-exist-p)) ()
    (holes-replace 
     (or str (holes-get-selection) (error "nothing to put in hole"))
     holes-active-hole)
    ))


(defun holes-replace-update-active-hole (&optional str)

  "replace holes-active-hole by str like holes-replace-active-hole,
  but then sets active-hole to the following hole if it
  exists."

  (interactive)
  (assert (holes-active-hole-exist-p) t 
	  "holes-replace-update-active-hole: no active hole")
  (if (not (holes-active-hole-exist-p)) 
      ()
    (let ((nxthole (holes-next-after-active-hole)))
      (holes-replace-active-hole 
       (or str 
			  (and (holes-region-exists-p) (holes-copy-active-region))
			  (holes-get-selection) (error "nothing to put in hole")))
      (if nxthole (holes-set-active-hole nxthole)
		  (setq holes-active-hole holes-default-hole))
      )
    )
  )


(defun holes-delete-update-active-hole () 

  "deletes active-hole and supresses its content and sets
  holes-active-hole to the next hole if it exists"

  (interactive)
  (holes-replace-update-active-hole "")
  )

(defun holes-set-make-active-hole (&optional start end)
  (interactive)
  (holes-set-active-hole (holes-make-hole-at start end))
  )

;;; mouse stuff, I want to make something close to mouse-track-insert
;;; of xemacs, but with modifier ctrl-meta and ctrl-meta-shift

;; emacs and xemacs have different ways of dealing with mouse
;; selection, but mouse-track(xemacs) mouse-drag-region(fsf emacs)
;; have nearly the same meaning for me. So I define this
;; track-mouse-selection.
(eval-and-compile
 (cond
  ((fboundp 'mouse-track)   
   (defsubst holes-track-mouse-selection (event) 
     "see `mouse-track'"
     (mouse-track event)))
  ((fboundp 'mouse-drag-region)   
   (defsubst holes-track-mouse-selection (event)
     "see `mouse-drag-region'"
     (mouse-drag-region event)))
  (t
   (error 
    "Your (X)Emacs version is not compatible with holes (too old or
    new version?), sorry."))
  )
 )

;; number of clicks for emacs and xemacs
(eval-and-compile
 (cond
  ((fboundp 'mouse-track)   
   (defsubst holes-track-mouse-clicks () 
     "see `mouse-track-click-count'"
     mouse-track-click-count))
  ((fboundp 'mouse-drag-region)   
   (defsubst holes-track-mouse-clicks ()
     "see `mouse-selection-click-count'"
     (+ mouse-selection-click-count 1)))
  (t
   (error 
    "Your (X)Emacs version is not compatible with holes (too old or
    new version?), sorry."))
  )
 )

(defun holes-mouse-replace-active-hole (event)
  (interactive "*e")
  (holes-track-mouse-selection event)
  (save-excursion
    ;;HACK: nothing if one click (but a second is perhaps coming)
    (if (and (eq (holes-track-mouse-clicks) 1)
				 (not (holes-region-exists-p)))
		  ()
      (if (not (holes-region-exists-p)) 
			 (error "nothing to put in hole")
		  (holes-replace-update-active-hole (holes-get-selection))
		  (message "hole replaced")
		  )
      )
    )
;  (zmacs-deactivate-region)
  )

(defun holes-destroy-hole (&optional SPAN)
  (interactive)
  (let* ((sp (or SPAN (holes-hole-at (point)) (error "no hole to destroy"))))
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


(defun holes-hole-at-event (event) (span-at-event event 'hole))

(defun holes-mouse-destroy-hole (event)
  (interactive "*e")
  (holes-destroy-hole (holes-hole-at-event event))
  )


;(span-at-event EVENT &optional PROPERTY BEFORE AT-FLAG)
;;comprend pas??
(defun holes-mouse-forget-hole (event)
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
  (interactive "*e")
 ;(set-mark (point))
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
  (interactive "*e")
  (let ((ext (holes-hole-at-event event)))
    (if (and ext (holes-is-hole-p ext))
	(holes-set-active-hole ext)
      (error "No hole here"))
    )
  )


(defun holes-set-point-next-hole-destroy ()
  (interactive)
  (assert (holes-active-hole-exist-p) nil "no active hole")
  (assert (eq (current-buffer) (holes-active-hole-buffer)) nil
	  "active hole not in this buffer")
  (holes-goto-active-hole)
  (holes-delete-update-active-hole)
  )


;;;;;;;;;Customizable key bindings;;;;;;;;;;



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
  "Keymap to use on the holes's overlays.")

(defvar holes-mode-map
  (let ((map (make-sparse-keymap)))
	 (define-key map [(control c) h] 'holes-set-make-active-hole)
	 (define-key map [(control c) (meta y)] 'holes-replace-update-active-hole)
	 (define-key map [(control meta down-mouse-1)] 'holes-mouse-set-make-active-hole)
	 (define-key map [(control meta shift down-mouse-1)] 'holes-mouse-replace-active-hole)
	 (define-key map [(meta return)] 'holes-set-point-next-hole-destroy)
    map)
  "Keymap of holes-mode. This is not the keymap used on holes's overlay
(see `hole-map' instead). This one is active whenever we are on a
buffer where holes-mode is active.")  

(message "holes: milieu")

(or (assq 'holes-mode minor-mode-map-alist)
    (setq minor-mode-map-alist
          (cons (cons 'holes-mode holes-mode-map)
                minor-mode-map-alist)))

(message "holes: milieu après")

;(global-set-key  [(control meta **WRONG** space ) ] 'holes-set-active-hole-next)


;;;;;;;;;;; End Customizable key bindings ;;;;;

;;; utilities to be used in conjunction with abbrevs.
;;; The idea is to put abbrevs of the form:
;(define-abbrev-table 'tuareg-mode-abbrev-table 
;      '(
;	("l" "let # = # in" replace-#-after-abbrev2 0)
;	)
;      )
; where replace-#-after-abbrev2 should be a function which replace the
; two #'s (two occurences going backward from abbrev expantion point)
; by holes and leave point at the first # (deleting
; it). holes-set-point-next-hole-destroy allow to go to the next hole.

;following function allow to replace occurrences of a string by a
;hole.

;c must be a string of length 1
(defun holes-count-char-in-string (c str)
  (let ((cpt 0) (s str))
	 (while (not (string-equal s ""))
		(if (string-equal (substring s 0 1) c) (setq cpt (+ cpt 1)))
		(setq s (substring s 1))
		)
	 cpt
	 )
  )

(defun holes-count-re-in-string (regexp str)
  (let ((cpt 0) (s str))
	 (while (and (not (string-equal s "")) (string-match regexp s) )
		(setq cpt (+ cpt 1))
		(setq s (substring s (match-end 0)))
		)
	 cpt
	 )
  )

(defun holes-count-chars-in-last-expand ()
  (length (abbrev-expansion last-abbrev-text))
  )

(defun holes-count-newlines-in-last-expand ()
  (holes-count-char-in-string "\n" (abbrev-expansion last-abbrev-text))
  )

(defun holes-indent-last-expand ()
  "Indents last abbrev expansion. Must be called when the point is at
end of last abbrev expansion. "
  (let ((n (holes-count-newlines-in-last-expand)))
	 (save-excursion 
		(previous-line n)
		(while (>= n 0)
		  (funcall indent-line-function)
		  (next-line 1)
		  (setq n (- n 1))
		  )
		)
	 )
  )

(defun holes-count-holes-in-last-expand ()
  (holes-count-re-in-string holes-empty-hole-regexp (abbrev-expansion last-abbrev-text))
  )

(defun holes-replace-string-by-holes (start end str)

  "make occurrence of str holes between start and end. sets the
active hole to the last created hole and unsets it if no hole is
created"

  (interactive)
  (holes-disable-active-hole)
  (let ((lgth (length str)))
    (save-excursion
      (goto-char end)
      (while (search-backward str start t) 
	(holes-make-hole (point) (+ (point) lgth))
	(holes-set-active-hole-next)
	)
      )
    )
  )

(defun holes-replace-string-by-holes-backward (num regexp)

  "make num occurrences of str be holes looking backward. sets the
active hole to the last created hole and unsets it if no hole is
created. return t if num is > 0, nil otherwise."

  (interactive)
  (holes-disable-active-hole)
  (if (<= num 0) nil
	 (let* ((n num) (lgth 0))
		(save-excursion
		  (while (> n 0)
			 (progn 
				(re-search-backward regexp)
				(if (string-equal (match-string 0) holes-empty-hole-string) 
					 (holes-make-hole (match-beginning 0) (match-end 0))
				  (holes-make-hole (match-beginning 2) (match-end 2))
				  (goto-char (match-beginning 3))
				  (delete-char (length (match-string 3)))
				  (goto-char (match-beginning 1))
				  (delete-char (length (match-string 1))))
				  (holes-set-active-hole-next)
				(setq n (- n 1)))
			 )
		  )
		t
		)
	 )
  )


(defun holes-replace-string-by-holes-move-point (start end str)

  (interactive)
  (holes-replace-string-by-holes start end str)
  (holes-set-point-next-hole-destroy)
  )

(defun holes-replace-string-by-holes-backward-move-point (num str)

  (interactive)
  (and (holes-replace-string-by-holes-backward num str)
		 t ;(holes-set-point-next-hole-destroy)
		 )
  )



(defun holes-abbrev-complete ()
  "Complete abbrev by putting holes and indenting. Moves point at beginning of expanded text."
  (let ((pos last-abbrev-location))
	 (holes-indent-last-expand)
	 (holes-replace-string-by-holes-backward-move-point 
	  (holes-count-holes-in-last-expand) holes-empty-hole-regexp)
	 (if (> (holes-count-holes-in-last-expand) 1) 
		  (progn (goto-char pos)
					(message "Hit M-ret to jump to active hole. M-x holes-short-doc to see holes doc."))

		(if (= (holes-count-holes-in-last-expand) 0) () ; no hole, stay here.
		  (goto-char pos)
		  (holes-set-point-next-hole-destroy) ; if only one hole, go to it.
		  )
		)
	 )
  )

; insert the expansion of abbrev s, and replace #s by holes. It was
; possible to implement it with a simple ((insert s) (expand-abbrev))
; but undo would show the 2 steps, which is bad.

(defun holes-insert-and-expand (s)
  (let* ((pos (point))
			(exp (abbrev-expansion s))
			(c (holes-count-re-in-string holes-empty-hole-regexp exp)))
	 (insert exp)
	 (holes-replace-string-by-holes-backward-move-point c holes-empty-hole-regexp)
	 (if (> c 1) (goto-char pos)
		(goto-char pos)
		(holes-set-point-next-hole-destroy) ; if only one hole, go to it.
		)
	 (if (> c 1) (message "Hit M-ret to jump to active hole. M-x holes-short-doc to see holes doc.")
		)	 
	 )
  )

(defvar holes-mode nil "t if holes mode is on, nil otherwise.")

(defun holes-mode (&optional arg)
  "if arg is nil, then toggle holes mode on/off. If arg is
positive, then turn holes mode on. If arg is negative, then
turn it off."
  (interactive)
  (setq holes-mode (if (null arg) (not holes-mode)
							(> (prefix-numeric-value arg) 0)))
  )

(or (assq 'holes-mode minor-mode-alist)
	 (setq minor-mode-alist
			 (cons '(holes-mode " Holes") minor-mode-alist)))

(provide 'holes)

