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

;Pierre: added, should do almost what it does in xemacs
(cond
 ((string-match "NU Emacs" (emacs-version))
  (transient-mark-mode 1)  ; for holes created by a simple click
  (defmacro hole-region-exists-p nil
	 "Returns t if the mark is active, nil otherwise."
	 `(not (eq mark-active nil))
	 )))

(cond
 ((string-match "XEmacs" (emacs-version))
  (defmacro hole-region-exists-p nil "see region-exists-p"
	 '(region-exists-p)
	 )))

;intialization;;;;;;;;;;;;;;;;;;;;;;;;;
(setq default-hole (make-detached-span))
(detach-span default-hole)
(setq active-hole default-hole)
;this counter is used to differenciate every hole
(setq hole-counter 0)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;customizable;;;;;;;;;;;;;;;;;;;;;;;;;;
(defcustom empty-hole-string "#"
  "string to be inserted for empty hole (don't put an empty string).")

(defcustom hole-search-limit 1000
  "number of chars to look forward when looking for the next hole, unused for now");unused for the moment


; The following is customizable by a command of the form:
;for dark background
;(custom-set-faces
; '(active-hole-face 
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

(setq hole-map (make-keymap))






(defun region-beginning-or-nil ()
  (and (hole-region-exists-p) (region-beginning))
  )

(defun region-end-or-nil ()  
  (and (hole-region-exists-p) (region-end))
  )

(defun copy-active-region ()
  (assert (hole-region-exists-p) nil "the region is not active now.")
  (copy-region-as-kill (region-beginning) (region-end))
  (car kill-ring)
  )

(defun is-hole-p (SPAN) 
	(span-property SPAN 'hole)
	
  )

(defun hole-start-position (HOLE)
  (assert (is-hole-p HOLE) t "hole-start-position: given span is not a hole")
  (span-start HOLE)
  )

(defun hole-end-position (HOLE)
  (assert (is-hole-p HOLE) t "hole-end-position:given span is not a hole")
  (span-end HOLE)
  )

(defun hole-buffer (HOLE)
  (assert (is-hole-p HOLE) t "hole-buffer: given span is not a hole")
  (span-buffer HOLE)
  )

(defun hole-at (&optional pos)
  "Returns the hole (an span) at pos in current buffer if pos is not
  in a hole raises an error."

  (interactive)
  (span-at (or pos (point)) 'hole)
  )


(defun active-hole-exist-p ()

  "Returns t if the active hole exists and is not empty (ie
  detached). Use this to know if the active hole is set and
  usable (don't use the active-hole-marker variable)."

  (not (span-detached-p active-hole))
  )


(defun active-hole-start-position ()
  "Returns the position of the start of the active hole
  (see `active-hole-buffer' to get its buffer). Returns an
  error if active hole doesn't exist (the marker is set to
  nothing)."

  (assert (active-hole-exist-p) t 
	  "active-hole-start-position: no active hole")
  (hole-start-position active-hole)
  )

(defun active-hole-end-position ()
  "Returns the position of the start of the active hole
  (see `active-hole-buffer' to get its buffer). Returns an
  error if active hole doesn't exist (the marker is set to
  nothing)."
  
  (assert (active-hole-exist-p) t
	  "active-hole-end-position: no active hole")
  (hole-end-position active-hole)
  )


(defun active-hole-buffer ()

  "Returns the buffer containing the active hole, raise an
  error if the active hole is not set. Don't care if the
  active hole is empty."

  (assert (active-hole-exist-p) t
	  "active-hole-buffer: no active hole")
  (hole-buffer active-hole)
  )

(defun goto-active-hole ()
  
  "Sets point to active hole and raises an error if
  active-hole is not set"
  
  (interactive)
  (assert (active-hole-exist-p) t 
	  "goto-active-hole: no active hole")
  (goto-char (active-hole-start-position)) ; (active-hole-buffer)
  )


(defun highlight-hole-as-active (HOLE)
  "Highlights a hole with the `active-hole-face'. DON'T USE
  this as it would break synchronization (non active hole
  highlighted)."

  (assert (is-hole-p HOLE) t
	  "highlight-hole-as-active: given span is not a hole")
;  (message "debug: highlight as active avant")
  (set-span-face HOLE 'active-hole-face)
;  (message "debug: highlight as active avant")
  )

(defun highlight-hole (HOLE)
  "Highlights a hole with the not active face. DON'T USE
  this as it would break synchronization (active hole non
  highlighted)."

  (assert (is-hole-p HOLE) t
	  "highlight-hole: given span is not a hole %S" HOLE)
  (set-span-face HOLE 'inactive-hole-face)
  )


(defun disable-active-hole ()
  "Disable the active hole, the goal remains but is not the
  active one anymore. Does nothing if the active hole is
  already disable."

  (if (not (active-hole-exist-p)) 
      ()
     ; HACK: normal hole color, this way undo will show this
     ; hole normally and not as active hole. Ideally, undo
     ; should restore the active hole, but it doesn't, so
     ; we put the 'not active' color
    (highlight-hole active-hole)
    (setq active-hole default-hole)
    )
  )



(defun set-active-hole (HOLE)

  "Sets active hole to HOLE. Error if HOle is not a hole."
  
  (assert (is-hole-p HOLE) t
	  "set-active-hole: given span is not a hole")
  (if (active-hole-exist-p) (highlight-hole active-hole))
  (setq active-hole HOLE)
  (highlight-hole-as-active active-hole)
  )


(defun is-in-hole (&optional pos)

  "Returns t if pos (default: point) is in a hole, nil
  otherwise."

  (not (eq (hole-at pos) nil))
  )



(defun make-hole (start end)
  "Makes and returns an (span) hole from start to end."
  (let ((ext (make-span start end)))

    (set-span-properties
     ext `(
       hole ,hole-counter
       mouse-face highlight
       priority 5 ; what should I put here, I want holes to have big priority 
       face secondary-selection
       start-open nil
       end-open t
       duplicable t
;       unique t
       detachable t ;really disappear if empty; doesn't work with overlays
;       pointer frame-icon-glyph
		 help-echo "this is a \"hole\", button 2 to forget, button 3 to destroy, button 1 to make active"
		 'balloon-help "this is a \"hole\", button 2 to forget, button 3 to destroy, button 1 to make active"
       ))

    (set-span-keymap ext hole-map)
    (setq hole-counter (+ hole-counter 1))
    ext
    ) 
  )

(defun make-hole-at (&optional start end)

  "makes a hole from start to end, if no arg default hole after point,
  if only one arg: error. Returns the span"
  (interactive)
  
  (let* ((rstart (or start (region-beginning-or-nil) (point)))
	 (rend (or end (region-end-or-nil) (point))))
    (if (eq rstart rend) 
	(progn 
	  (insert-string empty-hole-string)
	  (setq rend (point))
	  )
      )
    (make-hole rstart rend)
    )
  )


(defun clear-hole (HOLE)
  (assert (is-hole-p HOLE) t
	  "clear-hole: given span is not a hole")
  
  (if (and (active-hole-exist-p) (eq active-hole HOLE))
      (disable-active-hole)
    )
  (delete-span HOLE)
  )

(defun clear-hole-at (&optional pos)

  "Clears hole at pos (default=point)."

  (interactive)
  (if (not (is-in-hole (or pos (point)))) 
	   (error "clear-hole-at: no hole here"))
  (clear-hole (hole-at (or pos (point))))
  )


(defun map-holes (FUNCTION &optional OBJECT FROM TO)
  (fold-spans FUNCTION OBJECT FROM TO nil nil 'hole) 
  )



(defun mapcar-holes (FUNCTION &optional BUFFER-OR-STRING FROM TO)
  (mapcar-spans FUNCTION nil 
		  BUFFER-OR-STRING FROM 
		  TO nil 'hole)
  )

(defun clear-all-buffer-holes (&optional start end)

  "clears all holes leaving their contents"

  (interactive)
  (disable-active-hole)
  (mapcar-holes 'clear-hole nil start end)
  )



; limit ?
(defun next-hole (pos BUFFER)

  "returns the first hole after pos (or after the hole at pos if there
  is one) (default pos= point), if no hole found, returns nil. limit
  is unused for now."
  
  (map-holes '(lambda (h x) (and (is-hole-p h) h)) BUFFER pos)
  )

(defun next-after-active-hole ()
  (assert (active-hole-exist-p) t 
	  "next-active-hole: no active hole")
  (next-hole (active-hole-end-position)
	     (active-hole-buffer))
  )

(defun set-active-hole-next (&optional BUFFER pos)

  "sets the active hole to the first hole after pos
  (default pos=point), in BUFFER."
  
  (interactive)
  (let ((nxthole (next-hole (or pos (point))
			    (or BUFFER (current-buffer)))))
    (if nxthole 
	(progn 
	       (set-active-hole nxthole)
	  )
      (message "ici")
      (disable-active-hole)
      )
    )
  )

(defun set-active-hole-next-after-active ()
  "sets the active hole to the first hole after active
  hole."

  (interactive)
  (next-after-active-hole)
)




(defun replace-segment (start end str &optional BUFFER)

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



(defun replace-hole (str &optional thehole)

  "Replace the hole (default = the active hole) by str (str was
  optionnal but not anymore), do not use this, it breaks the right
  colorization of the active goal(FIXME?). Use `replace-active-hole'
  instead. "

  (if (and (not thehole)
	   (not (active-hole-exist-p)))
      (error "no hole to fill")
    ; defensive: replacing the hole should make it 
    ; detached and therefore inexistent
    ; other reason: this a hack: unhighlight so
    ; that undo wont show it highlighted)
    (if (and (active-hole-exist-p)
				 thehole
				 (eq active-hole thehole))
		  (disable-active-hole)
      )
    (let ((exthole (or thehole active-hole)))
      (replace-segment (hole-start-position exthole)
							  (hole-end-position exthole)
							  (or str (car kill-ring)) ;kill ring?
							  (span-buffer exthole)
							  )
		(detach-span exthole) ; this seems necessary for span overlays,
			    ; where the buffer attached to the span is not removed
			    ; automatically by the fact that the span is removed from
			    ; the buffer (replace-segment should perhaps take care of
			    ; that)
		)
    )
  )

(defun replace-active-hole (&optional str)
   "Replace the active hole by str, if no str is given, then put the selection instead."
  (if (not (active-hole-exist-p)) ()
    (replace-hole 
     (or str (x-get-selection) (error "nothing to put in hole"))
     active-hole)
    ))


(defun replace-update-active-hole (&optional str)

  "replace active-hole by str like replace-active-hole,
  but then sets active-hole to the following hole if it
  exists."

  (interactive)
  (assert (active-hole-exist-p) t 
	  "replace-update-active-hole: no active hole")
  (if (not (active-hole-exist-p)) 
      ()
    (let ((nxthole (next-after-active-hole)))
      (replace-active-hole 
       (or str 
			  (and (hole-region-exists-p) (copy-active-region))
			  (x-get-selection) (error "nothing to put in hole")))
      (if nxthole (set-active-hole nxthole)
		  (setq active-hole default-hole))
      )
    )
  )


(defun delete-update-active-hole () 

  "deletes active-hole and supresses its content and sets
  active-hole to the next hole if it exists"

  (interactive)
  (replace-update-active-hole "")
  )

(defun set-make-active-hole (&optional start end)
  (interactive)
  (set-active-hole (make-hole-at start end))
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
   (defsubst track-mouse-selection (event) 
     "see `mouse-track'"
     (mouse-track event)))
  ((fboundp 'mouse-drag-region)   
   (defsubst track-mouse-selection (event)
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
   (defsubst track-mouse-clicks () 
     "see `mouse-track-click-count'"
     mouse-track-click-count))
  ((fboundp 'mouse-drag-region)   
   (defsubst track-mouse-clicks ()
     "see `mouse-selection-click-count'"
     (+ mouse-selection-click-count 1)))
  (t
   (error 
    "Your (X)Emacs version is not compatible with holes (too old or
    new version?), sorry."))
  )
 )

(defun mouse-replace-active-hole (event)
  (interactive "e" event)
  (track-mouse-selection event)
  (save-excursion
    ;;HACK: nothing if one click (but a second is perhaps coming)
    (if (and (eq (track-mouse-clicks) 1)
				 (not (hole-region-exists-p)))
		  ()
      (if (not (hole-region-exists-p)) 
			 (error "nothing to put in hole")
		  (replace-update-active-hole (x-get-selection))
		  (message "hole replaced")
		  )
      )
    )
;  (zmacs-deactivate-region)
  )

(defun destroy-hole (&optional SPAN)
  (interactive)
  (let* ((sp (or SPAN (hole-at (point)) (error "no hole to destroy"))))
	 (save-excursion
		(if (and (active-hole-exist-p)
					(eq sp active-hole))
			 (disable-active-hole))
		(replace-hole "" sp)
		(detach-span sp)
		)
	 (message "hole killed")
	 )
  )


(defun mouse-destroy-hole (event)
  (interactive "e" event)
  (destroy-hole (span-at-event event))
  )


;(span-at-event EVENT &optional PROPERTY BEFORE AT-FLAG)
;;comprend pas??
(defun mouse-forget-hole (event)
  (interactive "e" event)
  (save-excursion
    (let ((ext (span-at-event event)))
      (if (eq ext active-hole)
			 (disable-active-hole))
      (detach-span ext)
      )
    )
  (message "hole deleted")
  )



(defun mouse-set-make-active-hole (event)
  (interactive "e" event)
 ;(set-mark (point))
  (track-mouse-selection event)

  (if (and (eq (track-mouse-clicks) 1)
			  (not (hole-region-exists-p)))
		(set-make-active-hole (point) (point))

	 (if (hole-region-exists-p)
		  (set-make-active-hole)
		(let ((ext (span-at-event event)))
		  (if (and ext (is-hole-p ext))
				(error "Already a hole here")
			 (set-active-hole (make-hole-at)))
		  )
		)
	 )
  )

(defun mouse-set-active-hole (event)
  (interactive "e" event)
  (let ((ext (span-at-event event)))
    (if (and ext (is-hole-p ext))
	(set-active-hole ext)
      (error "No hole here"))
    )
  )


(defun set-point-next-hole-destroy ()
  (interactive)
  (assert (active-hole-exist-p) nil "no active hole")
  (assert (eq (current-buffer) (active-hole-buffer)) nil
	  "active hole not in this buffer")
  (goto-active-hole)
  (delete-update-active-hole)
  )


;;;;;;;;;Customizable key bindings;;;;;;;;;;




;;this for both, these are global keybindings because holes.el is
;;actually a mini mode that can be used in any mode.

(cond
 ((string-match "NU Emacs" (emacs-version))
  ; the mouse binding specific to the keymap of an overlay does not
  ; work for fsf emacs < 21
  (define-key hole-map [(mouse-1)] 'mouse-set-active-hole)
  (define-key hole-map [(mouse-3)] 'mouse-destroy-hole)
  (define-key hole-map [(mouse-2)] 'mouse-forget-hole)
  ; this shortcut was for mark-sexp
  (global-set-key  [(control meta ? ) ] 'set-active-hole-next)
  )

 ((string-match "XEmacs" (emacs-version))
  ;don't know how to make these three work for fsf emacs
  (define-key hole-map [(button1)] 'mouse-set-active-hole)
  (define-key hole-map [(button3)] 'mouse-destroy-hole)
  (define-key hole-map [(button2)] 'mouse-forget-hole)
  ; this shortcut was for mark-sexp
  (global-set-key [(control meta space)] 'set-active-hole-next)
  ))

  (global-set-key [(control meta y)] 'replace-update-active-hole)
  ; this shortcut was for mark-defun
  (global-set-key [(control meta h)]   'set-make-active-hole)
  (global-set-key [(control meta down-mouse-1)] 'mouse-set-make-active-hole)
  (global-set-key [(control meta shift down-mouse-1)]
	 'mouse-replace-active-hole)
  (global-set-key [(meta return)] 'set-point-next-hole-destroy)

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
; it). set-point-next-hole-destroy allow to go to the next hole.

;following function allow to replace occurrences of a string by a
;hole.


(defun replace-string-by-holes (start end str)

  "make occurrence of str holes between start and end. sets the
active hole to the last created hole and unsets it if no hole is
created"

  (interactive)
  (disable-active-hole)
  (let ((lgth (length str)))
    (save-excursion
      (goto-char end)
      (while (search-backward str start t) 
	(make-hole (point) (+ (point) lgth))
	(set-active-hole-next)
	)
      )
    )
  )

(defun replace-string-by-holes-backward (num str)

  "make num occurrences of str be holes looking backward. sets the
active hole to the last created hole and unsets it if no hole is
created"

  (interactive)
  (disable-active-hole)
  (setq n num)
  (let* ((lgth (length str)))
    (save-excursion
      (while (> n 0)
	(progn 
	  (search-backward str) 
	  (make-hole (point) (+ (point) lgth))
	  (set-active-hole-next)
	  (setq n (- n 1)))
	)
      )
    )
  )


(defun replace-string-by-holes-move-point (start end str)

  (interactive)
  (replace-string-by-holes start end str)
  (set-point-next-hole-destroy)
  )

(defun replace-string-by-holes-backward-move-point (num str)

  (interactive)
  (replace-string-by-holes-backward num str)
  (set-point-next-hole-destroy)
  )


;this functions can be used in abbrev definition
(defun holes-abbrev-complete1 ()
  (replace-string-by-holes-backward-move-point 1 empty-hole-string)
  )

(defun holes-abbrev-complete2 ()
  (replace-string-by-holes-backward-move-point 2 empty-hole-string)
  )

(defun holes-abbrev-complete3 ()
  (replace-string-by-holes-backward-move-point 3 empty-hole-string)
  )

(defun holes-abbrev-complete4 ()
  (replace-string-by-holes-backward-move-point 4 empty-hole-string)
  )

(defun holes-abbrev-complete5 ()
  (replace-string-by-holes-backward-move-point 5 empty-hole-string)
  )

(defun holes-abbrev-complete6 ()
  (replace-string-by-holes-backward-move-point 6 empty-hole-string)
  )



(provide 'holes)

