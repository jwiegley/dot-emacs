;; This file implements spans in terms of extents, for emacs19.
;;
;; Copyright (C) 1998 LFCS Edinburgh
;; Author:	Healfdene Goguen
;; Maintainer:  David Aspinall <David.Aspinall@ed.ac.uk>
;; License:     GPL (GNU GENERAL PUBLIC LICENSE)
;;
;; $Id$

;; XEmacs-Emacs compatibility: define "spans" in terms of overlays.

(defalias 'span-start 'overlay-start)
(defalias 'span-end 'overlay-end)
(defalias 'span-set-property 'overlay-put)
(defalias 'span-property 'overlay-get)
(defalias 'span-make 'make-overlay)
(defalias 'span-detach 'delete-overlay)
(defalias 'span-set-endpoints 'move-overlay)
(defalias 'span-buffer 'overlay-buffer)

(defun span-read-only-hook (overlay after start end &optional len)
  (unless inhibit-read-only
    (error "Region is read-only")))

(defun span-read-only (span)
  "Set SPAN to be read only."
  ;; This function may be called on spans which are detached from a
  ;; buffer, which gives an error here, since text-properties are
  ;; associated with text in a particular buffer position.  So we use
  ;; our own read only hook.
  ;(add-text-properties (span-start span) (span-end span) '(read-only t)))
  ;; 30.8.02: tested using overlay-put as below with Emacs 21.2.1,
  ;; bit this seems to have no effect when the overlay is added to
  ;; the buffer.  (Maybe read-only is only a text property, not an
  ;; overlay property?).
  ;; (overlay-put span 'read-only t))
  (span-set-property span 'modification-hooks '(span-read-only-hook))
  (span-set-property span 'insert-in-front-hooks '(span-read-only-hook)))

(defun span-read-write (span)
  "Set SPAN to be writeable."
  ;; See comment above for text properties problem.
  (span-set-property span 'modification-hooks nil)
  (span-set-property span 'insert-in-front-hooks nil))

(defun span-give-warning (&rest args)
  "Give a warning message."
  (message "You should not edit here!"))

(defun span-write-warning (span)
  "Give a warning message when SPAN is changed."
  (span-set-property span 'modification-hooks '(span-give-warning))
  (span-set-property span 'insert-in-front-hooks '(span-give-warning)))

;; We use end first because proof-locked-queue is often changed, and
;; its starting point is always 1
(defun span-lt (s u)
  (or (< (span-end s) (span-end u))
      (and (eq (span-end s) (span-end u))
	   (< (span-start s) (span-start u)))))

(defun spans-at-point-prop (pt prop)
  (let ((ols ()))
    (dolist (ol (overlays-at pt))
      (if (or (null prop) (overlay-get ol prop)) (push ol ols)))
    ols))

(defun spans-at-region-prop (start end prop &optional val)
  (let ((ols ()))
    (dolist (ol (overlays-in start end))
      (if (or (null prop)
	      (if val (eq val (overlay-get ol prop)) (overlay-get ol prop)))
	  (push ol ols)))
    ols))

(defun span-at (pt prop)
  "Return the SPAN at point PT with property PROP.
For XEmacs, span-at gives smallest extent at pos.
For Emacs, we assume that spans don't overlap."
  (car (spans-at-point-prop pt prop)))

(defsubst span-delete (span)
  "Delete SPAN."
  (let ((predelfn (span-property span 'span-delete-action)))
    (and predelfn (funcall predelfn)))
  (delete-overlay span))

;; The next two change ordering of list of spans:
(defsubst span-mapcar-spans (fn start end prop &optional val)
  "Apply function FN to all spans between START and END with property PROP set"
  (mapcar fn (spans-at-region-prop start end prop (or val nil))))

(defun span-at-before (pt prop)
  "Return the smallest SPAN at before PT with property PROP.
A span is before PT if it begins before the character before PT."
  (let ((ols (if (eq (point-min) pt)
		 nil ;; (overlays-at pt)
	       (overlays-in (1- pt) pt))))
    ;; Check the PROP is set.
    (when prop
      (dolist (ol (prog1 ols (setq ols nil)))
	(if (overlay-get ol prop) (push ol ols))))
    ;; Eliminate the case of an empty overlay at (1- pt).
    (dolist (ol (prog1 ols (setq ols nil)))
      (if (>= (overlay-end ol) pt) (push ol ols)))
    ;; "Get the smallest".  I have no idea what that means, so I just do
    ;; something somewhat random but vaguely meaningful.  -Stef
    (car (last (sort ols 'span-lt)))))
  
(defun prev-span (span prop)
  "Return span before SPAN with property PROP."
  (span-at-before (span-start span) prop))

; overlays are [start, end)
 
(defun next-span (span prop)
  "Return span after SPAN with property PROP."
  ;; Presuming the span-extents.el is the reference, its code does the same
  ;; as the code below.
  (span-at (span-end span) prop)
  ;; ;; 3.4 fix here: Now we do a proper search, so this should work with
  ;; ;; nested overlays, after a fashion.  Use overlays-in to get a list
  ;; ;; for the entire buffer, this avoids repeatedly checking the same
  ;; ;; overlays in an ever expanding list (see v6.1).  (However, this
  ;; ;; list may be huge: is it a bottleneck?)
  ;; ;; [Why has this function never used the before-list ?]
  ;; (let* ((start     (overlay-start span))
  ;; 	 ;; (pos       start)
  ;; 	 (nextos    (overlays-in (overlay-end span) 
  ;; 		     (1+ start)
  ;; 		     (point-max)))
  ;; 	 (resstart  (1+ (point-max)))
  ;; 	 spanres)
  ;;   ;; overlays are returned in an unspecified order; we
  ;;   ;; must search whole list for a closest-next one.
  ;;   (dolist (newres nextos spanres)
  ;;     (if (and (span-property newres prop)
  ;; 	       (< start (span-start newres))
  ;; 	       (< (span-start newres) resstart))
  ;; 	  (progn
  ;; 	    (setq spanres newres)
  ;; 	    (setq resstart (span-start spanres))))))
)

(defsubst span-live-p (span)
  "Return non-nil if SPAN is in a live buffer."
  (and span
       (overlay-buffer span)
       (buffer-live-p (overlay-buffer span))))

(defun span-raise (span)
  "Set priority of span to make it appear above other spans.
FIXME: new hack added nov 99 because of disappearing overlays.
Behaviour is still worse than before."	;??? --Stef
  (span-set-property span 'priority 100))

(defalias 'span-object 'overlay-buffer)

(defun span-string (span)
  (with-current-buffer (overlay-buffer span)
    (buffer-substring (overlay-start span) (overlay-end span))))


;Pierre: new utility functions for "holes" 
(defun set-span-properties (span plist)
  "Set SPAN's properties, plist is a plist."
  (let ((pl plist))
    (while pl
      (let* ((name (car pl))
	     (value (car (cdr pl))))
	(overlay-put span name value)
	(setq pl (cdr (cdr pl))))
      )
    )
  )

(defun span-find-span (overlay-list &optional prop)
  "Returns the first overlay of overlay-list having property prop (default 'span), nil if no such overlay belong to the list."
  (let ((l overlay-list))
    (while (and l (not (overlay-get (car l) (or prop 'span))))
      (setq l (cdr l)))
    (car l)))

(defsubst span-at-event (event &optional prop)
  (span-find-span (overlays-at (posn-point (event-start event))) prop)
  )


(defun make-detached-span ()
  (let ((ol (make-overlay 0 0)))
    (delete-overlay ol)
    ol))

(defun fold-spans (f &optional buffer from to maparg ignored-flags prop val)
  (with-current-buffer (or buffer (current-buffer))
    (let ((ols (overlays-in (or from (point-min)) (or to (point-max))))
	  res)
      ;; Check the PROP.
      (when prop
	(dolist (ol (prog1 ols (setq ols nil)))
	  (if (if val (eq val (overlay-get ol prop)) (overlay-get ol prop))
	      (push ol ols))))
      ;; Iterate in order.
      (setq ols (sort ols 'span-lt))
      (while (and ols (not (setq res (funcall f (pop ols) maparg)))))
      res)))


(defsubst span-detached-p (span)
  "is this span detached? nil for no, t for yes"
  (null (overlay-buffer span)))

(defsubst set-span-face (span face)
  "set the face of a span"
  (overlay-put span 'face face))

(defun set-span-keymap (span map)
  "Set the keymap of SPAN to MAP"
  (overlay-put span 'keymap map)
  (overlay-put span 'local-map map))

(provide 'span-overlay)
