;;; This file implements spans in terms of overlays, for emacs19.
;;; Copyright (C) 1998 LFCS Edinburgh
;;; Author: Healfdene Goguen

;; Maintainer: LEGO Team <lego@dcs.ed.ac.uk>

;; $Id$

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;               Bridging the emacs19/xemacs gulf                   ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; before-list represents a linked list of spans for each buffer.
;; It has the invariants of:
;; * being ordered wrt the starting point of the spans in the list,
;;   with detached spans at the end.
;; * not having overlapping overlays of the same type.

(defvar before-list nil
  "Start of backwards-linked list of spans")

(make-variable-buffer-local 'before-list)


(or (fboundp 'foldr)
(defun foldr (func a seq)
  "Return (func (func (func (... (func a Sn) ...) S2) S1) S0)
when func's argument is 2 and seq is a sequence whose
elements = S0 S1 S2 ... Sn. [tl-seq.el]"
  (let ((i (length seq)))
    (while (> i 0)
      (setq i (1- i))
      (setq a (funcall func a (elt seq i)))
      )
    a)))

(or (fboundp 'foldl)
(defun foldl (func a seq)
  "Return (... (func (func (func a S0) S1) S2) ...)
when func's argument is 2 and seq is a sequence whose
elements = S0 S1 S2 .... [tl-seq.el]"
  (let ((len (length seq))
        (i 0))
    (while (< i len)
      (setq a (funcall func a (elt seq i)))
      (setq i (1+ i))
      )
    a)))

(defsubst span-start (span)
  "Return the start position of SPAN."
  (overlay-start span))

(defsubst span-end (span)
  "Return the end position of SPAN."
  (overlay-end span))

(defun set-span-property (span name value)
  "Set SPAN's property NAME to VALUE."
  (overlay-put span name value))

(defsubst span-property (span name)
  "Return SPAN's value for property PROPERTY."
  (overlay-get span name))

(defun span-read-only-hook (overlay after start end &optional len)
  (error "Region is read-only"))

(defun span-read-only (span)
  "Set SPAN to be read only."
  (set-span-property span 'modification-hooks '(span-read-only-hook))
  (set-span-property span 'insert-in-front-hooks '(span-read-only-hook)))

(defun span-read-write (span)
  "Set SPAN to be writeable."
  (set-span-property span 'modification-hooks nil)
  (set-span-property span 'insert-in-front-hooks nil))

(defun int-nil-lt (m n)
  (cond
   ((eq m n) nil)
   ((not n) t)
   ((not m) nil)
   (t (< m n))))

;; We use end first because proof-locked-queue is often changed, and
;; its starting point is always 1
(defun span-lt (s u)
  (or (int-nil-lt (span-end s) (span-end u))
      (and (eq (span-end s) (span-end u))
	   (int-nil-lt (span-start s) (span-start u)))))

(defun span-traverse (span prop)
  (cond
   ((not before-list)
    ;; before-list empty
    'empty)
   ((funcall prop before-list span)
    ;; property holds for before-list and span
    'hd)
   (t
    ;; traverse before-list for property
    (let ((l before-list) (before (span-property before-list 'before)))
      (while (and before (not (funcall prop before span)))
	(setq l before)
	(setq before (span-property before 'before)))
      l))))

(defun add-span (span)
  (let ((ans (span-traverse span 'span-lt)))
    (cond
     ((eq ans 'empty)
      (set-span-property span 'before nil)
      (setq before-list span))
     ((eq ans 'hd)
      (set-span-property span 'before before-list)
      (setq before-list span))
     (t
      (set-span-property span 'before
			 (span-property ans 'before))
      (set-span-property ans 'before span)))))

(defun make-span (start end)
  "Make a span for the range [START, END) in current buffer."
  (add-span (make-overlay start end)))

(defun remove-span (span)
  (let ((ans (span-traverse span 'eq)))
    (cond
     ((eq ans 'empty)
      (error "Bug: empty span list"))
     ((eq ans 'hd)
      (setq before-list (span-property before-list 'before)))
     (ans
      (set-span-property ans 'before (span-property span 'before)))
     (t (error "Bug: span does not occur in span list")))))

;; extent-at gives "smallest" extent at pos
;; we're assuming right now that spans don't overlap
(defun spans-at-point (pt)
  (let ((overlays nil) (os nil))
    (setq os (overlays-at pt))
    (while os
      (if (not (memq (car os) overlays))
	  (setq overlays (cons (car os) overlays)))
      (setq os (cdr os)))
    overlays))

;; assumes that there are no repetitions in l or m
(defun append-unique (l m)
  (foldl (lambda (n a) (if (memq a m) n (cons a n))) m l))

(defun spans-at-region (start end)
  (let ((overlays nil) (pos start))
    (while (< pos end)
      (setq overlays (append-unique (spans-at-point pos) overlays))
      (setq pos (next-overlay-change pos)))
    overlays))

(defun spans-at-point-prop (pt prop)
  (let ((f (cond
	    (prop (lambda (spans span)
		    (if (span-property span prop) (cons span spans)
		      spans)))
	    (t (lambda (spans span) (cons span spans))))))
    (foldl f nil (spans-at-point pt))))

(defun spans-at-region-prop (start end prop)
  (let ((f (cond
	    (prop (lambda (spans span)
		    (if (span-property span prop) (cons span spans)
		      spans)))
	    (t (lambda (spans span) (cons span spans))))))
    (foldl f nil (spans-at-region start end))))

(defun span-at (pt prop)
  "Return the SPAN at point PT with property PROP.
For XEmacs, span-at gives smallest extent at pos.
For Emacs, we assume that spans don't overlap."
  (car (spans-at-point-prop pt prop)))

(defsubst detach-span (span)
  "Remove SPAN from its buffer."
  (remove-span span)
  (delete-overlay span)
  (add-span span))

(defsubst delete-span (span)
  "Delete SPAN."
  (remove-span span)
  (delete-overlay span))

;; The next two change ordering of list of spans:
(defsubst set-span-endpoints (span start end)
  "Set the endpoints of SPAN to START, END."
  (remove-span span)
  (move-overlay span start end)
  (add-span span))

(defsubst set-span-start (span value)
  "Set the start point of SPAN to VALUE."
  (set-span-endpoints span value (span-end span)))

;; This doesn't affect invariant:
(defsubst set-span-end (span value)
  "Set the end point of SPAN to VALUE."
  (set-span-endpoints span (span-start span) value))

(defsubst delete-spans (start end prop)
  "Delete all spans between START and END with property PROP set."
  (mapcar 'delete-span (spans-at-region-prop start end prop)))

(defun map-spans-aux (f l)
  (cond (l (cons (funcall f l) (map-spans-aux f (span-property l 'before))))
	(t ())))

(defsubst map-spans (f)
  (map-spans-aux f before-list))

(defun find-span-aux (prop-p l)
  (while (and l (not (funcall prop-p l)))
       (setq l (span-property l 'before)))
     l)

(defun find-span (prop-p)
  (find-span-aux prop-p before-list))

(defun span-at-before (pt prop)
  "Return the smallest SPAN at before PT with property PROP.
A span is before PT if it covers the character before PT."
  (let ((prop-pt-p
	 (cond (prop (lambda (span)
		       (let ((start (span-start span)))
			 (and start (> pt start)
			    (span-property span prop)))))
	       (t (lambda (span)
		    (let ((start (span-start span)))
		      (and start (> pt start))))))))
    (find-span prop-pt-p)))
  
(defun prev-span (span prop)
  "Return span before SPAN with property PROP."
  (let ((prev-prop-p
	 (cond (prop (lambda (span) (span-property span prop)))
	       (t (lambda (span) t)))))
    (find-span-aux prev-prop-p (span-property span 'before))))

; overlays are [start, end)
(defun next-span (span prop)
  "Return span after SPAN with property PROP.
If there are two spans overlapping then this won't work."
  (let ((l (member-if (lambda (span) (span-property span prop))
		       (overlays-at
			(next-overlay-change (overlay-start span))))))
    (if l (car l) nil)))


(provide 'span-overlay)
