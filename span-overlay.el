;;; This file implements spans in terms of extents, for xemacs.
;;; Copyright (C) 1998 LFCS Edinburgh
;;; Author: Healfdene Goguen

;; Maintainer: LEGO Team <lego@dcs.ed.ac.uk>

;; $Log$
;; Revision 1.2  1998/05/19 15:31:37  hhg
;; Added header and log message.
;; Fixed set-span-endpoints so it preserves invariant.
;; Changed add-span and remove-span so that they update last-span
;; correctly themselves, and don't take last-span as an argument.
;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;               Bridging the emacs19/xemacs gulf                   ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; last-span represents a linked list of spans for each buffer.
;; It has the invariant of being ordered wrt the starting point of
;; the spans in the list, with detached spans at the end.

(defvar last-span nil
  "Start of backwards-linked list of spans")

(make-variable-buffer-local 'last-span)


(defsubst span-start (span)
  (overlay-start span))

(defsubst span-end (span)
  (overlay-end span))

(defun add-span-aux (span l)
  (cond (l (if (or (not (span-start l))
		   (and (span-start span)
			(< (span-start span) (span-start l))))
	       (progn
		 (overlay-put l 'before
			      (add-span-aux span (overlay-get l 'before)))
		 l)
	     (overlay-put span 'before l)
	     span))
	(t span)))

(defun add-span (span)
  (setq last-span (add-span-aux span last-span))
  span)

(defun make-span (start end)
  (add-span (make-overlay start end)))

(defsubst span-property (span name)
  (overlay-get span name))

(defsubst set-span-property (span name value)
  (overlay-put span name value))

;; relies on only being called from detach-span or delete-span, and so
;; resets value of last-span
(defun remove-span-aux (span l)
  (cond ((not l) (error "Bug: removing span from empty list"))
	((eq span (span-property l 'before))
	 (set-span-property l 'before (span-property span 'before))
	 l)
	(t (remove-span-aux span (span-property l 'before)))))

(defun remove-span (span)
  (cond ((not last-span) (error "Bug: empty span list"))
	((eq span last-span)
	 (setq last-span (span-property last-span 'before)))
	(t (remove-span-aux span last-span))))

(defsubst detach-span (span)
  (remove-span span)
  (cond (running-emacs19 (delete-overlay span))
	(running-xemacs (detach-extent span)))
  (add-span span))

(defsubst delete-span (span)
  (remove-span span)
  (delete-overlay span))

;; The next two change ordering of list of spans:
(defsubst set-span-endpoints (span start end)
  (remove-span span)
  (move-overlay span start end)
  (add-span span))

(defsubst set-span-start (span value)
  (set-span-endpoints span value (span-end span)))

;; This doesn't affect invariant:
(defsubst set-span-end (span value)
  (set-span-endpoints span (span-start span) value))

(defun spans-at (start end)
  (let ((overlays nil) (pos start) (os nil))
    (while (< pos end)
      (setq os (overlays-at pos))
      (while os
	(if (not (memq (car os) overlays))
	    (setq overlays (cons (car os) overlays)))
	(setq os (cdr os)))
      (setq pos (next-overlay-change pos)))
    overlays))

(defun spans-at-prop (start end prop)
  (let ((f (cond
	    (prop (lambda (spans span)
		    (if (span-property span prop) (cons span spans)
		      spans)))
	    (t (lambda (spans span) (cons span spans))))))
    (foldl f nil (spans-at start end))))

(defun type-prop (spans span)
  (if (span-property span 'type) (cons span spans) spans))

(defun spans-at-type (start end)
  (foldl 'type-prop nil (spans-at start end)))

(defsubst delete-spans (start end prop)
  (mapcar 'delete-span (spans-at-prop start end prop)))

(defun map-spans-aux (f l)
  (cond (l (cons (funcall f l) (map-spans-aux f (span-property l 'before))))
	(t ())))

(defsubst map-spans (f)
  (map-spans-aux f last-span))

;; extent-at gives "smallest" extent at pos
;; we're assuming right now that spans don't overlap
(defun span-at (pt prop)
  (car (spans-at-prop pt (+ pt 1) prop)))

(defun find-span-aux (prop-p l)
  (cond ((not l) ())
	((funcall prop-p l) l)
	(t (find-span-aux prop-p (span-property l 'before)))))

(defun find-span (prop-p)
  (find-span-aux prop-p last-span))

(defun span-at-before (pt prop)
  (let ((prop-pt-p
	 (cond (prop (lambda (span)
		       (and (> pt (span-start span))
			    (span-property span prop))))
	       (t (lambda (span) (> pt (span-end span)))))))
    (find-span prop-pt-p)))
  
(defun prev-span (span prop)
  (let ((prev-prop-p
	 (cond (prop (lambda (span) (span-property span prop)))
	       (t (lambda (span) t)))))
    (find-span-aux prev-prop-p (span-property span 'before))))

(defun next-span-aux (prop spans)
  (cond ((not spans) nil)
	((span-property (car spans) prop) (car spans))
	(t (next-span-aux prop (cdr spans)))))

;; overlays are [start, end)
(defun next-span (span prop)
  (next-span-aux prop
		 (overlays-at (next-overlay-change (overlay-start span)))))


(provide 'span-overlay)
