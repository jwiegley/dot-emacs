;;; This file implements spans in terms of overlays, for emacs19.

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

(defun add-span (span l)
  (cond (l (if (or (not (span-start l))
		   (and (span-start span)
			(< (span-start span) (span-start l))))
	       (progn
		 (overlay-put l 'before
			      (add-span span (overlay-get l 'before)))
		 l)
	     (overlay-put span 'before l)
	     span))
	(t span)))

(defsubst make-span (start end)
  (let ((new-span (make-overlay start end)))
    (setq last-span (add-span new-span last-span))
    new-span))

(defsubst set-span-endpoints (span start end)
  (move-overlay span start end))

(defsubst set-span-start (span value)
  (set-span-endpoints span value (span-end span)))

(defsubst set-span-end (span value)
  (set-span-endpoints span (span-start span) value))

(defsubst span-property (span name)
  (overlay-get span name))

(defsubst set-span-property (span name value)
  (overlay-put span name value))

;; relies on only being called from detach-span or delete-span, and so
;; resets value of last-span
(defun remove-span (span l)
  (cond ((not l) ())
	((eq span l) (setq last-span (span-property l 'before)))
	((eq span (span-property l 'before))
	 (set-span-property l 'before (span-property span 'before))
	 l)
	(t (remove-span span (span-property l 'before)))))

(defsubst detach-span (span)
  (remove-span span last-span)
  (cond (running-emacs19 (delete-overlay span))
	(running-xemacs (detach-extent span)))
  (add-span span last-span))

(defsubst delete-span (span)
  (remove-span span last-span)
  (delete-overlay span))

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
