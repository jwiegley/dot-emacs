;;; This file implements spans in terms of overlays, for emacs19.
;;; Copyright (C) 1998 LFCS Edinburgh
;;; Author: Healfdene Goguen

;; Maintainer: LEGO Team <lego@dcs.ed.ac.uk>

;; $Log$
;; Revision 1.6  1998/06/02 15:36:51  hhg
;; Corrected comment about this being for emacs19.
;;
;; Revision 1.5  1998/05/29 09:50:10  tms
;; o outsourced indentation to proof-indent
;; o support indentation of commands
;; o replaced test of Emacs version with availability test of specific
;;   features
;; o C-c C-c, C-c C-v and M-tab is now available in all buffers
;;
;; Revision 1.4  1998/05/21 17:27:41  hhg
;; Removed uninitialized os variable in spans-at-region.
;;
;; Revision 1.3  1998/05/21 08:28:52  hhg
;; Initialize 'before pointer in add-span-aux when last-span is nil.
;; Removed span-at-type.
;; Fixed bug in span-at-before, where (span-start span) may be nil.
;; Added spans-at-(point|region)[-prop], which fixes bug of C-c u at end
;; of buffer.
;;
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

(defsubst span-property (span name)
  (overlay-get span name))

(defsubst set-span-property (span name value)
  (overlay-put span name value))

(defun span-lt (s t)
  (or (not (span-start t))
      (and (span-start s)
	   (< (span-start s) (span-start t)))))

(defun add-span (span)
  (if last-span
      (let ((l last-span) (cont (span-lt span l)) tmp)
	(while (and l cont)
	  (if (not (span-property l 'before))
	      (setq cont nil)
	    (setq l (span-property l 'before))
	    (setq cont (span-lt span l))))
	(setq tmp (span-property l 'before))
	(set-span-property l 'before span)
	(set-span-property span 'before tmp))
    (setq last-span span)
    (set-span-property span 'before nil))
  span)

(defun make-span (start end)
  (add-span (make-overlay start end)))

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
  (delete-overlay span)
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

(defun spans-at-region (start end)
  (let ((overlays nil) (pos start))
    (while (< pos end)
      (setq overlays (append (spans-at-point pos) overlays))
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
  (car (spans-at-point-prop pt prop)))

(defsubst delete-spans (start end prop)
  (mapcar 'delete-span (spans-at-region-prop start end prop)))

(defun map-spans-aux (f l)
  (cond (l (cons (funcall f l) (map-spans-aux f (span-property l 'before))))
	(t ())))

(defsubst map-spans (f)
  (map-spans-aux f last-span))

(defun find-span-aux (prop-p l)
  (cond ((not l) ())
	((funcall prop-p l) l)
	(t (find-span-aux prop-p (span-property l 'before)))))

(defun find-span (prop-p)
  (find-span-aux prop-p last-span))

(defun span-at-before (pt prop)
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
