;;; This file implements spans in terms of extents, for xemacs.
;;; Copyright (C) 1998 LFCS Edinburgh
;;; Author: Healfdene Goguen

;; Maintainer: LEGO Team <lego@dcs.ed.ac.uk>

;; $Id$

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;               Bridging the emacs19/xemacs gulf                   ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Now define "spans" in terms of extents.

(defsubst make-span (start end)
  "Make a span for the range [START, END) in current buffer."
  (make-extent start end))

(defsubst detach-span (span)
  "Remove SPAN from its buffer."
  (detach-extent span))

(defsubst set-span-endpoints (span start end)
  "Set the endpoints of SPAN to START, END."
  (set-extent-endpoints span start end))

(defsubst set-span-start (span value)
  "Set the start point of SPAN to VALUE."
  (set-extent-endpoints span value (extent-end-position span)))

(defsubst set-span-end (span value)
  "Set the end point of SPAN to VALUE."
  (set-extent-endpoints span (extent-start-position span) value))

(defsubst span-read-only (span)
  "Set SPAN to be read only."
  (set-span-property span 'read-only t))

(defsubst span-read-write (span)
  "Set SPAN to be writeable."
  (set-span-property span 'read-only nil))

(defsubst span-property (span name)
  "Return SPAN's value for property PROPERTY."
  (extent-property span name))

(defsubst set-span-property (span name value)
  "Set SPAN's property NAME to VALUE."
  (set-extent-property span name value))

(defsubst delete-span (span)
  "Delete SPAN."
  (delete-extent span))

(defsubst delete-spans (start end prop)
  "Delete all spans between START and END with property PROP set."
  (mapcar-extents 'delete-extent nil (current-buffer) start end  nil prop))

(defsubst span-at (pt prop)
  "Return the smallest SPAN at point PT with property PROP."
  (extent-at pt nil prop))

(defsubst span-at-before (pt prop)
  "Return the smallest SPAN at before PT with property PROP.
A span is before PT if it covers the character before PT."
  (extent-at pt nil prop nil 'before))
  
(defsubst span-start (span)
  "Return the start position of SPAN."
  (extent-start-position span))

(defsubst span-end (span)
  "Return the end position of SPAN."
  (extent-end-position span))

(defsubst prev-span (span prop)
  "Return span before SPAN with property PROP."
  (extent-at (extent-start-position span) nil prop nil 'before))

(defsubst next-span (span prop)
  "Return span after SPAN with property PROP."
  (extent-at (extent-end-position span) nil prop nil 'after))

(provide 'span-extent)
