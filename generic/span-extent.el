;; This file implements spans in terms of extents, for xemacs.
;;
;; Copyright (C) 1998 LFCS Edinburgh
;; Author:	Healfdene Goguen
;; Maintainer:  David Aspinall <David.Aspinall@ed.ac.uk>
;; License:     GPL (GNU GENERAL PUBLIC LICENSE)
;;
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

(defsubst set-span-property (span name value)
  "Set SPAN's property NAME to VALUE."
  (set-extent-property span name value))

(defsubst span-read-only (span)
  "Set SPAN to be read only."
  (set-span-property span 'read-only t))

(defsubst span-read-write (span)
  "Set SPAN to be writeable."
  (set-span-property span 'read-only nil))

(defun span-give-warning ()
  "Give a warning message."
  (message "You should not edit here!"))

(defun span-write-warning (span)
  "Give a warning message when SPAN is changed."
  ;; FIXME: implement this in XEmacs, perhaps with after-change-functions
  (set-span-property span 'read-only nil))

(defsubst span-property (span name)
  "Return SPAN's value for property PROPERTY."
  (extent-property span name))

(defsubst delete-span (span)
  "Delete SPAN."
  (let ((predelfn (span-property span 'span-delete-action)))
    (and predelfn (funcall predelfn)))
  (delete-extent span))

(defsubst mapcar-spans (fn start end prop &optional val)
  "Apply function FN to all spans between START and END with property PROP set"
  (mapcar-extents fn nil (current-buffer) start end  nil prop val))

(defsubst span-at (pt prop)
  "Return the smallest SPAN at point PT with property PROP."
  (extent-at pt nil prop))

(defsubst span-at-before (pt prop)
  "Return the smallest SPAN at before PT with property PROP.
A span is before PT if it covers the character before PT."
  (extent-at pt nil prop nil 'before))
  
(defsubst span-start (span)
  "Return the start position of SPAN, or nil if SPAN is detatched."
  (extent-start-position span))

(defsubst span-end (span)
  "Return the end position of SPAN, or nil if SPAN is detatched."
  (extent-end-position span))

(defsubst prev-span (span prop)
  "Return span before SPAN with property PROP."
  (extent-at (extent-start-position span) nil prop nil 'before))

(defsubst next-span (span prop)
  "Return span after SPAN with property PROP."
  (extent-at (extent-end-position span) nil prop nil 'after))

(defsubst span-live-p (span)
    "Return non-nil if SPAN is live and in a live buffer."
  (and span
       (extent-live-p span)
       (buffer-live-p (extent-object span))
       ;; PG 3.4: add third test here to see not detached.
       (not (extent-detached-p span))))

(defun span-raise (span)
  "Function added for FSF Emacs compatibility.  Do nothing here."
  nil)

(defalias 'span-object 'extent-object)
(defalias 'span-string 'extent-string)
  
;Pierre: new untility functions for "holes" 
(defsubst make-detached-span ()
  "Return the buffer owning span."
  (make-extent nil nil)
  )


(defsubst span-buffer (span)
  "Return the buffer owning span."
  (extent-buffer span)
  )

(defsubst span-detached-p (span)
  "is this span detached? nil for no, t for yes"
  (extent-detached-p span)
)

(defsubst set-span-face (span face)
  "set the face of a span"
  (set-extent-face span face)
)

(defsubst fold-spans (FUNCTION &optional OBJECT FROM TO MAPARG FLAGS PROPERTY VALUE)
  "map on span, see map-extent on xemacs"
  (map-extents FUNCTION OBJECT FROM TO MAPARG FLAGS PROPERTY VALUE)
)

(defsubst set-span-properties (span plist)
  "see extent-properties"
  (set-extent-properties span plist)
)

(defsubst set-span-keymap (span kmap)
  (set-extent-keymap span kmap)
  )

;there are more args to extent-at-event
(defsubst span-at-event (event)
  (extent-at-event event)
  )

(provide 'span-extent)
