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
  (make-extent start end))

(defsubst detach-span (span)
  (detach-extent span))

(defsubst set-span-endpoints (span start end)
  (set-extent-endpoints span start end))

(defsubst set-span-start (span value)
  (set-extent-endpoints span value (extent-end-position span)))

(defsubst set-span-end (span value)
  (set-extent-endpoints span (extent-start-position span) value))

(defsubst span-read-only (span)
  (set-span-property span 'read-only t))

(defsubst span-read-write (span)
  (set-span-property span 'read-only nil))

(defsubst span-property (span name)
  (extent-property span name))

(defsubst set-span-property (span name value)
  (set-extent-property span name value))

(defsubst delete-span (span)
  (delete-extent span))

(defsubst delete-spans (start end prop)
  (mapcar-extents 'delete-extent nil (current-buffer) start end  nil prop))

(defsubst span-at (pt prop)
  (extent-at pt nil prop))

(defsubst span-at-before (pt prop)
  (extent-at pt nil prop nil 'before))
  
(defsubst span-start (span)
  (extent-start-position span))

(defsubst span-end (span)
  (extent-end-position span))

(defsubst prev-span (span prop)
  (extent-at (extent-start-position span) nil prop nil 'before))

(defsubst next-span (span prop)
  (extent-at (extent-end-position span) nil prop nil 'after))


(provide 'span-extent)
