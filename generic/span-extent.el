;;; This file implements spans in terms of extents, for xemacs.
;;; Copyright (C) 1998 LFCS Edinburgh
;;; Author: Healfdene Goguen

;; Maintainer: LEGO Team <lego@dcs.ed.ac.uk>

;; $Log$
;; Revision 1.1  1998/09/03 13:51:33  da
;; Renamed for new subdirectory structure
;;
;; Revision 2.0  1998/08/11 15:00:13  da
;; New branch
;;
;; Revision 1.4  1998/06/10 14:01:48  hhg
;; Wrote generic span functions for making spans read-only or read-write.
;;
;; Revision 1.3  1998/06/02 15:36:44  hhg
;; Corrected comment about this being for xemacs.
;;
;; Revision 1.2  1998/05/19 15:30:27  hhg
;; Added header and log message.
;;

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
