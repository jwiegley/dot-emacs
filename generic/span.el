;; span.el	Datatype of "spans" for Proof General.
;;
;; Copyright (C) 1998 LFCS Edinburgh
;; Author:    Healfdene Goguen
;; License:   GPL (GNU GENERAL PUBLIC LICENSE)
;;
;; $Id$

;;
;; Spans are our abstraction of extents/overlays.
;;
(eval-and-compile
  (cond ((string-match "XEmacs" emacs-version)  
	 (require 'span-extent))
 	(t 
	 (require 'span-overlay))))

;;
;; Generic functions built on low-level concrete ones.
;; 

(defsubst delete-spans (start end prop)
  "Delete all spans between START and END with property PROP set."
  (mapcar-spans 'delete-span start end prop))

(defsubst span-property-safe (span name)
  "Like span-property, but return nil if SPAN is nil."
  (and span (span-property span name)))
  
(defsubst set-span-start (span value)
  "Set the start point of SPAN to VALUE."
  (set-span-endpoints span value (span-end span)))

(defsubst set-span-end (span value)
  "Set the end point of SPAN to VALUE."
  (set-span-endpoints span (span-start span) value))

(provide 'span)
;; span.el ends here.
