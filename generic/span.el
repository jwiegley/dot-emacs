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
;; Generic functions built on low-level abstract ones
;;

(defun span-property-safe (span name)
  "Like span-property, but return nil if SPAN is nil."
  (and span (span-property span name)))
  
(provide 'span)
;; span.el ends here.
