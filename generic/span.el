;; span.el	Datatype of "spans" for Proof General.
;; Copyright (C) 1998 LFCS Edinburgh
;; Author:	Healfdene Goguen
;; Maintainer:  Proof General maintainer <proofgen@dcs.ed.ac.uk>
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
  
(provide 'span)
;; span.el ends here.
