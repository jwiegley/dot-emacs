;;; visiblity-attempt.el --- Test area for invisibility

;; This file is part of Proof General.

;; Portions © Copyright 1994-2012  David Aspinall and University of Edinburgh
;; Portions © Copyright 2003, 2012, 2014  Free Software Foundation, Inc.
;; Portions © Copyright 2001-2017  Pierre Courtieu
;; Portions © Copyright 2010, 2016  Erik Martin-Dorel
;; Portions © Copyright 2011-2013, 2016-2017  Hendrik Tews
;; Portions © Copyright 2015-2017  Clément Pit-Claudel

;;; Commentary:
;;
;; Test area for invisibility
;;

;;; Code:

(defvar vis nil)

(overlay-put (make-overlay 18 22) 'invisible 'smaller)
(overlay-put (make-overlay 9 43) 'invisible 'larger)

(defun toggle-invis ()
  (interactive)
  (if vis 
      (add-to-invisibility-spec '(larger . t))
    (remove-from-invisibility-spec '(larger . t)))
  (setq vis (not vis)))


;; In this buffer:

;;    M-x eval-buffer RET
;;    M-x toggle-invis

;; The smaller area remains visible, although there is a surrounding
;; overlay which has an invisibility spec which should cover the
;; revealed characters.  Arguably a bug.






