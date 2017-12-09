;; $Header: /usr/local/cvsroot/emacs-cl/contrib/gabriel/stak.cl,v 1.1 2004/05/05 05:41:56 lars Exp $
;; $Locker:  $

;;; STAK -- The TAKeuchi function with special variables instead of
;;; parameter passing.

(defvar stak-x)
(defvar stak-y)
(defvar stak-z)
(proclaim '(type fixnum stak-x stak-y stak-z))

(defun stak (stak-x stak-y stak-z)
  (stak-aux))

(defun stak-aux ()
  (if (not (< stak-y stak-x))
      stak-z
    (let ((stak-x (let ((stak-x (the fixnum (1- stak-x)))
			(stak-y stak-y)
			(stak-z stak-z))
		    (stak-aux)))
	  (stak-y (let ((stak-x (the fixnum (1- stak-y)))
			(stak-y stak-z)
			(stak-z stak-x))
		    (stak-aux)))
	  (stak-z (let ((stak-x (the fixnum (1- stak-z)))
			(stak-y stak-x)
			(stak-z stak-y))
		    (stak-aux))))
      (stak-aux))))

(defun teststak ()
  (print (time (stak 18 12 6))))
