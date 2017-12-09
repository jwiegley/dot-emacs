;; $Header: /usr/local/cvsroot/emacs-cl/contrib/gabriel/tak-mod.cl,v 1.1 2004/05/05 05:41:56 lars Exp $
;; $Locker:  $

#+excl
(eval-when (compile) (setq comp::register-use-threshold 6))

(proclaim '(function tak (fixnum fixnum fixnum) fixnum))

(defun tak (x y z)
  (declare (type fixnum x y z))
  (cond ((not (< y x)) z)
	(t
	 (tak
	   (tak (the fixnum (1- x)) y z)
	   (tak (the fixnum (1- y)) z x)
	   (tak (the fixnum (1- z)) x y)))))

(defun testtak ()
  (print (time
	   (progn (tak 18 12 6)
		  (tak 18 12 6)
		  (tak 18 12 6)
		  (tak 18 12 6)
		  (tak 18 12 6)
		  (tak 18 12 6)
		  (tak 18 12 6)
		  (tak 18 12 6)
		  (tak 18 12 6)
		  (tak 18 12 6)))))

#+excl (eval-when (compile) (setq comp::register-use-threshold 3))
