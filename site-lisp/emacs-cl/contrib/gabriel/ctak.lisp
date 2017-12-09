;; $Header: /usr/local/cvsroot/emacs-cl/contrib/gabriel/ctak.cl,v 1.1 2004/05/05 05:41:56 lars Exp $
;; $Locker:  $

;;; CTAK -- A version of the TAKeuchi function that uses the CATCH/THROW facility. 

(defun ctak (x y z)
  (catch 'ctak (ctak-aux x y z)))

(defun ctak-aux (x y z)
  (declare (type fixnum x y z))
  (cond ((not (< y x))
	 (throw 'ctak z))
	(t (ctak-aux
	     (catch 'ctak
	       (ctak-aux (the fixnum (1- x))
			 y
			 z))
	     (catch 'ctak
	       (ctak-aux (the fixnum (1- y))
			 z
			 x))
	     (catch 'ctak
	       (ctak-aux (the fixnum (1- z))
			 x
			 y))))))

(defun testctak ()
  (print (time (ctak 18 12 6))))
