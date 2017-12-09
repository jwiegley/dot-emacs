;; $Header: /usr/local/cvsroot/emacs-cl/contrib/gabriel/tprint.cl,v 1.1 2004/05/05 05:41:56 lars Exp $
;; $Locker:  $

;;; TPRINT -- Benchmark to print and read to the terminal.

(defvar test-atoms '(abc1 cde2 efg3 ghi4 ijk5 klm6 mno7 opq8 qrs9
			  stu0 uvw1 wxy2 xyz3 123a 234b 345c 456d 
			  567d 678e 789f 890g))

(defun tprint-init (m n atoms)
  (let ((atoms (subst () () atoms)))
    (do ((a atoms (cdr a)))
	((null (cdr a)) (rplacd a atoms)))
    (tprint-init-aux m n atoms)))

(defun tprint-init-aux (m n atoms)
  (declare (type fixnum m n))
  (cond ((= m 0) (pop atoms))
	(t (do ((i n (the fixnum (- i 2)))
		(a ()))
	       ((< i 1) a)
	     (push (pop atoms) a)
	     (push (tprint-init-aux (the fixnum (1- m)) n atoms) a)))))

(defvar test-pattern (tprint-init 6. 6. test-atoms))


(defun standard-tprint-test () 
      (print test-pattern))

(defun testtprint ()
  (print (time (print test-pattern))))
