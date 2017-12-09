;; $Header: /usr/local/cvsroot/emacs-cl/contrib/gabriel/div2.cl,v 1.1 2004/05/05 05:41:56 lars Exp $
;; $Locker:  $

;;; DIV2 -- Benchmark which divides by 2 using lists of n ()'s.
;;; This file contains a recursive as well as an iterative test.

(defun create-n (n)
  (declare (type fixnum n))
  (do ((n n (the fixnum (1- n)))
       (a () (push () a)))
      ((= (the fixnum n) 0) a)
    (declare (type fixnum n))))

(defvar ll (create-n 200.))


(defun iterative-div2 (l)
  (do ((l l (cddr l))
       (a () (push (car l) a)))
      ((null l) a)))

(defun recursive-div2 (l)
  (cond ((null l) ())
	(t (cons (car l) (recursive-div2 (cddr l))))))

(defun test-1 (l)
  (do ((i 300 (the fixnum (1- i))))
      ((= (the fixnum i) 0))
    (declare (type fixnum i))
    (iterative-div2 l)
    (iterative-div2 l)
    (iterative-div2 l)
    (iterative-div2 l)))

(defun test-2 (l)
  (do ((i 300 (the fixnum (1- i))))
      ((= (the fixnum i) 0))
    (declare (type fixnum i))
    (recursive-div2 l)
    (recursive-div2 l)
    (recursive-div2 l)
    (recursive-div2 l)))

(defun testdiv2 ()
  (testdiv2-iter)
  (testdiv2-recur))

(defun testdiv2-iter ()
   (print (time (test-1 ll))))

(defun testdiv2-recur ()
   (print (time (test-2 ll))))
