;; $Header: /usr/local/cvsroot/emacs-cl/contrib/gabriel/puzzle-sda.cl,v 1.1 2004/05/05 05:41:56 lars Exp $
;; $Locker:  $

(eval-when (compile load eval)
	(cl:spy *package*) ; SDA
  (defconstant puzzle-size 511.)	
  (defconstant puzzle-classmax 3.)
  (defconstant puzzle-typemax 12.))

(defvar **iii** 0)
(defvar **kount** 0)
(defvar puzzle-d 8.)
;(proclaim '(type fixnum **iii** **kount** puzzle-d))
;(declaim (type fixnum **iii** **kount** puzzle-d))

(defvar piececount (make-array (1+ puzzle-classmax) :element-type 'fixnum :initial-element 0))
(defvar puzzle-class (make-array (1+ puzzle-typemax) :element-type 'fixnum :initial-element 0))
(defvar piecemax (make-array (1+ puzzle-typemax) :element-type 'fixnum :initial-element 0))
(defvar puzzle (make-array (1+ puzzle-size)))
(defvar puzzle-p (make-array (list (1+ puzzle-typemax) (1+ puzzle-size))))

;(proclaim '(type (array fixnum) piececount puzzle-class piecemax))
;(declaim (type (array fixnum) piececount puzzle-class piecemax))
(defmacro fref (a i) `(the fixnum (aref ,a (the fixnum ,i))))


;(proclaim '(type simple-vector   puzzle))
;(declaim (type simple-vector   puzzle))

;(proclaim '(type (simple-array t (#.(1+ puzzle-typemax) #.(1+ puzzle-size))) puzzle-p))
;(declaim (type (simple-array t (#.(1+ puzzle-typemax) #.(1+ puzzle-size))) puzzle-p))

(defun fit (i j)
  (declare (type fixnum i j))
  (let ((end (fref piecemax i)))
    (declare (type fixnum end))
    (do ((k 0 (the fixnum (1+ k))))
	((> k end) t)
      (declare (type fixnum k))
      (cond ((aref puzzle-p i k)
	     (cond ((aref puzzle (the fixnum (+ j k)))
		    (return nil))))))))

;(proclaim '(function place (fixnum fixnum ) fixnum))
;(declaim (function place (fixnum fixnum ) fixnum))

(defun jil () 3)
(defun place (i j)
  (declare (type fixnum i j))
  (let ((end (fref piecemax i)))
    (declare (type fixnum end))
    (do ((k 0 (the fixnum (1+ k))))
	((> k end))
      (declare (type fixnum k))
      (cond ((aref puzzle-p i k) 
	     (setf (aref puzzle (the fixnum (+ j k))) t))))
    (setf (fref piececount (fref puzzle-class i)) 
	  (the fixnum
	       (- (the fixnum
		       (fref piececount (fref puzzle-class i))) 1)))
    (do ((k j (the fixnum (1+ k))))
	((> k puzzle-size)
	 (terpri)
	 (princ "Puzzle filled")
	 0)
      (declare (type fixnum k))
      (cond ((not (aref puzzle k))
	     (return k))))))

;; SDA
(eval-when (:compile-toplevel)
  (cl:spy (cl:macroexpand '(fref piececount (fref puzzle-class i)))))

;; SDA
(defun test-fn1 (i)
  (declare (type fixnum i))
  (setf (fref piececount (fref puzzle-class i))
	(the fixnum
	     (+ (the fixnum (fref piececount (fref puzzle-class i))) 1))))

;; SDA
(defun test-fn2 (i)
  (declare (type fixnum i))
  (setf (the fixnum (aref piececount (the fixnum (aref puzzle-class i))))
	(the fixnum
	     (+ (the fixnum (the fixnum (aref piececount (the fixnum (aref puzzle-class i))))) 1))))

;; SDA
(defun test-fn3 (i)
  (declare (type fixnum i))
  (setf (the fixnum (aref piececount (the fixnum i)))
	(the fixnum
	     (+ (the fixnum i) 1))))

;; SDA
(defun test-fn4 (i)
  (declare (type fixnum i))
  (setf (the fixnum (aref piececount i))
	(1+ i)))

;; SDA
(defun test-fn5 (i)
  (declare (type fixnum i))
  (setf (aref piececount i)
	(1+ i)))

;(cl:in-package :cl-user)

;; SDA
(defun test-fn6 (i)
  (declare (type fixnum i))
  (setf (aref piececount i)
	(1+ i)))

(defun puzzle-remove (i j)
  (declare (type fixnum i j))
  (let ((end (fref piecemax i)))
    (declare (type fixnum end))
    (do ((k 0 (the fixnum (1+ k))))
	((> k end))
	(declare (type fixnum k))
	(cond ((aref puzzle-p i k)
	       (setf (aref puzzle (the fixnum (+ j k)))  nil))))
    (setf (fref piececount (fref puzzle-class i))
	  (the fixnum
	       (+ (the fixnum (fref piececount (fref puzzle-class i))) 1)))))

(defun trial (j)
  (declare (type fixnum j))
  (let ((k 0))
    (declare (type fixnum k))
    (do ((i 0 (the fixnum (1+ i))))
	((> i puzzle-typemax) 
	 (setq **kount** (the fixnum (1+ **kount**))) nil)
      (declare (type fixnum i))
      (cond ((not (= (the fixnum (fref piececount (fref puzzle-class i))) 0))
	     (cond ((fit i j)
		    (setq k (place i j))
		    (cond ((or (trial k)
			       (= k 0))
			   (setq **kount** (the fixnum (+ **kount** 1)))
			   (return t))
			  (t (puzzle-remove i j))))))))))

(defun definepiece (iclass ii jj kk)
  (declare (type fixnum ii jj kk))
  (let ((index 0))
    (declare (type fixnum index))
    (do ((i 0 (the fixnum (1+ i))))
	((> i ii))
      (declare (type fixnum i))
      (do ((j 0 (the fixnum (1+ j))))
	  ((> j jj))
	(declare (type fixnum j))
	(do ((k 0 (the fixnum (1+ k))))
	    ((> k kk))
	  (declare (type fixnum k))
	  (setq index  
	    (+ i 
	       (the fixnum 
		    (* puzzle-d 
		       (the fixnum 
			    (+ j 
			       (the fixnum 
				    (* puzzle-d k))))))))
	  (setf (aref puzzle-p **iii** index)  t))))
    (setf (fref puzzle-class **iii**) iclass)
    (setf (fref piecemax **iii**) index) 
    (cond ((not (= **iii** puzzle-typemax))
	   (setq **iii** (the fixnum (+ **iii** 1)))))))

(defun puzzle-start ()
  (do ((m 0 (the fixnum (1+ m))))
      ((> m puzzle-size))
    (declare (type fixnum m))
    (setf (aref puzzle m) t))
  (do ((i 1 (the fixnum (1+ i))))
      ((> i 5))
    (declare (type fixnum i))
    (do ((j 1 (the fixnum (1+ j))))
	((> j 5))
      (declare (type fixnum j))
      (do ((k 1 (the fixnum (1+ k))))
	  ((> k 5))
	(declare (type fixnum k))
	(setf (aref puzzle 
		    (+ i 
		       (the fixnum
			    (* puzzle-d 
			       (the fixnum
				    (+ j 
				       (the fixnum
					    (* puzzle-d k))))))))
	      nil)))) 
  (do ((i 0 (the fixnum (1+ i))))
      ((> i puzzle-typemax))
    (declare (type fixnum i))
    (do ((m 0 (the fixnum (1+ m))))
	((> m puzzle-size))
      (declare (type fixnum m))
      (setf (aref puzzle-p i m)  nil)))
  (setq **iii** 0)
  (definepiece 0 3 1 0)
  (definepiece 0 1 0 3)
  (definepiece 0 0 3 1)
  (definepiece 0 1 3 0)
  (definepiece 0 3 0 1)
  (definepiece 0 0 1 3)
  
  (definepiece 1 2 0 0)
  (definepiece 1 0 2 0)
  (definepiece 1 0 0 2)
  
  (definepiece 2 1 1 0)
  (definepiece 2 1 0 1)
  (definepiece 2 0 1 1)
  
  (definepiece 3 1 1 1)
  
  (setf (fref piececount 0) 13.)
  (setf (fref piececount 1) 3)
  (setf (fref piececount 2) 1)
  (setf (fref piececount 3) 1)
  (let ((m (+ 1 (the fixnum (* puzzle-d (the fixnum (+ 1 puzzle-d))))))
	(n 0)(**kount** 0))
    (declare (type fixnum m n **kount**))
    (cond ((fit 0 m) (setq n (place 0 m)))
	  (t (format t "~%Error.")))
    (cond ((trial n) 
	   (format t "~%Success in ~4D trials." **kount**))
	  (t (format t "~%Failure.")))))

(defun testpuzzle ()
  (time (puzzle-start)))
