;; $Header: /usr/local/cvsroot/emacs-cl/contrib/gabriel/frpoly.cl,v 1.1 2004/05/05 05:41:56 lars Exp $
;; $Locker:  $

;; FRPOLY -- Benchmark from Berkeley based on polynomial arithmetic.
;; Originally writen in Franz Lisp by Richard Fateman.

;; PDIFFER1 appears in the code, but is not defined; is not called for in this
;; test, however.

;;
;;	This contain 2 fixes from Gabriel's book.
;;
;;         "ptimes3": after label 'b', change the "if" to a "cond".
;;		The "go" should be activated when the condition
;;		holds, NOT when it fails.
;;
;;	   The variables *x*, u*, and v are used specially, since this is
;;		used to handle polynomial coefficients in a recursive
;;		way. Declaring them global is the wrong approach.

(defvar ans)
(defvar coef)
(defvar f)
(defvar inc)
(defvar i)
(defvar qq)
(defvar ss)
(defvar v)
(defvar *x*)
(defvar *alpha*)
(defvar *a*)
(defvar *b*)
(defvar *chk)
(defvar *l)
(defvar *p)
(defvar q*)
(defvar u*)
(defvar *var)
(defvar *y*)
(defvar r)
(defvar r2)
(defvar r3)
(defvar start)
(defvar res1)
(defvar res2)
(defvar res3)

(defmacro pointergp (x y) `(> (get ,x 'order)(get ,y 'order)))
(defmacro pcoefp (e) `(atom ,e))

(defmacro pzerop (x) 
  `(if (numberp ,x) 					; no signp in CL	
       (zerop ,x)))		      
(defmacro pzero () 0)
(defmacro cplus (x y) `(+ ,x ,y))
(defmacro ctimes (x y) `(* ,x ,y))

(defun pcoefadd (e c x) 
  (if (pzerop c)
      x
      (cons e (cons c x))))

(defun pcplus (c p)
  (if (pcoefp p)
      (cplus p c)
      (psimp (car p) (pcplus1 c (cdr p)))))

(defun pcplus1 (c x)
  (cond ((null x)
	 (if (pzerop c)
	     nil
	     (cons 0 (cons c nil))))
	((pzerop (car x))
	 (pcoefadd 0 (pplus c (cadr x)) nil))
	(t
	 (cons (car x) (cons (cadr x) (pcplus1 c (cddr x)))))))

(defun pctimes (c p) 
  (if (pcoefp p)
      (ctimes c p)
      (psimp (car p) (pctimes1 c (cdr p)))))

(defun pctimes1 (c x)
  (if (null x)
      nil
      (pcoefadd (car x)
		(ptimes c (cadr x))
		(pctimes1 c (cddr x)))))

(defun pplus (x y) 
  (cond ((pcoefp x)
	 (pcplus x y))
	((pcoefp y)
	 (pcplus y x))
	((eq (car x) (car y))
	 (psimp (car x) (pplus1 (cdr y) (cdr x))))
	((pointergp (car x) (car y))
	 (psimp (car x) (pcplus1 y (cdr x))))
	(t
	 (psimp (car y) (pcplus1 x (cdr y))))))

(defun pplus1 (x y)
  (cond ((null x) y)
	((null y) x)
	((= (car x) (car y))
	 (pcoefadd (car x)
		   (pplus (cadr x) (cadr y))
		   (pplus1 (cddr x) (cddr y))))
	((> (car x) (car y))
	 (cons (car x) (cons (cadr x) (pplus1 (cddr x) y))))
	(t (cons (car y) (cons (cadr y) (pplus1 x (cddr y)))))))

(defun psimp (var x)
  (cond ((null x) 0)
	((atom x) x)
	((zerop (car x))
	 (cadr x))
	(t
	 (cons var x))))

(defun ptimes (x y) 
  (cond ((or (pzerop x) (pzerop y))
	 (pzero))
	((pcoefp x)
	 (pctimes x y))
	((pcoefp y)
	 (pctimes y x))
	((eq (car x) (car y))
	 (psimp (car x) (ptimes1 (cdr x) (cdr y))))
	((pointergp (car x) (car y))
	 (psimp (car x) (pctimes1 y (cdr x))))
	(t
	 (psimp (car y) (pctimes1 x (cdr y))))))

(defun ptimes1 (*x* y) 
  (prog (u* v)
	(setq v (setq u* (ptimes2 y)))
     a  
	(setq *x* (cddr *x*))
	(if (null *x*)
	    (return u*))
	(ptimes3 y)
	(go a)))

(defun ptimes2 (y)
  (if (null y)
      nil
      (pcoefadd (+ (car *x*) (car y))
		(ptimes (cadr *x*) (cadr y))
		(ptimes2 (cddr y)))))

(defun ptimes3 (y) 
  (prog (e u c) 
     a1	(if (null y) 
	    (return nil))
	(setq e (+ (car *x*) (car y))
	      c (ptimes (cadr y) (cadr *x*) ))
	(cond ((pzerop c)
	       (setq y (cddr y)) 
	       (go a1))
	      ((or (null v) (> e (car v)))
	       (setq u* (setq v (pplus1 u* (list e c))))
	       (setq y (cddr y))
	       (go a1))
	      ((= e (car v))
	       (setq c (pplus c (cadr v)))
	       (if (pzerop c) 			; never true, evidently
		   (setq u* (setq v (pdiffer1 u* (list (car v) (cadr v)))))
		   (rplaca (cdr v) c))
	       (setq y (cddr y))
	       (go a1)))
     a  (cond ((and (cddr v) (> (caddr v) e))
	       (setq v (cddr v))
	       (go a)))
	(setq u (cdr v))
     b  (cond ((or (null (cdr u)) (< (cadr u) e))
	       (rplacd u (cons e (cons c (cdr u)))) (go e)))
	(cond ((pzerop (setq c (pplus (caddr u) c)))
	       (rplacd u (cdddr u))
	       (go d))
	      (t
	       (rplaca (cddr u) c)))
     e  (setq u (cddr u))
     d  (setq y (cddr y))
	(if (null y)
	    (return nil))
	(setq e (+ (car *x*) (car y))
	      c (ptimes (cadr y) (cadr *x*)))
     c  (cond ((and (cdr u) (> (cadr u) e))
	       (setq u (cddr u))
	       (go c)))
	(go b))) 

(defun pexptsq (p n)
  (do ((n (floor n 2) (floor n 2))
       (s (if (oddp n) p 1)))
      ((zerop n) s)
    (setq p (ptimes p p))
    (and (oddp n) (setq s (ptimes s p)))))

(eval-when (load eval)
  (setf (get 'x 'order) 1)
  (setf (get 'y 'order) 2)
  (setf (get 'z 'order) 3)
  (setq r (pplus '(x 1 1 0 1) (pplus '(y 1 1) '(z 1 1)))	; r= x+y+z+1
	r2 (ptimes r 100000)				 	; r2 = 100000*r
	r3 (ptimes r 1.0)))					; r3 = r with floating point coefficients	


(defun standard-frpoly-test1 ()
  (progn (pexptsq r 2)  (pexptsq r2 2) (pexptsq r3 2) nil))

(defun standard-frpoly-test2 ()
  (progn (pexptsq r 5) (pexptsq r2 5) (pexptsq r3 5) nil))

(defun standard-frpoly-test3 ()
  (progn (pexptsq r 10) (pexptsq r2 10) (pexptsq r3 10) nil))

(defun standard-frpoly-test4 ()
  (progn (pexptsq r 15) (pexptsq r2 15) (pexptsq r3 15) nil))

(defun testfrpoly ()
  (testfrpoly-1)
  (testfrpoly-2)
  (testfrpoly-3)
  (testfrpoly-4))

(defun testfrpoly-1 ()
  (print (time (standard-frpoly-test1))))

(defun testfrpoly-2 ()
  (print (time (standard-frpoly-test2))))

(defun testfrpoly-3 ()
  (print (time (standard-frpoly-test3))))

(defun testfrpoly-4 ()
  (print (time (standard-frpoly-test4))))
