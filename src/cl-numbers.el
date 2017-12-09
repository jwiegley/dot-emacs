;;;; -*- emacs-lisp -*-
;;;
;;; Copyright (C) 2003, 2004 Lars Brinkhoff.
;;; This file implements operators in chapter 12, Numbers.

(IN-PACKAGE "EMACS-CL")

;;; System Class NUMBER
;;; System Class COMPLEX
;;; System Class REAL
;;; System Class FLOAT
;;; Type SHORT-FLOAT, SINGLE-FLOAT, DOUBLE-FLOAT, LONG-FLOAT
;;; System Class RATIONAL
;;; System Class RATIO
;;; System Class INTEGER
;;; Type SIGNED-BYTE
;;; Type UNSIGNED-BYTE
;;; Type Specifier MOD
;;; Type BIT
;;; Type FIXNUM
;;; Type BIGNUM

(define-storage-layout ratio (num den))

(define-storage-layout complex (real imag))

(define-storage-layout random-state (x))

(defun cl:= (number &rest numbers)
  (every (lambda (n) (binary= number n)) numbers))

(defun binary= (num1 num2)
  ;; TODO: This doesn't work for all possible pairs of numbers.
  (cond
    ((and (or (integerp num1) (floatp num1))
	  (or (integerp num2) (floatp num2)))
     (= num1 num2))
    ((or (COMPLEXP num1) (COMPLEXP num2))
     (and (binary= (REALPART num1) (REALPART num2))
	  (binary= (IMAGPART num1) (IMAGPART num2))))
    ((or (ratiop num1) (ratiop num2))
     (and (binary= (NUMERATOR num1) (NUMERATOR num2))
	  (binary= (DENOMINATOR num1) (DENOMINATOR num2))))
    ((and (bignump num1) (bignump num2))
     (and (= (length num1) (length num2))
	  (every #'eql num1 num2)))
    ((and (NUMBERP num1) (NUMBERP num2))
     nil)
    (t
     (unless (NUMBERP num1)
       (type-error num1 'NUMBER))
     (type-error num2 'NUMBER))))

(defun cl:/= (number &rest numbers)
  (if (null numbers)
      T
      (and (not (some (lambda (num) (binary= number num)) numbers))
	   (apply #'cl:/= (first numbers) (rest numbers)))))

(defun cl:< (number &rest numbers)
  (if (null numbers)
      T
      (and (binary< number (first numbers))
	   (apply #'cl:< (first numbers) (rest numbers)))))

(defun binary< (num1 num2)
  (cond
    ((and (or (integerp num1) (floatp num1))
	  (or (integerp num2) (floatp num2)))
     (< num1 num2))
    ((or (ratiop num1) (ratiop num2))
     ;; TODO
     (< (/ (FLOAT (NUMERATOR num1)) (FLOAT (DENOMINATOR num1)))
	(/ (FLOAT (NUMERATOR num2)) (FLOAT (DENOMINATOR num2)))))
    ((or (bignump num1) (bignump num2))
     (MINUSP (binary- num1 num2)))
    (t
     (unless (REALP num1)
       (type-error num1 'REAL))
     (type-error num2 'REAL))))

(defun cl:> (number &rest numbers)
  (if (null numbers)
      T
      (and (binary< (first numbers) number)
	   (apply #'cl:> (first numbers) (rest numbers)))))

(defun cl:<= (number &rest numbers)
  (if (null numbers)
      T
      (and (binary<= number (first numbers))
	   (apply #'cl:<= (first numbers) (rest numbers)))))

(defun binary<= (num1 num2)
  (cond
    ((and (or (integerp num1) (floatp num1))
	  (or (integerp num2) (floatp num2)))
     (<= num1 num2))
    ((or (ratiop num1) (ratiop num2))
     ;; TODO
     (<= (/ (FLOAT (NUMERATOR num1)) (FLOAT (DENOMINATOR num1)))
	 (/ (FLOAT (NUMERATOR num2)) (FLOAT (DENOMINATOR num2)))))
    ((or (bignump num1) (bignump num2))
     (let ((diff (binary- num1 num2)))
       (or (MINUSP diff) (ZEROP diff))))
    (t
     (unless (REALP num1)
       (type-error num1 'REAL))
     (type-error num2 'REAL))))

(defun cl:>= (number &rest numbers)
  (if (null numbers)
      t
      (and (binary<= (first numbers) number)
	   (apply #'cl:>= (first numbers) (rest numbers)))))

(defun MAX (&rest numbers)
  (if (null numbers)
      (error "")
      (reduce (lambda (num1 num2) (if (cl:>= num1 num2) num1 num2)) numbers)))

(defun MIN (&rest numbers)
  (if (null numbers)
      (error "")
      (reduce (lambda (num1 num2) (if (cl:<= num1 num2) num1 num2)) numbers)))

(defun MINUSP (num)
  (cond
    ((or (integerp num) (floatp num))
     (minusp num))
    ((bignump num)
     (minusp (aref num (1- (length num)))))
    ((ratiop num)
     (MINUSP (NUMERATOR num)))
    (t
     (type-error num 'REAL))))

(defun PLUSP (num)
  (cond
    ((or (integerp num) (floatp num))
     (plusp num))
    ((bignump num)
     (>= (aref num (1- (length num))) 0))
    ((ratiop num)
     (PLUSP (NUMERATOR num)))
    (t
     (type-error num 'REAL))))

(defun ZEROP (num)
  (cond
    ((or (integerp num) (floatp num))
     (zerop num))
    ((ratiop num)
     (ZEROP (NUMERATOR num)))
    ((COMPLEXP num)
     (and (ZEROP (REALPART num)) (ZEROP (IMAGPART num))))
    ((bignump num)
     nil)
    (t
     (type-error num 'NUMBER))))

(defconst fixnum-bits (1+ (round (log most-positive-fixnum 2))))

(defun integer-truncate (x y)
  (cond
    ((and (integerp x) (integerp y))
     (if (and (eql x MOST-NEGATIVE-FIXNUM) (eql y -1))
	 (cl:values (vector 'BIGNUM MOST-NEGATIVE-FIXNUM 0) nil)
	 (cl:values (/ x y) (not (zerop (% x y))))))
    ((and (INTEGERP x) (INTEGERP y))
     (let ((sign 1)
	   (q 0)
	   (r 0)
	   (i (1- (if (integerp x) fixnum-bits (* fixnum-bits (1- (length x)))))))
       (when (MINUSP x)
	 (setq x (cl:- x) sign -1))
       (when (MINUSP y)
	 (setq y (cl:- y) sign (- sign)))
       (while (>= i 0)
;	 (print (format "x=%s y=%s q=%s r=%s" x y q r))
	 (setq r (ASH r 1))
	 (when (LOGBITP i x)
	   (setq r (LOGIOR r 1)))
	 (setq q (ASH q 1))
	 (when (cl:>= r y)
	   (setq q (LOGIOR q 1))
	   (setq r (binary- r y)))
	 (decf i))
       (cl:values (binary* sign q) (not (ZEROP r)))))
    (t
     (unless (INTEGERP x)
       (type-error x 'INTEGER))
     (type-error y 'INTEGER))))

(defconst two^fixnum-bits
    (* 2 (1+ (float most-positive-fixnum))))

(defun floor-to-bignum (float)
  (let ((list nil))
    (while (or (>= float 1.0) (<= float -1.0))
      (let ((residue (mod float two^fixnum-bits)))
	(push (truncate (if (> residue most-positive-fixnum)
			    (- residue two^fixnum-bits)
			    residue))
	      list))
      (setq float (/ float two^fixnum-bits)))
    (canonical-bignum (nreverse list))))

(cl:defun FLOOR (number &OPTIONAL (divisor 1))
  (let (quotient remainder)
    (cond
      ((or (floatp number) (floatp divisor))
       (setq number (FLOAT number)
	     divisor (FLOAT divisor)
	     quotient
	     (condition-case condition
		 (floor number divisor)
	       (range-error (floor-to-bignum (/ number divisor))))))
      ((or (ratiop number) (ratiop divisor))
       (MULTIPLE-VALUE-SETQ (quotient remainder)
	 (integer-truncate
	  (binary* (NUMERATOR number) (DENOMINATOR divisor))
	  (binary* (DENOMINATOR number) (NUMERATOR divisor)))))
      ((and (INTEGERP number) (INTEGERP divisor))
       (MULTIPLE-VALUE-SETQ (quotient remainder)
	 (integer-truncate number divisor)))
      (t
       (unless (REALP number)
	 (type-error number 'REAL))
       (type-error divisor 'REAL)))
    (when (and remainder (or (MINUSP quotient)
			     (and (ZEROP quotient) (MINUSP number))))
      (setq quotient (binary- quotient 1)))
    (cl:values quotient (binary- number (binary* quotient divisor)))))

(cl:defun FFLOOR (number &OPTIONAL (divisor 1))
  (MULTIPLE-VALUE-BIND (quotient remainder) (FLOOR number divisor)
    (cl:values (FLOAT quotient) remainder)))

(defun ceiling-to-bignum (float)
  (cl:- (floor-to-bignum (- float))))

(cl:defun CEILING (number &OPTIONAL (divisor 1))
  (let (quotient remainder)
    (cond
      ((or (floatp number) (floatp divisor))
       (setq number (FLOAT number)
	     divisor (FLOAT divisor)
	     quotient
	     (condition-case condition
		 (ceiling number divisor)
	       (range-error (ceiling-to-bignum (/ number divisor))))))
      ((or (ratiop number) (ratiop divisor))
       (MULTIPLE-VALUE-SETQ (quotient remainder)
	 (integer-truncate
	  (binary* (NUMERATOR number) (DENOMINATOR divisor))
	  (binary* (DENOMINATOR number) (NUMERATOR divisor)))))
      ((and (INTEGERP number) (INTEGERP divisor))
       (MULTIPLE-VALUE-SETQ (quotient remainder)
	 (integer-truncate number divisor)))
      (t
       (unless (REALP number)
	 (type-error number 'REAL))
       (type-error divisor 'REAL)))
    (when (and remainder (or (PLUSP quotient)
			     (and (ZEROP quotient) (PLUSP number))))
      (setq quotient (binary+ quotient 1)))
    (cl:values quotient (binary- number (binary* quotient divisor)))))

(cl:defun FCEILING (number &OPTIONAL (divisor 1))
  (MULTIPLE-VALUE-BIND (quotient remainder) (CEILING number divisor)
    (cl:values (FLOAT quotient) remainder)))

(defun truncate-to-bignum (float)
  (if (minusp float)
      (ceiling-to-bignum float)
      (floor-to-bignum float)))

(condition-case c
    (progn
      (truncate 1 2)
      (defmacro trunc2 (num div) `(truncate ,num ,div)))
  (wrong-number-of-arguments
   (defmacro trunc2 (num div) `(truncate (/ ,num ,div)))))

(cl:defun TRUNCATE (number &OPTIONAL (divisor 1))
  (let (quotient)
    (cond
      ((or (floatp number) (floatp divisor))
       (setq number (FLOAT number)
	     divisor (FLOAT divisor)
	     quotient
	     (condition-case c
		 (trunc2 number divisor)
	       (range-error (truncate-to-bignum (/ number divisor))))))
      ((or (ratiop number) (ratiop divisor))
       (setq quotient (integer-truncate
		       (binary* (NUMERATOR number) (DENOMINATOR divisor))
		       (binary* (DENOMINATOR number) (NUMERATOR divisor)))))
      ((and (INTEGERP number) (INTEGERP divisor))
       (setq quotient (integer-truncate number divisor)))
      (t
       (unless (REALP number)
	 (type-error number 'REAL))
       (type-error divisor 'REAL)))
    (cl:values quotient (binary- number (binary* quotient divisor)))))

(cl:defun FTRUNCATE (number &OPTIONAL (divisor 1))
  (MULTIPLE-VALUE-BIND (quotient remainder) (TRUNCATE number divisor)
    (cl:values (FLOAT quotient) remainder)))

(cl:defun ROUND (number &OPTIONAL (divisor 1))
  (MULTIPLE-VALUE-BIND (quotient remainder)
      ;; TODO: proper rounding
      (TRUNCATE (binary+ number .5) divisor)
    (cl:values quotient remainder)))

(cl:defun FROUND (number &OPTIONAL (divisor 1))
  (MULTIPLE-VALUE-BIND (quotient remainder) (ROUND number divisor)
    (cl:values (FLOAT quotient) remainder)))

(defun SIN (x)
  (cond
    ((REALP x)		(sin (FLOAT x)))
    ((COMPLEXP x)	(error "TODO"))
    (t			(type-error x 'NUMBER))))

(defun COS (x)
  (cond
    ((REALP x)		(cos (FLOAT x)))
    ((COMPLEXP x)	(error "TODO"))
    (t			(type-error x 'NUMBER))))

(defun TAN (x)
  (cond
    ((REALP x)		(tan (FLOAT x)))
    ((COMPLEXP x)	(error "TODO"))
    (t			(type-error x 'NUMBER))))

(defun ASIN (x)
  (cond
    ((REALP x)		(asin (FLOAT x)))
    ((COMPLEXP x)	(error "TODO"))
    (t			(type-error x 'NUMBER))))

(defun ACOS (x)
  (cond
    ((REALP x)		(acos (FLOAT x)))
    ((COMPLEXP x)	(error "TODO"))
    (t			(type-error x 'NUMBER))))

(defun ATAN (x &optional y)
  (when y (error "TODO"))
  (cond
    ((REALP x)		(atan (FLOAT x)))
    ((COMPLEXP x)	(error "TODO"))
    (t			(type-error x 'NUMBER))))

(DEFCONSTANT PI 3.141592653589793)

(defun SINH (x)
  (binary* 0.5 (binary- (EXP x) (EXP (cl:- x)))))

(defun COSH (x)
  (binary* 0.5 (binary+ (EXP x) (EXP (cl:- x)))))

(defun TANH (x)
  (binary/ (binary- (EXP x) (EXP (cl:- x)))
	   (binary+ (EXP x) (EXP (cl:- x)))))

(defun ASINH (x)
  (LOG (binary+ x (SQRT (1+ (binary* x x))))))

(defun ACOSH (x)
  (binary* 2 (LOG (binary+ (SQRT (binary* 0.5 (1+ x)))
			   (SQRT (binary* 0.5 (1- x)))))))

(defun ATANH (x)
  (binary* 0.5 (binary- (LOG (1+ x)) (LOG (binary- 1 x)))))

(defun cl:* (&rest numbers)
  (reduce #'binary* numbers :initial-value 1))

(defconst multiplication-limit (floor (sqrt most-positive-fixnum)))

(defun binary* (x y)
  (cond
    ((and (integerp x) (integerp y))
     (if (and (< x multiplication-limit)
	      (> x (- multiplication-limit))
	      (< y multiplication-limit)
	      (> y (- multiplication-limit)))
	 (* x y)
	 (bignum* (vector 'BIGNUM x (if (minusp x) -1 0))
		  (vector 'BIGNUM y (if (minusp y) -1 0)))))
    ((or (COMPLEXP x) (COMPLEXP y))
     (COMPLEX (binary- (binary* (REALPART x) (REALPART y))
		       (binary* (IMAGPART x) (IMAGPART y)))
	      (binary+ (binary* (REALPART x) (IMAGPART y))
		       (binary* (IMAGPART x) (REALPART y)))))
    ((floatp x)
     (* x (FLOAT y)))
    ((floatp y)
     (* (FLOAT x) y))
    ((or (ratiop x) (ratiop y))
     (make-ratio (binary* (NUMERATOR x) (NUMERATOR y))
		 (binary* (DENOMINATOR x) (DENOMINATOR y))))
    ((or (INTEGERP x) (INTEGERP y))
     (when (integerp x)
       (setq x (vector 'BIGNUM x (if (minusp x) -1 0))))
     (when (integerp y)
       (setq y (vector 'BIGNUM y (if (minusp y) -1 0))))
     (bignum* x y))
    (t
     (unless (NUMBERP x)
       (type-error x 'NUMBER))
     (type-error y 'NUMBER))))

(defun bignum* (x y)
  (cond
    ((equal x [BIGNUM 1 0])
     (canonical-bignum y))
    ((equal x [BIGNUM -1 -1])
     (cl:- (canonical-bignum y)))
    ((equal y [BIGNUM 10 0])
     (setq x (canonical-bignum x))
;    (print (format "(bignum* %s %s)" x y))
     (let* ((2x (binary+ x x))
	    (4x (binary+ 2x 2x))
	    (5x (binary+ 4x x)))
;      (print (format "%s %s %s" 2x 4x 5x))
       (binary+ 5x 5x)))
    (t
     (setq x (canonical-bignum x))
     (setq y (canonical-bignum y))
     (let ((sign 1)
	   (z 0))
       (when (MINUSP x)
	 (setq x (cl:- x) sign -1))
       (when (MINUSP y)
	 (setq y (cl:- y) sign (- sign)))
       (while (PLUSP x)
	 (when (LOGBITP 0 x)
	   (setq z (binary+ z y)))
	 (setq y (ASH y 1))
	 (setq x (ASH x -1)))
       (binary* sign z)))))

(defun cl:+ (&rest numbers)
  (reduce #'binary+ numbers :initial-value 0))

(defun binary+ (x y)
  (cond
    ((and (integerp x) (integerp y))
     (let ((sum (+ x y)))
       (cond
	 ((and (>= x 0) (>= y 0) (minusp sum))
	  (vector 'BIGNUM sum 0))
	 ((and (minusp x) (minusp y) (>= sum 0))
	  (vector 'BIGNUM sum -1))
	 (t
	  sum))))
    ((or (COMPLEXP x) (COMPLEXP y))
     (COMPLEX (binary+ (REALPART x) (REALPART y))
	      (binary+ (IMAGPART x) (IMAGPART y))))
    ((floatp x)
     (+ x (FLOAT y)))
    ((floatp y)
     (+ (FLOAT x) y))
    ((or (ratiop x) (ratiop y))
     (make-ratio (binary+ (binary* (NUMERATOR x) (DENOMINATOR y))
			  (binary* (DENOMINATOR x) (NUMERATOR y)))
		 (binary* (DENOMINATOR x) (DENOMINATOR y))))
    ((or (bignump x) (bignump y))
;    (print (format "%s %s" x y))
     (cond
       ((integerp x)	(bignum+fixnum y x))
       ((integerp y)	(bignum+fixnum x y))
       (t		(bignum+bignum x y))))
    (t
     (error "error"))))

(defun bignum+fixnum (x y)
  (let* ((x0 (aref x 1))
	 (sum (+ x0 y))
	 (new (copy-sequence x)))
    (aset new 1 sum)
;   (print x0)
;   (print y)
;   (print sum)
    (cond
      ;; negative + positive -> positive: carry
      ((and (minusp x0) (>= y 0) (>= sum 0))
       (bignum+bignum new [BIGNUM 0 1]))
      ;; positive + negative -> negative: borrow
      ((and (>= x0 0) (minusp y) (minusp sum))
       (bignum+bignum new [BIGNUM 0 -1]))
      ;; positive + positive -> negative: no overflow
      ;; negative + negative -> positive: no overflow
      (t
       (canonical-bignum new)))))

(defun bignum+bignum (x y)
  (canonical-bignum (bignum+ (bignum-list x) (bignum-list y))))

(cl:defun bignum-list (num &OPTIONAL (index 1))
  (if (= index (length num))
      nil
      (cons (aref num index) (bignum-list num (1+ index)))))

(defun canonical-bignum (object)
  (cond
    ((bignump object)
     (canonical-bignum (bignum-list object)))
    ((listp object)
     (setq object (truncate-sign-extension object))
     (if (eql (length object) 1)
	 (first object)
	 (let ((bignum (make-vector (1+ (length object)) 'BIGNUM))
	       (i 0))
	   (dolist (n object)
	     (aset bignum (incf i) n))
	   bignum)))
    (t
     (error "error"))))

(defun truncate-sign-extension (list &optional prev)
  (if (null list)
      nil
      (let ((rest (truncate-sign-extension (rest list) (first list))))
	(setf (cdr list) rest)
	(if (null rest)
	    (let ((this (first list)))
	      (cond
		((and (zerop this) prev (>= prev 0))
		 nil)
		((and (eql this -1) prev (minusp prev))
		 nil)
		(t
		 list)))
	    list))))

(cl:defun bignum+ (x y &OPTIONAL (carry 0))
; (print (format "(bignum+ %s %s %s)" x y carry))
  (cond
    ((null x)
     (if (zerop carry)
	 y
	 (bignum+ y (list carry))))
    ((null y)
     (if (zerop carry)
	 x 
	 (bignum+ x (list carry))))
    (t
     (let* ((x0 (car x))
	    (y0 (car y))
	    (sum (+ x0 y0 carry)))
;      (print (format "x0=%s y0=%s sum=%s" x0 y0 sum))
       (if (and (null (rest x)) (null (rest y))
		(>= x0 0) (>= y0 0) (minusp sum))
	   ;; Last number wrapped from positive to negative.
	   ;; Need a final zero.
	   (cons sum '(0))
	   (cons sum
		 (bignum+
		  (rest x)
		  (rest y)
		  (if (or (and (minusp x0) (>= y0 0) (>= sum 0) (rest x))
			  (and (>= x0 0) (minusp y0) (>= sum 0) (rest y))
			  (and (minusp x0) (minusp y0) (rest x) (rest y)))
		      1 0))))))))

(defun cl:- (number &rest numbers)
  (if (null numbers)
      (cond
	((or (integerp number) (floatp number))
	 (if (eql number MOST-NEGATIVE-FIXNUM)
	     (vector 'BIGNUM number 0)
	     (- number)))
	((ratiop number)
	 (vector 'RATIO (cl:- (NUMERATOR number)) (DENOMINATOR number)))
	((COMPLEXP number)
	 (vector 'COMPLEX (cl:- (REALPART number)) (cl:- (IMAGPART number))))
	((bignump number)
	 (bignum+fixnum (LOGNOT number) 1))
	(t
	 (error "error")))
      (dolist (num numbers number)
	(setq number (binary- number num)))))

(defun binary- (x y)
  (binary+ x (cl:- y)))

(defun cl:/ (number &rest numbers)
  (if (null numbers)
      (cond
	((integerp number)
	 (vector 'RATIO 1 number))
	((floatp number)
	 (/ 1.0 number))
	((bignump number)
	 (vector 'RATIO 1 number))
	((ratiop number)
	 (make-ratio (DENOMINATOR number) (NUMERATOR number)))
	((COMPLEXP number)
	 (let* ((r (REALPART number))
		(i (IMAGPART number))
		(x (binary- (binary* r r) (binary* i i))))
	   (COMPLEX (binary/ r x) (cl:- (binary/ i x)))))
	(t
	 (error "error")))
      (dolist (num numbers number)
	(setq number (binary/ number num)))))

(defun binary/ (x y)
  (cond
    ((and (INTEGERP x) (INTEGERP y))
     (make-ratio x y))
    ((or (COMPLEXP x) (COMPLEXP y))
     (let* ((rx (REALPART x))
	    (ry (REALPART y))
	    (ix (IMAGPART x))
	    (iy (IMAGPART y))
	    (div (binary+ (binary* ry ry) (binary* iy iy))))
       (COMPLEX (binary/ (binary+ (binary* rx ry) (binary* ix iy)) div)
		(binary/ (binary- (binary* ix ry) (binary* rx iy)) div))))
    ((floatp x)
     (/ x (FLOAT y)))
    ((floatp y)
     (/ (FLOAT x) y))
    ((or (RATIONALP x) (RATIONALP y))
     (make-ratio (binary* (NUMERATOR x) (DENOMINATOR y))
		 (binary* (DENOMINATOR x) (NUMERATOR y))))
    (t
     (unless (NUMBERP x)
       (type-error x 'NUMBER))
     (type-error y 'NUMER))))
  
(defun cl:1+ (number)
  (binary+ number 1))

(defun cl:1- (number)
  (binary- number 1))

(defun ABS (number)
  (cond
    ((integerp number)
     (if (eql number MOST-NEGATIVE-FIXNUM)
	 (vector 'BIGNUM number 0)
	 (abs number)))
    ((floatp number)
     (abs number))
    ((ratiop number)
     (vector 'RATIO (ABS (NUMERATOR number)) (DENOMINATOR number)))
    ((COMPLEXP number)
     (let ((r (FLOAT (REALPART number)))
	   (i (FLOAT (IMAGPART number))))
       (sqrt (+ (* r r) (* i i)))))
    ((bignump number)
     (if (MINUSP number)
	 (cl:- number)
	 number))
    (t
     (type-error number 'NUMBER))))

(defun EVENP (num)
  (if (INTEGERP num)
      (not (LOGBITP 0 num))
      (type-error num 'INTEGER)))

(defun ODDP (num)
  (if (INTEGERP num)
      (LOGBITP 0 num)
      (type-error num 'INTEGER)))

(defun EXP (num)
  (cond
    ((REALP num)	(exp (FLOAT num)))
    ((COMPLEXP num)	(error "TODO"))
    (t			(type-error num 'NUMBER))))

(defun EXPT (base power)
  (cond
    ((and (RATIONALP base) (INTEGERP power))
     (exact-expt base power))
    ((and (REALP base) (REALP power))
     (expt (FLOAT base) (FLOAT power)))
    ((and (NUMBERP base) (NUMBERP power))
     (error "TODO"))
    (t
     (unless (NUMBERP base)
       (type-error base 'NUMBER))
     (type-error power 'NUMBER))))

(defun exact-expt (base power)
  (cond
    ((ZEROP power)
     1)
    ((MINUSP power)
     (exact-expt (make-ratio (DENOMINATOR base) (NUMERATOR base))
		 (cl:- power)))
    (t
     (let ((result 1))
       (while (PLUSP power)
	 (when (LOGBITP 0 power)
	   (setq result (binary* result base)))
	 (setq base (binary* base base))
	 (setq power (ASH power -1)))
       result))))

(defun GCD (&rest numbers)
  (reduce #'binary-gcd numbers :initial-value 0))

(defun binary-gcd (x y)
  (cond
    ((or (eq x 1) (eq y 1))
     1)
    ((and (integerp x) (integerp y))
     (when (> y x)
       (psetq x y y x))
     (while (not (zerop y))
       (psetq y (% x y) x y))
     (abs x))
    (t
     (when (cl:> y x)
       (psetq x y y x))
     (while (not (ZEROP y))
       (psetq y (REM x y) x y))
     (ABS x))))

(cl:defmacro INCF (place &optional delta)
  (unless delta
    (setq delta 1))
  (MULTIPLE-VALUE-BIND (temps values variables setter getter)
      (GET-SETF-EXPANSION place nil) ;TODO: &environment
    `(LET* (,@(MAPCAR #'list temps values)
	    (,(first variables)
	     ,(if (eq delta 1)
		  `(,(INTERN "1+" *cl-package*) ,getter)
		  `(,(INTERN "+" *cl-package*) ,getter ,delta))))
       ,setter)))

(cl:defmacro DECF (place &optional delta)
  (unless delta
    (setq delta 1))
  (MULTIPLE-VALUE-BIND (temps values variables setter getter)
      (GET-SETF-EXPANSION place nil) ;TODO: &environment
    `(LET* (,@(MAPCAR #'list temps values)
	    (,(first variables)
	     ,(if (eq delta 1)
		  `(,(INTERN "1-" *cl-package*) ,getter)
		  `(,(INTERN "-" *cl-package*) ,getter ,delta))))
       ,setter)))

(defun LCM (&rest numbers)
  (if (null numbers)
      1
      (reduce #'binary-lcm numbers)))

(defun binary-lcm (x y)
  (if (or (ZEROP x) (ZEROP y))
      0
      (integer-truncate (ABS (binary* x y)) (GCD x y))))

(cl:defun LOG (number &OPTIONAL (base (exp 1)))
  (cond
    ((and (REALP number) (REALP base))
     (log (FLOAT number) (FLOAT base)))
    ((and (NUMBERP number) (NUMBERP base))
     (error "TODO"))
    (t
     (unless (NUMBERP number)
       (type-error number 'NUMBER))
     (type-error base 'NUMBER))))
  
(defun MOD (number divisor)
  (NTH-VALUE 1 (FLOOR number divisor)))

(defun REM (number divisor)
  (NTH-VALUE 1 (TRUNCATE number divisor)))

(defun SIGNUM (number)
  (cond
    ((RATIONALP number) (cond ((PLUSP number)	1)
			      ((ZEROP number)	0)
			      ((MINUSP number)	-1)))
    ((floatp number)	(cond ((plusp number)	1.0)
			      ((zerop number)	0.0)
			      ((minusp number)	-1.0)))
    ((COMPLEXP number)	(if (ZEROP number)	number
						(binary/ number (ABS number))))
    (t			(type-error number 'NUMBER))))

(defun SQRT (number)
  (cond
    ((REALP number)	(sqrt (FLOAT number)))
    ((COMPLEXP number)	(error "TODO"))
    (t			(type-error number 'NUMBER))))

;;; http://www.embedded.com/98/9802fe2.htm
(defun ISQRT (number)
  (unless (and (INTEGERP number) (not (MINUSP number)))
    (type-error number '(INTEGER 0 *)))
  (do ((rem 0)
       (root 0)
       (i (LOGAND (INTEGER-LENGTH number) -2) (- i 2)))
      ((minusp i)
       (ASH root -1))
    (setq root (binary+ root root)
	  rem (binary+ (ASH rem 2) (LOGAND (ASH number (- i)) 3))
	  root (binary+ root 1))
    (if (binary<= root rem)
	(setq rem (binary- rem root)
	      root (binary+ root 1))
	(setq root (binary+ root -1)))))
; (defun ISQRT (number)
;   (do ((rem 0)
;        (root 0)
;        divisor
;        (i (LOGAND (INTEGER-LENGTH number) -2) (- i 2)))
;       ((minusp i)
;        root)
;     (setq root (binary+ root root)
; 	  rem (binary+ (ASH rem 2) (LOGAND (ASH number (- i)) 3))
; 	  divisor (binary+ (binary+ root root) 1))
;     (when (binary<= divisor rem)
;       (setq rem (binary- rem divisor)
; 	    root (binary+ root 1)))))

;;; System Class RANDOM-STATE

(defun MAKE-RANDOM-STATE (&optional state)
  (vector
   'RANDOM-STATE
   (cond
     ((null state)		0)
     ((eq state T)		(random-state-x *RANDOM-STATE*))
     ((RANDOM-STATE-P state)	(random-state-x state))
     (t				(type-error state
					    '(OR BOOLEAN RANDOM-STATE))))))

(defun RANDOM (limit &optional state)
  ;; TODO: use state
  (cond
    ((integerp limit)
     (random limit))
    ((floatp limit)
     (/ (* limit (random MOST-POSITIVE-FIXNUM)) MOST-POSITIVE-FIXNUM))
    ((bignump limit)
     ;; TODO
     0)))

(defun RANDOM-STATE-P (object)
  (vector-and-typep object 'RANDOM-STATE))

(DEFVAR *RANDOM-STATE* (MAKE-RANDOM-STATE))

(defun NUMBERP (object)
  (or (numberp object)
      (and (vectorp object)
	   (let ((type (aref object 0)))
	     (or (eq type 'BIGNUM)
		 (eq type 'RATIO)
		 (eq type 'COMPLEX))))))

(defun CIS (x)
  (unless (REALP x)
    (type-error x 'REAL))
  (EXP (vector 'COMPLEX 0 x)))

(cl:defun COMPLEX (realpart &OPTIONAL (imagpart 0))
  (cond
    ((floatp realpart)
     (setq imagpart (float imagpart)))
    ((floatp imagpart)
     (setq realpart (float realpart))))
  (if (eq imagpart 0)
      realpart
      (vector 'COMPLEX realpart imagpart)))

(defun COMPLEXP (object)
  (vector-and-typep object 'COMPLEX))

(defun CONJUGATE (num)
  (vector 'COMPLEX (REALPART num) (cl:- (IMAGPART num))))

(defun PHASE (num)
  (ATAN (IMAGPART num) (REALPART num)))

(defun REALPART (num)
  (if (COMPLEXP num)
      (complex-real num)
      num))

(defun IMAGPART (num)
  (if (COMPLEXP num)
      (complex-imag num)
      0))

(defun UPGRADED-COMPLEX-PART-TYPE (typespec &optional env)
  'REAL)

(defun REALP (num)
  (or (RATIONALP num) (floatp num)))

(defun make-ratio (num den)
  (unless (INTEGERP num)
    (type-error num 'INTEGER))
  (unless (INTEGERP den)
    (type-error den 'INTEGER))
  (when (ZEROP den)
    (ERROR 'DIVISION-BY-ZERO))
  (if (and (eq num MOST-NEGATIVE-FIXNUM) (eq den -1))
      (vector 'BIGNUM MOST-NEGATIVE-FIXNUM 0)
      (let* ((gcd (GCD num den))
	     (num (integer-truncate num gcd))
	     (den (integer-truncate den gcd)))
	(cl:values
	 (cond
	   ((eq den 1)
	    num)
	   ((MINUSP den)
	    (vector 'RATIO (cl:- num) (cl:- den)))
	   (t
	    (vector 'RATIO num den)))))))

(defun ratiop (num)
  (vector-and-typep num 'RATIO))

(defun NUMERATOR (num)
  (if (ratiop num)
      (ratio-num num)
      num))

(defun DENOMINATOR (num)
  (if (ratiop num)
      (ratio-den num)
      1))

(defun RATIONAL (num)
  (cond
    ((floatp num)
     (MULTIPLE-VALUE-BIND (significand exp sign) (INTEGER-DECODE-FLOAT num)
       (let ((bits (max exp 53)))
	 (cl:values
	  (make-ratio (ROUND (SCALE-FLOAT significand bits))
		      (EXPT 2 (- bits exp)))))))
    ((RATIONALP num)
     num)
    (t
     (type-error num 'REAL))))

(defun* RATIONALIZE (num)
  (cond
    ((floatp num)
     ;; Algorithm from Gareth McCaughan.
     (let ((p 0) (q 1) (r 1) (s 0))
       (while (binary< s max-rationalize-denominator)
	 (MULTIPLE-VALUE-BIND (intpart fracpart) (FLOOR num)
	   (setq p (prog1 r
		     (setq r (binary+ p (binary* intpart r)))))
	   (setq q (prog1 s
		     (setq s (binary+ q (binary* intpart s)))))
	   (when (< fracpart 1e-14)
	     (return-from RATIONALIZE (cl:values (make-ratio r s))))
	   (setq num (binary/ 1 fracpart))))
       (cl:values (make-ratio p q))))
    ((RATIONALP num)
     num)
    (t
     (type-error num 'REAL))))

(defun RATIONALP (num)
  (or (INTEGERP num) (ratiop num)))

(defun ASH (num shift)
  (cond
    ((ZEROP shift)
     num)
    ((MINUSP shift)
     (cond
       ((integerp num)
	(ash num shift))
       ((bignump num)
	(let ((new (copy-sequence num)))
	  (while (MINUSP shift)
	    (shift-right new)
	    (incf shift))
	  (canonical-bignum new)))
       (t
	(error "error"))))
    (t
     (while (> shift 0)
       (setq num (binary+ num num)
	     shift (1- shift)))
     num)))

(defun shift-right (num)
  (let ((i (1- (length num)))
	(first t)
	(carry 0))
    (while (plusp i)
      (let ((n (aref num i)))
	(aset num i (if first
			(ash n -1)
			(logior (lsh n -1) (ash carry (1- fixnum-bits)))))
	(setq carry (logand n 1)
	      first nil))
      (decf i))))

(defun INTEGER-LENGTH (num)
  (when (MINUSP num)
    (setq num (cl:- num)))
  (cond
    ((eq num 0)		0)
    ((integerp num)	(1+ (logb num)))
    ((bignump num)	(let* ((len (1- (length num)))
			       (last (aref num len)))
			  (+ (* fixnum-bits (1- len))
			     (if (zerop last)
				 0
				 (1+ (logb last))))))
    (t			(type-error num 'INTEGER))))

(defun bignump (num)
  (vector-and-typep num 'BIGNUM))

(defun INTEGERP (num)
  (or (integerp num) (bignump num)))

(cl:defun PARSE-INTEGER (string &KEY (START 0) (END (LENGTH string))
			             (RADIX 10) JUNK-ALLOWED)
  (let ((sign 1)
	(integer 0)
	(i START)
	char digit)
    (catch 'PARSE-INTEGER
      (while (whitespacep (CHAR string i))
	(incf i)
	(when (= i END)
	  (if JUNK-ALLOWED
	      (throw 'PARSE-INTEGER (cl:values nil i))
	      (ERROR 'PARSE-ERROR))))
      (setq char (CHAR string i))
      (when (FIND char "+-")
	(when (ch= char 45)
	  (setq sign -1))
	(incf i)
	(when (= i END)
	  (if JUNK-ALLOWED
	      (throw 'PARSE-INTEGER (cl:values nil i))
	      (ERROR 'PARSE-ERROR)))
	(setq char (CHAR string i)))
      (unless (DIGIT-CHAR-P char RADIX)
	(if JUNK-ALLOWED
	    (throw 'PARSE-INTEGER (cl:values nil i))
	    (ERROR 'PARSE-ERROR)))
      (while (setq digit (DIGIT-CHAR-P char RADIX))
	(setq integer (cl:+ (cl:* integer RADIX) digit))
	(incf i)
	(when (= i END)
	  (throw 'PARSE-INTEGER (cl:values (cl:* sign integer) i)))
	(setq char (CHAR string i)))
      (if JUNK-ALLOWED
	  (cl:values (cl:* sign integer) i)
	  (do ((i i (1+ i)))
	      ((= i END)
	       (cl:values (cl:* sign integer) i))
	    (unless (whitespacep (CHAR string i))
	      (ERROR 'PARSE-ERROR)))))))

(DEFCONSTANT BOOLE-1		 1)
(DEFCONSTANT BOOLE-2		 2)
(DEFCONSTANT BOOLE-AND		 3)
(DEFCONSTANT BOOLE-ANDC1	 4)
(DEFCONSTANT BOOLE-ANDC2	 5)
(DEFCONSTANT BOOLE-C1		 6)
(DEFCONSTANT BOOLE-C2		 7)
(DEFCONSTANT BOOLE-CLR		 8)
(DEFCONSTANT BOOLE-EQV		 9)
(DEFCONSTANT BOOLE-IOR		10)
(DEFCONSTANT BOOLE-NAND		11)
(DEFCONSTANT BOOLE-NOR		12)
(DEFCONSTANT BOOLE-ORC1		13)
(DEFCONSTANT BOOLE-ORC2		14)
(DEFCONSTANT BOOLE-SET		15)
(DEFCONSTANT BOOLE-XOR		16)

(defun BOOLE (op integer1 integer2)
  (ecase op
    (1	integer1)
    (2	integer2)
    (3	(LOGAND integer1 integer2))
    (4	(LOGANDC1 integer1 integer2))
    (5	(LOGANDC2 integer1 integer2))
    (6	(LOGNOT integer1))
    (7	(LOGNOT integer2))
    (8	0)
    (9	(LOGEQV integer1 integer2))
    (10	(LOGIOR integer1 integer2))
    (11	(LOGNAND integer1 integer2))
    (12	(LOGNOR integer1 integer2))
    (13	(LOGORC1 integer1 integer2))
    (14	(LOGORC2 integer1 integer2))
    (15	-1)
    (16	(LOGXOR integer1 integer2))))
    
(defun LOGNOT (num)
  (cond
    ((integerp num)
     (lognot num))
    ((bignump num)
     ;; TODO: may need one more element in result.
     (let ((new (make-vector (length num) 'BIGNUM)))
       (dotimes (i (1- (length num)))
	 (aset new (1+ i) (lognot (aref num (1+ i)))))
       new))
    (t
     (type-error num 'INTEGER))))

(defun LOGAND (&rest numbers)
  (reduce #'binary-logand numbers :initial-value -1))

(defun binary-logand (x y)
  (cond
    ((and (integerp x) (integerp y))
     (logand x y))
    ((and (bignump x) (integerp y))
     (if (minusp y)
	 (let ((new (copy-sequence x)))
	   (aset new 1 (logand (aref x 1) y))
	   new)
	 (logand (aref x 1) y)))
    ((and (bignump y) (integerp x))
     (if (minusp x)
	 (let ((new (copy-sequence y)))
	   (aset new 1 (logand (aref y 1) x))
	   new)
	 (logand (aref y 1) x)))
    ((and (bignump x) (bignump y))
     (bignum-logand x y))
    (t
     (unless (INTEGERP x)
       (type-error x 'INTEGER))
     (type-error y 'INTEGER))))

(defun bignum-logand (x y)
  (setq x (bignum-list x))
  (setq y (bignum-list y))
  (when (< (length x) (length y))
    (psetq x y y x))
  (when (< (length y) (length x))
    (setq y (nreverse y))
    (while (< (length y) (length x))
      (push (if (MINUSP (first y)) -1 0) y))
    (setq y (nreverse y)))
  (canonical-bignum (MAPCAR (lambda (n m) (logand n m)) x y)))

(defun LOGIOR (&rest numbers)
  (reduce #'binary-logior numbers :initial-value 0))

(defun binary-logior (x y)
  (cond
    ((and (integerp x) (integerp y))
     (logior x y))
    ((and (bignump x) (integerp y))
     (if (minusp y)
	 (logior (aref x 1) y)
	 (let ((new (copy-sequence x)))
	   (aset new 1 (logior (aref x 1) y))
	   new)))
    ((and (bignump y) (integerp x))
     (if (minusp x)
	 (logior (aref y 1) x)
	 (let ((new (copy-sequence y)))
	   (aset new 1 (logior (aref y 1) x))
	   new)))
    ((and (bignump x) (bignump y))
     (bignum-logior x y))
    (t
     (unless (INTEGERP x)
       (type-error x 'INTEGER))
     (type-error y 'INTEGER))))

(defun bignum-logior (x y)
  (setq x (bignum-list x))
  (setq y (bignum-list y))
  (when (< (length x) (length y))
    (psetq x y y x))
  (when (< (length y) (length x))
    (setq y (nreverse y))
    (while (< (length y) (length x))
      (push (if (MINUSP (first y)) -1 0) y))
    (setq y (nreverse y)))
  (canonical-bignum (MAPCAR (lambda (n m) (logior n m)) x y)))

(defun LOGNAND (x y)
  (LOGNOT (LOGAND x y)))

(defun LOGANDC1 (x y)
  (LOGAND (LOGNOT x) y))

(defun LOGANDC2 (x y)
  (LOGAND x (LOGNOT y)))

(defun LOGNOR (x y)
  (LOGNOT (LOGIOR x y)))

(defun LOGORC1 (x y)
  (LOGIOR (LOGNOT x) y))

(defun LOGORC2 (x y)
  (LOGIOR x (LOGNOT y)))

(defun LOGEQV (&rest numbers)
  (LOGNOT (apply #'LOGXOR numbers)))

(defun LOGXOR (&rest numbers)
  (reduce #'binary-logxor numbers :initial-value 0))

(defun binary-logxor (x y)
  (cond
    ((and (integerp x) (integerp y))
     (logxor x y))
    ((and (bignump x) (integerp y))
     (let ((new (copy-sequence x)))
       (aset new 1 (logxor (aref x 1) y))
       (when (minusp y)
	 (dotimes (i (- (length x) 2))
	   (aset new (+ i 2) (lognot (aref new (+ i 2))))))
       new))
    ((and (bignump y) (integerp x))
     (let ((new (copy-sequence y)))
       (aset new 1 (logior (aref y 1) x))
       (when (minusp x)
	 (dotimes (i (- (length y) 2))
	   (aset new (+ i 2) (lognot (aref new (+ i 2))))))
       new))
    ((and (bignump x) (bignump y))
     (bignum-logxor x y))
    (t
     (unless (INTEGERP x)
       (type-error x 'INTEGER))
     (type-error y 'INTEGER))))

(defun bignum-logxor (x y)
  (setq x (bignum-list x))
  (setq y (bignum-list y))
  (when (< (length x) (length y))
    (psetq x y y x))
  (when (< (length y) (length x))
    (setq y (nreverse y))
    (while (< (length y) (length x))
      (push (if (MINUSP (first y)) -1 0) y))
    (setq y (nreverse y)))
  (canonical-bignum (MAPCAR (lambda (n m) (logxor n m)) x y)))


(defun LOGBITP (index integer)
  (unless (integerp index)
    (error "TODO"))
  (when (minusp index)
    (type-error index '(INTEGER 0 *)))
  (cond
    ((integerp integer)
     (if (>= index fixnum-bits)
	 (minusp integer)
	 (not (zerop (logand integer (ash 1 index))))))
    ((bignump integer)
     (if (>= index (* fixnum-bits (1- (length integer))))
	 (MINUSP integer)
	 (let ((i (1+ (/ index fixnum-bits)))
	       (j (% index fixnum-bits)))
	   (not (zerop (logand (aref integer i) (ash 1 j)))))))
    (t
     (type-error integer 'INTEGER))))

(defconst max-rationalize-denominator (exact-expt 2 52))

(defun LOGCOUNT (num)
  (when (MINUSP num)
    (setq num (cl:- num)))
  (let ((len 0))
    (cond
      ((integerp num)
       (dotimes (i fixnum-bits)
	 (when (LOGBITP i num)
	   (incf len))))
      (t
       (dotimes (i (1- (length num)))
	 (dotimes (j fixnum-bits)
	   (when (LOGBITP i num)
	     (incf len))))))
    len))

(defun LOGTEST (num1 num2)
  (NOT (ZEROP (LOGAND num1 num2))))

(defun BYTE (size pos)
  (list size pos))

(defun BYTE-SIZE (bytespec)
  (first bytespec))

(defun BYTE-POSITION (bytespec)
  (second bytespec))

(defun DEPOSIT-FIELD (newbyte bytespec integer)
  (LOGIOR (LOGAND integer (LOGNOT (DPB -1 bytespec 0)))
	  (MASK-FIELD bytespec newbyte)))

(defun DPB (newbyte bytespec integer)
  (let ((mask (cl:1- (ASH 1 (BYTE-SIZE bytespec)))))
    (LOGIOR (LOGANDC2 integer (ASH mask (BYTE-POSITION bytespec)))
	    (ASH (LOGAND newbyte mask) (BYTE-POSITION bytespec)))))

(defun LDB (bytespec integer)
  (LOGAND (ASH integer (cl:- (BYTE-POSITION bytespec)))
	  (cl:1- (ASH 1 (BYTE-SIZE bytespec)))))

(DEFINE-SETF-EXPANDER LDB (bytespec integer)
  (MULTIPLE-VALUE-BIND (temps values variables setter getter)
      (GET-SETF-EXPANSION integer nil) ;TODO: environment
    (let ((byte (gensym))
	  (value (gensym)))
      (values (cons byte temps)
	      (cons bytespec values)
	      (list value)
	      `(let ((,(first variables) (DPB ,value ,byte ,getter)))
		,setter
		,value)
	      `(LDB ,byte ,getter)))))

(defun LDB-TEST (bytespec integer)
  (NOT (ZEROP (LDB bytespec integer))))

(defun MASK-FIELD (bytespec integer)
  (LOGAND integer (DPB -1 bytespec 0)))

(DEFCONSTANT MOST-POSITIVE-FIXNUM most-positive-fixnum)

(DEFCONSTANT MOST-NEGATIVE-FIXNUM most-negative-fixnum)

(DEFINE-SETF-EXPANDER MASK-FIELD (bytespec integer)
  (MULTIPLE-VALUE-BIND (temps values variables setter getter)
      (GET-SETF-EXPANSION integer nil) ;TODO: &environment
    (let ((byte (gensym))
	  (value (gensym)))
    (values (cons byte temps)
	    (cons bytespec values)
	    (list value)
	    `(let ((,(first variables) (DEPOSIT-FIELD ,value ,byte ,getter)))
	      ,setter
	      ,value)
	    `(MASK-FIELD ,byte ,getter)))))

(defun DECODE-FLOAT (float)
  (unless (floatp float)
    (type-error float 'FLOAT))
  (if (zerop float)
      (cl:values 0.0 0 1.0)
      (let ((exponent (1+ (logb float))))
	(cl:values (* (abs float) (expt 2 (- (float exponent))))
		   exponent
		   (if (minusp float) -1.0 1.0)))))

(defun SCALE-FLOAT (float integer)
  (unless (floatp float)
    (type-error float 'FLOAT))
  (unless (INTEGERP integer)
    (type-error integer 'INTEGER))
  (* float (expt 2.0 (FLOAT integer))))

(defun FLOAT-RADIX (float)
  (unless (floatp float)
    (type-error float 'FLOAT))
  2)

(cl:defun FLOAT-SIGN (float1 &OPTIONAL (float2 1.0))
  (if (minusp float1)
      (- float2)
      float2))

(defun FLOAT-DIGITS (float)
  (unless (floatp float)
    (type-error float 'FLOAT))
  53)

(defun FLOAT-PRECISION (float)
  (unless (floatp float)
    (type-error float 'FLOAT))
  (if (zerop float)
      0
      ;; TODO: return number of significant digits in denormals.
      53))

(defun INTEGER-DECODE-FLOAT (float)
  (unless (floatp float)
    (type-error float 'FLOAT))
  (if (zerop float)
      (cl:values 0.0 0 1)
      (let ((exponent (1+ (logb float))))
	(cl:values (* (abs float) (expt 2 (- (float exponent))))
		   exponent
		   (if (minusp float) 1 1)))))

(defun bignum-float (num)
  (do ((i 1 (1+ i))
       (w 1.0 (* w two^fixnum-bits))
       (x 0.0)
       (len (1- (length num))))
      ((eq i len)
       (+ x (* w (aref num i))))
    (let ((y (aref num i)))
      (incf x (* w (if (minusp y) (+ two^fixnum-bits y) y))))))

(defun FLOAT (num &optional prototype)
  (cond
    ((integerp num)
     (float num))
    ((floatp num)
     num)
    ((ratiop num)
     (/ (FLOAT (NUMERATOR num)) (FLOAT (DENOMINATOR num))))
    ((bignump num)
     (bignum-float num))
    (t
     (type-error num 'REAL))))

(fset 'FLOATP (symbol-function 'floatp))

(DEFCONSTANT MOST-POSITIVE-SHORT-FLOAT 0.0)
(DEFCONSTANT LEAST-POSITIVE-SHORT-FLOAT 0.0)
(DEFCONSTANT LEAST-POSITIVE-NORMALIZED-SHORT-FLOAT 0.0)
(DEFCONSTANT MOST-POSITIVE-DOUBLE-FLOAT 0.0)
(DEFCONSTANT LEAST-POSITIVE-DOUBLE-FLOAT 0.0)
(DEFCONSTANT LEAST-POSITIVE-NORMALIZED-DOUBLE-FLOAT 0.0)
(DEFCONSTANT MOST-POSITIVE-LONG-FLOAT 0.0)
(DEFCONSTANT LEAST-POSITIVE-LONG-FLOAT 0.0)
(DEFCONSTANT LEAST-POSITIVE-NORMALIZED-LONG-FLOAT 0.0)
(DEFCONSTANT MOST-POSITIVE-SINGLE-FLOAT 0.0)
(DEFCONSTANT LEAST-POSITIVE-SINGLE-FLOAT 0.0)
(DEFCONSTANT LEAST-POSITIVE-NORMALIZED-SINGLE-FLOAT 0.0)
(DEFCONSTANT MOST-NEGATIVE-SHORT-FLOAT 0.0)
(DEFCONSTANT LEAST-NEGATIVE-SHORT-FLOAT 0.0)
(DEFCONSTANT LEAST-NEGATIVE-NORMALIZED-SHORT-FLOAT 0.0)
(DEFCONSTANT MOST-NEGATIVE-SINGLE-FLOAT 0.0)
(DEFCONSTANT LEAST-NEGATIVE-SINGLE-FLOAT 0.0)
(DEFCONSTANT LEAST-NEGATIVE-NORMALIZED-SINGLE-FLOAT 0.0)
(DEFCONSTANT MOST-NEGATIVE-DOUBLE-FLOAT 0.0)
(DEFCONSTANT LEAST-NEGATIVE-DOUBLE-FLOAT 0.0)
(DEFCONSTANT LEAST-NEGATIVE-NORMALIZED-DOUBLE-FLOAT 0.0)
(DEFCONSTANT MOST-NEGATIVE-LONG-FLOAT 0.0)
(DEFCONSTANT LEAST-NEGATIVE-LONG-FLOAT 0.0)
(DEFCONSTANT LEAST-NEGATIVE-NORMALIZED-LONG-FLOAT 0.0)

(DEFCONSTANT SHORT-FLOAT-EPSILON 0.0)
(DEFCONSTANT SHORT-FLOAT-NEGATIVE-EPSILON 0.0)
(DEFCONSTANT SINGLE-FLOAT-EPSILON 0.0)
(DEFCONSTANT SINGLE-FLOAT-NEGATIVE-EPSILON 0.0)
(DEFCONSTANT DOUBLE-FLOAT-EPSILON 0.0)
(DEFCONSTANT DOUBLE-FLOAT-NEGATIVE-EPSILON 0.0)
(DEFCONSTANT LONG-FLOAT-EPSILON 0.0)
(DEFCONSTANT LONG-FLOAT-NEGATIVE-EPSILON 0.0)

;;; Defined in cl-conditions.el: ARITHMETIC-ERROR,
;;; ARITHMETIC-ERROR-OPERANDS, ARITHMETIC-ERROR-OPERATION,
;;; DIVISION-BY-ZERO, FLOATING-POINT-INVALID-OPERATION,
;;; FLOATING-POINT-INEXACT, FLOATING-POINT-OVERFLOW,
;;; FLOATING-POINT-UNDERFLOW
