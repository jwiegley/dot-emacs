;;;; -*- emacs-lisp -*-
;;;
;;; Copyright (C) 2003, 2004 Lars Brinkhoff.
;;;
;;; This file implements the SUBTYPEP function from chapter 4, Types
;;; and Classes.  The implementation is based on Henry Baker's paper A
;;; Decision Procedure for Common Lisp's SUBTYPEP Predicate.

(IN-PACKAGE "EMACS-CL")

(defvar *types*
  '(nil COMPLEX KEYWORD SYMBOL CONS CHARACTER FUNCTION COMPILED-FUNCTION))

(defvar *subtypep-objects*
  (list (COMPLEX 0 1) nil T (make-symbol "") (cons nil nil)
	;; Should really be an uninterned keyword.
	(kw really-unlikely-keyword-name)
	;; This guarantees unique character objects.
	(vector 'CHARACTER 0)
	(vector 'CHARACTER 65)
	(vector 'INTERPRETED-FUNCTION '(LAMBDA ()) nil nil nil)
	(byte-compile '(lambda ()))))

(defvar *type-val* (make-hash-table :test 'equal))

(defun object-val (object)
  (ASH 1 (position object *subtypep-objects*)))

(defun register-object (object)
  ;(FORMAT T "~&Object #<~S>:" (TYPE-OF object))
  (dolist (type *types*)
    (when (TYPEP object type)
      ;(FORMAT T " ~S" type)
      (setf (gethash type *type-val*)
	    (LOGIOR (gethash type *type-val*) (object-val object))))))

(dolist (type *types*)
  (setf (gethash type *type-val*) 0))

(dolist (object *subtypep-objects*)
  (register-object object))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(defun integer-endpoint (x high)
  (cond
    ((eq x star)
     x)
    ((INTEGERP x)
     x)
    ((REALP x)
     (cl:values (if high (FLOOR x) (CEILING x))))
    ((consp x)
     (setq x (car x))
     (if (INTEGERP x)
	 (if high (cl:1- x) (cl:1+ x))
	 (cl:values (if high
			(cl:1- (CEILING x))
			(cl:1+ (FLOOR x))))))
    (t
     (type-error x `(OR REAL (CONS REAL NULL) (EQL ,star))))))

(defun* simplify-integer-range (range &optional high)
  (unless (null range)
    (let ((x (integer-endpoint (pop range) high)))
      (cond
	((eq x star)
	 (cons x (simplify-integer-range range (not high))))
	((and high
	      (not (null range))
	      (EQL (cl:1+ x)
		   (integer-endpoint (first range) (not high))))
	 (pop range)
	 (simplify-integer-range range high))
	((and (not high)
	      (not (eq (first range) star))
	      (cl:> x (integer-endpoint (first range) high)))
	 (when (= (length range) 1)
	   (return-from simplify-integer-range nil))
	 (pop range)
	 (simplify-integer-range range high))
	(t
	 (cons x (simplify-integer-range range (not high))))))))

(defun not-integer-p (x)
  (or (ratiop x)
      (and (floatp x)
	   (not (zerop (NTH-VALUE 1 (TRUNCATE x)))))))

(defun* simplify-ratio-range (range &optional high)
  (unless (null range)
    (let ((x (pop range)))
      (cond
	((eq x star)
	 (cons x (simplify-ratio-range range (not high))))
	((and (EQUAL x (first range))
	      (if high
		  (or (and (consp x) (INTEGERP (car x)))
		      (not-integer-p x))
		  (or (and (consp x) (not-integer-p (car x)))
		      (INTEGERP x))))
	 ;; For example, leave (* (1/2) (1/2) *) alone,
	 ;; but merge (* (0) (0) *) into (* *).
	 (pop range)
	 (simplify-ratio-range range high))
	(t
	 (cons x (simplify-ratio-range range (not high))))))))

(defun range-complement (range)
  (cond
    ((null range)
     (list star star))
    (t
     (setq range (if (eq (first range) star)
		     (rest range)
		     (cons star range)))
     (setq range (if (eq (first (last range)) star)
		     (butlast range)
		     (append range (list star))))
     (mapcar (lambda (x)
	       (cond
		 ((eq x star) star)
		 ((consp x) (first x))
		 (t (list x))))
	     range))))

(defun ll<= (x y)
  (cond
    ((eq x star))
    ((eq y star) nil)
    ((consp x)
     (if (consp y)
	 (binary<= (first x) (first y))
	 (binary< (first x) y)))
    ((consp y)
     (binary<= x (first y)))
    ((binary<= x y))))

(defun lh> (x y)
  (cond
    ((eq x star) nil)
    ((eq y star) nil)
    ((consp x)
     (if (consp y)
	 (if (and (ratiop x) (ratiop y))
	     (binary< (first y) (first x))
	     (binary<= (first y) (first x)))
	 (binary< y (first x))))
    ((consp y)
     (binary< (first y) x))
    ((binary< y x))))

(defun hh<= (x y)
  (cond
    ((eq x star) nil)
    ((eq y star))
    ((consp x)
     (if (consp y)
	 (binary<= (first x) (first y))
	 (binary<= (first x) y)))
    ((consp y)
     (binary< x (first y)))
    ((binary<= x y))))

(defun range-union (ranges1 ranges2)
  (when (and ranges1 ranges2 (ll<= (first ranges2) (first ranges1)))
    (psetq ranges1 ranges2
	   ranges2 ranges1))
;   (print (format "union %s %s" ranges1 ranges2))
  (let ((low1 (first ranges1))
	(low2 (first ranges2))
	(high1 (second ranges1))
	(high2 (second ranges2)))
    (cond
      ((null ranges1)
       ranges2)
      ((null ranges2)
       ranges1)
      ((lh> low2 high1)
;        (print
; 	(let ((standard-output (lambda (ch) nil)))
; 	 (format "A: (%s %s ...)   %s + %s -> %s\n=> %s"
; 		 low1 high1 (cddr ranges1) ranges2
; 		 (range-union (cddr ranges1) ranges2)
; 		 (list* low1 high1 (range-union (cddr ranges1) ranges2)))))
       (list* low1 high1 (range-union (cddr ranges1) ranges2)))
      ((hh<= high1 high2)
;        (print
; 	(let ((standard-output (lambda (ch) nil)))
; 	 (format "B: (%s %s ...)   %s + %s -> %s\n=> %s"
; 		 low1 high2 (cddr ranges1) ranges2
; 		 (range-union (cddr ranges1) ranges2)
; 		 (let ((u (range-union (cddr ranges1) ranges2)))
; 		   (when (and u (hh<= high2 (second u)))
; 		     (setq high2 (second u)))
; 		   (list* low1 high2 (cddr u))))))
       (let ((u (range-union (cddr ranges1) ranges2)))
	 (when (and u (hh<= high2 (second u)))
	   (setq high2 (second u)))
	 (list* low1 high2 (cddr u))))
      (t
;        (print
; 	(let ((standard-output (lambda (ch) nil)))
; 	 (format "C: (%s %s ...)   %s + %s -> %s"
; 		 low1 high1 ranges1 (cddr ranges2)
; 		 (range-union ranges1 (cddr ranges2)))))
       (list* low1 high1 (cddr (range-union ranges1 (cddr ranges2))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(defun integer-union (r1 r2)
  (simplify-integer-range (range-union r1 r2)))

(defun ratio-union (r1 r2)
  (simplify-ratio-range (range-union r1 r2)))

(defun range-intersection (r1 r2)
  (range-complement (range-union (range-complement r1)
				 (range-complement r2))))

(defun integer-intersection (r1 r2)
  (integer-complement (integer-union (integer-complement r1)
				     (integer-complement r2))))

(defun type-union (v1 v2)
  `(,(discrete-union (first v1) (first v2))
    ,(real-union (second v1) (second v2))
    ,(array-union (third v1) (third v2))))

(defun discrete-union (t1 t2)
  (LOGIOR t1 t2))

(defun real-union (r1 r2)
  `(,(integer-union (first r1) (first r2))
    ,(ratio-union (second r1) (second r2))
    ,(range-union (third r1) (third r2))))

(defun array-union (t1 t2)
  (MAPCAR #'LOGIOR t1 t2))

(defun type-intersection (v1 v2)
  `(,(discrete-intersection (first v1) (first v2))
    ,(real-intersection (second v1) (second v2))
    ,(array-intersection (third v1) (third v2))))

(defun discrete-intersection (t1 t2)
  (LOGAND t1 t2))

(defun real-intersection (r1 r2)
  `(,(integer-intersection (first r1) (first r2))
    ,(range-intersection (second r1) (second r2))
    ,(range-intersection (third r1) (third r2))))

(defun array-intersection (t1 t2)
  (MAPCAR #'LOGAND t1 t2))

(defun type-complement (type)
  `(,(discrete-complement (first type))
    ,(real-complement (second type))
    ,(array-complement (third type))))

(defun discrete-complement (type)
  (LOGNOT type))

(defun real-complement (type)
  `(,(integer-complement (first type))
    ,(range-complement (second type))
    ,(range-complement (third type))))

(defun integer-complement (range)
  (simplify-integer-range (range-complement range)))

(defun array-complement (type)
  (mapcar #'LOGNOT type))

(defun discrete-type-val (type)
  (or (gethash type *type-val*)
      (let ((val 0))
	(dolist (object *subtypep-objects*)
	  (when (TYPEP object type)
	    (setq val (LOGIOR val (object-val object)))))
	val)))

(defun real-type-val (type)
  (if (atom type)
      (case type
	(INTEGER
		`((,star ,star) () ()))
	(RATIONAL
		`((,star ,star) (,star ,star) ()))
	(SINGLE-FLOAT
		`(() () (,star ,star)))
	(t
		`(() () ())))
      (case (first type)
	(INTEGER
		(let ((range (rest type)))
		  (while (< (length range) 2)
		    (setq range (append range (list star))))
		  `(,(simplify-integer-range range) () ())))
	(RATIONAL
		(let ((range (rest type)))
		  (while (< (length range) 2)
		    (setq range (append range (list star))))
		  `(,(simplify-integer-range range) ,range ())))
	(SINGLE-FLOAT
		(let ((range (rest type)))
		  (while (< (length range) 2)
		    (setq range (append range (list star))))
		  `(() () ,range)))
	(EQL
	 (let ((obj (second type)))
	   (cond
	     ((INTEGERP obj)
		`((,obj ,obj) () ()))
	     ((ratiop obj)
		`(() (,obj ,obj) ()))
	     ((FLOATP obj)
		`(() () (,obj ,obj)))
	     (t
		'(() () ())))))
	((ARRAY COMPLEX CONS SIMPLE-ARRAY)
		`(() () ()))
	(t	(ERROR "Uknown type specifier: ~S." type)))))

(defun stars (n)
  (with-collector collect
    (dotimes (i n)
      (collect star))))

(defun iterate-over-dimensions (dimensions rank i w pos dims)
  (cond
    ((null dimensions)
     ;(FORMAT T "~& i=~D w=~D pos=~S dims=~S" i w pos dims)
     (let ((v t))
       (dotimes (j rank)
	 ;(FORMAT T "~&   ~S ~S" (nth j pos) (nth j dims))
	 (unless (or (eq (nth j dims) star)
		     (eql (nth j pos) (nth j dims)))
	   (setq v nil)))
       ;(FORMAT T "~&   v=~S" v)
       (when v
	 (setq *val* (LOGIOR *val* (ASH 1 i))))))
    (t
     (let ((w2 (* w (1+ (length (first dimensions))))))
       (dolist (d (append (first dimensions) (list star)))
	 (iterate-over-dimensions
	  (rest dimensions) rank i w2 (append pos (list d)) dims)
	 (incf i w))))))

(defun array-type-val (type)
  (setq type (ensure-list type))
  (cond
    ((or (eq (first type) 'ARRAY)
	 (eq (first type) 'SIMPLE-ARRAY))
     (while (< (length type) 3)
       (setq type (append type (list star))))
     (let* ((*val* (if (eq (first type) 'ARRAY) 1 0))
	    (element-type (second type))
	    (dims (third type))
	    (rank dims)
	    (n 1)
	    (pos 0))
       (cond
	 ((eq dims star)
	  (setq *val* (logior *val* -2)))
	 ((integerp dims)
	  (setq dims (stars dims)))
	 (t
	  (setq rank (length dims))))
       (unless (eq dims star)
	 (iterate-over-dimensions
	  (gethash rank *array-bounds*) rank
	  (gethash rank *rank-index*) 1 nil dims))
;	 (FORMAT T "~&~S dimensions ~S => " (first type) dims)
;	 (WRITE *val* (kw BASE) 2)
       (if (eq element-type star)	`(,*val* ,*val* ,*val* ,*val*)
	   (case (UPGRADED-ARRAY-ELEMENT-TYPE element-type)
	     ((nil)			`(,*val* 0 0 0))
	     (BIT			`(0 ,*val* 0 0))
	     (CHARACTER			`(0 0 ,*val* 0))
	     (T				`(0 0 0 ,*val*))))))
    (t
     '(0 0 0 0))))

(defun type-val (type)
  (setq type (expand-type type nil))
  (cond
    ((eq type 'T)
     `(-1 ((,star ,star) (,star ,star) (,star ,star)) (-1 -1 -1)))
    ;((memq type *types*)
     ;`(,(gethash type *type-val*) (() () ()) ,(array-type-val type)))
    ((atom type)
     `(,(discrete-type-val type) ,(real-type-val type) ,(array-type-val type)))
    (t
     (case (first type)
       ((FUNCTION SATISFIES VALUES)
	(throw 'SUBTYPEP (cl:values nil nil)))
       (AND
	(if (null (rest type))
	    (type-val 'T)
	    (reduce #'type-intersection (rest type) :key #'type-val)))
       (OR
	(if (null (rest type))
	    (type-val nil)
	    (reduce #'type-union (rest type) :key #'type-val)))
       (NOT
	(type-complement (type-val (second type))))
       (t
	`(,(discrete-type-val type)
	  ,(real-type-val type)
	  ,(array-type-val type)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(defvar *array-bounds*)
(defvar *rank-index*)
(defvar *highest-rank*)

(defun do-array-stuff (dims)
  (unless (eq dims star)
    (when (integerp dims)
      (setq dims (stars dims)))
    (let ((n (length dims)))
      (when (> n *highest-rank*)
	(setq *highest-rank* n))
      (when (null (gethash n *array-bounds*))
	(setf (gethash n *array-bounds*)
	      (make-list n nil)))
      (dotimes (i n)
	(unless (eq (nth i dims) star)
	  (pushnew (nth i dims)
		   (nth i (gethash n *array-bounds*))
		   :test #'eql))))))

(defun find-new-objects (type env)
  (setq type (expand-type type env))
  (when (consp type)
    (case (first type)
      ((AND OR NOT)
       (mapc #'find-new-objects (rest type)))
      (EQL
       (push type *types*)
       (pushnew (second type) *subtypep-objects*))
      ((ARRAY SIMPLE-ARRAY)
       (let ((dims star))
	 (when (> (length type) 2)
	   (setq dims (third type)))
	 (do-array-stuff dims))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(defun* SUBTYPEP (type1 type2 &optional env)
  (when (null type1)
    (return-from SUBTYPEP (cl:values 'T 'T)))
  (when (eq type2 'T)
    (return-from SUBTYPEP (cl:values 'T 'T)))
  (let ((*types* *types*)
	(*type-val* *type-val*)
	(*subtypep-objects* *subtypep-objects*)
	(*array-bounds* (make-hash-table :test #'eql))
	(*rank-index* (make-hash-table :test #'eql))
	(*highest-rank* 0))
    (find-new-objects type1 env)
    (find-new-objects type2 env)
    (let ((bit-index 1))
      (dotimes (i (1+ *highest-rank*))
	(setf (gethash i *rank-index*) bit-index)
	(let ((bits 1))
	  (dotimes (j (length (gethash i *array-bounds*)))
	    (setq bits
		  (* bits (1+ (length (nth j (gethash i *array-bounds*))))))
	    (setf (nth j (gethash i *array-bounds*))
		  (sort (nth j (gethash i *array-bounds*)) #'binary<)))
	  (incf bit-index bits))))
;   (dotimes (i (1+ *highest-rank*))
;     (FORMAT T "~&Rank ~D: ~S, index ~D"
;	      i (gethash i *array-bounds*) (gethash i *rank-index*)))
    (dolist (type *types*)
      (setf (gethash type *type-val*) 0))
    (dolist (object *subtypep-objects*)
      (register-object object))
    (catch 'SUBTYPEP
;     (FORMAT T "~&Type ~S = ~S => ~S"
;	     type1 (expand-type type1 nil) (type-val type1))
;     (FORMAT T "~&Type ~S = ~S => ~S"
;	     type2 (expand-type type2 nil) (type-val type2))
;     (PRINT (type-val `(AND ,type1 (NOT ,type2))))
     (let* ((val (type-val `(AND ,type1 (NOT ,type2))))
	    (ranges (second val)))
       (cl:values (and (ZEROP (first val))
		       (null (first ranges))
		       (null (second ranges))
		       (null (third ranges))
		       (every #'ZEROP (third val)))
		  'T)))))
