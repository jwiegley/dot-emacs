;;;; -*- emacs-lisp -*-
;;;
;;; Copyright (C) 2003, 2004 Lars Brinkhoff.
;;; This file implements the TYPEP function from chapter 4, Types and Classes.

(IN-PACKAGE "EMACS-CL")

(defvar *atomic-typespecs* (make-hash-table))
(defvar *compound-typespecs* (make-hash-table))

(defun ensure-type (name predicate)
  (setf (gethash name *atomic-typespecs*) predicate))

;;; Implements TYPEP for "typespec".
(defmacro* define-typep ((var typespec env &optional compound-only) &body body)
  (if (consp typespec)
      `(progn
	 (setf (gethash ',(first typespec) *compound-typespecs*)
	       (function* (lambda (,var ,env ,@(rest typespec)) ,@body)))
	,@(unless compound-only
	   `((ensure-type ',(first typespec)
	                  (function* (lambda (,var ,env ,@(rest typespec))
			               ,@body))))))
      `(ensure-type ',typespec (function* (lambda (,var ,env) ,@body)))))

(defun in-range (num low high)
  "Check that NUM is in the range specified by the interval designators
   LOW and HIGH."
  (let* ((low-exclusive (consp low))
	 (low (if low-exclusive (car low) low))
	 (high-exclusive (consp high))
	 (high (if high-exclusive (car high) high)))
    (and (cond
	   ((eq low star) t)
	   (low-exclusive (cl:< low num))
	   (t (cl:<= low num)))
	 (cond
	   ((eq high star) t)
	   (high-exclusive (cl:< num high))
	   (t (cl:<= num high))))))

(defvar star (INTERN "*" "EMACS-CL"))

(defmacro star-or (type &rest forms)
  `(or (eq ,type star) ,@forms))


;;; Definitions for all type specifiers recognized by TYPEP follows.

(define-typep (object (AND &rest types) env :compound-only)
  (every (lambda (type) (TYPEP object type env)) types))

(define-typep (object (ARRAY &optional (type star) (dims star)) env)
  (and (ARRAYP object)
       (star-or type (eq (UPGRADED-ARRAY-ELEMENT-TYPE type)
			 (ARRAY-ELEMENT-TYPE object)))
       (cond
	 ((eq dims star)	'T)
	 ((INTEGERP dims)	(eql (ARRAY-RANK object) dims))
	 (t			(dims-match dims (ARRAY-DIMENSIONS object))))))

(defun dims-match (d1 d2)
  (cond
    ((null d1)	(null d2))
    ((null d2)	nil)
    (t		(and (or (eq (first d1) star)
			 (eq (first d2) star)
			 (eql (first d1) (first d2)))
		     (dims-match (rest d1) (rest d2))))))

(define-typep (object CHARACTER env)
  (CHARACTERP object))

(define-typep (object COMPILED-FUNCTION env)
  (COMPILED-FUNCTION-P object))

(define-typep (object (COMPLEX &optional (type star)) env)
  (and (COMPLEXP object)
       (star-or
	type
	(unless (cl:values (SUBTYPEP type 'REAL))
	  (ERROR "(COMPLEX ~S) is not a valid type specifier." type))
	'T)))

(define-typep (object (CONS &optional (car-type star) (cdr-type star)) env)
  (and (consp object)
       (star-or car-type (TYPEP (car object) car-type env))
       (star-or cdr-type (TYPEP (cdr object) cdr-type env))))

(define-typep (obj1 (EQL obj2) env :compound-only)
  (EQL obj1 obj2))

(define-typep (object FUNCTION env)
  (FUNCTIONP object))

(define-typep (object (FUNCTION &rest args) env :compound-only)
  (ERROR "TYPEP does not accept a compound FUNCTION type specifier."))

(define-typep (object HASH-TABLE env)
  (HASH-TABLE-P object))

(define-typep (object (INTEGER &optional (low star) (high star)) env)
  (and (INTEGERP object) (in-range object low high)))

(define-typep (object INTERPRETED-FUNCTION env)
  (INTERPRETED-FUNCTION-P object))

(define-typep (object KEYWORD env)
  (KEYWORDP object))

(define-typep (object LOGICAL-PATHNAME env)
  (vector-and-typep object 'LOGICAL-PATHNAME))

(define-typep (object nil env)
  nil)

(define-typep (object (NOT type) env :compound-only)
  (not (TYPEP object type env)))

(define-typep (object (OR &rest types) env :compound-only)
  (some (lambda (type) (TYPEP object type env)) types))

(define-typep (object PACKAGE env)
  (PACKAGEP object))

(define-typep (object PATHNAME env)
  (PATHNAMEP object))

(define-typep (object RANDOM-STATE env)
  (RANDOM-STATE-P object))

(define-typep (object (RATIONAL &optional (low star) (high star)) env)
  (and (RATIONALP object) (in-range object low high)))

(define-typep (object (SATISFIES fn) env :compound-only)
  (unless (symbolp fn)
    (type-error fn '(CONS (EQL SATISFIES) (CONS SYMBOL NULL))))
  (funcall fn object))

(define-typep (object (SIMPLE-ARRAY &optional (type star) (dims star)) env)
  (and (or (bit-vector-p object)
	   (stringp object)
	   (SIMPLE-VECTOR-P object))
       (star-or type
		(eq (UPGRADED-ARRAY-ELEMENT-TYPE type)
		    (ARRAY-ELEMENT-TYPE object)))
       (star-or dims
		(eql dims 1)
		(equal dims (list star)))))

(define-typep (object (SINGLE-FLOAT &optional (low star) (high star)) env)
  (and (floatp object) (in-range object low high)))

(define-typep (object STANDARD-CHAR env)
  (and (CHARACTERP object)
       (STANDARD-CHAR-P object)))

(define-typep (object SYMBOL env)
  (SYMBOLP object))

(define-typep (object T env)
  T)

(define-typep (object (VALUES &rest args) env :compound-only)
  (ERROR "TYPEP does not accept a VALUES type specifier."))



(defun TYPEP (object type &optional env)
  (setq type (expand-type type env))
  (cond
    ((consp type)
     (let ((fn (gethash (first type) *compound-typespecs*)))
       (if fn
	   (APPLY fn object env (rest type))
	   (error "invalid typespec: %s" type))))
    ((symbolp type)
     (let ((fn (gethash type *atomic-typespecs*)))
       (if fn
	   (FUNCALL fn object env)
	   (ERROR "Invalid typespec: ~A" type))))
    (t
     (type-error type '(OR SYMBOL CONS CLASS)))))

;;; Bootstrap issue.  Redefined later.
(defun INTERPRETED-FUNCTION-P (fn)
  nil)
