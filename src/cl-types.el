;;;; -*- emacs-lisp -*-
;;;
;;; Copyright (C) 2003, 2004 Lars Brinkhoff.
;;; This file implements operators in chapter 4, Types and Classes.

(IN-PACKAGE "EMACS-CL")

;;; TODO: GENERIC-FUNCTION
;;; TODO: STANDARD-GENERIC-FUNCTION
;;; TODO: CLASS
;;; TODO: BUILT-IN-CLASS
;;; TODO: STRUCTURE-CLASS
;;; TODO: STANDARD-CLASS
;;; TODO: METHOD
;;; TODO: STANDARD-METHOD
;;; TODO: STRUCTURE-OBJECT
;;; TODO: STANDARD-OBJECT
;;; TODO: METHOD-COMBINATION

(unless (fboundp 'puthash)
  (defun puthash (key value table)
    (setf (gethash key table) value)))

(defun COERCE (object type)
  (cond
    ((or (eq type 'T) (TYPEP object type))
     object)
    ((null type)
     (ERROR 'SIMPLE-TYPE-ERROR
	    (kw format) "~S can't be coerced to type ~S."
	    (kw args) (list object type)))
    ((cl:values (SUBTYPEP type 'SEQUENCE))
     (when (consp type)
       (let ((n (second type)))
	 (when (and (eq (first type) 'ARRAY)
		    (listp n))
	   (unless (eql (length n) 1)
	     (ERROR 'TYPE-ERROR))
	   (setq n (first n)))
	 (unless (or (eq n star)
		     (eql n (LENGTH object)))
	   (ERROR 'TYPE-ERROR))))
     (MAP type #'IDENTITY object))
    ((eq type 'CHARACTER)
     (CHARACTER object))
    ((eq type 'COMPLEX)
     (cond
       ((RATIONALP object)	object)
       ((FLOATP object)		(COMPLEX object 0.0))
       (t			(type-error object 'NUMBER))))
    ((cl:values (SUBTYPEP type 'FLOAT))
     (FLOAT object))
    ((eq type 'FUNCTION)
     (if (lambda-expr-p object)
	 (cl:values (COMPILE nil object))
	 (FDEFINITION object)))
    (t
     (ERROR 'SIMPLE-TYPE-ERROR
	    (kw format) "~S can't be coerced to type ~S."
	    (kw args) (list object type)))))

(defvar *deftype-expanders* (make-hash-table))

(defmacro* cl:deftype (name lambda-list &body body)
  `(progn
     (puthash ',name
	      ,(make-macro-el-function name lambda-list body)
	      *deftype-expanders*)
     ',name))

(cl:defmacro DEFTYPE (name lambda-list &body body &environment env)
  `(EVAL-WHEN (,(kw COMPILE-TOPLEVEL) ,(kw LOAD-TOPLEVEL) ,(kw EXECUTE))
     (puthash (QUOTE ,name)
	      ,(make-macro-function name lambda-list body env)
	      *deftype-expanders*)
     (QUOTE ,name)))

;;; Redefined later.
(defun classp (x)
  nil)

(defun expand-type (orig-type env)
  (if (classp orig-type)
      (CLASS-NAME orig-type)
      (let* ((type (ensure-list orig-type))
	     (fn (gethash (first type) *deftype-expanders*)))
	(if fn
	    (expand-type (FUNCALL fn type env) env)
	    orig-type))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(cl:deftype ATOM ()
  '(NOT CONS))

(cl:deftype BASE-CHAR ()
  'CHARACTER)

(cl:deftype BASE-STRING (&optional n)
  (unless n (setq n star))
  `(STRING ,n))

(cl:deftype BIGNUM ()
  '(AND INTEGER (NOT FIXNUM)))

(cl:deftype BIT ()
  '(INTEGER 0 1))

(cl:deftype BIT-VECTOR (&optional n)
  (unless n (setq n star))
  `(ARRAY BIT (,n)))

(cl:deftype BOOLEAN ()
  '(MEMBER nil T))

(cl:deftype DOUBLE-FLOAT (&optional m n)
  (unless m (setq m star))
  (unless n (setq n star))
  `(SINGLE-FLOAT ,m ,n))

(cl:deftype EXTENDED-CHAR ()
  '(AND CHARACTER (NOT BASE-CHAR)))

(cl:deftype FIXNUM ()
  (eval-when-compile `(INTEGER ,most-negative-fixnum ,most-positive-fixnum)))

(cl:deftype FLOAT (&optional m n)
  (unless m (setq m star))
  (unless n (setq n star))
  `(SINGLE-FLOAT ,m ,n))

(cl:deftype LIST ()
  '(OR NULL CONS))

(cl:deftype LONG-FLOAT (&optional m n)
  (unless m (setq m star))
  (unless n (setq n star))
  `(SINGLE-FLOAT ,m ,n))

(cl:deftype MEMBER (&rest objects)
  `(OR ,@(mapcar (curry #'list 'EQL) objects)))

(cl:deftype MOD (n)
  `(INTEGER 0 ,(binary+ n -1)))

(cl:deftype NULL ()
  '(EQL nil))

(cl:deftype NUMBER ()
  '(OR REAL COMPLEX))

(cl:deftype RATIO ()
  '(AND RATIONAL (NOT INTEGER)))

(cl:deftype REAL (&optional m n)
  (unless m (setq m star))
  (unless n (setq n star))
  `(OR (RATIONAL ,m ,n) (SINGLE-FLOAT ,m ,n)))

(cl:deftype SEQUENCE ()
  '(OR LIST VECTOR))

(cl:deftype SHORT-FLOAT (&optional m n)
  (unless m (setq m star))
  (unless n (setq n star))
  `(SINGLE-FLOAT ,m ,n))

(cl:deftype SIGNED-BYTE (&optional n)
  (unless n (setq n star))
  (let ((m n))
    (unless (eq n star)
      (setq n (EXPT 2 (cl:1- n)))
      (setq m (cl:- n))
      (setq n (cl:1- n)))
    `(INTEGER ,m ,n)))

(cl:deftype SIMPLE-BASE-STRING (&optional n)
  (unless n (setq n star))
  `(SIMPLE-STRING (,n)))

(cl:deftype SIMPLE-BIT-VECTOR (&optional n)
  (unless n (setq n star))
  `(SIMPLE-ARRAY BIT (,n)))

(cl:deftype SIMPLE-STRING (&optional n)
  (unless n (setq n star))
  `(OR (SIMPLE-ARRAY CHARACTER (,n))
       (SIMPLE-ARRAY nil (,n))))

(cl:deftype SIMPLE-VECTOR (&optional n)
  (unless n (setq n star))
  `(SIMPLE-ARRAY T (,n)))

(cl:deftype STRING (&optional n)
  (unless n (setq n star))
  `(OR (ARRAY CHARACTER (,n))
       (ARRAY nil (,n))))

(cl:deftype UNSIGNED-BYTE (&optional n)
  (unless n (setq n star))
  (unless (eq n star)
    (setq n (cl:1- (EXPT 2 n))))
  `(INTEGER 0 ,n))

(cl:deftype VECTOR (&whole w &optional type n)
  (when (null (rest w)) (setq type star))
  (unless n (setq n star))
  `(ARRAY ,type (,n)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(defun TYPE-OF (object)
  (case object
    ((nil)		'NULL)
    (T			'BOOLEAN)
    ((0 1)		'BIT)
    (t
     (ecase (type-of object)
       ;; This is supposed to be an exhaustive enumeration of all
       ;; possible return values for Emacs Lisp type-of.
       ((bit-vector bool-vector)
			`(SIMPLE-BIT-VECTOR ,(length object)))
       (subr
			'COMPILED-FUNCTION)
       (compiled-function
			(let ((info (gethash object *funcallable-objects*)))
			  (if info
			      (car info)
			      'COMPILED-FUNCTION)))
       (character	'CHARACTER)
       (cons		'CONS)
       (float		'SINGLE-FLOAT)
       (hash-table	'HASH-TABLE)
       (integer		(if (minusp object)
			    'FIXNUM
			    `(INTEGER 0 ,MOST-POSITIVE-FIXNUM)))
       (string		`(SIMPLE-STRING ,(length object)))
       (symbol		(if (eq (SYMBOL-PACKAGE object) *keyword-package*)
			    'KEYWORD
			    'SYMBOL))
       (vector
	(case (aref object 0)
	  (ARRAY	`(ARRAY T ,(array-dims object)))
	  (BIGNUM	(if (MINUSP object)
			    'BIGNUM
			    `(INTEGER ,(binary+ MOST-POSITIVE-FIXNUM 1))))
	  (bit-array	`(ARRAY BIT ,(array-dims object)))
	  (BIT-VECTOR	`(BIT-VECTOR ,(vector-size object)))
	  (char-array	`(ARRAY CHARACTER ,(array-dims object)))
	  (CHARACTER	'CHARACTER)
	  (COMPLEX	'COMPLEX)
	  (INTERPRETED-FUNCTION
			'INTERPRETED-FUNCTION)
	  (RATIO	'RATIO)
	  (SIMPLE-VECTOR
			`(SIMPLE-VECTOR ,(1- (length object))))
	  (STRING	`(STRING ,(vector-size object)))
	  (VECTOR	`(VECTOR T ,(vector-size object)))
	  (t		(aref object 0))))
       ;; For now, throw an error on these.
       ((buffer char-table frame marker overlay process
	 subr window window-configuration)
			(error "Unknown type: %s" (type-of object)))))))

;;; TYPEP defined in cl-typep.el.

;;; TYPE-ERROR, TYPE-ERROR-DATUM, TYPE-ERROR-EXPECTED-TYPE, and
;;; SIMPLE-TYPE-ERROR defined in cl-conditions.el.
