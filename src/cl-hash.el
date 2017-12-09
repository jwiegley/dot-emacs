;;;; -*- emacs-lisp -*-
;;;
;;; Copyright (C) 2003, 2004 Lars Brinkhoff.
;;; This file implements operators in chapter 18, Hash Tables.

(IN-PACKAGE "EMACS-CL")

(if (eval-when-compile (eq (type-of (make-hash-table)) 'hash-table))
    (progn
      (cl:defun MAKE-HASH-TABLE (&KEY TEST (SIZE 10) REHASH-SIZE
				 REHASH-THRESHOLD)
	(make-hash-table :test (el-test TEST) :size SIZE))

      (when (eval-when-compile (fboundp 'define-hash-table-test))
	(define-hash-table-test 'EQL #'EQL #'sxhash)
	(define-hash-table-test 'EQUAL #'EQUAL #'sxhash)
	(define-hash-table-test 'EQUALP #'EQUALP #'equalp-hash)

	(defun equalp-hash (object)
	  (cond
	    ((CHARACTERP object)	(sxhash (CHAR-UPCASE object)))
	    ((REALP object)		(sxhash (FLOAT object)))
	    ((NUMBERP object)		(+ (sxhash (FLOAT (REALPART object)))
					   (sxhash (FLOAT (IMAGPART object)))))
	    ((consp object)		(+ (equalp-hash (car object))
					   (equalp-hash (cdr object))))
	    ((STRINGP object)		(sxhash (STRING-UPCASE object)))
	    (t				(ERROR "TODO: equalp-hash")))))

      (defun el-test (fn)
	(cond
	  ((null fn)				'EQL)
	  ((eq fn 'EQ)				'eq)
	  ((eq fn (symbol-function 'EQ))	'eq)
	  ((eq fn 'EQL)			'EQL)
	  ((eq fn (symbol-function 'EQL))	'EQL)
	  ((eq fn 'EQUAL)			'EQUAL)
	  ((eq fn (symbol-function 'EQUAL))	'EQUAL)
	  ((eq fn 'EQUALP)			'EQUALP)
	  ((eq fn (symbol-function 'EQUALP))	'EQUALP)
	  (t
	   (ERROR "Unknown hash table test function"))))

      (defmacro htab (hash)
	hash)

      (cl:defmacro HTAB (hash)
	hash)

      (defun HASH-TABLE-P (object)
	(hash-table-p object))

      (defun HASH-TABLE-TEST (hash)
	(hash-table-test hash)))

    ;; If there isn't a real hash-table type, make one using defstruct.
    (progn
      (DEFSTRUCT (HASH-TABLE (:copier nil) (:constructor mkhash (TABLE TEST)))
        TABLE TEST)

      (cl:defun MAKE-HASH-TABLE (&KEY (TEST #'EQL) (SIZE 10) REHASH-SIZE
				 REHASH-THRESHOLD)
	(mkhash (make-hash-table :test TEST :size SIZE) TEST))

      (defun htab (hash)
	(HASH-TABLE-TABLE hash))

      (cl:defmacro HTAB (hash)
	`(HASH-TABLE-TABLE ,hash))))

(defun HASH-TABLE-COUNT (hash)
  (hash-table-count (htab hash)))

(defun HASH-TABLE-REHASH-SIZE (hash)
  ;; TODO
  0)

(defun HASH-TABLE-REHASH-THRESHOLD (hash)
  ;; TODO
  0)

(defun HASH-TABLE-SIZE (hash)
  ;; TODO
  0)

(defun GETHASH (key hash &optional default)
  (let ((object (gethash key (htab hash) not-found)))
    (if (eq object not-found)
	(cl:values default nil)
	(cl:values object T))))

(DEFINE-SETF-EXPANDER GETHASH (key hash &optional default)
  (with-gensyms (keytemp hashtemp val)
    (cl:values (list keytemp hashtemp)
	       (list key hash)
	       (list val)
	       `(puthash ,keytemp ,val (HTAB ,hashtemp))
	       `(GETHASH ,keytemp ,hashtemp))))

(defun REMHASH (key hash)
  (remhash key (htab hash)))

(defun MAPHASH (fn hash)
  (maphash (el-function fn) (htab hash))
  nil)

(defun hashlist (hash)
  (let ((list nil))
    (maphash (lambda (k v) (push (cons k v) list)) hash)
    list))

(cl:defmacro WITH-HASH-TABLE-ITERATOR ((name hash) &body body)
  (with-gensyms (list)
    `(LET ((,list (hashlist ,hash)))
       (MACROLET ((,name ()
		    (QUOTE (IF (NULL ,list) (cl:values nil nil nil)
			       (LET ((cons (POP ,list)))
				 (cl:values T (CAR cons) (CDR cons)))))))
	 ,@body))))

(defun CLRHASH (hash)
  (clrhash (htab hash))
  hash)

(if (eval-when-compile (fboundp 'sxhash))
    (fset 'SXHASH (symbol-function 'sxhash))
    (defun SXHASH (object) 42))
