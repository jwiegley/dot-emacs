;;;; -*- emacs-lisp -*-
;;;
;;; Copyright (C) 2003, 2004 Lars Brinkhoff.
;;; This file implements operators in chapter 3, Evaluation and Compilation.

(IN-PACKAGE "EMACS-CL")

;;; Assigned later in populate-packages.
(defvar *global-environment* nil)

(defvar *compiler-macro-functions* (make-hash-table :test 'equal))

(defvar *macro-functions* (make-hash-table))

(defvar *symbol-macro-functions* (make-hash-table))

(defun COMPILER-MACRO-FUNCTION (name &optional env)
  (gethash name *compiler-macro-functions*))

(defsetf COMPILER-MACRO-FUNCTION (name &optional env) (fn)
  `(setf (gethash ,name *compiler-macro-functions*) ,fn))

;; DEFINE-COMPILER-MACRO defined later.

;;; Redefined later in cl-eval.el.
(defun lexical-function (name env)
  nil)

(defun MACRO-FUNCTION (name &optional env)
  (when (null env)
    (setq env *global-environment*))
  (multiple-value-bind (type localp decl) (function-information name env)
    (when (eq type :macro)
      (if localp
	  (lexical-function name env)
	  (gethash name *macro-functions*)))))

(defsetf MACRO-FUNCTION (name &optional env) (fn)
  `(if (null ,env)
       (setf (gethash ,name *macro-functions*) ,fn)
       (set-local-macro ,name ,fn ,env)))

(defun make-macro-el-function (name lambda-list body)
  (with-gensyms (fvar evar)
    (let ((e (memq '&environment lambda-list))
	  (form fvar))
      (when e
	(when (null (cdr e))
	  (ERROR 'PROGRAM-ERROR))
	(setq evar (second e))
	(let ((x lambda-list))
	  (while x
	    (when (eq (cadr x) '&environment)
	      (setf (cdr x) (cdddr x)))
	    (setq x (cdr x)))))
      (if (eq (first lambda-list) '&whole)
	  (unless (= (length lambda-list) 2)
	    (push (gensym) (cddr lambda-list)))
	  (setq form `(cdr ,fvar)))
      (unless (null lambda-list)
	(setq body `((destructuring-bind ,lambda-list ,form ,@body))))
      `(lambda (,fvar ,evar) ,@body))))

(defmacro* cl:defmacro (name lambda-list &body body)
  (when byte-compile-warnings
    (byte-compile-log-1 (format "cl:defmacro %s" name)))
  `(progn
     (unless (fboundp ',name)
       (fset ',name nil))
     (setf (MACRO-FUNCTION ',name)
           ,(make-macro-el-function name lambda-list body))
    ',name))

(cl:defmacro DEFMACRO (name lambda-list &body body)
  `(EVAL-WHEN (,(kw COMPILE-TOPLEVEL) ,(kw LOAD-TOPLEVEL) ,(kw EXECUTE))
     (fset (QUOTE ,name) nil)
     (SETF (MACRO-FUNCTION (QUOTE ,name))
           ,(make-macro-function name lambda-list body))
     (QUOTE ,name)))

(cl:defmacro DEFINE-COMPILER-MACRO (name lambda-list &body body)
  `(EVAL-WHEN (,(kw COMPILE-TOPLEVEL) ,(kw LOAD-TOPLEVEL) ,(kw EXECUTE))
     (SETF (COMPILER-MACRO-FUNCTION (QUOTE ,name))
           ,(make-macro-function name lambda-list body nil
				 :type 'COMPILER-MACRO))
     (QUOTE ,name)))

(cl:defmacro LAMBDA (lambda-list &body body)
  `(FUNCTION (LAMBDA ,lambda-list ,@body)))

;;; COMPILE is defined in cl-compile.el.

(defun MACROEXPAND-1 (form &optional env)
  (cond
    ((and (consp form)
	  (symbolp (car form)))
     (let ((fn (MACRO-FUNCTION (car form) env)))
       (if fn
	   (let ((new (FUNCALL *MACROEXPAND-HOOK* fn form env)))
	     (cl:values new (not (eq form new))))
	   (cl:values form nil))))
    ((symbolp form)
     (multiple-value-bind (type localp decls) (variable-information form env)
       (if (eq type :symbol-macro)
	   (if localp
	       (let ((fn (lexical-value form env)))
		 (cl:values (funcall *MACROEXPAND-HOOK* fn form env) T))
	       (let ((fn (gethash form *symbol-macro-functions*)))
		 (if fn
		     (cl:values (funcall *MACROEXPAND-HOOK* fn form env) T)
		     (cl:values form nil))))
	   (cl:values form nil))))
    (t
     (cl:values form nil))))

(defun* MACROEXPAND (form &optional env)
  (let ((form form) (expanded-p nil) exp)
    (loop
     (MULTIPLE-VALUE-SETQ (form exp) (MACROEXPAND-1 form env))
     (if exp
	 (setq expanded-p T)
	 (return-from MACROEXPAND (cl:values form expanded-p))))))

(defmacro* DEFINE-SYMBOL-MACRO (symbol expansion)
  `(eval-when (:compile-toplevel :load-toplevel :execute)
     (setf (gethash ',symbol *symbol-macro-functions*)
           (cl:lambda (form env) ',expansion))
     ',symbol))

(cl:defmacro DEFINE-SYMBOL-MACRO (symbol expansion)
  `(EVAL-WHEN (,(kw COMPILE-TOPLEVEL) ,(kw LOAD-TOPLEVEL) ,(kw EXECUTE))
     (puthash (QUOTE ,symbol) (LAMBDA (form env) (QUOTE ,expansion))
              *symbol-macro-functions*)
     (QUOTE ,symbol)))

(defvar *MACROEXPAND-HOOK* 'FUNCALL)

(defvar *declarations*
  '(IGNORE IGNORABLE DYNAMIC-EXTENT TYPE INLINE
    NOTINLINE FTYPE DECLARATION OPTIMIZE SPECIAL
    ;; Emacs Common Lisp extensions:
    INTERACTIVE)
  "A list of valid declaration identifiers.")

(defun valid-declaration-identifier-p (object)
  (or (memq object *declarations*)
      (gethash object *atomic-typespecs*)
      (gethash object *deftype-expanders*)
      (classp object)))

(defun PROCLAIM (declaration)
  (unless (and (consp declaration)
	       (valid-declaration-identifier-p (car declaration)))
    (type-error declaration `(CONS (MEMBER ,@*declarations*) LIST)))
  (case (first declaration)
    (SPECIAL
     (dolist (var (rest declaration))
       (pushnew var *specials*)))
    (INLINE)
    (NOTINLINE)
    (DECLARATION
     (dolist (name (rest declaration))
       (pushnew name *declarations*))))
  nil)

(cl:defmacro DECLAIM (&rest declarations)
  `(EVAL-WHEN (,(kw COMPILE-TOPLEVEL) ,(kw LOAD-TOPLEVEL) ,(kw EXECUTE))
     ,@(mapcar (lambda (decl) `(PROCLAIM (QUOTE ,decl)))
	       declarations)))

;;; THE setf expansion defined in cl-flow.el.

(defun SPECIAL-OPERATOR-P (symbol)
  (unless (symbolp symbol)
    (type-error symbol 'SYMBOL))
  (memq symbol
	'(BLOCK CATCH EVAL-WHEN FLET FUNCTION GO IF LABELS LET LET*
	  LOAD-TIME-VALUE LOCALLY MACROLET MULTIPLE-VALUE-CALL
	  MULTIPLE-VALUE-PROG1 PROGN PROGV QUOTE RETURN-FROM SETQ
	  SYMBOL-MACROLET TAGBODY THE THROW UNWIND-PROTECT)))

(defun quoted-object-p (object)
  (and (consp object)
       (eq (car object) 'QUOTE)))

(defun CONSTANTP (object &optional env)
  (unless env
    (setq env *global-environment*))
  (cond
    ((KEYWORDP object))
    ((symbolp object)
     (memq object *constants*))
    ((atom object))
    ((quoted-object-p object))))
