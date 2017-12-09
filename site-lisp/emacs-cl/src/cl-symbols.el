;;;; -*- emacs-lisp -*-
;;;
;;; Copyright (C) 2003, 2004 Lars Brinkhoff.
;;; This file implements operators in chapter 10, Symbols.

(IN-PACKAGE "EMACS-CL")

;;; Note that the Emacs Lisp symbol nil doubles as the Common Lisp
;;; symbol NIL.  This requires special attention in SYMBOL-NAME.

;;; The SYMBOL system class is built in.

(fset 'SYMBOLP (symbol-function 'symbolp))

(defun KEYWORDP (sym)
  (and (SYMBOLP sym)
       (eq (SYMBOL-PACKAGE sym) *keyword-package*)))

(defun MAKE-SYMBOL (string)
  (unless (STRINGP string)
    (type-error string 'STRING))
  (make-symbol string))

(defun COPY-SYMBOL (sym &optional copy-properties)
  (let ((new (make-symbol (SYMBOL-NAME sym))))
    (when copy-properties
      (when (boundp sym)
	(setf (symbol-value new) (symbol-value sym)))
      (when (fboundp sym)
	(setf (symbol-function new) (symbol-function sym)))
      (setf (symbol-plist new) (copy-list (symbol-plist sym))))
    new))

(cl:defun GENSYM (&OPTIONAL (x "G"))
  (multiple-value-bind (prefix suffix)
      (cond
	((STRINGP x)	(values x (prog1 *GENSYM-COUNTER*
				      (setq *GENSYM-COUNTER*
					    (binary+ *GENSYM-COUNTER* 1)))))
	((INTEGERP x)	(values "G" x))
	(t		(type-error x '(OR STRING INTEGER))))
    (MAKE-SYMBOL (FORMAT nil "~A~D" prefix suffix))))

(DEFVAR *GENSYM-COUNTER* 1)

(defvar *gentemp-counter* 1)

(cl:defun GENTEMP (&OPTIONAL (prefix "T") (package *PACKAGE*))
  (catch 'GENTEMP
    (loop
      (MULTIPLE-VALUE-BIND (symbol found)
	  (INTERN (FORMAT nil "~A~D" prefix *gentemp-counter*) package)
	(unless found
	  (throw 'GENTEMP (cl:values symbol)))
	(incf *gentemp-counter*)))))

; (defun SYMBOL-FUNCTION (symbol)
;   (unless (symbolp symbol)
;     (type-error symbol 'SYMBOL))
;   (unless (fboundp symbol)
;     (ERROR 'UNDEFINED-FUNCTION (kw NAME) symbol))
;   (symbol-function symbol))

; (DEFSETF SYMBOL-FUNCTION (symbol) (fn)
;   `(fset ,symbol ,fn))

(defun SYMBOL-FUNCTION (symbol)
  (unless (symbolp symbol)
    (type-error symbol 'SYMBOL))
  (unless (fboundp symbol)
    (ERROR 'UNDEFINED-FUNCTION (kw NAME) symbol))
  (let ((fn (symbol-function symbol)))
    (cond
      ((and (consp fn)
	    (eq (car fn) 'macro))
       nil)
      ((and (consp fn)
	    (consp (third fn))
	    (eq (first (third fn)) 'APPLY))
       (let ((ifn (second (third fn))))
	 (if (INTERPRETED-FUNCTION-P ifn) ifn fn)))
      ((and (consp fn)
	    (consp (fourth fn))
	    (eq (first (fourth fn)) 'APPLY))
       (let ((ifn (second (fourth fn))))
	 (if (INTERPRETED-FUNCTION-P ifn) ifn fn)))
      (t fn))))

(defsetf SYMBOL-FUNCTION set-symbol-function)

(DEFSETF SYMBOL-FUNCTION set-symbol-function)

(defun interactive-stuff (forms)
  (some (lambda (form)
	  (and (consp form)
	       (eq (car form) 'DECLARE)
	       (consp (cdr form))
	       (or (when (eq (cadr form) 'INTERACTIVE)
		     '((interactive)))
		   (when (and (consp (cadr form))
			      (eq (caadr form) 'INTERACTIVE))
		     `((interactive ,@(cdadr form)))))))
	forms))

(defun el-function (fn)
  (if (vectorp fn)
      `(lambda (&rest args)
	,@(interactive-stuff
	   (cddr (cl:values (FUNCTION-LAMBDA-EXPRESSION fn))))
	(APPLY ,fn args))
      fn))

(defun set-symbol-function (symbol fn)
  (fset symbol
	(cond
	  ((INTERPRETED-FUNCTION-P fn)	(el-function fn))
	  ((FUNCTIONP fn)		fn)
	  (t				(type-error fn 'FUNCTION)))))

(defun SYMBOL-NAME (symbol)
  (if symbol
      (symbol-name symbol)
      "NIL"))

(defvar *symbol-package-table* (make-hash-table :test 'eq :weakness t))

(defun SYMBOL-PACKAGE (sym)
  (or (gethash sym *symbol-package-table*)
      (when (interned-p sym) *emacs-lisp-package*)))

(defsetf SYMBOL-PACKAGE (sym) (package)
  `(if (null ,package)
       (progn (remhash ,sym *symbol-package-table*) ,package)
       (setf (gethash ,sym *symbol-package-table*) ,package)))

(fset 'SYMBOL-PLIST (symbol-function 'symbol-plist))

(DEFSETF SYMBOL-PLIST (symbol) (plist)
  `(setplist ,symbol ,plist))

(fset 'SYMBOL-VALUE (symbol-function 'symbol-value))

(defsetf SYMBOL-VALUE (symbol) (val)
  `(set ,symbol ,val))

(DEFSETF SYMBOL-VALUE (symbol) (val)
  `(SET ,symbol ,val))

(defun GET (symbol property &optional default)
  (let ((val (member property (symbol-plist symbol))))
    (if val
	(cadr val)
	default)))

(DEFSETF GET (symbol property &optional default) (val)
  `(put ,symbol ,property ,val))

(defun REMPROP (symbol indicator)
  (setplist symbol (delete-property (symbol-plist symbol) indicator)))

(defun BOUNDP (symbol)
  (unless (symbolp symbol)
    (type-error symbol 'SYMBOL))
  (boundp symbol))

(defun MAKUNBOUND (symbol)
  (unless (symbolp symbol)
    (type-error symbol 'SYMBOL))
  (makunbound symbol))

(fset 'SET (symbol-function 'set))

;;; UNBOUND-VARIABLE in cl-conditions.el.
