;;;; -*- emacs-lisp -*-
;;;
;;; Copyright (C) 2003, 2004 Lars Brinkhoff.
;;; This file implements operators in chapter 5, Data and Control Flow.

(IN-PACKAGE "EMACS-CL")

(define-storage-layout interp-fn (lambda-exp env name doc))

(defvar *setf-definitions* (make-hash-table))

(unless (fboundp 'functionp)
  (defun functionp (object)
    (or (subrp object)
	(byte-code-function-p object)
	(and (consp object)
	     (eq (car object) 'lambda)))))

(defun APPLY (fn &rest args)
  (cond
    ((COMPILED-FUNCTION-P fn)
     (cond
       ((null args)		(funcall fn))
       ((null (rest args))	(apply fn (first args)))
       (t			(apply #'apply fn args))))
    ((INTERPRETED-FUNCTION-P fn)
     (eval-lambda-expr (interp-fn-lambda-exp fn)
		       (append (butlast args)
			       (car (last args)))
		       (interp-fn-env fn)))
    ((functionp fn)
     (apply #'apply fn args))
    ((or (symbolp fn) (consp fn))
     (apply #'APPLY (FDEFINITION fn) args))
    (t
     (type-error fn '(OR FUNCTION SYMBOL CONS)))))

(defun function-block-name (name)
  (cond
    ((symbolp name)		name)
    ((setf-name-p name)		(second name))
    (t				(not-function-name-error name))))

(cl:defmacro DEFUN (name lambda-list &body forms)
  (MULTIPLE-VALUE-BIND (body decls doc) (parse-body forms t)
    `(EVAL-WHEN (,(kw LOAD-TOPLEVEL) ,(kw EXECUTE))
       (set-fun (QUOTE ,name) (LAMBDA ,lambda-list
				,@(when doc `(,doc))
				,@(when decls `((DECLARE ,@decls)))
				(BLOCK ,(function-block-name name)
				  ,@body))))))

(defun set-fun (name fn)
  (setf (FDEFINITION name) fn)
  (setf (function-name fn) name)
  name)

(defun setf-name-p (name)
  (and (consp name)
       (eq (car name) 'SETF)
       (symbolp (cadr name))
       (null (cddr name))))

(defun not-function-name-error (name)
  (type-error name '(OR SYMBOL (CONS (EQL SETF) (CONS SYMBOL NULL)))))

(defun FDEFINITION (name)
  (cond
    ((symbolp name)
     (unless (FBOUNDP name)
       (ERROR 'UNDEFINED-FUNCTION (kw NAME) name))
     (if (or (SPECIAL-OPERATOR-P name) (MACRO-FUNCTION name))
	 nil
	 (SYMBOL-FUNCTION name)))
    ((setf-name-p name)
     (let ((fn (gethash (second name) *setf-definitions*)))
       (if (null fn)
	   (ERROR 'UNDEFINED-FUNCTION (kw NAME) name)
	   fn)))
    (t
     (not-function-name-error name))))

(defsetf FDEFINITION (name) (fn)
  `(cond
    ((symbolp ,name)
     (setf (SYMBOL-FUNCTION ,name) ,fn))
    ((setf-name-p ,name)
     (puthash (second ,name) ,fn *setf-definitions*))
    (t
     (not-function-name-error ,name))))

(defun FBOUNDP (name)
  (cond
    ((symbolp name)
     (if (SPECIAL-OPERATOR-P name)
	 'T
	 (fboundp name)))
    ((setf-name-p name)
     (not (null (gethash (second name) *setf-definitions*))))
    (t
     (not-function-name-error name))))
    
(defun FMAKUNBOUND (name)
  (cond
    ((symbolp name)
     (fmakunbound name)
     (remhash name *macro-functions*))
    ((setf-name-p name)
     (remhash (second name) *setf-definitions*))
    (t
     (not-function-name-error name)))
  name)
    
;;; Special operators: FLET, LABELS, MACROLET

(defun FUNCALL (fn &rest args)
  (cond
    ((COMPILED-FUNCTION-P fn)
     (apply fn args))
    ((INTERPRETED-FUNCTION-P fn)
     (eval-lambda-expr (interp-fn-lambda-exp fn)
		       args
		       (interp-fn-env fn)))
    ((functionp fn)
     (apply fn args))
    (t
     (APPLY (FDEFINITION fn) args))))

;;; Special operator: FUNCTION

(defun FUNCTION-LAMBDA-EXPRESSION (fn)
  (cond
    ((INTERPRETED-FUNCTION-P fn)	(cl:values (interp-fn-lambda-exp fn)
						   T nil))
    ((subrp fn)				(cl:values nil nil nil))
    ((byte-code-function-p fn)		(cl:values nil nil nil))
    ((FUNCTIONP fn)			(cl:values nil T nil))
    (t					(type-error fn 'FUNCTION))))

(defun FUNCTIONP (object)
  (or (byte-code-function-p object)
      (subrp object)
      (INTERPRETED-FUNCTION-P object)))

(defun COMPILED-FUNCTION-P (object)
  (or (byte-code-function-p object)
      (subrp object)))

(defvar *constants* '(nil T PI))

(defmacro* DEFCONSTANT (name initial-value &optional documentation)
  `(eval-when (:compile-toplevel :load-toplevel :execute)
     (defconst ,name ,initial-value
       ,@(when documentation `(,documentation)))
     (pushnew ',name *constants*)
     ',name))

(cl:defmacro DEFCONSTANT (name initial-value &optional documentation)
  (with-gensyms (value)
    `(EVAL-WHEN (,(kw COMPILE-TOPLEVEL) ,(kw LOAD-TOPLEVEL) ,(kw EXECUTE))
       (PUSHNEW (QUOTE ,name) *constants*)
       (LET ((,value ,initial-value))
	 (WHEN (AND (BOUNDP (QUOTE ,name))
		    (NOT (EQL ,name ,value)))
	   (WARN "Redefining constant ~S." (QUOTE ,name)))
	 ;; Using Emacs Lisp set lets of sneak by the access check
	 ;; that Common Lisp SETQ does for constants.
	 (set (QUOTE ,name) ,value))
       (QUOTE ,name))))

(DEFCONSTANT CALL-ARGUMENTS-LIMIT 50)

(DEFCONSTANT LAMBDA-LIST-KEYWORDS
  '(&ALLOW-OTHER-KEYS &AUX &BODY &ENVIRONMENT &KEY &OPTIONAL &REST &WHOLE))

(DEFCONSTANT LAMBDA-PARAMETERS-LIMIT 50)

(defvar *specials* (list '*MACROEXPAND-HOOK*))

(defmacro DEFVAR (name &rest rest)
  `(progn
    (pushnew ',name *specials*)
    (defvar ,name ,@rest)))

(cl:defmacro DEFVAR (name &optional (initial-value nil valuep) documentation)
  `(PROGN
     (EVAL-WHEN (,(kw COMPILE-TOPLEVEL) ,(kw LOAD-TOPLEVEL) ,(kw EXECUTE))
       (DECLAIM (SPECIAL ,name)))
     (EVAL-WHEN (,(kw LOAD-TOPLEVEL) ,(kw EXECUTE))
       ,@(when valuep
	   `((UNLESS (BOUNDP (QUOTE ,name))
	       (SETQ ,name ,initial-value))))
       (QUOTE ,name))))

(cl:defmacro DEFPARAMETER (name initial-value &optional documentation)
  `(PROGN
     (EVAL-WHEN (,(kw COMPILE-TOPLEVEL) ,(kw LOAD-TOPLEVEL) ,(kw EXECUTE))
       (DECLAIM (SPECIAL ,name)))
     (EVAL-WHEN (,(kw LOAD-TOPLEVEL) ,(kw EXECUTE))
       (SETQ ,name ,initial-value)
       (QUOTE ,name))))

(defun lambda-list-keyword-p (x)
  (member x LAMBDA-LIST-KEYWORDS))

(defun dotted-memq (item list)
  (let ((result nil))
    (while (consp list)
      (if (eq (car list) item)
	  (setq result list list nil)
	  (setq list (cdr list))))
    result))

(defun destructure (lambda-list list)
  (let ((result nil)
	(current nil)
	(seen-&rest nil)
	(seen-&key nil))
    (do-lambda-list (((key var) default supp) kind lambda-list)
      (setq current
	    (case kind
	      (&WHOLE		(if (eql (length lambda-list) 2)
				    `(PROG1 ,list (SETQ ,list nil))
				    list))
	      (:required	`(IF ,list
				     (POP ,list)
				     (ERROR (QUOTE PROGRAM-ERROR))))
	      (&OPTIONAL	`(PROGN
				   ,@(when supp
				       `((SETQ ,supp (NOT (NULL ,list)))))
				   (IF ,list (POP ,list) ,default)))
	      ((&REST &BODY)	(setq seen-&rest t)
				list)
	      (&KEY		(setq seen-&key t)
				(with-gensyms (foo val valp)
				  `(MULTIPLE-VALUE-BIND (,foo ,val ,valp)
				       (GET-PROPERTIES ,list (QUOTE (,key)))
				    ,@(when supp
				        `((SETQ ,supp (NOT (NULL ,valp)))))
				    (REMF ,list (QUOTE ,key))
				    (IF ,valp ,val ,default))))
	      (&AUX		default)
	      (t		(ERROR "~S not allowed in destructuring."
				       kind))))
      (if (symbolp var)
	  (push `(SETQ ,var ,current) result)
	  (let ((sublist (gensym)))
	    (push `(LET ((,sublist ,current))
		     ,@(destructure var sublist))
		  result))))
    (cond
      ((dotted-memq '&ALLOW-OTHER-KEYS lambda-list))
      (seen-&key
       (push `(WHEN (AND ,list (NOT (GETF ,list ,(kw ALLOW-OTHER-KEYS-P))))
	        (ERROR (QUOTE PROGRAM-ERROR)))
	     result))
      (seen-&rest)
      (t
       (push `(WHEN ,list
	        (ERROR (QUOTE PROGRAM-ERROR)))
	     result)))
    (nreverse result)))

(cl:defmacro DESTRUCTURING-BIND (lambda-list form &body forms)
  (with-gensyms (list)
    (MULTIPLE-VALUE-BIND (body decls) (parse-body forms)
      `(LET ,(lambda-list-variables lambda-list)
	 ,@(when decls `((DECLARE ,@decls)))
	 (LET ((,list ,form))
	   ,@(destructure lambda-list list))
	 (PROGN ,@body)))))

;;; Special Operators: LET, LET*

;;; Special Operator: PROGV

;;; Special Operator: SETQ

(cl:defmacro PSETQ (&rest forms)
  `(PSETF ,@forms))

;;; Special Operator: BLOCK

;;; Special Operator: CATCH

;;; Special Operator: GO

;;; Special Operator: RETURN-FROM

(cl:defmacro RETURN (&optional form)
  `(RETURN-FROM nil ,form))

;;; Special Operator: TAGBODY

;;; Special Operator: THROW

;;; Special Operator: UNWIND-PROTECT

;;; Constant Variable: NIL

(defun NOT (x)
  (if x nil 'T))

(DEFCONSTANT T 'T)

(fset 'EQ (symbol-function 'eq))

(defun EQL (x y)
  (or (eq x y)
      (cond
	((and (CHARACTERP x) (CHARACTERP y))
	 (eq (CHAR-CODE x) (CHAR-CODE y)))
	((and (floatp x) (floatp y))
	 (equal x y))
	((and (bignump x) (bignump y))
	 (and (eq (length x) (length y))
	      (every #'eq x y)))
	((and (ratiop x) (ratiop y))
	 (and (EQL (NUMERATOR x) (NUMERATOR y))
	      (EQL (DENOMINATOR x) (DENOMINATOR y))))
	((and (COMPLEXP x) (COMPLEXP y))
	 (and (EQL (REALPART x) (REALPART y))
	      (EQL (IMAGPART x) (IMAGPART y))))
	(t
	 nil))))

(defun EQUAL (x y)
  (or (EQL x y)
      (cond
	((and (consp x) (consp y))
	 (and (EQUAL (car x) (car y))
	      (EQUAL (cdr x) (cdr y))))
	((and (STRINGP x) (STRINGP y))
	 (and (eq (LENGTH x) (LENGTH y))
	      (EVERY #'CHAR= x y)))
	((and (BIT-VECTOR-P x) (BIT-VECTOR-P y))
	 (and (eq (LENGTH x) (LENGTH y))
	      (EVERY #'EQL x y)))
	((and (PATHNAMEP x) (PATHNAMEP y))
	 ;; TODO: pathnames
	 (and (EQUAL (pathname-host x) (pathname-host y))
	      (EQUAL (pathname-device x) (pathname-device y))
	      (EQUAL (pathname-directory x) (pathname-directory y))
	      (EQUAL (pathname-name x) (pathname-name y))
	      (EQUAL (pathname-type x) (pathname-type y))
	      (EQUAL (pathname-version x) (pathname-version y))))
	(t
	 nil))))

(defun EQUALP (x y)
  (or (EQUAL x y)
      (cond
	((and (CHARACTERP x) (CHARACTERP y))
	 (CHAR-EQUAL x y))
	((and (NUMBERP x) (NUMBERP y))
	 (cl:= x y))
	((and (consp x) (consp y))
	 (and (EQUAL (car x) (car y))
	      (EQUAL (cdr x) (cdr y))))
	((and (VECTORP x) (VECTORP y))
	 (and (eq (LENGTH x) (LENGTH y))
	      (EVERY #'EQUALP x y)))
	((and (ARRAYP x) (ARRAYP y))
	 (and (equal (ARRAY-DIMENSIONS x) (ARRAY-DIMENSIONS y))
	      (catch 'result
		(dotimes (i (ARRAY-TOTAL-SIZE x) 'T)
		  (unless (EQUALP (ROW-MAJOR-AREF x i)
				  (ROW-MAJOR-AREF y i))
		    (throw 'result nil))))))
	;; TODO: structures and hash tables
	(t
	 nil))))

(cl:defun IDENTITY (object)
  object)

(defun COMPLEMENT (fn)
  (let ((env (augment-environment nil :variable '(fn)))
	(name "complemented function"))
    (setf (lexical-value 'fn env) fn)
    (enclose '(LAMBDA (&REST args) (NOT (APPLY fn args))) env name)))

(defun CONSTANTLY (value)
  (let ((env (augment-environment nil :variable '(value))))
    (setf (lexical-value 'value env) value)
    (enclose '(LAMBDA (&REST x) value) env
	     (format "\"constantly %s\"" (PRIN1-TO-STRING value)))))

(defun EVERY (predicate &rest sequences)
  (catch 'EVERY
    (apply #'MAP nil
	   (lambda (&rest elts)
	     (unless (APPLY predicate elts)
	       (throw 'EVERY nil)))
	   sequences)
    T))

(defun SOME (predicate &rest sequences)
  (catch 'SOME
    (apply #'MAP nil
	   (lambda (&rest elts)
	     (let ((val (APPLY predicate elts)))
	       (when val
		 (throw 'SOME val))))
	   sequences)
    nil))

(defun NOTEVERY (predicate &rest sequences)
  (not (apply #'EVERY predicate sequences)))

(defun NOTANY (predicate &rest sequences)
  (not (apply #'SOME predicate sequences)))

(cl:defmacro AND (&rest forms)
  (cond
    ((null forms)
     T)
    ((null (rest forms))
     (first forms))
    (t
     `(IF ,(first forms) (AND ,@(rest forms))))))

(cl:defmacro COND (&rest clauses)
  (if (null clauses)
      nil
      (let ((clause (first clauses)))
	(case (length clause)
	  (0	(ERROR 'PROGRAM-ERROR))
	  (1	`(OR ,(first clause) (COND ,@(rest clauses))))
	  (t	`(IF ,(first clause)
		     (PROGN ,@(rest clause))
		     (COND ,@(rest clauses))))))))

;;; Special Operator: IF

(cl:defmacro OR (&rest forms)
  (cond
    ((null forms)		nil)
    ((null (rest forms))	(first forms))
    (t				(with-gensyms (x)
				  `(LET ((,x ,(first forms)))
				    (IF ,x ,x (OR ,@(rest forms))))))))

(cl:defmacro WHEN (condition &body body)
  `(IF ,condition (PROGN ,@body)))

(cl:defmacro UNLESS (condition &body body)
  `(IF ,condition nil (PROGN ,@body)))

(cl:defmacro CASE (form &rest clauses)
  (let ((val (gensym))
	(seen-otherwise nil))
    `(LET ((,val ,form))
       (COND
	 ,@(mapcar (destructuring-lambda ((key &rest forms))
		     (when seen-otherwise
		       (ERROR 'PROGRAM-ERROR))
		     (setq seen-otherwise
			   (memq key '(T OTHERWISE)))
		     (cond
		       (seen-otherwise
			`(T (PROGN ,@forms)))
		       ((null key)
			'(nil))
		       ((atom key)
			`((EQL ,val (QUOTE ,key))
			  (PROGN ,@forms)))
		       (t
			`((MEMBER ,val (QUOTE ,key))
			  (PROGN ,@forms)))))
		   clauses)))))

(cl:defmacro CCASE (place &rest clauses)
  (with-gensyms (block loop)
    `(BLOCK ,block
       (TAGBODY
	 ,loop
	 (RESTART-BIND ((STORE-VALUE (LAMBDA (object)
				       (SETF ,place object)
				       (GO ,loop))))
	   (RETURN-FROM ,block (ECASE ,place ,@clauses)))))))

(cl:defmacro ECASE (form &rest clauses)
  (with-gensyms (val)
    `(LET ((,val ,form))
       (CASE ,val
	 ,@(mapcar (destructuring-lambda ((&whole clause key &rest forms))
		     (if (memq key  '(T OTHERWISE))
			 `((,key) ,@forms)
			 clause))
		   clauses)
	 (T (type-error ,val (QUOTE (MEMBER ,@(mappend
					       (lambda (x)
						 (ensure-list (first x)))
					       clauses)))))))))

(cl:defmacro TYPECASE (form &rest clauses)
  (let ((val (gensym))
	(seen-otherwise nil))
    `(LET ((,val ,form))
       (COND
	 ,@(mapcar (destructuring-lambda ((key &rest forms))
		     (when seen-otherwise
		       (ERROR (QUOTE PROGRAM-ERROR)))
		     (setq seen-otherwise
			   (memq key '(T OTHERWISE)))
		     `(,(if seen-otherwise
			    T
			    `(TYPEP ,val (QUOTE ,key)))
		       (PROGN ,@forms)))
		   clauses)))))

(cl:defmacro CTYPECASE (place &rest clauses)
  (with-gensyms (block loop)
    `(BLOCK ,block
       (TAGBODY
	 ,loop
	 (RESTART-BIND ((STORE-VALUE (LAMBDA (object)
				       (SETF ,place object)
				       (GO ,loop))))
	   (RETURN-FROM ,block (ETYPECASE ,place ,@clauses)))))))

(cl:defmacro ETYPECASE (form &rest clauses)
  (with-gensyms (val)
    `(LET ((,val ,form))
       (TYPECASE ,val
	 ,@clauses
	 ,@(unless (some (lambda (clause) (eq (first clause) T)) clauses)
	    `((T (type-error ,val
		             (QUOTE (OR ,@(mapcar #'first clauses)))))))))))

(defmacro* MULTIPLE-VALUE-BIND (vars form &body body)
  (case (length vars)
    (0	`(progn ,form ,@body))
    (1	`(let ((,(first vars) ,form)) ,@body))
    (t	(let ((n -1))
	  `(let* ((,(first vars) ,form)
		  ,@(mapcar (lambda (var) `(,var (nth ,(incf n) mvals)))
			    (rest vars)))
	     ,@body)))))

(cl:defmacro MULTIPLE-VALUE-BIND (vars form &body body)
  (case (length vars)
    (0	`(PROGN ,form ,@body))
    (1	`(LET ((,(first vars) ,form)) ,@body))
    (t	(with-gensyms (ignore)
	  `(MULTIPLE-VALUE-CALL
	    (LAMBDA (&OPTIONAL ,@vars &REST ,ignore) ,@body) ,form)))))

;;; MULTIPLE-VALUE-CALL is a special operator.

(defmacro* MULTIPLE-VALUE-LIST (form)
  (let ((val (gensym)))
    `(let ((,val ,form))
       (if (zerop nvals)
	   nil
	   (cons ,val mvals)))))

(cl:defmacro MULTIPLE-VALUE-LIST (form)
  `(MULTIPLE-VALUE-CALL (FUNCTION LIST) ,form))

;;; MULTIPLE-VALUE-PROG1 is a special operator.

(defmacro* MULTIPLE-VALUE-SETQ (vars form)
  (if (null vars)
      form
      (let ((n -1))
	`(setq ,(first vars) ,form
	       ,@(mappend (lambda (var) `(,var (nth ,(incf n) mvals)))
			  (rest vars))))))

(cl:defmacro MULTIPLE-VALUE-SETQ (vars form)
  (let ((vals (gensym))
	(n -1))
    `(LET ((,vals (MULTIPLE-VALUE-LIST ,form)))
       (SETQ ,@(mappend (lambda (var) `(,var (NTH ,(incf n) ,vals))) vars))
       (FIRST ,vals))))

(defun VALUES (&rest vals)
  (VALUES-LIST vals))

(defun VALUES-LIST (list)
  (setq nvals (length list))
  (setq mvals (cdr-safe list))
  (car list))

(DEFCONSTANT MULTIPLE-VALUES-LIMIT 20)

(defmacro* NTH-VALUE (n form)
  (cond
    ((eq n 0)		`(cl:values ,form))
    ((integerp n)	`(progn ,form (cl:values (nth ,(1- n) mvals))))
    (t			`(progn ,form (cl:values (nth (1- ,n) mvals))))))

(cl:defmacro NTH-VALUE (n form)
  `(NTH ,n (MULTIPLE-VALUE-LIST ,form)))

(defun expand-prog (let bindings body)
  (MULTIPLE-VALUE-BIND (body decl) (parse-body body)
    `(BLOCK nil
       (,let ,bindings
	 (DECLARE ,@decl)
	 (TAGBODY ,@body)))))

(cl:defmacro PROG (bindings &body body)
  (expand-prog 'LET bindings body))

(cl:defmacro PROG* (bindings &body body)
  (expand-prog 'LET* bindings body))

(cl:defmacro PROG1 (form1 &rest forms)
  (with-gensyms (val)
    `(LET ((,val ,form1))
       ,@forms
       ,val)))

(cl:defmacro PROG2 (form1 form2 &rest forms)
  (with-gensyms (val)
    `(PROGN
       ,form1
       (LET ((,val ,form2))
	 ,@forms
	 ,val))))

;;; Special Operator: PROGN

(cl:defmacro DEFINE-MODIFY-MACRO (name lambda-list fn &optional documentation)
  (with-gensyms (place env temps values variables setter getter)
    `(DEFMACRO ,name (,place ,@lambda-list &ENVIRONMENT ,env)
       ,documentation
       (MULTIPLE-VALUE-BIND (,temps ,values ,variables ,setter ,getter)
	   (GET-SETF-EXPANSION ,place ,env)
	 (BACKQUOTE
	   (LET* ((COMMA-AT (MAPCAR (FUNCTION LIST) ,temps ,values))
		  ((COMMA (FIRST ,variables))
		   ;; TODO: only params from lambda-list
		   (,fn (COMMA ,getter) ,@lambda-list)))
	     (COMMA ,setter)))))))

(defmacro* DEFSETF (access-fn &rest args)
  (case (length args)
    (0 (ERROR "Syntax error"))
    (1 (short-form-defsetf access-fn (first args)))
    (t (apply #'long-form-defsetf access-fn args))))

(defun short-form-defsetf (access-fn update-fn)
  `(DEFINE-SETF-EXPANDER ,access-fn (&rest args)
     (let ((var (gensym))
	   (temps (map-to-gensyms args)))
       (cl:values temps
		  args
		  (list var)
		  (append '(,update-fn) temps (list var))
		  (list* ',access-fn temps)))))

(defun* long-form-defsetf (access-fn lambda-list variables &body body)
  (let ((args (remove-if (lambda (x) (memq x '(&optional &rest &key)))
			 lambda-list)))
    `(DEFINE-SETF-EXPANDER ,access-fn ,lambda-list
       (let* ((var (gensym))
	     (temps (map-to-gensyms ',args))
	     (,(first variables) var))
	 (cl:values temps
		    (list ,@args)
		    (list var)
		    (apply (lambda ,lambda-list ,@body) temps)
		    (cons ',access-fn temps))))))

(cl:defmacro DEFSETF (access-fn &rest args)
  (case (length args)
    (0	(ERROR "Syntax error"))
    (1	(cl-short-form-defsetf access-fn (first args)))
    (2	(cond
	  ((STRINGP (second args))
	   (cl-short-form-defsetf access-fn (first args) (second args)))
	  ((listp (second args))
	   (apply #'cl-long-form-defsetf access-fn args))
	  (t
	   (type-error (second args) '(OR STRING LIST)))))
    (t	(apply #'cl-long-form-defsetf access-fn args))))

(defun cl-short-form-defsetf (access-fn update-fn &optional doc)
  (with-gensyms (args var temps)
    `(DEFINE-SETF-EXPANDER ,access-fn (&REST ,args)
      (LET ((,var (GENSYM))
	    (,temps (map-to-gensyms ,args)))
	(VALUES ,temps
		,args
		(LIST ,var)
		(BACKQUOTE (,update-fn (COMMA-AT ,temps) (COMMA ,var)))
		(BACKQUOTE (,access-fn (COMMA-AT ,temps))))))))

(defun* cl-long-form-defsetf (access-fn lambda-list variables &body body)
  (let ((args (remove-if (lambda (x) (memq x LAMBDA-LIST-KEYWORDS))
			 lambda-list)))
    (with-gensyms (var temps)
      `(DEFINE-SETF-EXPANDER ,access-fn ,lambda-list
	(LET* ((,var (GENSYM))
	       (,temps (map-to-gensyms (QUOTE ,args)))
	       (,(first variables) ,var))
	  (VALUES ,temps
		  (LIST ,@args)
		  (LIST ,var)
		  (APPLY (LAMBDA ,lambda-list ,@body) ,temps)
		  (BACKQUOTE (,access-fn (COMMA-AT ,temps)))))))))

(defvar *setf-expanders* (make-hash-table))

(defmacro* DEFINE-SETF-EXPANDER (access-fn lambda-list &body body)
  `(eval-when (:compile-toplevel :load-toplevel :execute)
     (setf (gethash ',access-fn *setf-expanders*)
           ,(make-macro-el-function access-fn lambda-list body))
     ',access-fn))

(cl:defmacro DEFINE-SETF-EXPANDER (access-fn lambda-list &body body)
  `(EVAL-WHEN (,(kw COMPILE-TOPLEVEL) ,(kw LOAD-TOPLEVEL) ,(kw EXECUTE))
      (puthash (QUOTE ,access-fn) 
               ,(make-macro-function access-fn lambda-list body)
	       *setf-expanders*)
      (QUOTE ,access-fn)))

(DEFINE-SETF-EXPANDER VALUES (&rest forms)
  (let ((temporaries nil)
	(values nil)
	(vars nil)
	(setters nil)
	(getters nil))
    (dolist (form forms)
      (MULTIPLE-VALUE-BIND (temps vals variables setter getter)
	  (GET-SETF-EXPANSION form nil) ;TODO: env
	(setq temporaries (append temporaries temps))
	(setq values (append values vals))
	(push (first variables) vars)
	(push setter setters)
	(push getter getters)))
    (cl:values temporaries
	       values
	       (nreverse vars)
	       `(PROGN ,@(nreverse setters))
	       `(VALUES ,@(nreverse getters)))))

(DEFSETF FDEFINITION (name) (fn)
  `(COND
    ((SYMBOLP ,name)
     (SETF (SYMBOL-FUNCTION ,name) ,fn))
    ((setf-name-p ,name)
     (puthash (SECOND ,name) ,fn *setf-definitions*))
    (T
     (not-function-name-error ,name))))

(DEFSETF MACRO-FUNCTION (name &optional env) (fn)
  `(IF (NULL ,env)
       (puthash ,name ,fn *macro-functions*)
       (set-local-macro ,name ,fn ,env)))

(DEFSETF COMPILER-MACRO-FUNCTION (name &optional env) (fn)
  `(puthash ,name ,fn *compiler-macro-functions*))

(DEFINE-SETF-EXPANDER THE (type form)
  (MULTIPLE-VALUE-BIND (temps values variables setter getter)
      (GET-SETF-EXPANSION form nil) ;TODO: env
    (with-gensyms (val)
      (cl:values temps
		 values
		 (list val)
		 `(LET ((,(first variables) (THE ,type ,val))) ,setter)
		 getter))))

(defun GET-SETF-EXPANSION (place &optional env)
  (cond
   ((consp place)
    (let* ((name (car place))
	   (fn (gethash name *setf-expanders*)))
      (if fn
	  (FUNCALL fn place env)
	  (MULTIPLE-VALUE-BIND (place expandedp) (MACROEXPAND place env)
	    (if expandedp
		(GET-SETF-EXPANSION place env)
		(let ((temps (map-to-gensyms (rest place)))
		      (var (gensym)))
		  (cl:values temps
			     (rest place)
			     (list var)
			     `(FUNCALL (FUNCTION (SETF ,name)) ,var ,@temps)
			     `(,name ,@temps))))))))
   ((symbolp place)
    (if (eq (nth-value 0 (variable-information place env)) :symbol-macro)
	(GET-SETF-EXPANSION (MACROEXPAND place env) env)
	(let ((var (gensym)))
	  (cl:values nil nil (list var) `(SETQ ,place ,var) place))))
   (t
    (type-error place '(OR CONS SYMBOL)))))

(defmacro* SETF (place value &rest more &environment env)
  (MULTIPLE-VALUE-BIND (temps values variables setter getter)
      (GET-SETF-EXPANSION place env)
    `(let* (,@(MAPCAR #'list temps values)
	    (,(first variables) ,value))
       ,setter
       ,@(when more
	   `((SETF ,@more))))))

(cl:defmacro SETF (&rest forms &environment env)
  (when (oddp (length forms))
    (ERROR 'PROGRAM-ERROR))
  (when (not (null forms))
    (let ((place (first forms))
	  (value (second forms))
	  (more (cddr forms)))
      (MULTIPLE-VALUE-BIND (temps values variables setter getter)
	  (GET-SETF-EXPANSION place env)
	`(LET* ,(MAPCAR #'list temps values)
	   (MULTIPLE-VALUE-BIND ,variables ,value
	     ,setter
	     ,(if more
		  `(SETF ,@more)
		  `(VALUES ,@variables))))))))

(cl:defmacro PSETF (&rest forms &environment env)
  (when (oddp (length forms))
    (ERROR 'PROGRAM-ERROR))
  (when (not (null forms))
    (let ((place (first forms))
	  (value (second forms))
	  (more (cddr forms)))
      (MULTIPLE-VALUE-BIND (temps values variables setter getter)
	  (GET-SETF-EXPANSION place env)
	`(LET* ,(MAPCAR #'list temps values)
	   (MULTIPLE-VALUE-BIND ,variables ,value
	     ,@(when more
	         `((PSETF ,@more)))
	     ,setter
	     nil))))))

(cl:defmacro SHIFTF (place x &rest more) ;TODO: &environment
  (MULTIPLE-VALUE-BIND (temps values variables setter getter)
      (GET-SETF-EXPANSION place)
    (with-gensyms (val)
      `(LET* (,@(MAPCAR #'list temps values)
	      (,val ,getter)
	      (,(first variables) ,(if (null more) x `(SHIFTF ,x ,@more))))
	 ,setter
	 ,val))))

(cl:defmacro ROTATEF (&rest places) ;TODO: &environment
  (if (or (null places) (null (rest places)))
      nil
      (let ((place (first places))
	    (places (rest places))
	    (val (gensym)))
      (MULTIPLE-VALUE-BIND (temps values variables setter getter)
	  (GET-SETF-EXPANSION place env)
	`(LET* (,@(MAPCAR #'list temps values)
		(,val ,getter)
		(,(first variables) (SHIFTF ,@places ,val)))
	   ,setter
	   nil)))))
    
;;; CONTROL-ERROR, PROGRAM-ERROR, and UNDEFINED-FUNCTION are defined
;;; in cl-conditions.el.
