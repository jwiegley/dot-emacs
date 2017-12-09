;;;; -*- emacs-lisp -*-
;;;
;;; Copyright (C) 2003, 2004 Lars Brinkhoff.
;;; This file provides cl:lambda, cl:function, and cl:defun.

(defmacro cl:function (name)
  (let ((fn (FDEFINITION name)))
    (if (subrp fn)
	;; Have to return symbol since #<subr ...> in .elc isn't readable.
	`',name
	fn)))

(defmacro cl:defun (name lambda-list &rest body)
  (when byte-compile-warnings
    (byte-compile-log-1 (format "cl:defun %s" name)))
  `(progn
     (fset ',name (cl:lambda ,lambda-list ,@body))
     ',name))

(defmacro parse-parameter (p kind k v i s err)
  `(cond
    ((or (symbolp ,p) (not (memq ,kind '(&OPTIONAL &KEY &AUX))))
     (when (and ',k (eq ,kind '&KEY) (not (listp ,p)))
       (setq ,k (keyword (symbol-name ,p))))
     (when ',v (setq ,v ,p)))
    ((and (consp ,p) (<= (length ,p) 3))
     (cond
       ((or (symbolp (first ,p)) (not (eq ,kind '&KEY)))
	(when (and ',k (eq ,kind '&KEY))
	  (setq ,k (keyword (symbol-name (first ,p)))))
	(when ',v (setq ,v (first ,p))))
       ((and (consp (first ,p)) (= (length (first ,p)) 2))
	(when ',k (setq ,k (first (first ,p))))
	(when ',v (setq ,v (second (first ,p)))))
       (t
	,err))
     (when ',i (setq ,i (second ,p)))
     (when ',s (setq ,s (third ,p))))
    (t
     ,err)))

(defmacro* do-lambda-list ((var kind lambda-list &optional result
			    &key (keywords 'LAMBDA-LIST-KEYWORDS))
			   &body body)
  (let ((keyword-var nil)
	(var-var nil)
	(default-var nil)
	(supplied-var nil)
	(v (gensym)))
    (parse-parameter var '&KEY keyword-var var-var default-var supplied-var
		     (error "Syntax error in do-lambda-list."))
    (with-gensyms (list)
      `(do ((,kind :required)
	    (,list ,lambda-list (rest ,list)))
	   ((atom ,list)
	    (unless (null ,list)
	      (setq ,kind '&REST)
	      (let (,@(when keyword-var `((,keyword-var nil)))
		    ,@(when var-var `((,var-var ,list)))
		    ,@(when default-var `((,default-var nil)))
		    ,@(when supplied-var `((,supplied-var nil))))
		,@body))
	    ,result)
	 (let ((,v (car ,list)))
	   (if (memq ,v ,keywords)
	       (setq ,kind ,v)
	       (let ,(remove nil (list var-var keyword-var
				       default-var supplied-var))
		 (parse-parameter ,v ,kind ,keyword-var ,var-var ,default-var
				  ,supplied-var (ERROR 'PROGRAM-ERROR))
		 ,@body
		 (when (memq ,kind '(&ENVIRONMENT &WHOLE))
		   (setq ,kind :required)))))))))

;;; Allowed lambda list keywords:
;;; Ordinary		&optional &rest &key &allow-other-keys &aux
;;; Generic Function	&optional &rest &key &allow-other-keys
;;; Specialized		&optional &rest &key &allow-other-keys &aux
;;; Macro		&whole &optional &rest &body &key &allow-other-keys
;;;			&aux &environment
;;; Destructuring	&whole &optional &rest &body &key &allow-other-keys
;;;			&aux
;;; Boa			Same as Ordinary.
;;; Defsetf		&optional &rest &key &allow-other-keys &environment
;;; Deftype		Same as Macro.
;;; Define-modify-macro	&optional &rest
;;; Define-method-combination
;;;			&whole &optional &rest &key &allow-other-keys &aux

(defvar rest-sym (make-symbol "rest"))

(defvar unbound (make-symbol "unbound"))

(defun* simplify-lambda-list (lambda-list &optional env)
  (let ((result nil)
	(push-optional t))
    (do-lambda-list ((var default supp) kind lambda-list)
      (case kind
        (&OPTIONAL
         (when push-optional
	   (push '&optional result)
	   (setq push-optional nil)))
        ((&REST &KEY)
         (push '&rest result)
         (push rest-sym result)
         (return-from simplify-lambda-list (nreverse result)))
	(&AUX
         (return-from simplify-lambda-list (nreverse result))))
      (when (or default supp)
         (when (eq (car result) '&optional)
           (pop result))
         (push '&rest result)
         (push rest-sym result)
         (return-from simplify-lambda-list (nreverse result)))
      (push (if env (compile-variable var env) var)
	    result))
    (nreverse result)))

(defun* lambda-list-bindings (lambda-list env)
  (let ((bindings nil)
	(optional-rest nil))
    (do-lambda-list ((var default supp) kind lambda-list)
      (when env
	(setq var (compile-variable var env))
	(when supp
	  (setq supp (compile-variable supp env))))
      (case kind
	(&OPTIONAL
	 (when (or default supp)
	   (setq optional-rest t))
	 (when optional-rest
	   (when supp
	     (push `(,supp ,rest-sym) bindings))
	   (when env
	     (setq default (compile-form default env)))
	   (push `(,var (if ,rest-sym (pop ,rest-sym) ,default))
		 bindings)))
	(&REST
	 (push `(,var ,rest-sym) bindings))
	(&KEY
	 (push `(,var ',unbound) bindings)
	 (when supp
	   (push `(,supp nil) bindings)))
	(&AUX
	 (push var bindings))))
    (nreverse bindings)))

(defun lambda-list-keys (lambda-list)
  (with-collector collect
    (do-lambda-list (((key var)) kind lambda-list)
      (when (eq kind '&KEY)
	(collect key)))))

(defun lambda-list-keyword-vars (lambda-list env &optional include-supplied)
  (with-collector collect
    (do-lambda-list ((var nil supp) kind lambda-list)
      (when (eq kind '&KEY)
	(collect (if env (lexical-value var env) var))
	(when (and supp include-supplied)
	  (collect (if env (lexical-value supp env) supp)))))))

(defun lambda-list-keyword-defaults (lambda-list)
  (with-collector collect
    (do-lambda-list ((var default) kind lambda-list)
      (when (eq kind '&KEY)
	(collect default)))))

(defun load-time-symbol (sym)
  (if (or (not (boundp '*keyword-package*))
	  (eq (SYMBOL-PACKAGE sym) *keyword-package*))
      `(keyword ,(symbol-name sym))
      `(INTERN ,(symbol-name sym) ,(PACKAGE-NAME (SYMBOL-PACKAGE sym)))))

(defun keyword-assignments (lambda-list env)
  (let ((allow-other-keys-p (memq '&ALLOW-OTHER-KEYS lambda-list))
	(temp (gensym))
	(allow (gensym))
	(val (gensym))
	(keys (lambda-list-keys lambda-list))
	(vars (lambda-list-keyword-vars lambda-list env))
	(defaults (lambda-list-keyword-defaults lambda-list)))
    (when keys
      (let* ((list `(list ,@(mapcar #'load-time-symbol keys)))
	     (keyword-list
	      (if (eval-when-compile (featurep 'xemacs))
		  list
		  `(load-time-value ,list)))
	     (body
	      `((while ,rest-sym
		  (let ((,temp (position (pop ,rest-sym) ,keyword-list)) ,val)
		    ,@(unless allow-other-keys-p
		       `((unless (or ,temp ,allow) (ERROR 'PROGRAM-ERROR))))
		    (when (null ,rest-sym)
		      (ERROR 'PROGRAM-ERROR))
		    (setq ,val (pop ,rest-sym))
		    (when ,temp
		      (set (nth ,temp ',vars) ,val))))
		,@(mappend (lambda (var default)
			     `((when (eq ,var ',unbound)
				 (setq ,var
				       ,(if env
					    (compile-form default env)
					    default)))))
			   vars defaults))))
	(unless allow-other-keys-p
	  (setq body
		`((let ((,allow (cadr (memq (kw ALLOW-OTHER-KEYS) ,rest-sym))))
		    ,@body))))
	body))))

(defun aux-assignments (lambda-list env)
  (let ((bindings nil))
    (do-lambda-list ((var default) kind lambda-list)
      (when (and (eq kind '&AUX)
		 default)
	(when env
	  (setq var (compile-variable var env)
		default (compile-form default env)))
	(push `(,var ,default) bindings)))
    (when bindings
      `((setq ,@(nreverse bindings))))))

(defun translate-lambda-list (lambda-list env)
  (mapcar (lambda (x)
	    (let ((cons (assq x '((&OPTIONAL . &optional) (&REST . &rest)))))
	      (cond
		(cons	(cdr cons))
		(env	(compile-variable x env))
		(t	x))))
	  lambda-list))

(defun lambda-list-variables (lambda-list)
  (let ((result nil))
    (do-lambda-list ((var default supp) kind lambda-list)
      (if (symbolp var)
	  (push var result)
	  (setq result (nconc result (lambda-list-variables var))))
      (when supp (push supp result)))
    result))

(defun expand-lambda (lambda-list body &optional env)
  (if (and (every 'symbolp lambda-list)
	   (notany (lambda (x) (memq x '(&KEY &AUX))) lambda-list))
      ;; Easy case: no defaults, suppliedp, keyword, or aux parameters.
      `(lambda ,(translate-lambda-list lambda-list env) ,@body)
      ;; Difficult case:
      `(lambda ,(simplify-lambda-list lambda-list env)
	(let* ,(lambda-list-bindings lambda-list env)
;; 	  ,@(unless (or (memq '&REST lambda-list) (memq '&KEY lambda-list))
;; 	      `((when ,rest-sym
;; 		  (ERROR 'PROGRAM-ERROR))))
	  ,@(keyword-assignments lambda-list env)
	  ,@(aux-assignments lambda-list env)
	  ,@body))))

(defmacro cl:lambda (lambda-list &rest body)
;  (byte-compile
   (expand-lambda lambda-list body));)
